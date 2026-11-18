From Stdlib Require Import ZArith List String Bool Arith Lia.
From SpatialCSL Require Import SpadaIR SpadaDataflow SpadaRaces SpadaDeadlock Summa.
Import ListNotations Spada.
Open Scope list_scope.
Open Scope nat_scope.

(** * Correctness of the SUMMA kernels under the dataflow semantics

    The proofs are about the IR terms [Summa.lower (Gemm example_dims o)]
    (P=2, Mt=2, Kt=3, Nt=2) for both local orders, run under
    [SpadaDataflow.run_phased]. These are the terms exported to SpaDA and
    lowered to CSL. Main results:
    - [summa_correct]: for any element type and any [fma], from initial
      memories holding arbitrary symbolic tiles, every PE [(x,y)] ends with
      [c[i + j*Mt] = Summa.run fma A B C (Gemm example_dims o) x y i j], the
      ordered fold of [fma] over stages and [k] ([Summa.accumulate] over
      [Summa.reduction_trace]), and every PE has run both of its phases;
    - [summa_baseline_cached]: the two orders leave the same [c] everywhere;
    - [summa_race_free], [summa_deadlock_free]: the race and rendezvous
      deadlock checkers accept both kernels.

    Whole-PE scheduling ([run]) cannot run SUMMA: PE [(0,0)] sends in phase 1
    but receives in phase 2, and PE [(1,1)] the reverse. [summa_order] runs
    phase 1 with the stage-0 senders first, then phase 2 with the stage-1
    senders first.

    The proof is by evaluation: initial tiles are concrete-length lists of
    symbolic values ([A x y n], ...), so [vm_compute] runs the interpreter
    with the data left free. *)

Definition kernel (o : Summa.order) := Summa.lower (Summa.Gemm Summa.example_dims o).
Definition at_pe (x y : nat) : pe := (Z.of_nat x, Z.of_nat y).
Definition pes := [(0, 0); (1, 0); (0, 1); (1, 1)].
(** Phase 1: (0,0) sends a and b, (1,0) sends b, (0,1) sends a. Phase 2:
    (1,1) sends a and b, (0,1) sends b, (1,0) sends a. *)
Definition summa_order : list pe :=
  [at_pe 0 0; at_pe 1 0; at_pe 0 1; at_pe 1 1;
   at_pe 1 1; at_pe 0 1; at_pe 1 0; at_pe 0 0].

Section Proof.
Context {V : Type} `{data_ops V}.
(** Tiles on PE [(x,y)], column major: [a[n] = A x y n], [b[n] = B x y n],
    [c[i + j*Mt] = C x y i j]. The scratch fields [abuf], [bbuf] and [acc]
    start with arbitrary contents too. *)
Variables (A B Abuf Bbuf : nat -> nat -> nat -> V) (C : nat -> nat -> nat -> nat -> V)
  (Acc : nat -> nat -> V).

Definition tile (f : nat -> V) n := map f (seq 0 n).
Definition init_mem (p : pe) : @memory V :=
  let x := Z.to_nat (fst p) in let y := Z.to_nat (snd p) in
  fun a =>
    if id_dec a (named "a") then tile (A x y) 6
    else if id_dec a (named "b") then tile (B x y) 6
    else if id_dec a (named "c") then tile (fun n => C x y (n mod 2) (n / 2)) 4
    else if id_dec a (named "abuf") then tile (Abuf x y) 6
    else if id_dec a (named "bbuf") then tile (Bbuf x y) 6
    else if id_dec a (named "acc") then [Acc x y]
    else [].

(** The SUMMA specification of PE [(x,y)]'s [c] tile. *)
Definition spec o x y : list V :=
  tile (fun n => Summa.run data_fma A B C (Summa.Gemm Summa.example_dims o) x y (n mod 2) (n / 2)) 4.

Definition result o := run_phased (kernel o) summa_order init_mem (fun _ => 0) (fun _ => []).

Lemma outputs o :
  option_map (fun r => map (fun '(x, y) => (fst (fst r) (at_pe x y) (named "c"), snd (fst r) (at_pe x y))) pes)
    (result o) =
  Some (map (fun '(x, y) => (spec o x y, 2)) pes).
Proof. destruct o; vm_compute; reflexivity. Qed.

(** Main theorem. *)
Theorem summa_correct o : exists ms pc sto,
  run_phased (kernel o) summa_order init_mem (fun _ => 0) (fun _ => []) = Some (ms, pc, sto) /\
  forall x y, x < 2 -> y < 2 ->
    ms (at_pe x y) (named "c") = spec o x y /\ pc (at_pe x y) = 2.
Proof.
  pose proof (outputs o) as E. unfold result in E.
  destruct (run_phased (kernel o) summa_order init_mem (fun _ => 0) (fun _ => []))
    as [[[ms pc] sto]|]; [|discriminate].
  exists ms, pc, sto; split; [reflexivity|].
  injection E as E1 E2 E3 E4 E5 E6 E7 E8. intros x y X Y.
  assert (x = 0 \/ x = 1) as [ -> | -> ] by lia; assert (y = 0 \/ y = 1) as [ -> | -> ] by lia;
    split; assumption.
Qed.

(** The two local orders agree on every output (via [Summa.example_equivalent]). *)
Lemma spec_baseline_cached x y : spec Summa.Baseline x y = spec Summa.Cached x y.
Proof.
  unfold spec, tile; apply map_ext_in; intros n N; apply in_seq in N.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3) as [ -> | [ -> | [ -> | -> ] ] ] by lia;
    apply Summa.example_equivalent; simpl; tauto.
Qed.

Corollary summa_baseline_cached : exists msb pcb stob msc pcc stoc,
  result Summa.Baseline = Some (msb, pcb, stob) /\ result Summa.Cached = Some (msc, pcc, stoc) /\
  forall x y, x < 2 -> y < 2 -> msb (at_pe x y) (named "c") = msc (at_pe x y) (named "c").
Proof.
  destruct (summa_correct Summa.Baseline) as (msb & pcb & stob & Rb & Cb).
  destruct (summa_correct Summa.Cached) as (msc & pcc & stoc & Rc & Cc).
  exists msb, pcb, stob, msc, pcc, stoc. split; [exact Rb|]. split; [exact Rc|].
  intros x y X Y. rewrite (proj1 (Cb x y X Y)), (proj1 (Cc x y X Y)). apply spec_baseline_cached.
Qed.
End Proof.

(** ** Races and deadlocks *)
Theorem summa_race_free o : race_free (kernel o) = true.
Proof. destruct o; vm_compute; reflexivity. Qed.

Theorem summa_deadlock_check o : SpadaDeadlock.kernel_check (kernel o) = true.
Proof. destruct o; vm_compute; reflexivity. Qed.

(** Extraction succeeds, so the deadlock theorem is not vacuous. *)
Lemma summa_extracts o : exists s0, SpadaDeadlock.init_state (kernel o) = Some s0.
Proof. destruct o; eexists; vm_compute; reflexivity. Qed.

Theorem summa_deadlock_free o s0 : SpadaDeadlock.init_state (kernel o) = Some s0 ->
  forall s, SpadaDeadlock.rstar s0 s -> SpadaDeadlock.final s \/ exists s', SpadaDeadlock.rstep s s'.
Proof. intros I; exact (SpadaDeadlock.kernel_check_sound _ _ I (summa_deadlock_check o)). Qed.
