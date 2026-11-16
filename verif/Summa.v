From Stdlib Require Import ZArith List String Bool Arith.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaArithmetic SpadaElaboration.
Import ListNotations Spada SpatialSemantics.
Open Scope nat_scope.
Open Scope list_scope.


Module Summa.
Record dimensions := Dims { processors : nat; mt : nat; kt : nat; nt : nat }.
Inductive order := Baseline | Cached.
Record kernel := Gemm { dims : dimensions; local_order : order }.
(** The communication stage fixes these tile operands: A(stage,y), B(x,stage).
    Indices are column major, exactly as in the SDK benchmark. *)
Record update := Update { stage : nat; kindex : nat; column : nat; row : nat }.
Definition stages d := seq 0 (processors d).
Definition schedule d o := flat_map (fun s => match o with
 | Baseline => flat_map (fun k => flat_map (fun j =>
     map (fun i => Update s k j i) (seq 0 (mt d))) (seq 0 (nt d))) (seq 0 (kt d))
 | Cached => flat_map (fun j => flat_map (fun i =>
     map (fun k => Update s k j i) (seq 0 (kt d))) (seq 0 (mt d))) (seq 0 (nt d))
 end) (stages d).
Definition touches i j u := (Nat.eqb i (row u) && Nat.eqb j (column u))%bool.
Definition reduction_trace d o i j :=
 map (fun u => (stage u,kindex u)) (filter (touches i j) (schedule d o)).
Definition pair_eq_dec : forall a b : nat * nat, {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition trace_equal a b := if list_eq_dec pair_eq_dec a b then true else false.
Definition certificate d := forallb (fun i => forallb (fun j =>
 trace_equal (reduction_trace d Baseline i j) (reduction_trace d Cached i j))
 (seq 0 (nt d))) (seq 0 (mt d)).

Section Semantics.
Context {V : Type}.
Variable fma : V -> V -> V -> V.
(** A(x,y,offset), B(x,y,offset), C(x,y,i,j). Inputs may contain any bits. *)
Variable A B : nat -> nat -> nat -> V.
Variable C : nat -> nat -> nat -> nat -> V.
Definition accumulate d x y i j trace := fold_left (fun acc sk =>
 fma acc (A (fst sk) y (i + snd sk * mt d))
         (B x (fst sk) (j * kt d + snd sk))) trace (C x y i j).
Definition run program x y i j :=
 accumulate (dims program) x y i j (reduction_trace (dims program) (local_order program) i j).
Theorem certified_equivalence : forall d, certificate d = true ->
 forall x y i j, In i (seq 0 (mt d)) -> In j (seq 0 (nt d)) ->
 run (Gemm d Baseline) x y i j = run (Gemm d Cached) x y i j.
Proof.
 intros d H x y i j I J; unfold certificate in H.
 rewrite forallb_forall in H; specialize (H i I).
 rewrite forallb_forall in H; specialize (H j J).
 unfold trace_equal in H; destruct (list_eq_dec pair_eq_dec _ _) as [E|E]; try discriminate.
 unfold run; simpl; rewrite E; reflexivity.
Qed.
End Semantics.

(** Concrete nontrivial example: 2x2 PEs, 2x3 and 3x2 local tiles.
    The global multiplication is (4x6) * (6x4). *)
Definition example_dims := Dims 2 2 3 2.
Theorem example_certificate : certificate example_dims = true.
Proof. vm_compute; reflexivity. Qed.
Theorem example_equivalent : forall V (fma : V -> V -> V -> V) A B C x y i j,
 In i (seq 0 2) -> In j (seq 0 2) ->
 @run V fma A B C (Gemm example_dims Baseline) x y i j =
 @run V fma A B C (Gemm example_dims Cached) x y i j.
Proof. intros; apply certified_equivalence; auto using example_certificate. Qed.
Definition ieee_fma (a b c : atom) := ReferenceArithmetic.fma_reference a b c.
(** Use option-valued exact IEEE operations, so exceptional arithmetic is not
    replaced by real-number algebra. Successful and failing results agree. *)
Definition lifted_fma (a b c : option atom) :=
 obind a (fun a => obind b (fun b => obind c (fun c => ieee_fma a b c))).
Corollary example_f32_equivalent : forall A B C x y i j,
 In i (seq 0 2) -> In j (seq 0 2) ->
 run lifted_fma A B C (Gemm example_dims Baseline) x y i j =
 run lifted_fma A B C (Gemm example_dims Cached) x y i j.
Proof. intros; apply example_equivalent; assumption. Qed.

Definition nlit n := int (Z.of_nat n).
Definition ident s := named s.
Definition cell s e := Slice (ident s) [e].
Definition plus a b := Binary a Plus b.
Definition times a b := Binary a Times b.
Definition address i j stride := plus i (times j (nlit stride)).
Definition loop id n body := For [coord id] [interval 0 (Z.of_nat n)] body.
Definition cc d := cell "c" (address (var "i") (var "j") (mt d)).
Definition aa d a := cell a (address (var "i") (var "k") (mt d)).
Definition bb d b := cell b (address (var "k") (var "j") (kt d)).
Definition ccell d i j := cell "c" (nlit (i + j * mt d)).
Definition acell d a i k := cell a (nlit (i + k * mt d)).
Definition bcell d b k j := cell b (nlit (k + j * kt d)).
(** Static unrolling avoids the checkout backend's dynamic indexed-store bug.
    Both schedules remain explicit DSL assignments and explicit FMAs. *)
Definition local_compute d o a b := match o with
 | Baseline => flat_map (fun k => flat_map (fun j => map (fun i =>
     Assign (ccell d i j) (FusedMultiplyAdd (ccell d i j)
       (acell d a i k) (bcell d b k j))) (seq 0 (mt d))) (seq 0 (nt d))) (seq 0 (kt d))
 | Cached => flat_map (fun j => flat_map (fun i =>
     [Assign (var "acc") (ccell d i j)] ++
     map (fun k => Assign (var "acc") (FusedMultiplyAdd (var "acc")
       (acell d a i k) (bcell d b k j))) (seq 0 (kt d)) ++
     [Assign (ccell d i j) (var "acc")]) (seq 0 (mt d))) (seq 0 (nt d))
 end.
Definition coords := [coord "x";coord "y"].
Definition grid d := rectangle (Z.of_nat (processors d)) (Z.of_nat (processors d)).
Definition point x y := Grid (Range (nlit x) None None) (Range (nlit y) None None).
Definition buffer id n external := Field (Array (Scalar F32) [nlit n]) (ident id) external.
Definition stream_name prefix s target := (prefix ++ "_" ++ SpatialElaboration.decimal s ++ "_" ++ SpatialElaboration.decimal target)%string.
Definition targets d s := filter (fun t => negb (Nat.eqb s t)) (seq 0 (processors d)).
Definition streams d s := flat_map (fun target => [
 StreamDecl (Stream F32 (Some (nlit (mt d * kt d))))
   (ident (stream_name "arow" s target))
   (Relative (int (Z.of_nat target-Z.of_nat s)) (int 0) auto_route);
 StreamDecl (Stream F32 (Some (nlit (kt d * nt d))))
   (ident (stream_name "bcol" s target))
   (Relative (int 0) (int (Z.of_nat target-Z.of_nat s)) auto_route)]) (targets d s).
Definition communications d s x y :=
 ((if Nat.eqb x s then map (fun target =>
    Send (var "a") (var (stream_name "arow" s target)) None) (targets d s)
   else [Receive (var "abuf") (var (stream_name "arow" s x)) None]) ++
  (if Nat.eqb y s then map (fun target =>
    Send (var "b") (var (stream_name "bcol" s target)) None) (targets d s)
   else [Receive (var "bbuf") (var (stream_name "bcol" s y)) None]))%list.
Definition phase_body d o s := Phase
 (Dataflow coords (grid d) (streams d s) ::
 flat_map (fun y => map (fun x => Compute coords (point x y)
   (communications d s x y ++ local_compute d o
      (if Nat.eqb x s then "a" else "abuf")
      (if Nat.eqb y s then "b" else "bbuf"))) (seq 0 (processors d))) (seq 0 (processors d))).
Definition lower program : Spada.kernel := let d := dims program in
 Kernel (match local_order program with Baseline => "summa_baseline" | Cached => "summa_cached" end) [] []
 (Place coords (grid d)
   [buffer "a" (mt d * kt d) true;buffer "b" (kt d * nt d) true;
    buffer "c" (mt d * nt d) true;buffer "abuf" (mt d * kt d) false;
    buffer "bbuf" (kt d * nt d) false;Field (Scalar F32) (ident "acc") false] ::
 map (phase_body d (local_order program)) (stages d)).
Definition baseline := lower (Gemm example_dims Baseline).
Definition optimized := lower (Gemm example_dims Cached).
Definition baseline_json := export baseline.
Definition optimized_json := export optimized.
Definition baseline_c_stores d := processors d * kt d * nt d * mt d.
Definition cached_c_stores d := processors d * nt d * mt d.
Example store_reduction : (baseline_c_stores example_dims,cached_c_stores example_dims) = (24,8).
Proof. reflexivity. Qed.
Print Assumptions example_f32_equivalent.
End Summa.
