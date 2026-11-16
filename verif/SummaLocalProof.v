From Stdlib Require Import ZArith List String Lia.
From SpatialCSL Require Import SpadaIR SpadaSemantics Summa.
Import ListNotations Spada SpatialSemantics Summa.
Open Scope nat_scope.

(** Denotation of the concrete, statically indexed assignment/FMA fragment
    emitted by Summa.lower. All fields have the same f32 type. *)
Section Local.
Context {V : Type}.
Variable fma : V -> V -> V -> V.
Definition store := identifier -> nat -> V.
Definition address e : option (identifier * nat) := match e with
 | EVar id => Some (id,0)
 | Slice id [Constant I32 (Integer z)] =>
   if Z.leb 0 z then Some (id,Z.to_nat z) else None
 | _ => None end.
Fixpoint value (m : store) e : option V := match e with
 | FusedMultiplyAdd a b c => obind (value m a) (fun a =>
   obind (value m b) (fun b => obind (value m c) (fun c => Some (fma a b c))))
 | _ => option_map (fun p => m (fst p) (snd p)) (address e) end.
Definition write (m : store) p v : store := fun id n =>
 if (id_eqb id (fst p) && Nat.eqb n (snd p))%bool then v else m id n.
Fixpoint execute body (m : store) : option store := match body with
 | [] => Some m | Assign dst src :: tail =>
   obind (address dst) (fun p => obind (value m src) (fun v => execute tail (write m p v)))
 | _ => None end.
Definition outputs (result : option store) := option_map (fun m => map (fun n => m (named "c") n) (seq 0 4)) result.
Theorem emitted_local_assignments_equivalent : forall m a b,
 In (a,b) [("a","b");("a","bbuf");("abuf","b");("abuf","bbuf")]%string ->
 outputs (execute (local_compute example_dims Baseline a b) m) =
 outputs (execute (local_compute example_dims Cached a b) m).
Proof.
 intros m a b H; destruct H as [H|[H|[H|[H|[]]]]]; inversion H; subst;
 vm_compute; reflexivity.
Qed.
End Local.
Print Assumptions emitted_local_assignments_equivalent.

Section Specification.
Context {V : Type}.
Variable fma : V -> V -> V -> V.
Definition expected_tile (m : @store V) a b := map (fun ij =>
 let i := fst ij in let j := snd ij in
 fold_left (fun acc k => fma acc (m (named a) (i+k*2)) (m (named b) (k+j*3)))
   (seq 0 3) (m (named "c") (i+j*2))) [(0,0);(1,0);(0,1);(1,1)].
Theorem emitted_baseline_is_tile_gemm : forall m a b,
 In (a,b) [("a","b");("a","bbuf");("abuf","b");("abuf","bbuf")]%string ->
 outputs (@execute V fma (local_compute example_dims Baseline a b) m) = Some (expected_tile m a b).
Proof.
 intros m a b H; destruct H as [H|[H|[H|[H|[]]]]]; inversion H; subst;
 vm_compute; reflexivity.
Qed.
Theorem emitted_cached_is_tile_gemm : forall m a b,
 In (a,b) [("a","b");("a","bbuf");("abuf","b");("abuf","bbuf")]%string ->
 outputs (@execute V fma (local_compute example_dims Cached a b) m) = Some (expected_tile m a b).
Proof.
 intros; rewrite <- emitted_local_assignments_equivalent; auto using emitted_baseline_is_tile_gemm.
Qed.
End Specification.

Section Scratch.
Context {V : Type}.
Variable fma : V -> V -> V -> V.
Theorem cached_scratch_initial_value_irrelevant : forall (m : @store V) a b scratch,
 In (a,b) [("a","b");("a","bbuf");("abuf","b");("abuf","bbuf")]%string ->
 outputs (@execute V fma (local_compute example_dims Cached a b)
   (write m (named "acc",0) scratch)) =
 outputs (@execute V fma (local_compute example_dims Cached a b) m).
Proof.
 intros m a b scratch H; destruct H as [H|[H|[H|[H|[]]]]]; inversion H; subst;
 vm_compute; reflexivity.
Qed.
End Scratch.
