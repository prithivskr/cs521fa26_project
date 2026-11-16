From Stdlib Require Import ZArith List Bool Lia String.
From SpatialCSL Require Import Spatial CSL.
Import ListNotations.
Open Scope Z_scope.

(** Each PE has two length-four input vectors at slots 0..3 and 4..7,
    and a length-four output vector at 8..11. *)
Definition vector_add : command := for_range 0 4 (fun i =>
  Store (8 + i)%nat (Add (Load i) (Load (4 + i)%nat))).
Definition vector_add_swapped : command := for_range 0 4 (fun i =>
  Store (8 + i)%nat (Add (Load (4 + i)%nat) (Load i))).
Theorem vector_add_equivalent : equivalent vector_add vector_add_swapped.
Proof. apply for_range_congr; intros; apply add_comm_store. Qed.
Definition placed (body : command) : kernel :=
  {| width := 2; height := 2; slots := 13;
     compute := fun x y => Seq (Store 12 (Lit (Z.of_nat (x + 2 * y)))) body |}.
Definition example := placed vector_add.
Definition optimized := placed vector_add_swapped.
Theorem kernels_equivalent : kernel_equivalent example optimized.
Proof.
  apply kernel_congr; try reflexivity; intros.
  apply seq_congr; [apply equivalent_refl | apply vector_add_equivalent].
Qed.
Theorem compiled_kernels_equivalent : forall s x y,
  run_program (lower_kernel example) s x y =
  run_program (lower_kernel optimized) s x y.
Proof. apply equivalence_preserved; apply kernels_equivalent. Qed.

Definition increment := Store 0 (Add (Load 0) (Lit 1)).
Example loop_unrolling : equivalent (Repeat 3 increment)
  (Seq increment (Seq increment (Seq increment Skip))).
Proof. intros m; reflexivity. Qed.
Example overflow_is_modular :
  execute increment (fun _ => 4294967295) 0%nat = 0.
Proof. vm_compute; reflexivity. Qed.
Example multiply_wraps_exactly :
  eval (Mul (Lit 4294967295) (Lit 4294967295)) (fun _ => 0) = 1.
Proof. vm_compute; reflexivity. Qed.
Example compiler_accepts_example : valid example = true.
Proof. vm_compute; reflexivity. Qed.
Example compiler_rejects_oob :
  compile {| width := 1; height := 1; slots := 1;
             compute := fun _ _ => Store 1 (Lit 7) |} = None.
Proof. vm_compute; reflexivity. Qed.
Example compiler_rejects_oob_read :
  compile {| width := 1; height := 1; slots := 1;
             compute := fun _ _ => Store 0 (Load 1) |} = None.
Proof. vm_compute; reflexivity. Qed.
Example compiler_rejects_empty_grid :
  compile {| width := 0; height := 1; slots := 1;
             compute := fun _ _ => Skip |} = None.
Proof. vm_compute; reflexivity. Qed.

(** A scratch-elimination example: full-state equality would be too strong. *)
Definition with_scratch : command :=
  Seq (Store 1 (Add (Load 0) (Lit 7))) (Store 2 (Load 1)).
Definition without_scratch : command := Store 2 (Add (Load 0) (Lit 7)).
Lemma scratch_elimination : forall m,
  execute with_scratch m 2%nat = execute without_scratch m 2%nat.
Proof.
  intros m; cbn [execute with_scratch without_scratch eval].
  rewrite !write_same; rewrite !word_idempotent; reflexivity.
Qed.
Definition scratch_kernel (c : command) : kernel :=
  {| width := 2; height := 1; slots := 3; compute := fun _ _ => c |}.
Theorem scratch_kernels_equivalent : observationally_equivalent [2%nat]
  (scratch_kernel with_scratch) (scratch_kernel without_scratch).
Proof.
  split; [reflexivity | split; [reflexivity |]].
  intros s x y i H; destruct H as [H | []]; subst i.
  unfold run; simpl.
  destruct (Nat.ltb x 2 && Nat.ltb y 1)%bool;
    [apply scratch_elimination | reflexivity].
Qed.
Theorem compiled_scratch_equivalent : forall s x y,
  run_program (lower_kernel (scratch_kernel with_scratch)) s x y 2%nat =
  run_program (lower_kernel (scratch_kernel without_scratch)) s x y 2%nat.
Proof.
  intros; apply observational_equivalence_preserved with [2%nat].
  - apply scratch_kernels_equivalent.
  - simpl; auto.
Qed.

(** Evaluating this term returns filenames and complete CSL source strings. *)
Definition example_files := compile_files example.
Example emits_layout_and_four_tiles :
  option_map (@List.length file) example_files = Some 5%nat.
Proof. vm_compute; reflexivity. Qed.

Example negative_literal_prints_as_word :
  word_decimal (-1) = "4294967295"%string.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions lower_correct.
Print Assumptions compile_correct.
Print Assumptions kernels_equivalent.
Print Assumptions scratch_kernels_equivalent.
