From Stdlib Require Import List Permutation.
Import ListNotations.

(** * Specification: element-wise reduction (shared by the reduction proofs)

    [reduce [a0; a1; ...; aK-1]] is the element-wise sum
    [a0 + (a1 + (... + aK-1))], nested to the right. Addition is an arbitrary
    binary operation (e.g. IEEE f32 addition); only [reduce_permutation]
    assumes it is associative and commutative. *)

Class Plus (V : Type) := plus : V -> V -> V.

Section Spec.
Context {V : Type} `{Plus V}.

(** Element-wise sum, truncated to the shorter vector. *)
Definition zip_add (a b : list V) : list V :=
  map (fun p => plus (fst p) (snd p)) (combine a b).

Fixpoint reduce (vs : list (list V)) : list V :=
  match vs with
  | [] => []
  | [a] => a
  | a :: rest => zip_add a (reduce rest)
  end.

Lemma zip_add_length a b : length (zip_add a b) = Nat.min (length a) (length b).
Proof. unfold zip_add; rewrite length_map, length_combine; reflexivity. Qed.

Lemma reduce_cons x l : l <> [] -> reduce (x :: l) = zip_add x (reduce l).
Proof. destruct l; [congruence|reflexivity]. Qed.

(** ** Order independence *)
Section Algebra.
Hypothesis plus_assoc : forall x y z, plus x (plus y z) = plus (plus x y) z.
Hypothesis plus_comm : forall x y, plus x y = plus y x.

Lemma zip_add_comm : forall x y, zip_add x y = zip_add y x.
Proof.
  induction x as [|h t IH]; intros [|h' t']; unfold zip_add in *; simpl; auto.
  rewrite plus_comm, IH; reflexivity.
Qed.

Lemma zip_add_assoc : forall x y z, zip_add x (zip_add y z) = zip_add (zip_add x y) z.
Proof.
  induction x as [|h t IH]; intros [|h' t'] [|h'' t'']; unfold zip_add in *; simpl; auto.
  rewrite plus_assoc, IH; reflexivity.
Qed.

(** Reordering the vectors does not change the reduction. *)
Theorem reduce_permutation : forall l l', Permutation l l' -> reduce l = reduce l'.
Proof.
  intros l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
  - reflexivity.
  - destruct l as [|z l]; [apply Permutation_nil in P; subst; reflexivity|].
    destruct l' as [|z' l']; [symmetry in P; apply Permutation_nil in P; discriminate|].
    rewrite !reduce_cons by discriminate. rewrite IH; reflexivity.
  - destruct l as [|z l].
    + simpl. apply zip_add_comm.
    + rewrite (reduce_cons y (x :: z :: l)), (reduce_cons x (z :: l)),
        (reduce_cons x (y :: z :: l)), (reduce_cons y (z :: l)) by discriminate.
      rewrite !zip_add_assoc, (zip_add_comm y x); reflexivity.
  - congruence.
Qed.
End Algebra.
End Spec.
