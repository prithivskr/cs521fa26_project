From Stdlib Require Import ZArith List Bool Arith Lia.
Import ListNotations.
Open Scope Z_scope.

(** A deliberately synchronous, PE-local fragment of Spatial IR. Slots are
    flattened placed arrays; Rocq functions specialize compute blocks by PE. *)
Definition word (z : Z) : Z := z mod 4294967296.
Definition memory := nat -> Z.
Definition write (m : memory) (slot : nat) (v : Z) : memory :=
  fun i => if Nat.eqb i slot then word v else m i.
Inductive expr :=
| Lit (v : Z) | Load (slot : nat)
| Add (a b : expr) | Mul (a b : expr).
Fixpoint eval (e : expr) (m : memory) : Z :=
  match e with
  | Lit v => word v | Load i => word (m i)
  | Add a b => word (eval a m + eval b m)
  | Mul a b => word (eval a m * eval b m)
  end.
Inductive command :=
| Skip | Store (slot : nat) (value : expr)
| Seq (a b : command) | Repeat (count : nat) (body : command).
Fixpoint iterate {A} (n : nat) (f : A -> A) (a : A) : A :=
  match n with O => a | S n => iterate n f (f a) end.
Fixpoint execute (c : command) (m : memory) : memory :=
  match c with
  | Skip => m | Store i e => write m i (eval e m)
  | Seq a b => execute b (execute a m)
  | Repeat n b => iterate n (execute b) m
  end.
Definition equivalent (a b : command) : Prop :=
  forall m, execute a m = execute b m.

Lemma equivalent_refl : forall a, equivalent a a.
Proof. intros a m; reflexivity. Qed.
Lemma equivalent_sym : forall a b, equivalent a b -> equivalent b a.
Proof. intros a b H m; symmetry; apply H. Qed.
Lemma equivalent_trans : forall a b c,
  equivalent a b -> equivalent b c -> equivalent a c.
Proof. intros a b c H K m; rewrite H; apply K. Qed.
Lemma seq_congr : forall a a' b b', equivalent a a' -> equivalent b b' ->
  equivalent (Seq a b) (Seq a' b').
Proof. intros a a' b b' H K m; simpl; rewrite H; apply K. Qed.
Lemma repeat_congr : forall n a b, equivalent a b ->
  equivalent (Repeat n a) (Repeat n b).
Proof.
  intros n a b H m; simpl; revert m; induction n; intros m; simpl.
  - reflexivity.
  - rewrite H; apply IHn.
Qed.
Lemma seq_assoc : forall a b c,
  equivalent (Seq (Seq a b) c) (Seq a (Seq b c)).
Proof. intros a b c m; reflexivity. Qed.
Lemma repeat_unroll : forall n b,
  equivalent (Repeat (S n) b) (Seq b (Repeat n b)).
Proof. intros n b m; reflexivity. Qed.
Lemma add_comm_store : forall i a b,
  equivalent (Store i (Add a b)) (Store i (Add b a)).
Proof. intros i a b m; simpl; rewrite Z.add_comm; reflexivity. Qed.

Record kernel := {
  width : nat; height : nat; slots : nat;
  compute : nat -> nat -> command
}.
Definition fabric := nat -> nat -> memory.
Definition run (k : kernel) (s : fabric) : fabric := fun x y =>
  if (Nat.ltb x (width k) && Nat.ltb y (height k))%bool
  then execute (compute k x y) (s x y) else s x y.
Definition kernel_equivalent (a b : kernel) : Prop :=
  width a = width b /\ height a = height b /\ slots a = slots b /\
  forall s x y, run a s x y = run b s x y.
(** Observation equivalence permits changes to private scratch slots. *)
Definition observationally_equivalent (outputs : list nat) (a b : kernel) :=
  width a = width b /\ height a = height b /\
  forall s x y i, In i outputs -> run a s x y i = run b s x y i.
Lemma kernel_congr : forall a b,
  width a = width b -> height a = height b -> slots a = slots b ->
  (forall x y, equivalent (compute a x y) (compute b x y)) ->
  kernel_equivalent a b.
Proof.
  intros a b W H S E; repeat split; auto.
  intros s x y; unfold run; rewrite W, H.
  destruct (Nat.ltb x (width b) && Nat.ltb y (height b))%bool; [apply E | reflexivity].
Qed.

Fixpoint expr_ok (size : nat) (e : expr) : bool :=
  match e with
  | Lit _ => true | Load i => Nat.ltb i size
  | Add a b | Mul a b => expr_ok size a && expr_ok size b
  end.
Fixpoint command_ok (size : nat) (c : command) : bool :=
  match c with
  | Skip => true
  | Store i e => Nat.ltb i size && expr_ok size e
  | Seq a b => command_ok size a && command_ok size b
  | Repeat _ b => command_ok size b
  end.
Lemma write_other : forall m i v j, i <> j -> write m i v j = m j.
Proof.
  intros m i v j H; unfold write; destruct (Nat.eqb j i) eqn:E; auto.
  apply Nat.eqb_eq in E; congruence.
Qed.
(** Accepted commands cannot modify storage outside their placed buffer. *)
Theorem execute_frame : forall c size m,
  command_ok size c = true -> forall j, (size <= j)%nat -> execute c m j = m j.
Proof.
  induction c; intros size m H j J; simpl in *; auto.
  - apply andb_true_iff in H as [H _]; apply Nat.ltb_lt in H.
    apply write_other; lia.
  - apply andb_true_iff in H as [A B]. rewrite (IHc2 size _ B j J).
    apply IHc1 with size; auto.
  - revert m; induction count; intros m; simpl; auto.
    rewrite IHcount. apply IHc with size; auto.
Qed.

(** Static indexed loops are Rocq elaboration, so indices can occur anywhere in
    addresses and placement decisions, without a parser or substitution pass. *)
Fixpoint for_range (start count : nat) (body : nat -> command) : command :=
  match count with
  | O => Skip
  | S n => Seq (body start) (for_range (S start) n body)
  end.
Lemma for_range_congr : forall count start a b,
  (forall i, equivalent (a i) (b i)) ->
  equivalent (for_range start count a) (for_range start count b).
Proof.
  induction count; intros start a b H; simpl.
  - apply equivalent_refl.
  - apply seq_congr; [apply H | apply IHcount; exact H].
Qed.
Lemma iterate_ext : forall A n (f g : A -> A),
  (forall x, f x = g x) -> forall x, iterate n f x = iterate n g x.
Proof.
  intros A n f g H; induction n; intros x; simpl; auto.
  rewrite H; apply IHn.
Qed.
Lemma write_same : forall m i v, write m i v i = word v.
Proof. intros; unfold write; rewrite Nat.eqb_refl; reflexivity. Qed.
