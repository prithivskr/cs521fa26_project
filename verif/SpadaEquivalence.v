From Stdlib Require Import List Relations Relation_Operators.
From SpatialCSL Require Import SpadaIR SpadaSemantics.
Import ListNotations Spada SpatialSemantics.

(** All finite observable traces, including silent scheduling steps. This does
    not select one scheduler and cannot prove a deadlocking kernel equivalent
    merely because another schedule terminates. *)
Inductive execution (ops : arithmetic) (net : network) :
  state -> list observation -> state -> Prop :=
 | ExecutionRefl : forall s, execution ops net s [] s
 | ExecutionSilent : forall s s' trace last,
   step ops net s None s' -> execution ops net s' trace last ->
   execution ops net s trace last
 | ExecutionVisible : forall s s' event trace last,
   step ops net s (Some event) s' -> execution ops net s' trace last ->
   execution ops net s (event :: trace) last.
Definition terminal (s : state) := tasks s = [].
Definition stuck ops net s := forall label next, ~ step ops net s label next.
Definition deadlocked ops net s := ~ terminal s /\ stuck ops net s.
Inductive outcome := Terminated | Deadlocked.
Definition has_outcome ops net s result := match result with
 | Terminated => terminal s | Deadlocked => deadlocked ops net s end.
Definition behavior {O} ops net (observe : state -> O) s trace result output :=
 exists last, execution ops net s trace last /\ has_outcome ops net last result /\ observe last = output.
Definition equivalent {O} ops net (observe : state -> O) a b :=
 forall trace result output,
 behavior ops net observe a trace result output <-> behavior ops net observe b trace result output.

Lemma equivalent_refl : forall O ops net (observe : state -> O) a,
 equivalent ops net observe a a.
Proof. intros; intros trace result output; reflexivity. Qed.
Lemma equivalent_sym : forall O ops net (observe : state -> O) a b,
 equivalent ops net observe a b -> equivalent ops net observe b a.
Proof. intros O ops net observe a b E trace result output; symmetry; apply E. Qed.
Lemma equivalent_trans : forall O ops net (observe : state -> O) a b c,
 equivalent ops net observe a b -> equivalent ops net observe b c -> equivalent ops net observe a c.
Proof. intros O ops net observe a b c A B trace result output; transitivity
 (behavior ops net observe b trace result output); [apply A | apply B]. Qed.

Record bisimulation ops net (R : state -> state -> Prop) : Prop := Bisimulation {
 bisim_forward : forall a b, R a b -> forall label a', step ops net a label a' ->
   exists b', step ops net b label b' /\ R a' b';
 bisim_backward : forall a b, R a b -> forall label b', step ops net b label b' ->
   exists a', step ops net a label a' /\ R a' b';
 bisim_terminal : forall a b, R a b -> (terminal a <-> terminal b)
}.
Lemma bisimulation_execution : forall ops net R,
 bisimulation ops net R -> forall a trace a', execution ops net a trace a' ->
 forall b, R a b -> exists b', execution ops net b trace b' /\ R a' b'.
Proof.
 intros ops net R B a trace a' E; induction E; intros b Related.
 - exists b; split; [constructor | exact Related].
 - destruct (bisim_forward _ _ _ B _ _ Related _ _ H) as [b' [S K]].
   destruct (IHE _ K) as [last' [X Y]].
   exists last'; split; [eapply ExecutionSilent; eauto | exact Y].
 - destruct (bisim_forward _ _ _ B _ _ Related _ _ H) as [b' [S K]].
   destruct (IHE _ K) as [last' [X Y]].
   exists last'; split; [eapply ExecutionVisible; eauto | exact Y].
Qed.
Lemma bisimulation_stuck : forall ops net R,
 bisimulation ops net R -> forall a b, R a b -> (stuck ops net a <-> stuck ops net b).
Proof.
 intros ops net R B a b H; split; intros S label next K.
 - destruct (bisim_backward _ _ _ B _ _ H _ _ K) as [a' [X _]].
   exact (S _ _ X).
 - destruct (bisim_forward _ _ _ B _ _ H _ _ K) as [b' [X _]].
   exact (S _ _ X).
Qed.
Lemma bisimulation_outcome : forall ops net R,
 bisimulation ops net R -> forall a b, R a b -> forall result,
 has_outcome ops net a result <-> has_outcome ops net b result.
Proof.
 intros ops net R B a b H result; destruct result; simpl.
 - exact (bisim_terminal _ _ _ B _ _ H).
 - unfold deadlocked; rewrite (bisim_terminal _ _ _ B _ _ H),
     (bisimulation_stuck _ _ _ B _ _ H); reflexivity.
Qed.
Theorem bisimulation_sound : forall O ops net (observe : state -> O) R,
 bisimulation ops net R ->
 (forall a b, R a b -> observe a = observe b) ->
 forall a b, R a b -> equivalent ops net observe a b.
Proof.
 intros O ops net observe R B Obs a b H trace result output; split.
 - intros [last [E [F V]]].
   destruct (bisimulation_execution _ _ _ B _ _ _ E _ H) as [last' [X Y]].
   exists last'; repeat split; auto.
   + apply (proj1 (bisimulation_outcome _ _ _ B _ _ Y _)); exact F.
   + rewrite <- (Obs _ _ Y); exact V.
 - assert (B' : bisimulation ops net (fun x y => R y x)).
   { constructor.
     - intros x y K; apply (bisim_backward _ _ _ B _ _ K).
     - intros x y K; apply (bisim_forward _ _ _ B _ _ K).
     - intros x y K; symmetry; apply (bisim_terminal _ _ _ B _ _ K). }
   intros [last [E [F V]]].
   destruct (bisimulation_execution _ _ _ B' _ _ _ E _ H) as [last' [X Y]].
   exists last'; repeat split; auto.
   + apply (proj1 (bisimulation_outcome _ _ _ B' _ _ Y _)); exact F.
   + rewrite (Obs _ _ Y); exact V.
Qed.

(** Infinite reductions are retained separately; no fairness assumption or
    dependent-choice axiom is hidden in finite trace equivalence. *)
CoInductive diverges ops net : state -> Prop :=
 | Diverges : forall s label next, step ops net s label next ->
   diverges ops net next -> diverges ops net s.
Theorem bisimulation_divergence : forall ops net R,
 bisimulation ops net R -> forall a b, R a b -> diverges ops net a -> diverges ops net b.
Proof.
 intros ops net R B; cofix CI; intros a b H D.
 inversion D as [s label next S Tail]; subst.
 destruct (bisim_forward _ _ _ B _ _ H _ _ S) as [b' [K L]].
 econstructor; [exact K | eapply CI; eauto].
Qed.
Definition total_equivalent {O} ops net (observe : state -> O) a b :=
 equivalent ops net observe a b /\ (diverges ops net a <-> diverges ops net b).

Print Assumptions bisimulation_sound.
Print Assumptions bisimulation_divergence.

Lemma bisimulation_reverse : forall ops net R,
 bisimulation ops net R -> bisimulation ops net (fun a b => R b a).
Proof.
 intros ops net R B; constructor.
 - intros a b H; apply (bisim_backward _ _ _ B _ _ H).
 - intros a b H; apply (bisim_forward _ _ _ B _ _ H).
 - intros a b H; symmetry; apply (bisim_terminal _ _ _ B _ _ H).
Qed.
Theorem bisimulation_total_sound : forall O ops net (observe : state -> O) R,
 bisimulation ops net R ->
 (forall a b, R a b -> observe a = observe b) ->
 forall a b, R a b -> total_equivalent ops net observe a b.
Proof.
 intros O ops net observe R B Obs a b H; split.
 - eapply bisimulation_sound; eauto.
 - split.
   + eapply bisimulation_divergence; eauto.
   + eapply bisimulation_divergence; [apply bisimulation_reverse; exact B | exact H].
Qed.
