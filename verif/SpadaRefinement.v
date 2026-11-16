From Stdlib Require Import List.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaEquivalence.
Import ListNotations Spada SpatialSemantics.

(** Certificates may relate different physical layouts, logical networks and
    scratch memories. Host edge identities are the common public interface. *)
Definition event_trace (l : label) : list observation :=
 match l with None => [] | Some e => [e] end.
Lemma execution_append : forall ops net a xs b ys c,
 execution ops net a xs b -> execution ops net b ys c ->
 execution ops net a (xs ++ ys) c.
Proof.
 intros ops net a xs b ys c H; induction H; intros K; simpl; auto.
 - eapply ExecutionSilent; eauto.
 - eapply ExecutionVisible; eauto.
Qed.
Lemma execution_step : forall ops net a l b,
 step ops net a l b -> execution ops net a (event_trace l) b.
Proof. intros; destruct l; [eapply ExecutionVisible | eapply ExecutionSilent]; eauto; constructor. Qed.

Record simulation ops netA netB (R : state -> state -> Prop) : Prop := Simulation {
 simulate_step : forall a b, R a b -> forall l a', step ops netA a l a' ->
   exists b', execution ops netB b (event_trace l) b' /\ R a' b'
}.
Theorem simulation_execution : forall ops netA netB R,
 simulation ops netA netB R -> forall a trace a', execution ops netA a trace a' ->
 forall b, R a b -> exists b', execution ops netB b trace b' /\ R a' b'.
Proof.
 intros ops netA netB R S a trace a' E; induction E; intros b Related.
 - exists b; split; [constructor | exact Related].
 - destruct (simulate_step _ _ _ _ S _ _ Related _ _ H) as [b' [X Y]].
   destruct (IHE _ Y) as [last' [K L]].
   exists last'; split; [change (execution ops netB b ([] ++ trace) last');
     eapply execution_append; eauto | exact L].
 - destruct (simulate_step _ _ _ _ S _ _ Related _ _ H) as [b' [X Y]].
   destruct (IHE _ Y) as [last' [K L]].
   exists last'; split; [change (execution ops netB b ([event] ++ trace) last');
     eapply execution_append; eauto | exact L].
Qed.

Definition across_equivalent {O} ops netA netB
 (observeA observeB : state -> O) a b :=
 (forall trace result output,
   behavior ops netA observeA a trace result output <->
   behavior ops netB observeB b trace result output) /\
 (diverges ops netA a <-> diverges ops netB b).

(** Matching silent steps with zero steps requires a separate divergence
    obligation: otherwise an infinite silent loop could be erased unsoundly. *)
Record weak_certificate {O} ops netA netB (observeA observeB : state -> O)
 (R : state -> state -> Prop) : Prop := WeakCertificate {
 weak_forward : simulation ops netA netB R;
 weak_backward : simulation ops netB netA (fun b a => R a b);
 weak_exit_forward : forall a b, R a b -> forall result,
   has_outcome ops netA a result -> exists b',
   execution ops netB b [] b' /\ has_outcome ops netB b' result /\ observeA a = observeB b';
 weak_exit_backward : forall a b, R a b -> forall result,
   has_outcome ops netB b result -> exists a',
   execution ops netA a [] a' /\ has_outcome ops netA a' result /\ observeA a' = observeB b;
 weak_divergence : forall a b, R a b -> (diverges ops netA a <-> diverges ops netB b)
}.
Theorem weak_certificate_sound : forall O ops netA netB (observeA observeB : state -> O) R,
 weak_certificate ops netA netB observeA observeB R -> forall a b, R a b ->
 across_equivalent ops netA netB observeA observeB a b.
Proof.
 intros O ops netA netB observeA observeB R C a b Related; split.
 - intros trace result output; split; intros [last [E [F V]]].
   + destruct (simulation_execution _ _ _ _ (weak_forward _ _ _ _ _ _ C)
       _ _ _ E _ Related) as [last' [X Y]].
     destruct (weak_exit_forward _ _ _ _ _ _ C _ _ Y _ F) as [final [K [L M]]].
     exists final; split.
     * rewrite <- (app_nil_r trace); eapply execution_append; eauto.
     * split; [exact L | rewrite <- M; exact V].
   + destruct (simulation_execution _ _ _ _ (weak_backward _ _ _ _ _ _ C)
       _ _ _ E _ Related) as [last' [X Y]].
     destruct (weak_exit_backward _ _ _ _ _ _ C _ _ Y _ F) as [final [K [L M]]].
     exists final; split.
     * rewrite <- (app_nil_r trace); eapply execution_append; eauto.
     * split; [exact L | rewrite M; exact V].
 - exact (weak_divergence _ _ _ _ _ _ C _ _ Related).
Qed.

(** The existing lock-step proof rule is a special case. *)
Theorem strong_to_weak : forall O ops net (observe : state -> O) R,
 bisimulation ops net R -> (forall a b, R a b -> observe a = observe b) ->
 weak_certificate ops net net observe observe R.
Proof.
 intros O ops net observe R B Obs; constructor.
 - constructor; intros a b H l a' S.
   destruct (bisim_forward _ _ _ B _ _ H _ _ S) as [b' [X Y]].
   exists b'; split; [apply execution_step; exact X | exact Y].
 - constructor; intros b a H l b' S.
   destruct (bisim_backward _ _ _ B _ _ H _ _ S) as [a' [X Y]].
   exists a'; split; [apply execution_step; exact X | exact Y].
 - intros a b H result F; exists b; split; [constructor | split].
   + apply (proj1 (bisimulation_outcome _ _ _ B _ _ H _)); exact F.
   + apply Obs; exact H.
 - intros a b H result F; exists a; split; [constructor | split].
   + apply (proj2 (bisimulation_outcome _ _ _ B _ _ H _)); exact F.
   + apply Obs; exact H.
 - intros a b H; split.
   + eapply bisimulation_divergence; eauto.
   + eapply bisimulation_divergence; [apply bisimulation_reverse; exact B | exact H].
Qed.

(** Labelled infinite executions retain the actual communication sequence,
    including silent actions, rather than recording only possible divergence. *)
CoInductive stream (A : Type) := Cons (head : A) (tail : stream A).
Arguments Cons {A} _ _.
CoInductive infinite_execution ops net : state -> stream label -> Prop :=
 | InfiniteStep : forall a l b labels, step ops net a l b ->
   infinite_execution ops net b labels -> infinite_execution ops net a (Cons l labels).
Theorem bisimulation_infinite_execution : forall ops net R,
 bisimulation ops net R -> forall a b labels, R a b ->
 infinite_execution ops net a labels -> infinite_execution ops net b labels.
Proof.
 intros ops net R B; cofix CI; intros a b labels Related E.
 inversion E as [x l y tail S T]; subst.
 destruct (bisim_forward _ _ _ B _ _ Related _ _ S) as [b' [X Y]].
 econstructor; [exact X | eapply CI; eauto].
Qed.
Print Assumptions weak_certificate_sound.
Print Assumptions bisimulation_infinite_execution.
