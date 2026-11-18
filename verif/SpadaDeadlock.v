From Stdlib Require Import ZArith List String Bool Lia.
From SpatialCSL Require Import SpadaIR SpadaDataflow ChainReduce ChainReduceVariant.
Import ListNotations Spada.
Open Scope nat_scope.
Open Scope list_scope.

(** * A rendezvous deadlock-freedom checker for SpaDA IR kernels

    [SpadaDataflow] proves the values a kernel computes but not deadlock
    freedom. SpaDA (irspec/docs/spatial/async.md, "Deadlocks") calls a program
    deadlocked if some progress order can leave it stuck, and a send may stall
    until the receiver is ready. This file checks that obligation.

    Modelling assumptions:
    - Rendezvous. Each element transfer needs the sender and the receiver at
      the matching operation at the same time. This is the strictest buffering
      (zero capacity): a deadlock-free program here never waits on a buffer.
    - The host is always ready. Events on argument streams ([Arg]) fire alone.
    - Program order. A separate race checker makes every [async] immediately
      awaited, so each PE's communications happen in program order. We ignore
      completions ([Await], the [done] fields) on that basis.
    - Event extraction mirrors [SpadaDataflow.exec]'s statement structure
      ([pe_program], [chan_of], [range_values], with an empty memory). Whole
      arrays move as one event per element. Array lengths come from the
      kernel's top-level [Place] field declarations, and the PEs come from the
      [Place] grids. Constructs that [exec] does not support make extraction
      fail.
    - Phases are not modelled as barriers. Channels carry their phase, as in
      [SpadaDataflow], so different phases never match.
    - Channels have one writer PE and one reader PE. The checker verifies this.

    How it works: this system is confluent. An enabled pair stays enabled
    until it fires, and distinct steps commute ([diamond]). Every step removes
    events ([rstep_size]). So if one schedule empties every PE, every reachable
    state can still reach the empty state, and therefore is final or can step
    ([kernel_check_sound]). The checker runs one deterministic schedule. *)

Module SpadaDeadlock.

#[local] Instance unit_ops : data_ops unit := DataOps unit (fun _ _ _ => tt) (fun _ _ => tt) (fun _ _ _ => tt).

(** ** Events and the rendezvous system *)
Inductive event := ESend (c : chan) | ERecv (c : chan).
Definition ev_chan e := match e with ESend c | ERecv c => c end.
Definition is_host (c : chan) : bool := match c with Arg _ _ => true | Edge _ _ _ => false end.
Definition event_dec (a b : event) : {a = b} + {a <> b}.
Proof. decide equality; apply chan_dec. Defined.

(** A state lists each PE's remaining events, in program order. *)
Definition evstate := list (list event).

Fixpoint upd (s : evstate) (i : nat) (l : list event) : evstate :=
  match s, i with
  | [], _ => []
  | _ :: t, O => l :: t
  | h :: t, S i => h :: upd t i l
  end.

Inductive rstep : evstate -> evstate -> Prop :=
 | StepHost i e l s : nth_error s i = Some (e :: l) -> is_host (ev_chan e) = true ->
     rstep s (upd s i l)
 | StepPair i j c l1 l2 s : i <> j -> is_host c = false ->
     nth_error s i = Some (ESend c :: l1) -> nth_error s j = Some (ERecv c :: l2) ->
     rstep s (upd (upd s i l1) j l2).

Inductive rstar : evstate -> evstate -> Prop :=
 | StarRefl s : rstar s s
 | StarStep s t u : rstep s t -> rstar t u -> rstar s u.

Definition final (s : evstate) := forall n l, nth_error s n = Some l -> l = [].
Definition size (s : evstate) := fold_right (fun l n => List.length l + n) 0 s.

(** Single writer and single reader per non-host channel. *)
Definition swsr (s : evstate) := forall i j li lj e,
  nth_error s i = Some li -> nth_error s j = Some lj -> In e li -> In e lj ->
  is_host (ev_chan e) = false -> i = j.

(** ** Basic lemmas *)
Lemma nth_error_upd s i l n : nth_error (upd s i l) n =
  if Nat.eq_dec i n then option_map (fun _ => l) (nth_error s n) else nth_error s n.
Proof.
  revert i n; induction s as [|h t IH]; intros i n; destruct i, n; cbn [upd nth_error];
    try rewrite IH; destruct (Nat.eq_dec _ _); try destruct (Nat.eq_dec _ _);
    try destruct (nth_error t n); try reflexivity; try lia.
Qed.

Ltac upd_goal :=
  rewrite ?nth_error_upd;
  repeat match goal with |- context [Nat.eq_dec ?a ?b] => destruct (Nat.eq_dec a b) end;
  subst; try (exfalso; congruence).

Ltac upd_eq :=
  apply nth_error_ext; intro; upd_goal;
  repeat match goal with |- context [nth_error ?s ?n] => destruct (nth_error s n) end;
  reflexivity.

Lemma step_host' s i e l t : nth_error s i = Some (e :: l) -> is_host (ev_chan e) = true ->
  t = upd s i l -> rstep s t.
Proof. intros; subst; eapply StepHost; eauto. Qed.
Lemma step_pair' s i j c l1 l2 t : i <> j -> is_host c = false ->
  nth_error s i = Some (ESend c :: l1) -> nth_error s j = Some (ERecv c :: l2) ->
  t = upd (upd s i l1) j l2 -> rstep s t.
Proof. intros; subst; eapply StepPair; eauto. Qed.

Lemma final_no_step s s' : final s -> rstep s s' -> False.
Proof. intros F H; destruct H as [i e l s Hi _ | i j c l1 l2 s _ _ Hi _]; apply F in Hi; discriminate. Qed.

Lemma rstep_shrink s s' : rstep s s' ->
  forall n l', nth_error s' n = Some l' -> exists l, nth_error s n = Some l /\ incl l' l.
Proof.
  intros H n l'; destruct H as [i e l s Hi _ | i j c l1 l2 s _ _ Hi Hj]; upd_goal;
    try (intro E; eexists; split; [exact E | apply incl_refl]).
  - rewrite Hi; cbn; intros E; injection E as <-; eexists; split; [reflexivity|].
    intros x X; right; exact X.
  - rewrite Hj; cbn; intros E; injection E as <-; eexists; split; [reflexivity|].
    intros x X; right; exact X.
  - rewrite Hi; cbn; intros E; injection E as <-; eexists; split; [reflexivity|].
    intros x X; right; exact X.
Qed.

Lemma swsr_step s s' : swsr s -> rstep s s' -> swsr s'.
Proof.
  intros W H i j li lj e Hi Hj Ei Ej He.
  destruct (rstep_shrink _ _ H _ _ Hi) as (li0 & Hi0 & Ii).
  destruct (rstep_shrink _ _ H _ _ Hj) as (lj0 & Hj0 & Ij).
  eapply W; eauto.
Qed.

Lemma size_upd s i l l0 : nth_error s i = Some l0 ->
  size (upd s i l) + List.length l0 = size s + List.length l.
Proof.
  unfold size; revert i; induction s as [|h t IH]; intros [|i] E; cbn [upd fold_right nth_error] in *; try discriminate.
  - injection E as <-; lia.
  - specialize (IH i E); lia.
Qed.

(** Termination: every step removes at least one event. *)
Theorem rstep_size s s' : rstep s s' -> size s' < size s.
Proof.
  intros H; destruct H as [i e l s Hi _ | i j c l1 l2 s D _ Hi Hj].
  - pose proof (size_upd _ _ l _ Hi); cbn [List.length] in *; lia.
  - pose proof (size_upd _ _ l1 _ Hi) as A.
    assert (Hj' : nth_error (upd s i l1) j = Some (ERecv c :: l2)) by (upd_goal; exact Hj).
    pose proof (size_upd _ _ l2 _ Hj') as B; cbn [List.length] in *; lia.
Qed.

(** ** Confluence *)
Ltac host_vs_pair :=
  match goal with
  | H1 : nth_error ?s ?i = Some (?e :: _), H2 : nth_error ?s ?i = Some (?f :: _) |- _ =>
      rewrite H1 in H2; injection H2 as <- <-; cbn in *; congruence
  end.

Lemma diamond s s1 s2 : swsr s -> rstep s s1 -> rstep s s2 ->
  s1 = s2 \/ exists u, rstep s1 u /\ rstep s2 u.
Proof.
  intros W H1 H2.
  destruct H1 as [i e l s Hi He | i j c l1 l2 s Dij Hc Hi Hj];
    destruct H2 as [i' e' l' ? Hi' He' | i' j' c' l1' l2' ? Dij' Hc' Hi' Hj'].
  - destruct (Nat.eq_dec i i') as [<-|Dii].
    + rewrite Hi in Hi'; injection Hi' as <- <-; left; reflexivity.
    + right; exists (upd (upd s i l) i' l'); split.
      * eapply (step_host' _ i' e' l'); [upd_goal; exact Hi' | exact He' | reflexivity].
      * eapply (step_host' _ i e l); [upd_goal; exact Hi | exact He | upd_eq].
  - destruct (Nat.eq_dec i i') as [<-|D1]; [host_vs_pair|].
    destruct (Nat.eq_dec i j') as [<-|D2]; [host_vs_pair|].
    right; exists (upd (upd (upd s i l) i' l1') j' l2'); split.
    + eapply (step_pair' _ i' j' c' l1' l2'); [exact Dij' | exact Hc' | upd_goal; exact Hi' | upd_goal; exact Hj' | reflexivity].
    + eapply (step_host' _ i e l); [upd_goal; exact Hi | exact He | upd_eq].
  - destruct (Nat.eq_dec i' i) as [<-|D1]; [host_vs_pair|].
    destruct (Nat.eq_dec i' j) as [<-|D2]; [host_vs_pair|].
    right; exists (upd (upd (upd s i l1) j l2) i' l'); split.
    + eapply (step_host' _ i' e' l'); [upd_goal; exact Hi' | exact He' | reflexivity].
    + eapply (step_pair' _ i j c l1 l2); [exact Dij | exact Hc | upd_goal; exact Hi | upd_goal; exact Hj | upd_eq].
  - destruct (Nat.eq_dec i i') as [<-|D1].
    { rewrite Hi in Hi'; injection Hi' as <- <-.
      assert (j = j') as <- by (eapply W; [exact Hj | exact Hj' | left; reflexivity | left; reflexivity | exact Hc]).
      rewrite Hj in Hj'; injection Hj' as <-; left; reflexivity. }
    destruct (Nat.eq_dec i j') as [<-|D2]; [rewrite Hi in Hj'; discriminate|].
    destruct (Nat.eq_dec j i') as [<-|D3]; [rewrite Hj in Hi'; discriminate|].
    destruct (Nat.eq_dec j j') as [<-|D4].
    { rewrite Hj in Hj'; injection Hj' as <- <-.
      exfalso; apply D1; eapply W; [exact Hi | exact Hi' | left; reflexivity | left; reflexivity | exact Hc]. }
    right; exists (upd (upd (upd (upd s i l1) j l2) i' l1') j' l2'); split.
    + eapply (step_pair' _ i' j' c' l1' l2'); [exact Dij' | exact Hc' | upd_goal; exact Hi' | upd_goal; exact Hj' | reflexivity].
    + eapply (step_pair' _ i j c l1 l2); [exact Dij | exact Hc | upd_goal; exact Hi | upd_goal; exact Hj | upd_eq].
Qed.

(** Any step from a state that can reach a final state keeps that ability. *)
Lemma step_keeps_final s f : rstar s f -> final f -> swsr s ->
  forall s', rstep s s' -> rstar s' f.
Proof.
  intros R F; induction R as [s | s t u Hst R IH]; intros W s' Hs'.
  - exfalso; exact (final_no_step _ _ F Hs').
  - destruct (diamond _ _ _ W Hst Hs') as [<- | (v & Htv & Hs'v)]; [exact R|].
    apply StarStep with v; [exact Hs'v|].
    exact (IH F (swsr_step _ _ W Hst) _ Htv).
Qed.

(** If one run from [s0] reaches a final state, then every state reachable
    from [s0] can reach that same final state. *)
Theorem reachable_can_finish s0 f : swsr s0 -> rstar s0 f -> final f ->
  forall s, rstar s0 s -> rstar s f.
Proof.
  intros W Rf F s R; induction R as [s | s t u Hst R IH]; [exact Rf|].
  apply IH; [exact (swsr_step _ _ W Hst)|].
  exact (step_keeps_final _ _ Rf F W _ Hst).
Qed.

(** ** The deterministic schedule *)
Fixpoint find_recv (c : chan) (i : nat) (js : list nat) (s : evstate) : option (nat * list event) :=
  match js with
  | [] => None
  | j :: r =>
      match nth_error s j with
      | Some (ERecv c' :: l2) =>
          if chan_dec c c' then if Nat.eq_dec i j then find_recv c i r s else Some (j, l2)
          else find_recv c i r s
      | _ => find_recv c i r s
      end
  end.

Definition try_at (s : evstate) (i : nat) : option evstate :=
  match nth_error s i with
  | Some (e :: l) =>
      if is_host (ev_chan e) then Some (upd s i l) else
      match e with
      | ESend c => match find_recv c i (seq 0 (List.length s)) s with
                   | Some (j, l2) => Some (upd (upd s i l) j l2)
                   | None => None
                   end
      | ERecv _ => None
      end
  | _ => None
  end.

Fixpoint pick_from (is : list nat) (s : evstate) : option evstate :=
  match is with
  | [] => None
  | i :: r => match try_at s i with Some s' => Some s' | None => pick_from r s end
  end.
Definition pick s := pick_from (seq 0 (List.length s)) s.

Fixpoint schedule (fuel : nat) (s : evstate) : evstate :=
  match fuel with
  | O => s
  | S f => match pick s with Some s' => schedule f s' | None => s end
  end.

Definition ev_eqb (a b : event) : bool := if event_dec a b then true else false.
Definition swsr_check (s : evstate) : bool :=
  let idx := seq 0 (List.length s) in
  forallb (fun i => forallb (fun j =>
    Nat.eqb i j || forallb (fun e => is_host (ev_chan e) || negb (existsb (ev_eqb e) (nth j s [])))
                           (nth i s [])) idx) idx.
Definition all_empty (s : evstate) : bool :=
  forallb (fun l => match l with [] => true | _ => false end) s.

Definition check (s : evstate) : bool := swsr_check s && all_empty (schedule (size s) s).

(** ** Checker soundness *)
Lemma find_recv_sound c i js s j l2 : find_recv c i js s = Some (j, l2) ->
  i <> j /\ nth_error s j = Some (ERecv c :: l2).
Proof.
  induction js as [|j0 r IH]; cbn; [discriminate|].
  destruct (nth_error s j0) as [[|[c0|c0] l0]|] eqn:E; auto.
  destruct (chan_dec c c0) as [<-|]; auto.
  destruct (Nat.eq_dec i j0); auto.
  intros H; injection H as <- <-; auto.
Qed.

Lemma try_at_sound s i s' : try_at s i = Some s' -> rstep s s'.
Proof.
  unfold try_at; destruct (nth_error s i) as [[|e l]|] eqn:E; try discriminate.
  destruct (is_host (ev_chan e)) eqn:H.
  - intros X; injection X as <-; eapply StepHost; eauto.
  - destruct e as [c|c]; [|discriminate].
    destruct (find_recv c i _ s) as [[j l2]|] eqn:F; [|discriminate].
    apply find_recv_sound in F as [D Fj].
    intros X; injection X as <-; eapply StepPair; eauto.
Qed.

Lemma pick_sound s s' : pick s = Some s' -> rstep s s'.
Proof.
  unfold pick; generalize (seq 0 (List.length s)); intros is.
  induction is as [|i r IH]; cbn; [discriminate|].
  destruct (try_at s i) eqn:T; [intros X; injection X as <-; exact (try_at_sound _ _ _ T) | exact IH].
Qed.

Lemma schedule_star fuel s : rstar s (schedule fuel s).
Proof.
  revert s; induction fuel as [|f IH]; intros s; cbn; [constructor|].
  destruct (pick s) eqn:P; [|constructor].
  apply StarStep with e; [exact (pick_sound _ _ P) | apply IH].
Qed.

Lemma all_empty_final s : all_empty s = true -> final s.
Proof.
  unfold all_empty, final; intros A n l E.
  apply nth_error_In in E. rewrite forallb_forall in A. specialize (A l E).
  destruct l; [reflexivity | discriminate].
Qed.

Lemma swsr_check_sound s : swsr_check s = true -> swsr s.
Proof.
  unfold swsr_check, swsr; intros C i j li lj e Hi Hj Ei Ej He.
  assert (Li : i < List.length s) by (apply nth_error_Some; congruence).
  assert (Lj : j < List.length s) by (apply nth_error_Some; congruence).
  rewrite forallb_forall in C. specialize (C i ltac:(apply in_seq; lia)).
  rewrite forallb_forall in C. specialize (C j ltac:(apply in_seq; lia)).
  apply orb_true_iff in C as [C|C]; [apply Nat.eqb_eq; exact C|].
  rewrite (nth_error_nth _ _ _ Hi), forallb_forall in C. specialize (C e Ei).
  rewrite He in C; cbn in C. apply negb_true_iff in C.
  rewrite (nth_error_nth _ _ _ Hj) in C.
  assert (existsb (ev_eqb e) lj = true) as X
    by (apply existsb_exists; exists e; split; [exact Ej | unfold ev_eqb; destruct (event_dec e e); congruence]).
  congruence.
Qed.

Lemma check_sound s0 : check s0 = true ->
  swsr s0 /\ rstar s0 (schedule (size s0) s0) /\ final (schedule (size s0) s0).
Proof.
  unfold check; intros C; apply andb_true_iff in C as [W A].
  split; [exact (swsr_check_sound _ W)|]. split; [apply schedule_star | exact (all_empty_final _ A)].
Qed.

(** Deadlock freedom under any progress order: every reachable state is
    final or can step. Together with [rstep_size], every run ends in the
    final state within [size s0] steps. *)
Theorem check_deadlock_free s0 : check s0 = true ->
  forall s, rstar s0 s -> final s \/ exists s', rstep s s'.
Proof.
  intros C s R. destruct (check_sound _ C) as (W & Rf & F).
  destruct (reachable_can_finish _ _ W Rf F _ R) as [s | s t u H _]; [left; exact F | right; eauto].
Qed.

(** ** Event extraction from SpaDA IR *)
Fixpoint opt_concat {A} (xs : list (option (list A))) : option (list A) :=
  match xs with
  | [] => Some []
  | Some l :: r => option_map (app l) (opt_concat r)
  | None :: _ => None
  end.
Fixpoint opt_all {A} (xs : list (option A)) : option (list A) :=
  match xs with
  | [] => Some []
  | Some x :: r => option_map (cons x) (opt_all r)
  | None :: _ => None
  end.

Definition place_blocks (k : kernel) :=
  flat_map (fun b => match b with Place _ g fs => [(g, fs)] | _ => [] end) (blocks k).
Fixpoint find_field (fs : list field) (a : identifier) : option field :=
  match fs with
  | [] => None
  | f :: r => if id_dec (field_id f) a then Some f else find_field r a
  end.
Definition zconst (x : expression) : option Z := @eval_z unit _ no_memory empty x.
(** The length of a one-dimensional [Place] field. *)
Definition field_len (k : kernel) (a : identifier) : option nat :=
  match find_field (flat_map snd (place_blocks k)) a with
  | Some (Field (Array _ [n]) _ _) => option_map Z.to_nat (zconst n)
  | _ => None
  end.
Definition points (r : expression) : option (list Z) :=
  match r with
  | Range lo None _ => option_map (fun l => [l]) (zconst lo)
  | _ => @range_values unit _ no_memory empty r
  end.
(** The PEs: every point of every top-level [Place] grid. *)
Definition kernel_pes (k : kernel) : option (list pe) :=
  opt_concat (map (fun gf => match points (xrange (fst gf)), points (yrange (fst gf)) with
                             | Some xs, Some ys => Some (list_prod xs ys)
                             | _, _ => None
                             end) (place_blocks k)).

Section Extract.
Variable k : kernel.
Variable t : @task unit.
Notation uenv := (@env unit).

(** A send's payload length, as in [SpadaDataflow.payload]. *)
Definition send_len (e : uenv) (x : expression) : option nat :=
  match x with
  | EVar a => match e a with Some (VD _) => Some 1 | Some (VZ _) => None | None => field_len k a end
  | _ => Some 1
  end.

Fixpoint stmt_events (e : uenv) (s : statement) {struct s} : option (list event) :=
  let fix body_events (ss : list statement) (e : uenv) : option (list event) :=
    match ss with
    | [] => Some []
    | s :: r => match stmt_events e s, body_events r e with
                | Some l1, Some l2 => Some (l1 ++ l2) | _, _ => None end
    end in
  match s with
  | Assign (Slice _ [_]) _ | Assign (EVar _) _ | Await _ | AwaitAll => Some []
  | Send x c _ =>
      match send_len e x, chan_of true t no_memory e c with
      | Some n, Some ch => Some (repeat (ESend ch) n)
      | _, _ => None
      end
  | Receive (EVar a) c _ =>
      match e a, field_len k a, chan_of false t no_memory e c with
      | None, Some n, Some ch => Some (repeat (ERecv ch) n)
      | _, _, _ => None
      end
  | Foreach [Typed _ i] [r] (Typed _ x) c body _ =>
      match range_values no_memory e r, chan_of false t no_memory e c with
      | Some zs, Some ch =>
          opt_concat (map (fun z => option_map (cons (ERecv ch))
                             (body_events body (bind (bind e i (VZ z)) x (VD tt)))) zs)
      | _, _ => None
      end
  | Map [Typed _ i] [r] body _ | For [Typed _ i] [r] body =>
      match range_values no_memory e r with
      | Some zs => opt_concat (map (fun z => body_events body (bind e i (VZ z))) zs)
      | None => None
      end
  | Async body _ => body_events body e
  | _ => None
  end.

Fixpoint list_events (ss : list statement) (e : uenv) : option (list event) :=
  match ss with
  | [] => Some []
  | s :: r => match stmt_events e s, list_events r e with
              | Some l1, Some l2 => Some (l1 ++ l2) | _, _ => None end
  end.
End Extract.

Definition pe_events (k : kernel) (p : pe) : option (list event) :=
  match @pe_program unit _ k p with
  | Some ts => opt_concat (map (fun t => list_events k t (t_body t) (t_env t)) ts)
  | None => None
  end.
Definition init_state (k : kernel) : option evstate :=
  match kernel_pes k with
  | Some ps => opt_all (map (pe_events k) ps)
  | None => None
  end.
Definition kernel_check (k : kernel) : bool :=
  match init_state k with Some s => check s | None => false end.

(** ** Main theorem *)
Theorem kernel_check_sound k s0 : init_state k = Some s0 -> kernel_check k = true ->
  forall s, rstar s0 s -> final s \/ exists s', rstep s s'.
Proof. unfold kernel_check; intros I C; rewrite I in C; exact (check_deadlock_free _ C). Qed.

(** ** Applications *)
Lemma chain_reduce_checks :
  forallb (fun K => kernel_check (ChainReduce.kernel K)) [2; 3; 4; 5; 6]%Z = true.
Proof. vm_compute; reflexivity. Qed.
Lemma chain_reduce_recv_first_checks :
  forallb (fun K => kernel_check (ChainReduceRecvFirst.kernel K)) [2; 3; 4; 5; 6]%Z = true.
Proof. vm_compute; reflexivity. Qed.

Theorem chain_reduce_deadlock_free K s0 : (2 <= K <= 6)%Z ->
  init_state (ChainReduce.kernel K) = Some s0 ->
  forall s, rstar s0 s -> final s \/ exists s', rstep s s'.
Proof.
  intros B I; apply (kernel_check_sound _ _ I).
  pose proof chain_reduce_checks as C.
  assert (K = 2 \/ K = 3 \/ K = 4 \/ K = 5 \/ K = 6)%Z as KS by lia.
  cbn [forallb] in C; repeat rewrite andb_true_iff in C.
  destruct KS as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; tauto.
Qed.
Theorem chain_reduce_recv_first_deadlock_free K s0 : (2 <= K <= 6)%Z ->
  init_state (ChainReduceRecvFirst.kernel K) = Some s0 ->
  forall s, rstar s0 s -> final s \/ exists s', rstep s s'.
Proof.
  intros B I; apply (kernel_check_sound _ _ I).
  pose proof chain_reduce_recv_first_checks as C.
  assert (K = 2 \/ K = 3 \/ K = 4 \/ K = 5 \/ K = 6)%Z as KS by lia.
  cbn [forallb] in C; repeat rewrite andb_true_iff in C.
  destruct KS as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; tauto.
Qed.

(** Extraction succeeds, so the theorems above are not vacuous. *)
Lemma chain_reduce_extracts :
  forallb (fun K => match init_state (ChainReduce.kernel K),
                          init_state (ChainReduceRecvFirst.kernel K) with
                    | Some _, Some _ => true | _, _ => false end) [2; 3; 4; 5; 6]%Z = true.
Proof. vm_compute; reflexivity. Qed.

(** ** Negative test: crossed sends and receives

    PE (1,0) does [send(a, s1); send(b, s2)] while PE (0,0) does
    [receive(u, s2); receive(w, s1)]. Data only flows one way, and with
    buffers ([SpadaDataflow]) this runs, but under rendezvous each PE waits
    on the other at the very first step. *)
Module Crossed.
Import ChainReduce.
Definition f1 (s : string) := Field (Array (Scalar F32) [int 1]) (named s) false.
Definition kernel : Spada.kernel := Kernel "crossed" [] [] [
  Place xy (row 0 2) [f1 "a"; f1 "b"; f1 "u"; f1 "w"];
  Phase [
    Dataflow xy (row 0 2) [west "s1"; west "s2"];
    Compute xy (at_x 1) [Send (var "a") (var "s1") None; Send (var "b") (var "s2") None];
    Compute xy (at_x 0) [Receive (var "u") (var "s2") None; Receive (var "w") (var "s1") None]]].
End Crossed.

Lemma crossed_rejected : kernel_check Crossed.kernel = false.
Proof. vm_compute; reflexivity. Qed.

(** The rejection is a real deadlock, not checker incompleteness: the initial
    state is stuck and not final. *)
Lemma crossed_deadlocks : exists s0, init_state Crossed.kernel = Some s0 /\
  ~ final s0 /\ ~ exists s', rstep s0 s'.
Proof.
  eexists; split; [vm_compute; reflexivity|]. split.
  - intros F. specialize (F 0 _ eq_refl). discriminate.
  - intros [s' H]. inversion H as [i e l s Hi He | i j c l1 l2 s D Hc Hi Hj]; subst.
    + destruct i as [|[|[|i]]]; cbn in Hi; inversion Hi; subst; cbn in He; discriminate.
    + destruct i as [|[|[|i]]], j as [|[|[|j]]]; cbn in Hi, Hj; congruence.
Qed.

End SpadaDeadlock.
