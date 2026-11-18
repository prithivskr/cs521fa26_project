From Stdlib Require Import ZArith List String Bool Lia Sorting.Permutation.
From SpatialCSL Require Import SpadaIR ReduceSpec SpadaDataflow ChainReduce ChainReduceVariant.
Import ListNotations Spada.
Open Scope list_scope.

(** * A conservative data-race-freedom checker for SpaDA IR

    [SpadaDataflow.exec] runs every statement in program order. SpaDA
    (irspec/docs/spatial/async.md) lets an asynchronous statement ([send],
    [receive], [foreach], [map], [async]) with completion [Some c] run
    concurrently with later statements until [await c], and runs the
    iterations of a [map] in parallel. Program order is one legal schedule,
    so it gives the program's values only when there are no data races. This
    file discharges that assumption for a syntactic class of programs.

    ** The check ([race_free])

    Over every compute block body (also inside [Phase] and [MetaFor]):
    - every asynchronous statement has completion [None], or [Some c] and is
      immediately followed by [Await c];
    - [foreach] and [for] bodies obey the same discipline recursively (SpaDA
      requires asyncs inside a loop to be awaited inside it), and loops have
      one index and one range;
    - a [map] has one index [k], and its body consists only of assignments
      [x[k] = e] where every array access in [e] is [y[k]] (exactly the map
      index) and the only variable in [e] is [k] (a variable could name a
      scalar field), so it assigns no scalars and has no sends or receives;
    - anything else ([async], [close], multi-index loops) fails the check.

    ** Why this is enough

    - [Some c; Await c] is equivalent to [None]. A statement's completion
      only matters for the statements that may run before its [await]. With
      the [await] immediately next, no statement lies between the two, so
      the statement completes before any later one starts: it is blocking,
      exactly as if its completion were [None] (async.md, "Local Order":
      "asynchronous statements that immediately await their completion" are
      blocking). Hence under the check every statement outside a [map] is
      ordered before the next one in local order, and there is no
      statement-level concurrency on a PE; in particular no two sends or
      receives on one stream overlap.
    - The only concurrency left is between the iterations of a [map]. An
      iteration's body runs in program order (assignments are blocking).
      Iteration [z] reads and writes only cell [z] of each array, and
      assigns no locals, so two distinct iterations touch disjoint cells:
      no race. Moreover any interleaving of the statements of several
      iterations can be rearranged, by swapping adjacent statements of
      different iterations (they commute since they touch disjoint cells),
      into some sequential order of whole iterations. So it suffices to
      show that every order of the iterations gives [exec]'s result. That
      is what [race_free_sound] proves, for the relation [pexec] below,
      which is [exec] except that a [map] runs its iterations in any order
      (any permutation of its index list).

    States are compared extensionally ([st_eq]): memories are functions, and
    different orders build different (pointwise equal) functions. *)

(** ** The checker *)
Definition id_eqb (a b : identifier) : bool := if id_dec a b then true else false.

(** Expressions allowed in a [map] body over index [k]. *)
Fixpoint expr_ok (k : identifier) (x : expression) : bool :=
  match x with
  | EVar i => id_eqb i k
  | Constant _ _ | EParam _ _ => true
  | Unary _ a => expr_ok k a
  | Binary a _ b => expr_ok k a && expr_ok k b
  | Select a c b => expr_ok k a && expr_ok k c && expr_ok k b
  | FusedMultiplyAdd a b c => expr_ok k a && expr_ok k b && expr_ok k c
  | Slice _ [EVar i] => id_eqb i k
  | _ => false
  end.
Definition map_stmt_ok (k : identifier) (s : statement) : bool :=
  match s with
  | Assign (Slice _ [EVar i]) src => id_eqb i k && expr_ok k src
  | _ => false
  end.
Definition map_ok (k : identifier) (body : list statement) := forallb (map_stmt_ok k) body.

Definition done_of (s : statement) : completion :=
  match s with
  | Send _ _ d | Receive _ _ d | Close _ d | Foreach _ _ _ _ _ d | Map _ _ _ d
  | Async _ d => d
  | _ => None
  end.
(** A completion [Some c] must be awaited by the very next statement. *)
Definition awaited (d : completion) (rest : list statement) : bool :=
  match d, rest with
  | None, _ => true
  | Some c, Await c' :: _ => id_eqb c c'
  | Some _, _ => false
  end.
Fixpoint ok_seq (f : statement -> bool) (ss : list statement) : bool :=
  match ss with
  | [] => true
  | s :: r => f s && awaited (done_of s) r && ok_seq f r
  end.
Fixpoint ok_stmt (s : statement) : bool :=
  match s with
  | Assign _ _ | Send _ _ _ | Receive _ _ _ | Await _ | AwaitAll => true
  | Foreach [Typed _ _] [_] (Typed _ _) _ body _ => ok_seq ok_stmt body
  | For [Typed _ _] [_] body => ok_seq ok_stmt body
  | Map [Typed _ k] [_] body _ => map_ok k body
  | _ => false
  end.
Definition ok_list (ss : list statement) : bool := ok_seq ok_stmt ss.
Fixpoint ok_block (b : block) : bool :=
  match b with
  | Compute _ _ body => ok_list body
  | Phase bs | MetaFor _ _ bs => forallb ok_block bs
  | _ => true
  end.
Definition race_free (k : kernel) : bool := forallb ok_block (blocks k).

(** ** Map-reordering semantics *)
Section Reorder.
Context {V : Type} `{data_ops V}.
Variable t : @task V.

(** Statements that [exec] runs through a nested body. *)
Definition compound (s : statement) : bool :=
  match s with Foreach _ _ _ _ _ _ | Map _ _ _ _ | For _ _ _ | Async _ _ => true | _ => false end.
Definition well_shaped (s : statement) : bool :=
  match s with
  | Foreach [Typed _ _] [_] (Typed _ _) _ _ _ | Map [Typed _ _] [_] _ _ | For [Typed _ _] [_] _
  | Async _ _ => true
  | Foreach _ _ _ _ _ _ | Map _ _ _ _ | For _ _ _ => false
  | _ => true
  end.

(** [exec], [exec_list] and [iter_loop] as relations, except that [Map]
    runs its index list in any permuted order. *)
Inductive pexec : @env V -> statement -> @state V -> option (@state V) -> Prop :=
| P_basic : forall e s st, compound s = false -> pexec e s st (exec t e s st)
| P_ill : forall e s st, compound s = true -> well_shaped s = false -> pexec e s st None
| P_foreach : forall e ty k r ty' x c body d st zs ch out,
    range_values (mem st) e r = Some zs -> chan_of false t (mem st) e c = Some ch ->
    piter e k (Some (x, ch)) body zs st out ->
    pexec e (Foreach [Typed ty k] [r] (Typed ty' x) c body d) st out
| P_foreach_fail : forall e ty k r ty' x c body d st,
    match range_values (mem st) e r, chan_of false t (mem st) e c with
    | Some _, Some _ => False | _, _ => True end ->
    pexec e (Foreach [Typed ty k] [r] (Typed ty' x) c body d) st None
| P_map : forall e ty k r body d st zs zs' out,
    range_values (mem st) e r = Some zs -> Permutation zs zs' ->
    piter e k None body zs' st out -> pexec e (Map [Typed ty k] [r] body d) st out
| P_map_fail : forall e ty k r body d st,
    range_values (mem st) e r = None -> pexec e (Map [Typed ty k] [r] body d) st None
| P_for : forall e ty k r body st zs out,
    range_values (mem st) e r = Some zs ->
    piter e k None body zs st out -> pexec e (For [Typed ty k] [r] body) st out
| P_for_fail : forall e ty k r body st,
    range_values (mem st) e r = None -> pexec e (For [Typed ty k] [r] body) st None
| P_async : forall e body d st out,
    pexec_list body e st out -> pexec e (Async body d) st out
with pexec_list : list statement -> @env V -> @state V -> option (@state V) -> Prop :=
| PL_nil : forall e st, pexec_list [] e st (Some st)
| PL_fail : forall s r e st, pexec e s st None -> pexec_list (s :: r) e st None
| PL_cons : forall s r e st st' out,
    pexec e s st (Some st') -> pexec_list r e st' out -> pexec_list (s :: r) e st out
with piter : @env V -> identifier -> option (identifier * chan) -> list statement ->
             list Z -> @state V -> option (@state V) -> Prop :=
| PI_nil : forall e k src body st, piter e k src body [] st (Some st)
| PI_fetch_fail : forall e k src body z zs st,
    fetch src (bind e k (VZ z)) st = None -> piter e k src body (z :: zs) st None
| PI_body_fail : forall e k src body z zs st e1 st1,
    fetch src (bind e k (VZ z)) st = Some (e1, st1) ->
    pexec_list body e1 st1 None -> piter e k src body (z :: zs) st None
| PI_step : forall e k src body z zs st e1 st1 st2 out,
    fetch src (bind e k (VZ z)) st = Some (e1, st1) ->
    pexec_list body e1 st1 (Some st2) -> piter e k src body zs st2 out ->
    piter e k src body (z :: zs) st out.

Scheme pexec_mut := Induction for pexec Sort Prop
with pexec_list_mut := Induction for pexec_list Sort Prop
with piter_mut := Induction for piter Sort Prop.
Combined Scheme pexec_all from pexec_mut, pexec_list_mut, piter_mut.

(** ** Extensional state equality *)
Definition st_eq (a b : @state V) := (forall x, mem a x = mem b x) /\ (forall c, store a c = store b c).
Definition oeq (a b : option (@state V)) : Prop :=
  match a, b with Some a, Some b => st_eq a b | None, None => True | _, _ => False end.

Lemma st_eq_refl a : st_eq a a. Proof. split; reflexivity. Qed.
Lemma st_eq_sym a b : st_eq a b -> st_eq b a.
Proof. intros [M S]; split; intros; symmetry; auto. Qed.
Lemma st_eq_trans a b c : st_eq a b -> st_eq b c -> st_eq a c.
Proof. intros [M S] [M' S']; split; intros; etransitivity; eauto. Qed.
Lemma oeq_refl a : oeq a a. Proof. destruct a; simpl; auto using st_eq_refl. Qed.
Lemma oeq_sym a b : oeq a b -> oeq b a.
Proof. destruct a, b; simpl; auto using st_eq_sym. Qed.
Lemma oeq_trans a b c : oeq a b -> oeq b c -> oeq a c.
Proof. destruct a, b, c; simpl; try tauto; eauto using st_eq_trans. Qed.
Lemma st_eq_set_mem a b x l : st_eq a b -> st_eq (set_mem a x l) (set_mem b x l).
Proof.
  intros [M S]; split; intros y; [|exact (S y)].
  unfold set_mem; simpl; destruct (id_dec x y); auto.
Qed.
Lemma st_eq_set_store a b c l : st_eq a b -> st_eq (set_store a c l) (set_store b c l).
Proof.
  intros [M S]; split; intros y; [exact (M y)|].
  unfold set_store; simpl; destruct (chan_dec c y); auto.
Qed.

(** ** Reads depend on memory only pointwise *)
Lemma eval_ext m1 m2 (e : @env V) : (forall y, m1 y = m2 y) -> forall x, eval m1 e x = eval m2 e x.
Proof.
  intros Hm. fix IH 1. intros x. destruct x; cbn [eval]; try reflexivity.
  - rewrite Hm; reflexivity.
  - destruct op; try reflexivity. rewrite IH; reflexivity.
  - rewrite !IH; reflexivity.
  - rewrite !IH; reflexivity.
  - rewrite !IH; reflexivity.
  - match goal with l : list expression |- _ => destruct l as [|i [|]] end; try reflexivity.
    rewrite IH, Hm; reflexivity.
Qed.
Lemma eval_z_ext m1 m2 (e : @env V) x : (forall y, m1 y = m2 y) -> eval_z m1 e x = eval_z m2 e x.
Proof. intros Hm; unfold eval_z; rewrite (eval_ext m1 m2 e Hm); reflexivity. Qed.
Lemma eval_zs_ext m1 m2 (e : @env V) xs : (forall y, m1 y = m2 y) -> eval_zs m1 e xs = eval_zs m2 e xs.
Proof. intros Hm; induction xs; simpl; auto. rewrite (eval_z_ext m1 m2 e a Hm), IHxs; reflexivity. Qed.
Lemma range_values_ext m1 m2 (e : @env V) r : (forall y, m1 y = m2 y) -> range_values m1 e r = range_values m2 e r.
Proof.
  intros Hm; unfold range_values. destruct r; try reflexivity. destruct stop; try reflexivity.
  rewrite !(eval_z_ext m1 m2 e _ Hm). destruct stride; try rewrite !(eval_z_ext m1 m2 e _ Hm); reflexivity.
Qed.
Lemma chan_of_ext b m1 m2 (e : @env V) x : (forall y, m1 y = m2 y) -> chan_of b t m1 e x = chan_of b t m2 e x.
Proof.
  intros Hm; induction x; cbn [chan_of]; try reflexivity.
  - destruct (find_stream (t_streams t) id) as [[? ? []]|]; try reflexivity.
    destruct b; cbn [source]; try reflexivity. rewrite !(eval_z_ext m1 m2 e _ Hm); reflexivity.
  - rewrite (eval_z_ext m1 m2 e _ Hm), IHx1, IHx3; reflexivity.
  - rewrite (eval_zs_ext m1 m2 e _ Hm); reflexivity.
Qed.
Lemma payload_ext a b (e : @env V) x : st_eq a b -> payload a e x = payload b e x.
Proof.
  intros [M S]; unfold payload. destruct x; try (rewrite (eval_ext _ _ e M); reflexivity).
  rewrite M; reflexivity.
Qed.
Lemma fetch_ext src (e : @env V) a b : st_eq a b ->
  match fetch src e a, fetch src e b with
  | None, None => True
  | Some (e1, a1), Some (e2, b1) => e1 = e2 /\ st_eq a1 b1
  | _, _ => False end.
Proof.
  intros Hab; destruct src as [[x c]|]; simpl; [|auto].
  destruct Hab as [M S]. rewrite (S c). destruct (store b c); auto.
  split; [reflexivity|]. apply st_eq_set_store; split; auto.
Qed.

(** Non-loop statements respect [st_eq]. *)
Lemma basic_congr e s a b : ok_stmt s = true -> compound s = false -> st_eq a b ->
  oeq (exec t e s a) (exec t e s b).
Proof.
  intros Ok C Hab. pose proof Hab as [M S].
  destruct s; try discriminate; cbn [exec].
  - destruct destination as [f| | | | | | |arr indices|]; try exact I.
    { rewrite (eval_ext _ _ e M source0), M.
      destruct (e f), (mem b f) as [|? []], (eval (mem b) e source0) as [[|]|]; try exact I.
      simpl; auto using st_eq_set_mem. }
    destruct indices as [|i [|]]; try exact I.
    rewrite (eval_z_ext _ _ e i M), (eval_ext _ _ e M source0), M.
    destruct (eval_z (mem b) e i), (eval (mem b) e source0) as [[|]|]; try exact I.
    destruct (0 <=? z)%Z; try exact I.
    destruct (update_nth _ _ _); simpl; auto using st_eq_set_mem.
  - rewrite (payload_ext a b e _ Hab), (chan_of_ext true _ _ e stream M).
    destruct (SpadaDataflow.payload b e _), (chan_of true t (mem b) e stream); simpl; auto.
    rewrite S; apply st_eq_set_store; auto.
  - destruct destination; try exact I.
    rewrite (chan_of_ext false _ _ e stream M).
    destruct (e id), (chan_of false t (mem b) e stream); try exact I.
    rewrite M, S. destruct (Nat.leb _ _); simpl; auto.
    apply st_eq_set_store, st_eq_set_mem; auto.
  - exact Hab.
  - exact Hab.
Qed.

(** ** Map iterations touch only their own cell *)
Lemma update_nth_some (l : list V) n v l' : update_nth l n v = Some l' ->
  List.length l' = List.length l /\ nth_error l' n = Some v /\
  forall m, m <> n -> nth_error l' m = nth_error l m.
Proof.
  revert n l'; induction l as [|h l IH]; intros n l' U; [discriminate|].
  destruct n as [|n]; simpl in U.
  - injection U as <-. repeat split; auto. intros [|m] Hm; simpl; congruence.
  - destruct (update_nth l n v) as [l1|] eqn:U1; [|discriminate]. injection U as <-.
    destruct (IH n l1 U1) as (L & N & O). simpl; repeat split; auto.
    intros [|m] Hm; simpl; auto.
Qed.
Lemma update_nth_none_iff (l : list V) n v : update_nth l n v = None <-> (List.length l <= n)%nat.
Proof.
  revert n; induction l as [|h l IH]; intros [|n]; simpl; try (split; auto; lia).
  - split; [discriminate|lia].
  - specialize (IH n). destruct (update_nth l n v); simpl.
    + split; [discriminate|]. intros Hl. assert (X : Some l0 = None) by (apply IH; lia). discriminate.
    + split; [intros _; assert (X : (None : option (list V)) = None) by reflexivity; apply IH in X; lia|reflexivity].
Qed.

Lemma eval_local k z m1 m2 (e : @env V) x : expr_ok k x = true -> e k = Some (VZ z) ->
  (forall y, nth_error (m1 y) (Z.to_nat z) = nth_error (m2 y) (Z.to_nat z)) ->
  eval m1 e x = eval m2 e x.
Proof.
  intros Ok Ek Hc; induction x; cbn [eval]; cbn [expr_ok] in Ok;
    repeat rewrite andb_true_iff in Ok; try reflexivity.
  - unfold id_eqb in Ok; destruct (id_dec id k); [subst; rewrite Ek; reflexivity|discriminate].
  - destruct op; try reflexivity. rewrite IHx by tauto; reflexivity.
  - rewrite IHx1, IHx2 by tauto; reflexivity.
  - rewrite IHx1, IHx2, IHx3 by tauto; reflexivity.
  - rewrite IHx1, IHx2, IHx3 by tauto; reflexivity.
  - destruct indices as [|[] [|]]; try discriminate.
    unfold id_eqb in Ok; destruct (id_dec id k); [subst|discriminate].
    cbn [eval]; rewrite Ek. destruct (0 <=? z)%Z; [rewrite Hc|]; reflexivity.
Qed.

Definition agree n (a b : @state V) := forall x,
  List.length (mem a x) = List.length (mem b x) /\ nth_error (mem a x) n = nth_error (mem b x) n.
Definition frame n (a a' : @state V) := (forall c, store a' c = store a c) /\ forall x,
  List.length (mem a' x) = List.length (mem a x) /\
  forall m, m <> n -> nth_error (mem a' x) m = nth_error (mem a x) m.

Lemma frame_refl n a : frame n a a. Proof. split; auto. Qed.
Lemma frame_trans n a b c : frame n a b -> frame n b c -> frame n a c.
Proof.
  intros [S1 F1] [S2 F2]; split; [intros; rewrite S2; auto|].
  intros x; destruct (F1 x) as [L1 O1], (F2 x) as [L2 O2]; split; [lia|].
  intros m Hm; rewrite O2, O1; auto.
Qed.
Lemma frame_agree n n' a a' : frame n a a' -> n' <> n -> agree n' a a'.
Proof. intros [_ F] D x; destruct (F x) as [L O]; split; [auto|]. symmetry; auto. Qed.

Lemma map_ok_cons k s r : map_ok k (s :: r) = true -> map_stmt_ok k s = true /\ map_ok k r = true.
Proof. unfold map_ok; simpl; rewrite andb_true_iff; auto. Qed.

(** One iteration's effect on cell [n] depends only on cell [n] and the
    array lengths, and it changes nothing else. *)
Lemma iter_local k z body (e : @env V) : map_ok k body = true -> e k = Some (VZ z) -> (0 <= z)%Z ->
  forall a b, agree (Z.to_nat z) a b ->
  match exec_list t body e a, exec_list t body e b with
  | None, None => True
  | Some a', Some b' => agree (Z.to_nat z) a' b' /\ frame (Z.to_nat z) a a' /\ frame (Z.to_nat z) b b'
  | _, _ => False
  end.
Proof.
  intros Ok Ek Z0; induction body as [|s r IH]; intros a b Ag.
  - simpl; auto using frame_refl.
  - apply map_ok_cons in Ok as [Os Or]. rewrite !exec_list_cons.
    destruct s as [d src| | | | | | | | |]; try discriminate.
    destruct d; try discriminate. destruct indices as [|[] [|]]; try discriminate.
    cbn [map_stmt_ok] in Os; rewrite andb_true_iff in Os; destruct Os as [Oi Osrc].
    unfold id_eqb in Oi; destruct (id_dec id k); [subst|discriminate].
    cbn [exec]. unfold eval_z; cbn [eval]. rewrite Ek.
    rewrite (eval_local k z (mem a) (mem b) e src Osrc Ek) by (intros y; apply (Ag y)).
    destruct (eval (mem b) e src) as [[|v]|]; auto.
    rewrite (proj2 (Z.leb_le 0 z) Z0).
    destruct (Ag array) as [La Na].
    destruct (update_nth (mem a array) (Z.to_nat z) v) as [la|] eqn:Ua,
             (update_nth (mem b array) (Z.to_nat z) v) as [lb|] eqn:Ub; cbn [option_map].
    + destruct (update_nth_some _ _ _ _ Ua) as (LA & NA & OA).
      destruct (update_nth_some _ _ _ _ Ub) as (LB & NB & OB).
      assert (Ag1 : agree (Z.to_nat z) (set_mem a array la) (set_mem b array lb)).
      { intros y; destruct (id_dec array y) as [<-|D].
        - rewrite !mem_set_mem_same; split; congruence.
        - rewrite !mem_set_mem_other by exact D; apply Ag. }
      assert (Fa : frame (Z.to_nat z) a (set_mem a array la)).
      { split; [reflexivity|]. intros y; destruct (id_dec array y) as [<-|D].
        - rewrite mem_set_mem_same; auto.
        - rewrite !mem_set_mem_other by exact D; auto. }
      assert (Fb : frame (Z.to_nat z) b (set_mem b array lb)).
      { split; [reflexivity|]. intros y; destruct (id_dec array y) as [<-|D].
        - rewrite mem_set_mem_same; auto.
        - rewrite !mem_set_mem_other by exact D; auto. }
      specialize (IH Or _ _ Ag1).
      destruct (exec_list t r e (set_mem a array la)), (exec_list t r e (set_mem b array lb)); auto.
      destruct IH as (A' & F1 & F2); eauto using frame_trans.
    + apply update_nth_none_iff in Ub. apply update_nth_some in Ua as (LA & NA & _).
      assert (Z.to_nat z < List.length la)%nat by (apply nth_error_Some; congruence). lia.
    + apply update_nth_none_iff in Ua. apply update_nth_some in Ub as (LB & NB & _).
      assert (Z.to_nat z < List.length lb)%nat by (apply nth_error_Some; congruence). lia.
    + exact I.
Qed.

(** A negative index makes a non-empty map body fail. *)
Lemma iter_neg k z body (e : @env V) a : map_ok k body = true -> body <> [] ->
  e k = Some (VZ z) -> (z < 0)%Z -> exec_list t body e a = None.
Proof.
  intros Ok NE Ek Neg. destruct body as [|s r]; [congruence|].
  apply map_ok_cons in Ok as [Os _]. rewrite exec_list_cons.
  destruct s as [d src| | | | | | | | |]; try discriminate.
  destruct d; try discriminate. destruct indices as [|[] [|]]; try discriminate.
  cbn [map_stmt_ok] in Os; rewrite andb_true_iff in Os; destruct Os as [Oi _].
  unfold id_eqb in Oi; destruct (id_dec id k); [subst|discriminate].
  cbn [exec]. unfold eval_z; cbn [eval]. rewrite Ek.
  destruct (eval (mem a) e src) as [[|v]|]; auto.
  replace (0 <=? z)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Definition obind (o : option (@state V)) (f : @state V -> option (@state V)) :=
  match o with Some x => f x | None => None end.
Lemma oeq_bind o1 o2 f g : oeq o1 o2 -> (forall a b, st_eq a b -> oeq (f a) (g b)) ->
  oeq (obind o1 f) (obind o2 g).
Proof. intros E F; destruct o1, o2; simpl in *; auto; contradiction. Qed.
Lemma obind_assoc o f g : obind (obind o f) g = obind o (fun x => obind (f x) g).
Proof. destruct o; reflexivity. Qed.

Lemma lists_eq_cells (l1 l2 : list V) : (forall m, nth_error l1 m = nth_error l2 m) -> l1 = l2.
Proof. apply nth_error_ext. Qed.

(** One iteration respects [st_eq]. *)
Lemma iteration_congr k body (e : @env V) z a b : map_ok k body = true ->
  st_eq a b -> oeq (exec_list t body (bind e k (VZ z)) a) (exec_list t body (bind e k (VZ z)) b).
Proof.
  intros Ok Hab. pose proof (bind_same e k (VZ z)) as Ek.
  destruct body as [|s r] eqn:B; [exact Hab|]. rewrite <- B in *.
  destruct (Z.ltb_spec z 0) as [Neg|Pos].
  - rewrite !(iter_neg k z body _ _ Ok) by (auto; congruence). exact I.
  - assert (Ag : agree (Z.to_nat z) a b) by (intros x; destruct Hab as [M _]; rewrite M; auto).
    pose proof (iter_local k z body _ Ok Ek Pos a b Ag) as L.
    destruct (exec_list t body _ a) as [a'|], (exec_list t body _ b) as [b'|]; try contradiction; [|exact I].
    destruct L as (A & [Sa Fa] & [Sb Fb]); destruct Hab as [M S]. split.
    + intros x; apply lists_eq_cells; intros m.
      destruct (Nat.eq_dec m (Z.to_nat z)) as [->|D]; [apply A|].
      destruct (Fa x) as [_ Oa], (Fb x) as [_ Ob]. rewrite Oa, Ob, M by exact D; reflexivity.
    + intros c; rewrite Sa, Sb; auto.
Qed.

(** Two iterations commute. *)
Lemma iteration_commute k body (e : @env V) z1 z2 a : map_ok k body = true ->
  oeq (obind (exec_list t body (bind e k (VZ z1)) a) (exec_list t body (bind e k (VZ z2))))
      (obind (exec_list t body (bind e k (VZ z2)) a) (exec_list t body (bind e k (VZ z1)))).
Proof.
  intros Ok. destruct body as [|s r] eqn:B; [simpl; apply st_eq_refl|].
  assert (NE : body <> []) by congruence. rewrite <- B in *. clear B.
  set (I1 := exec_list t body (bind e k (VZ z1))).
  set (I2 := exec_list t body (bind e k (VZ z2))).
  pose proof (bind_same e k (VZ z1)) as E1. pose proof (bind_same e k (VZ z2)) as E2.
  destruct (Z.ltb_spec z1 0) as [N1|P1].
  { unfold I1; rewrite (iter_neg k z1 body _ a Ok NE E1 N1); simpl.
    destruct (I2 a); simpl; [|exact I]. unfold I1; rewrite (iter_neg k z1 body _ _ Ok NE E1 N1). exact I. }
  destruct (Z.ltb_spec z2 0) as [N2|P2].
  { unfold I2 at 2; rewrite (iter_neg k z2 body _ a Ok NE E2 N2); simpl.
    destruct (I1 a); simpl; [|exact I]. unfold I2; rewrite (iter_neg k z2 body _ _ Ok NE E2 N2). exact I. }
  destruct (Z.eq_dec z1 z2) as [<-|D]; [apply oeq_refl|].
  set (n1 := Z.to_nat z1). set (n2 := Z.to_nat z2).
  assert (Dn : n1 <> n2) by (unfold n1, n2; lia).
  assert (Ag : forall n x, agree n x x) by (intros n x y; auto).
  pose proof (iter_local k z1 body _ Ok E1 P1 a a (Ag _ a)) as L1.
  pose proof (iter_local k z2 body _ Ok E2 P2 a a (Ag _ a)) as L2.
  fold I1 I2 n1 n2 in L1, L2.
  destruct (I1 a) as [a1|] eqn:A1, (I2 a) as [a2|] eqn:A2; simpl.
  - destruct L1 as (_ & F1 & _), L2 as (_ & F2 & _).
    pose proof (iter_local k z2 body _ Ok E2 P2 a a1 (frame_agree _ _ _ _ F1 (not_eq_sym Dn))) as L12.
    pose proof (iter_local k z1 body _ Ok E1 P1 a a2 (frame_agree _ _ _ _ F2 Dn)) as L21.
    fold I1 I2 n1 n2 in L12, L21. rewrite A2 in L12. rewrite A1 in L21.
    destruct (I2 a1) as [b1|], (I1 a2) as [b2|]; try contradiction.
    destruct L12 as (G12 & _ & H12), L21 as (G21 & _ & H21).
    destruct F1 as [S1 F1], F2 as [S2 F2], H12 as [T12 H12], H21 as [T21 H21]. split.
    + intros x; apply lists_eq_cells; intros m.
      destruct (G12 x) as [_ G12x], (G21 x) as [_ G21x].
      destruct (H12 x) as [_ H12x], (H21 x) as [_ H21x].
      destruct (F1 x) as [_ F1x], (F2 x) as [_ F2x].
      destruct (Nat.eq_dec m n1) as [->|D1].
      * rewrite H12x by exact Dn. exact G21x.
      * destruct (Nat.eq_dec m n2) as [->|D2].
        -- rewrite H21x by exact (not_eq_sym Dn). symmetry; exact G12x.
        -- rewrite H12x, H21x, F1x, F2x by assumption; reflexivity.
    + intros c; rewrite T12, T21, S1, S2; reflexivity.
  - destruct L1 as (_ & F1 & _).
    pose proof (iter_local k z2 body _ Ok E2 P2 a a1 (frame_agree _ _ _ _ F1 (not_eq_sym Dn))) as L12.
    fold I2 n2 in L12. rewrite A2 in L12. destruct (I2 a1); [contradiction|exact I].
  - destruct L2 as (_ & F2 & _).
    pose proof (iter_local k z1 body _ Ok E1 P1 a a2 (frame_agree _ _ _ _ F2 Dn)) as L21.
    fold I1 n1 in L21. rewrite A1 in L21. destruct (I1 a2); [contradiction|exact I].
  - exact I.
Qed.

Lemma iter_loop_none_cons body (e : @env V) k z zs a :
  iter_loop (exec_list t body) e k None (z :: zs) a =
  obind (exec_list t body (bind e k (VZ z)) a) (iter_loop (exec_list t body) e k None zs).
Proof. reflexivity. Qed.

Lemma iter_loop_none_cons2 body (e : @env V) k z1 z2 zs a :
  iter_loop (exec_list t body) e k None (z1 :: z2 :: zs) a =
  obind (obind (exec_list t body (bind e k (VZ z1)) a) (exec_list t body (bind e k (VZ z2))))
    (iter_loop (exec_list t body) e k None zs).
Proof. cbn [iter_loop fetch]. destruct (exec_list t body (bind e k (VZ z1)) a); reflexivity. Qed.

Lemma map_iter_congr k body (e : @env V) zs : map_ok k body = true -> forall a b, st_eq a b ->
  oeq (iter_loop (exec_list t body) e k None zs a) (iter_loop (exec_list t body) e k None zs b).
Proof.
  intros Ok; induction zs as [|z zs IH]; intros a b Hab; [exact Hab|].
  rewrite !iter_loop_none_cons. apply oeq_bind; auto. eapply iteration_congr; eauto.
Qed.

(** Any order of a map's iterations gives the same result. *)
Lemma map_perm k body (e : @env V) zs zs' : map_ok k body = true -> Permutation zs zs' ->
  forall a b, st_eq a b ->
  oeq (iter_loop (exec_list t body) e k None zs a) (iter_loop (exec_list t body) e k None zs' b).
Proof.
  intros Ok P; induction P as [|z l l' P IH|z1 z2 l|l l' l'' P1 IH1 P2 IH2]; intros a b Hab.
  - exact Hab.
  - rewrite !iter_loop_none_cons. apply oeq_bind; auto. eapply iteration_congr; eauto.
  - rewrite !iter_loop_none_cons2.
    eapply oeq_trans; [apply oeq_bind; [apply iteration_commute; exact Ok|]|].
    + intros x y Hxy; apply (map_iter_congr k body e l Ok _ _ Hxy).
    + apply oeq_bind; [|intros x y Hxy; apply (map_iter_congr k body e l Ok _ _ Hxy)].
      apply oeq_bind; [eapply iteration_congr; eauto|].
      intros x y Hxy; eapply iteration_congr; eauto.
  - eapply oeq_trans; [apply IH1; exact Hab|]. apply IH2, st_eq_refl.
Qed.

(** ** Soundness *)
Lemma ok_list_cons s r : ok_list (s :: r) = true -> ok_stmt s = true /\ ok_list r = true.
Proof. unfold ok_list; cbn [ok_seq]; rewrite !andb_true_iff; tauto. Qed.
Lemma map_ok_ok_list k body : map_ok k body = true -> ok_list body = true.
Proof.
  induction body as [|s r IH]; [reflexivity|]. intros Ok; apply map_ok_cons in Ok as [Os Or].
  destruct s; try discriminate. unfold ok_list; cbn [ok_seq ok_stmt done_of awaited]. apply IH, Or.
Qed.
Lemma ok_well_shaped s : ok_stmt s = true -> well_shaped s = true.
Proof.
  destruct s as [ | | | | is rs [] ? ? ? | is rs ? ? | is rs ? | | | ]; try reflexivity;
    cbn [ok_stmt well_shaped]; destruct is as [|[] [|]]; try discriminate;
    destruct rs as [|? [|]]; try discriminate; reflexivity.
Qed.

Theorem pexec_sound_all :
  (forall e s st out, pexec e s st out -> ok_stmt s = true ->
     forall st0, st_eq st st0 -> oeq out (exec t e s st0)) /\
  (forall ss e st out, pexec_list ss e st out -> ok_list ss = true ->
     forall st0, st_eq st st0 -> oeq out (exec_list t ss e st0)) /\
  (forall e k src body zs st out, piter e k src body zs st out -> ok_list body = true ->
     forall st0, st_eq st st0 -> oeq out (iter_loop (exec_list t body) e k src zs st0)).
Proof.
  apply pexec_all.
  - intros e s st C Ok st0 E. apply basic_congr; auto.
  - intros e s st C W Ok. rewrite ok_well_shaped in W by exact Ok. discriminate.
  - intros e ty k r ty' x c body d st zs ch out R C Pi IH Ok st0 E.
    rewrite exec_foreach, <- (range_values_ext (mem st) (mem st0)) by apply E.
    rewrite <- (chan_of_ext false (mem st) (mem st0)) by apply E. rewrite R, C.
    apply IH; [exact Ok|exact E].
  - intros e ty k r ty' x c body d st F Ok st0 E.
    rewrite exec_foreach, <- (range_values_ext (mem st) (mem st0)) by apply E.
    rewrite <- (chan_of_ext false (mem st) (mem st0)) by apply E.
    destruct (range_values (mem st) e r), (chan_of false t (mem st) e c); try contradiction; exact I.
  - intros e ty k r body d st zs zs' out R P Pi IH Ok st0 E.
    rewrite exec_map, <- (range_values_ext (mem st) (mem st0)) by apply E. rewrite R.
    eapply oeq_trans; [apply IH; [eapply map_ok_ok_list; exact Ok|exact E]|].
    apply (map_perm k); [exact Ok|apply Permutation_sym, P|apply st_eq_refl].
  - intros e ty k r body d st R Ok st0 E.
    rewrite exec_map, <- (range_values_ext (mem st) (mem st0)) by apply E. rewrite R. exact I.
  - intros e ty k r body st zs out R Pi IH Ok st0 E.
    change (exec t e (For [Typed ty k] [r] body) st0) with
      (match range_values (mem st0) e r with
       | Some zs => iter_loop (exec_list t body) e k None zs st0 | None => None end).
    rewrite <- (range_values_ext (mem st) (mem st0)) by apply E. rewrite R.
    apply IH; [exact Ok|exact E].
  - intros e ty k r body st R Ok st0 E.
    change (exec t e (For [Typed ty k] [r] body) st0) with
      (match range_values (mem st0) e r with
       | Some zs => iter_loop (exec_list t body) e k None zs st0 | None => None end).
    rewrite <- (range_values_ext (mem st) (mem st0)) by apply E. rewrite R. exact I.
  - intros e body d st out _ _ Ok. discriminate.
  - intros e st _ st0 E. exact E.
  - intros s r e st Ps IH Ok st0 E. apply ok_list_cons in Ok as [Os Or].
    rewrite exec_list_cons. specialize (IH Os st0 E).
    destruct (exec t e s st0); [contradiction|exact I].
  - intros s r e st st' out Ps IHs Pr IHr Ok st0 E. apply ok_list_cons in Ok as [Os Or].
    rewrite exec_list_cons. specialize (IHs Os st0 E).
    destruct (exec t e s st0) as [s0|]; [|contradiction]. apply IHr; auto.
  - intros e k src body st _ st0 E. exact E.
  - intros e k src body z zs st F Ok st0 E. cbn [iter_loop].
    pose proof (fetch_ext src (bind e k (VZ z)) st st0 E) as X. rewrite F in X.
    destruct (fetch src _ st0) as [[]|]; [contradiction|exact I].
  - intros e k src body z zs st e1 st1 F Pb IH Ok st0 E. cbn [iter_loop].
    pose proof (fetch_ext src (bind e k (VZ z)) st st0 E) as X. rewrite F in X.
    destruct (fetch src _ st0) as [[e2 st1']|]; [|contradiction]. destruct X as [<- E1].
    specialize (IH Ok st1' E1). destruct (exec_list t body e1 st1'); [contradiction|exact I].
  - intros e k src body z zs st e1 st1 st2 out F Pb IHb Pr IHr Ok st0 E. cbn [iter_loop].
    pose proof (fetch_ext src (bind e k (VZ z)) st st0 E) as X. rewrite F in X.
    destruct (fetch src _ st0) as [[e2 st1']|]; [|contradiction]. destruct X as [<- E1].
    specialize (IHb Ok st1' E1). destruct (exec_list t body e1 st1') as [s2|]; [|contradiction].
    apply IHr; auto.
Qed.

(** Main theorem: for a statement that passes the check, every outcome of
    running it with map iterations in any order is [exec]'s outcome. *)
Theorem race_free_sound e s st out :
  ok_stmt s = true -> pexec e s st out -> oeq out (exec t e s st).
Proof. intros Ok P. exact (proj1 pexec_sound_all e s st out P Ok st (st_eq_refl st)). Qed.
Theorem race_free_list_sound ss e st out :
  ok_list ss = true -> pexec_list ss e st out -> oeq out (exec_list t ss e st).
Proof. intros Ok P. exact (proj1 (proj2 pexec_sound_all) ss e st out P Ok st (st_eq_refl st)). Qed.
End Reorder.

(** ** Kernels *)
Lemma computes_ok {V : Type} `{data_ops V} bs p cs body : forallb ok_block bs = true ->
  In (cs, body) (@computes_at V _ bs p) -> ok_list body = true.
Proof.
  intros Ok Hin. unfold computes_at in Hin. apply in_flat_map in Hin as [b [Hb Hin]].
  rewrite forallb_forall in Ok. specialize (Ok b Hb).
  destruct b; try contradiction. destruct (in_grid grid p); [|contradiction].
  destruct Hin as [Eq|[]]. injection Eq as <- <-. exact Ok.
Qed.
Lemma phase_tasks_ok {V : Type} `{data_ops V} n g bs p (ts : list (@task V)) : forallb ok_block bs = true ->
  phase_tasks n g bs p = Some ts -> forall tk, In tk ts -> ok_list (t_body tk) = true.
Proof.
  revert n ts; induction bs as [|b bs IH]; intros n ts Ok P tk Hin.
  - injection P as <-; contradiction.
  - cbn [forallb] in Ok; apply andb_true_iff in Ok as [Ob Obs].
    destruct b; cbn [phase_tasks] in P; try discriminate; try exact (IH n ts Obs P tk Hin).
    unfold phase_task in P. destruct (forallb flat_block body); [|discriminate].
    destruct (computes_at body p) as [|[cs b'] [|]] eqn:C; try discriminate;
      destruct (phase_tasks (S n) g bs p) as [us|] eqn:U; try discriminate;
      injection P as <-.
    + exact (IH (S n) us Obs U tk Hin).
    + destruct Hin as [<-|Hin]; [|exact (IH (S n) us Obs U tk Hin)]. cbn [t_body]. apply (computes_ok body p cs); [exact Ob|].
      rewrite C; left; reflexivity.
Qed.
Lemma race_free_tasks {V : Type} `{data_ops V} k p (ts : list (@task V)) tk :
  race_free k = true -> pe_program k p = Some ts -> In tk ts -> ok_list (t_body tk) = true.
Proof. intros Ok P; exact (phase_tasks_ok _ _ _ _ _ Ok P tk). Qed.

(** Every compute block instance of a race-free kernel computes [exec]'s
    result under any order of its map iterations. *)
Theorem race_free_run_task {V : Type} `{data_ops V} k p ts (tk : @task V) st out :
  race_free k = true -> pe_program k p = Some ts -> In tk ts ->
  pexec_list tk (t_body tk) (t_env tk) st out -> oeq out (run_task tk st).
Proof.
  intros Ok P Hin R. apply race_free_list_sound; [|exact R].
  exact (race_free_tasks k p ts tk Ok P Hin).
Qed.

(** ** The chain-reduction kernels (for every [K]) *)
Theorem chain_reduce_race_free K : race_free (ChainReduce.kernel K) = true.
Proof. reflexivity. Qed.
Theorem chain_reduce_recv_first_race_free K : race_free (ChainReduceRecvFirst.kernel K) = true.
Proof. reflexivity. Qed.

(** Sanity checks: an un-awaited send, and a map reading a neighbour cell,
    are rejected. *)
Example reject_unawaited :
  ok_list [Send (var "a") (var "s") (Some (named "c")); Assign (Slice (named "a") [int 0]) (int 1)]
  = false.
Proof. reflexivity. Qed.
Example reject_map_neighbour :
  ok_stmt (Map [coord "k"] [interval 0 4]
    [Assign (Slice (named "a") [var "k"])
            (Slice (named "a") [Binary (var "k") Spada.Plus (int 1)])] None) = false.
Proof. reflexivity. Qed.

(** All of these print "Closed under the global context". *)
Print Assumptions race_free_sound.
Print Assumptions race_free_run_task.
Print Assumptions chain_reduce_race_free.
Print Assumptions chain_reduce_recv_first_race_free.
