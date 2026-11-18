From Stdlib Require Import List Arith Lia Bool Permutation.
From Kahn Require Import Spec Kahn ChainReduce.
Import ListNotations.

(** * Correctness of the chain-reduction kernel

    Main results, for every [K >= 2], vector length [n], and both variants:
    - [chain_reduce_correct]: the run completes, [out[0]] holds [reduce inputs]
      (the right-nested element-wise sum), and every other stream is consumed;
    - [chain_reduce_any_order]: with associative, commutative addition, the
      output is the sum in any order of the PEs' vectors;
    - [chain_reduce_K1_deadlocks]: with [K = 1] the kernel gets stuck.

    Proof idea: run PEs [K-1] down to [0]. After PEs [K-1 .. i] have run, the
    stream PE [i] sends on holds [a_i + (... + a_{K-1})] ([Inv]). *)

(** ** Kernel shape *)
(** Each receiver listens on the colour its east neighbour sends on. *)
Lemma colors_match : forall K i, S i <= K - 1 -> in_color i = out_color K (S i).
Proof.
  intros K i H; unfold in_color, out_color, east_color.
  destruct (Nat.eqb_spec (S i) (K - 1)) as [E|E].
  - rewrite <- E, Nat.even_succ. destruct i as [|i]; [reflexivity|].
    change (S i =? 0) with false. destruct (Nat.odd (S i)); reflexivity.
  - rewrite Nat.odd_succ, <- Nat.negb_odd. destruct i as [|i]; [reflexivity|].
    change (S i =? 0) with false. destruct (Nat.odd (S i)); reflexivity.
Qed.

Lemma process_middle : forall v K n i, 0 < i -> i < K - 1 ->
  process v K n i = phase1 i ++ relay v n i (in_color i) (out_color K i).
Proof.
  intros v K n i P L. unfold process, in_color, out_color.
  assert (A : (i =? K - 1) = false) by (apply Nat.eqb_neq; lia).
  assert (B : (i =? 0) = false) by (apply Nat.eqb_neq; lia).
  assert (O : odd_pe K i = Nat.odd i).
  { unfold odd_pe. rewrite (proj2 (Nat.leb_le 1 i)) by lia.
    rewrite (proj2 (Nat.ltb_lt i (K - 1))) by lia. reflexivity. }
  assert (Ev : even_pe K i = Nat.even i).
  { unfold even_pe. rewrite (proj2 (Nat.ltb_lt i (K - 1))) by lia.
    destruct i as [|[|i]]; [lia|reflexivity|].
    rewrite (proj2 (Nat.leb_le 2 (S (S i)))) by lia. reflexivity. }
  rewrite A, B, O, Ev, <- Nat.negb_even.
  destruct (Nat.even i); simpl; rewrite ?app_nil_r; reflexivity.
Qed.
Lemma process_east : forall v K n, 2 <= K ->
  process v K n (K - 1) = phase1 (K - 1) ++ east K (K - 1).
Proof.
  intros v K n H; unfold process, odd_pe, even_pe.
  rewrite Nat.eqb_refl. assert (A : (K - 1 <? K - 1) = false) by (apply Nat.ltb_ge; lia).
  assert (B : (K - 1 =? 0) = false) by (apply Nat.eqb_neq; lia).
  rewrite A, B, !andb_false_r; simpl; rewrite ?app_nil_r; reflexivity.
Qed.
Lemma process_root : forall v K n, 2 <= K -> process v K n 0 = phase1 0 ++ root n.
Proof.
  intros v K n H; unfold process.
  assert (A : (0 =? K - 1) = false) by (apply Nat.eqb_neq; lia). rewrite A; reflexivity.
Qed.

(** Case-split on the first stream comparison in the goal. *)
Ltac dec_chan_as E :=
  match goal with |- context [chan_eq_dec ?x ?y] => destruct (chan_eq_dec x y) as [E|E] end.
Ltac dec_chan := let E := fresh "E" in dec_chan_as E.

Section Correctness.
Context {V : Type} `{Plus V}.
Variables (v : variant) (K n : nat) (inputs : list (list V)) (init : nat -> buf -> list V).
Hypothesis K2 : 2 <= K.
Hypothesis LI : length inputs = K.
Hypothesis LN : Forall (fun a => length a = n) inputs.
Hypothesis LA : forall i, i < K -> length (init i BufA) = n.
Hypothesis LT : forall i, i < K -> length (init i BufT) = n.

(** ** Partial sums *)
Definition a i := nth i inputs [].
(** What PE [i] sends west: [a_i + (... + a_{K-1})]. *)
Definition partial i := reduce (skipn i inputs).

Lemma skipn_cons_nth : forall (l : list (list V)) i, i < length l ->
  skipn i l = nth i l [] :: skipn (S i) l.
Proof. induction l as [|h t IH]; intros [|i] Hi; simpl in *; try lia; auto. apply IH; lia. Qed.
Lemma a_length i : i < K -> length (a i) = n.
Proof. intros; unfold a; rewrite Forall_forall in LN; apply LN, nth_In; lia. Qed.
Lemma partial_step i : S i < K -> partial i = zip_add (a i) (partial (S i)).
Proof.
  intros Hi; unfold partial, a. rewrite (skipn_cons_nth inputs i) by lia.
  destruct (skipn (S i) inputs) eqn:E.
  - apply (f_equal (@length _)) in E; rewrite length_skipn in E; simpl in E; lia.
  - reflexivity.
Qed.
Lemma partial_last : partial (K - 1) = a (K - 1).
Proof.
  unfold partial, a. rewrite (skipn_cons_nth inputs (K - 1)) by lia.
  replace (S (K - 1)) with K by lia. rewrite skipn_all2 by lia. reflexivity.
Qed.
Lemma partial_length i : i < K -> length (partial i) = n.
Proof.
  intros Hi. remember (K - 1 - i) as d. revert i Hi Heqd.
  induction d; intros i Hi D.
  - replace i with (K - 1) by lia. rewrite partial_last; apply a_length; lia.
  - rewrite partial_step by lia. rewrite zip_add_length, a_length, IHd by lia. lia.
Qed.

(** ** Invariant: streams after PEs [K-1 .. i] have run *)
Definition expected i (c : chan) : list V :=
  match c with
  | HostIn j => if j <? i then a j else []
  | HostOut _ => []
  | Link _ _ => if chan_eq_dec c (Link (out_color K i) i) then partial i else []
  end.
Definition Inv i (sto : chan -> list V) := forall c, sto c = expected i c.
Definition Final (sto : chan -> list V) :=
  sto (HostOut 0) = reduce inputs /\ forall c, c <> HostOut 0 -> sto c = [].

Lemma inv_next : forall m sto sto', 1 <= m -> S m <= K - 1 -> Inv (S m) sto ->
  sto' (Link (out_color K (S m)) (S m)) = [] ->
  sto' (Link (out_color K m) m) = partial m ->
  sto' (HostIn m) = [] ->
  (forall c, c <> Link (out_color K (S m)) (S m) -> c <> Link (out_color K m) m ->
     c <> HostIn m -> sto' c = sto c) ->
  Inv m sto'.
Proof.
  intros m sto sto' P L I H1 H2 H3 H4 c.
  destruct (chan_eq_dec c (Link (out_color K (S m)) (S m))) as [->|N1].
  { rewrite H1; simpl. dec_chan_as E; [inversion E; lia|reflexivity]. }
  destruct (chan_eq_dec c (Link (out_color K m) m)) as [->|N2].
  { rewrite H2; simpl. dec_chan; [reflexivity|congruence]. }
  destruct (chan_eq_dec c (HostIn m)) as [->|N3].
  { rewrite H3; simpl; rewrite Nat.ltb_irrefl; reflexivity. }
  rewrite H4, I by assumption. destruct c as [j|j|col s]; simpl.
  - destruct (Nat.ltb_spec j (S m)), (Nat.ltb_spec j m); auto.
    assert (j = m) by lia; congruence. lia.
  - reflexivity.
  - dec_chan; [congruence|]. dec_chan; [congruence|reflexivity].
Qed.

(** ** One step per PE *)
(** PE [K-1] receives its input and starts the chain. *)
Lemma step_east : exists ms sto,
  run_pe (process v K n) (K - 1) init (initial_store inputs) = Some (ms, sto) /\
  Inv (K - 1) sto /\ (forall j, j <> K - 1 -> ms j = init j).
Proof.
  set (st0 := St (init (K - 1)) (initial_store inputs)).
  assert (R1 : exec (RecvBuf BufA (HostIn (K - 1))) st0 =
      Some (set_store (set_mem st0 BufA (a (K - 1))) (HostIn (K - 1)) [])).
  { apply recv_exact. simpl. rewrite LA by lia. symmetry; apply a_length; lia. }
  set (st1 := set_store (set_mem st0 BufA (a (K - 1))) (HostIn (K - 1)) []) in *.
  set (st2 := set_store st1 (Link (east_color K) (K - 1))
                (store st1 (Link (east_color K) (K - 1)) ++ mem st1 BufA)).
  assert (R : run_proc (process v K n (K - 1)) st0 = Some st2).
  { rewrite process_east by lia. simpl app. rewrite run_proc_cons, R1. reflexivity. }
  eexists _, _; split; [apply run_pe_result; exact R|]. split.
  - intros c. unfold st2. destruct (chan_eq_dec c (Link (east_color K) (K - 1))) as [->|N].
    + autorewrite with kahn. unfold st1; autorewrite with kahn.
      rewrite store_set_store_other by discriminate. simpl.
      dec_chan_as E.
      * rewrite partial_last; reflexivity.
      * exfalso; apply E; unfold out_color; rewrite Nat.eqb_refl; reflexivity.
    + rewrite store_set_store_other by congruence. unfold st1.
      destruct (chan_eq_dec c (HostIn (K - 1))) as [->|N2].
      * autorewrite with kahn; simpl; rewrite Nat.ltb_irrefl; reflexivity.
      * rewrite store_set_store_other by congruence. simpl.
        destruct c as [j|j|col s]; simpl; auto.
        -- destruct (Nat.ltb_spec j (K - 1)); [reflexivity|].
           unfold a; apply nth_overflow; assert (j <> K - 1) by congruence; lia.
        -- dec_chan_as E; [|reflexivity].
           exfalso; apply N; inversion E; subst.
           unfold out_color; rewrite Nat.eqb_refl; reflexivity.
  - intros j J; destruct (dec (K - 1) j); [congruence|reflexivity].
Qed.

(** A middle PE [m] adds its vector to the incoming partial sum. *)
Lemma step_middle : forall m ms sto, 1 <= m -> S m <= K - 1 -> Inv (S m) sto ->
  ms m = init m ->
  exists ms' sto', run_pe (process v K n) m ms sto = Some (ms', sto') /\
  Inv m sto' /\ (forall j, j <> m -> ms' j = ms j).
Proof.
  intros m ms sto P L I M.
  set (cin := in_color m). set (cout := out_color K m).
  assert (Cin : cin = out_color K (S m)) by (apply colors_match; lia).
  assert (Dio : Link cin (S m) <> Link cout m) by (intros E; inversion E; lia).
  assert (Lp : length (partial (S m)) = n) by (apply partial_length; lia).
  assert (La : length (a m) = n) by (apply a_length; lia).
  assert (Sin : sto (Link cin (S m)) = partial (S m)).
  { rewrite I; simpl. rewrite Cin. dec_chan; [reflexivity|congruence]. }
  assert (Sout : sto (Link cout m) = []).
  { rewrite I; simpl. dec_chan_as E; [inversion E; lia|reflexivity]. }
  assert (Sa : sto (HostIn m) = a m).
  { rewrite I; simpl. destruct (Nat.ltb_spec m (S m)); [reflexivity|lia]. }
  set (st0 := St (ms m) sto).
  assert (R1 : exec (RecvBuf BufA (HostIn m)) st0 =
      Some (set_store (set_mem st0 BufA (a m)) (HostIn m) [])).
  { rewrite recv_exact; [simpl; rewrite Sa; reflexivity|].
    simpl. rewrite M, LA, Sa, La by lia. reflexivity. }
  set (st1 := set_store (set_mem st0 BufA (a m)) (HostIn m) []) in *.
  assert (S1 : forall c, c <> HostIn m -> store st1 c = sto c).
  { intros c C; unfold st1; rewrite store_set_store_other by congruence; reflexivity. }
  assert (M1 : mem st1 BufA = a m) by (unfold st1; autorewrite with kahn; reflexivity).
  assert (T1 : mem st1 BufT = init m BufT).
  { unfold st1; autorewrite with kahn; rewrite mem_set_mem_other by discriminate.
    simpl; rewrite M; reflexivity. }
  destruct v.
  - (* Original: foreach receive, add, forward. *)
    destruct (foreach_add_forward BufA (partial (S m)) [] (a m) st1 (Link cin (S m)) (Link cout m))
      as (st2 & R2 & MA & C0 & C1 & Oth & _); auto; try congruence.
    rewrite Lp in R2; simpl length in R2.
    assert (R : run_proc (process Original K n m) st0 = Some st2).
    { rewrite process_middle by lia. fold cin cout. simpl app.
      rewrite run_proc_cons, R1, run_proc_cons. simpl exec. rewrite R2. reflexivity. }
    eexists _, _; split; [apply run_pe_result; exact R|]. split.
    + apply (inv_next m sto); auto.
      * rewrite <- Cin; exact C0.
      * fold cout. rewrite C1, S1, Sout by discriminate; simpl.
        rewrite (partial_step m) by lia; reflexivity.
      * rewrite Oth by discriminate. unfold st1; autorewrite with kahn; reflexivity.
      * intros c N1 N2 N3. rewrite <- Cin in N1. rewrite Oth, S1 by assumption; reflexivity.
    + intros j J; destruct (dec m j); [congruence|reflexivity].
  - (* RecvFirst: receive the whole partial sum, map-add, send. *)
    assert (R2 : exec (RecvBuf BufT (Link cin (S m))) st1 =
        Some (set_store (set_mem st1 BufT (partial (S m))) (Link cin (S m)) [])).
    { rewrite recv_exact.
      - rewrite S1 by discriminate; rewrite Sin; reflexivity.
      - rewrite T1, S1, Sin, LT, Lp by (lia || discriminate); reflexivity. }
    set (st2 := set_store (set_mem st1 BufT (partial (S m))) (Link cin (S m)) []) in *.
    destruct (map_add BufA BufT (partial (S m)) [] (a m) st2) as (st3 & R3 & MA & Sto);
      auto; try congruence.
    { exists []; unfold st2; autorewrite with kahn; auto. }
    rewrite Lp in R3; simpl length in R3.
    set (st4 := set_store st3 (Link cout m) (store st3 (Link cout m) ++ mem st3 BufA)).
    assert (R : run_proc (process RecvFirst K n m) st0 = Some st4).
    { rewrite process_middle by lia. fold cin cout. simpl app.
      rewrite run_proc_cons, R1, run_proc_cons, R2, run_proc_cons.
      simpl exec. rewrite R3. reflexivity. }
    eexists _, _; split; [apply run_pe_result; exact R|]. split.
    + apply (inv_next m sto); auto.
      * unfold st4; rewrite store_set_store_other by congruence.
        rewrite Sto; unfold st2; rewrite <- Cin; autorewrite with kahn; reflexivity.
      * fold cout; unfold st4; autorewrite with kahn. rewrite Sto, MA; unfold st2.
        rewrite store_set_store_other by congruence. autorewrite with kahn.
        rewrite S1, Sout by discriminate; simpl. rewrite (partial_step m) by lia; reflexivity.
      * unfold st4; rewrite store_set_store_other by discriminate.
        rewrite Sto; unfold st2; rewrite store_set_store_other by discriminate.
        autorewrite with kahn; unfold st1; autorewrite with kahn; reflexivity.
      * intros c N1 N2 N3. rewrite <- Cin in N1. unfold st4. fold cout in N2.
        rewrite store_set_store_other by congruence. rewrite Sto; unfold st2.
        rewrite store_set_store_other by congruence. autorewrite with kahn.
        rewrite S1 by assumption; reflexivity.
    + intros j J; destruct (dec m j); [congruence|reflexivity].
Qed.

(** PE 0 adds its vector and emits the total. *)
Lemma step_root : forall ms sto, Inv 1 sto -> ms 0 = init 0 ->
  exists ms' sto', run_pe (process v K n) 0 ms sto = Some (ms', sto') /\ Final sto'.
Proof.
  intros ms sto I M.
  assert (Cin : Blue = out_color K 1) by (apply (colors_match K 0); lia).
  assert (Lp : length (partial 1) = n) by (apply partial_length; lia).
  assert (La : length (a 0) = n) by (apply a_length; lia).
  assert (Sin : sto (Link Blue 1) = partial 1).
  { rewrite I; simpl. rewrite Cin. dec_chan; [reflexivity|congruence]. }
  assert (Sa : sto (HostIn 0) = a 0) by (rewrite I; reflexivity).
  set (st0 := St (ms 0) sto).
  assert (R1 : exec (RecvBuf BufA (HostIn 0)) st0 =
      Some (set_store (set_mem st0 BufA (a 0)) (HostIn 0) [])).
  { rewrite recv_exact; [simpl; rewrite Sa; reflexivity|].
    simpl. rewrite M, LA, Sa, La by lia. reflexivity. }
  set (st1 := set_store (set_mem st0 BufA (a 0)) (HostIn 0) []) in *.
  destruct (foreach_add BufA (partial 1) [] (a 0) st1 (Link Blue 1))
    as (st2 & R2 & MA & C0 & Oth); auto.
  all: try congruence.
  all: try (unfold st1; autorewrite with kahn; reflexivity).
  all: try (unfold st1; rewrite store_set_store_other by discriminate; exact Sin).
  rewrite Lp in R2; simpl length in R2.
  set (st3 := set_store st2 (HostOut 0) (store st2 (HostOut 0) ++ mem st2 BufA)).
  assert (R : run_proc (process v K n 0) st0 = Some st3).
  { rewrite process_root by lia. simpl app.
    unfold root. rewrite run_proc_cons, R1, run_proc_cons. simpl exec. rewrite R2. reflexivity. }
  eexists _, _; split; [apply run_pe_result; exact R|]. split.
  - unfold st3; autorewrite with kahn. rewrite Oth by discriminate. unfold st1.
    rewrite store_set_store_other by discriminate. autorewrite with kahn.
    rewrite I, MA; simpl. replace (zip_add (a 0) (partial 1)) with (partial 0)
      by (apply partial_step; lia). reflexivity.
  - intros c N. unfold st3; rewrite store_set_store_other by congruence.
    destruct (chan_eq_dec c (Link Blue 1)) as [->|N1]; [exact C0|].
    rewrite Oth by assumption. unfold st1.
    destruct (chan_eq_dec c (HostIn 0)) as [->|N2]; [autorewrite with kahn; reflexivity|].
    rewrite store_set_store_other by congruence. simpl. rewrite I.
    destruct c as [j|j|col s]; simpl; auto.
    + destruct j; [congruence|reflexivity].
    + dec_chan_as E; [|reflexivity]. rewrite <- Cin in E; congruence.
Qed.

(** ** The whole chain *)
Lemma chain_from : forall m ms sto, S m <= K - 1 -> Inv (S m) sto ->
  (forall j, j <= m -> ms j = init j) ->
  exists ms' sto', run_net (down_from m) (process v K n) ms sto = Some (ms', sto') /\ Final sto'.
Proof.
  induction m as [|m IH]; intros ms sto L I M.
  - destruct (step_root ms sto I (M 0 (le_n 0))) as (ms' & sto' & R & F).
    exists ms', sto'; simpl; rewrite R; auto.
  - destruct (step_middle (S m) ms sto ltac:(lia) L I (M _ (le_n _))) as (ms1 & sto1 & R & I1 & U).
    destruct (IH ms1 sto1 ltac:(lia) I1) as (ms' & sto' & R' & F).
    { intros j J; rewrite U by lia; apply M; lia. }
    exists ms', sto'; simpl; rewrite R; auto.
Qed.

Theorem chain_reduce_correct : exists ms sto,
  run_net (down_from (K - 1)) (process v K n) init (initial_store inputs) = Some (ms, sto) /\
  sto (HostOut 0) = reduce inputs /\ (forall c, c <> HostOut 0 -> sto c = []).
Proof.
  destruct step_east as (ms1 & sto1 & R & I & U).
  replace (K - 1) with (S (K - 2)) in R, I |- * by lia.
  destruct (chain_from (K - 2) ms1 sto1 ltac:(lia) I) as (ms' & sto' & R' & F1 & F2).
  { intros j J; apply U; lia. }
  exists ms', sto'. simpl down_from. cbn [run_net]. rewrite R; auto.
Qed.
End Correctness.

(** ** Corollaries *)
Section Corollaries.
Context {V : Type} `{Plus V}.

Corollary chain_reduce_any_order :
  (forall x y z : V, plus x (plus y z) = plus (plus x y) z) ->
  (forall x y : V, plus x y = plus y x) ->
  forall v K n (inputs : list (list V)) init order,
  2 <= K -> length inputs = K -> Forall (fun a => length a = n) inputs ->
  (forall i, i < K -> length (init i BufA) = n) ->
  (forall i, i < K -> length (init i BufT) = n) ->
  Permutation inputs order ->
  exists ms sto,
  run_net (down_from (K - 1)) (process v K n) init (initial_store inputs) = Some (ms, sto) /\
  sto (HostOut 0) = reduce order.
Proof.
  intros Assoc Comm v K n inputs init order K2 LI LN LA LT P.
  destruct (chain_reduce_correct v K n inputs init K2 LI LN LA LT) as (ms & sto & R & O & _).
  exists ms, sto; split; [exact R|]. rewrite O; apply reduce_permutation; assumption.
Qed.

(** With [K = 1], PE 0 waits on a PE 1 that does not exist. *)
Theorem chain_reduce_K1_deadlocks : forall v n (input : list V) (init : nat -> buf -> list V),
  0 < n -> length input = n -> length (init 0 BufA) = n ->
  run_net (down_from 0) (process v 1 n) init (initial_store [input]) = None.
Proof.
  intros v n input init P L LA0. simpl down_from. cbn [run_net].
  unfold run_pe, process; simpl.
  rewrite LA0, L, Nat.leb_refl.
  destruct n as [|n]; [lia|]. simpl iter. unfold fetch.
  reflexivity.
Qed.
End Corollaries.
