From Stdlib Require Import ZArith List Arith Lia Bool Permutation String.
From SpatialCSL Require Import SpadaIR ReduceSpec SpadaDataflow ChainReduce ChainReduceVariant.
Import ListNotations Spada.
Open Scope list_scope.
Open Scope string_scope.
Open Scope nat_scope.

(** * Correctness of the chain-reduction kernels

    The proofs are about the IR terms in ChainReduce.v and
    ChainReduceVariant.v, run under SpadaDataflow.v; those terms are what gets
    exported to SpaDA and CSL. Main results, for every [K >= 2] and both
    variants:
    - [chain_reduce_correct]: [out[0]] holds [reduce inputs] (the right-nested
      element-wise sum, over any addition) and every other stream is drained;
    - [chain_reduce_any_order]: with associative, commutative addition, any
      order of the PEs' vectors gives the same sum;
    - [chain_reduce_K1_ill_formed]: [K = 1] is not a valid SpaDA program.

    Proof idea: run PEs [K-1] down to [0]. After PEs [K-1 .. i] have run, the
    stream PE [i] sends on holds [a_i + (... + a_{K-1})] ([Inv]). *)

Inductive variant := Original | RecvFirst.
Definition kernel v (K : nat) :=
  match v with
  | Original => ChainReduce.kernel (Z.of_nat K)
  | RecvFirst => ChainReduceRecvFirst.kernel (Z.of_nat K)
  end.
Definition at_pe (i : nat) : pe := (Z.of_nat i, 0%Z).

Definition phase1_body := [Receive (EVar (named "a")) (Slice (named "a_in") [EVar (named "x")]) (Some (named "got"));
                           Await (named "got")].
Definition east_body (K : nat) :=
  [Send (EVar (named "a")) (Select (EVar (named "red"))
     (Binary (Binary (int (Z.of_nat K - 1)) Modulo (int 2)) Equal (int 0)) (EVar (named "blue"))) None].
Definition root_body (K : nat) :=
  [Foreach [coord "k"] [interval 0 (Z.of_nat K)] (Typed (Scalar F32) (named "x")) (EVar (named "blue"))
     [Assign ChainReduce.a_k (Binary ChainReduce.a_k Plus (EVar (named "x")))] None;
   Send (EVar (named "a")) (Slice (named "out") [EVar (named "x")]) None].
Definition relay_body v K cin cout :=
  match v with
  | Original => ChainReduce.relay (Z.of_nat K) cin cout
  | RecvFirst => ChainReduceRecvFirst.relay (Z.of_nat K) cin cout
  end.
Definition role_body v K i :=
  if Nat.eqb i (K - 1) then east_body K else if Nat.eqb i 0 then root_body K
  else if Nat.odd i then relay_body v K "red" "blue" else relay_body v K "blue" "red".
Definition streams2 := [ChainReduce.west "red"; ChainReduce.west "blue"].
Definition task_at {V} `{data_ops V} n ds i body : @task V := Task n (at_pe i) ds (coord_env ChainReduce.xy (at_pe i)) body.

(** ** Which PE runs which compute block *)
Definition odd_pe K i := (1 <=? i) && (i <? K - 1) && Nat.odd i.
Definition even_pe K i := (2 <=? i) && (i <? K - 1) && Nat.even i.

Lemma zle i j : (Z.of_nat i <=? Z.of_nat j)%Z = (i <=? j).
Proof. destruct (Z.leb_spec (Z.of_nat i) (Z.of_nat j)), (Nat.leb_spec i j); lia. Qed.
Lemma zlt i j : (Z.of_nat i <? Z.of_nat j)%Z = (i <? j).
Proof. destruct (Z.ltb_spec (Z.of_nat i) (Z.of_nat j)), (Nat.ltb_spec i j); lia. Qed.
Lemma zeq i j : (Z.of_nat i =? Z.of_nat j)%Z = Nat.eqb i j.
Proof. destruct (Z.eqb_spec (Z.of_nat i) (Z.of_nat j)), (Nat.eqb_spec i j); lia. Qed.
(** [(z - d) mod 2 == 0] for [z = i], [d] in [{0, 1, 2}]. *)
Lemma zparity i d : (d <= 2)%Z -> (0 <= d)%Z ->
  ((Z.of_nat i - d) mod 2 =? 0)%Z = (if Z.even d then Nat.even i else Nat.odd i).
Proof.
  intros D1 D2. rewrite <- Nat.negb_even.
  destruct (Nat.even i) eqn:E.
  - apply Nat.even_spec in E as [m ->].
    assert (Hd : (d = 0 \/ d = 1 \/ d = 2)%Z) by lia; destruct Hd as [ -> | [ -> | -> ] ]; cbn [Z.even negb].
    + replace (Z.of_nat (2 * m) - 0)%Z with (0 + Z.of_nat m * 2)%Z by lia. now rewrite Z_mod_plus_full.
    + replace (Z.of_nat (2 * m) - 1)%Z with (1 + (Z.of_nat m - 1) * 2)%Z by lia. now rewrite Z_mod_plus_full.
    + replace (Z.of_nat (2 * m) - 2)%Z with (0 + (Z.of_nat m - 1) * 2)%Z by lia. now rewrite Z_mod_plus_full.
  - assert (O : Nat.odd i = true) by (rewrite <- Nat.negb_even, E; reflexivity).
    apply Nat.odd_spec in O as [m ->].
    assert (Hd : (d = 0 \/ d = 1 \/ d = 2)%Z) by lia; destruct Hd as [ -> | [ -> | -> ] ]; cbn [Z.even negb].
    + replace (Z.of_nat (2 * m + 1) - 0)%Z with (1 + Z.of_nat m * 2)%Z by lia. now rewrite Z_mod_plus_full.
    + replace (Z.of_nat (2 * m + 1) - 1)%Z with (0 + Z.of_nat m * 2)%Z by lia. now rewrite Z_mod_plus_full.
    + replace (Z.of_nat (2 * m + 1) - 2)%Z with (1 + (Z.of_nat m - 1) * 2)%Z by lia. now rewrite Z_mod_plus_full.
Qed.

Section Grids.
Context {V : Type} `{data_ops V}.
Lemma in_grid_row K i : i < K -> in_grid (ChainReduce.row 0 (Z.of_nat K)) (at_pe i) = true.
Proof.
  intros L. unfold in_grid; cbn. change 0%Z with (Z.of_nat 0). rewrite zle, zlt.
  destruct (Nat.ltb_spec i K); [reflexivity|lia].
Qed.
Lemma in_grid_at K i : 1 <= K -> in_grid (ChainReduce.at_x (Z.of_nat K - 1)) (at_pe i) = Nat.eqb i (K - 1).
Proof.
  intros L. unfold in_grid; cbn. replace (Z.of_nat K - 1)%Z with (Z.of_nat (K - 1)) by lia.
  rewrite zeq, andb_true_r. reflexivity.
Qed.
Lemma in_grid_root i : in_grid (ChainReduce.at_x 0) (at_pe i) = Nat.eqb i 0.
Proof. unfold in_grid; cbn. change 0%Z with (Z.of_nat 0). rewrite zeq, andb_true_r. reflexivity. Qed.
Lemma in_grid_odd K i : 1 <= K -> in_grid (ChainReduce.strided 1 (Z.of_nat K - 1) 2) (at_pe i) = odd_pe K i.
Proof.
  intros L. unfold in_grid, odd_pe; cbn. rewrite andb_true_r.
  replace (Z.of_nat K - 1)%Z with (Z.of_nat (K - 1)) by lia.
  change 1%Z with (Z.of_nat 1) at 1. rewrite zle, zlt, (zparity i 1) by lia. reflexivity.
Qed.
Lemma in_grid_even K i : 1 <= K -> in_grid (ChainReduce.strided 2 (Z.of_nat K - 1) 2) (at_pe i) = even_pe K i.
Proof.
  intros L. unfold in_grid, even_pe; cbn. rewrite andb_true_r.
  replace (Z.of_nat K - 1)%Z with (Z.of_nat (K - 1)) by lia.
  change 2%Z with (Z.of_nat 2) at 1. rewrite zle, zlt, (zparity i 2) by lia. reflexivity.
Qed.
End Grids.

Lemma program_shape {V} `{data_ops V} : forall v K i, 2 <= K -> i < K ->
  pe_program (V:=V) (kernel v K) (at_pe i) =
  Some [task_at 1 [] i phase1_body; task_at 2 streams2 i (role_body v K i)].
Proof.
  intros v K i HK Hi. unfold pe_program.
  destruct v; cbn [kernel ChainReduce.kernel ChainReduceRecvFirst.kernel blocks streams_of
    phase_tasks flat_map app]; unfold phase_task, computes_at;
    cbn [forallb flat_block flat_map app streams_of];
    rewrite in_grid_row, in_grid_at, in_grid_odd, in_grid_even, in_grid_root by lia;
    unfold role_body, odd_pe, even_pe; rewrite <- Nat.negb_even;
    destruct (Nat.eqb_spec i (K - 1)); destruct (Nat.eqb_spec i 0); try lia;
    destruct (Nat.ltb_spec i (K - 1)); try lia;
    destruct (Nat.leb_spec 1 i); try lia.
  all: destruct (Nat.leb_spec 2 i); try lia.
  all: try (assert (i = 1) by lia; subst i).
  all: try destruct (Nat.even i); try reflexivity.
Qed.

(** ** Streams and colours *)
Inductive color := Red | Blue.
Definition color_name c := match c with Red => "red" | Blue => "blue" end.
(** [link c i]: the colour-[c] stream PE [i] sends west on in phase 2. *)
Definition link c i : chan := Edge 2 (named (color_name c)) (at_pe i).
Definition host_in i : chan := Arg (named "a_in") [Z.of_nat i].
Definition host_out : chan := Arg (named "out") [0%Z].
(** Which [a_in] element a stream is, if any. *)
Definition in_index (c : chan) : option nat :=
  match c with
  | Arg id [z] => if id_dec id (named "a_in") then if (0 <=? z)%Z then Some (Z.to_nat z) else None else None
  | _ => None
  end.

Lemma at_pe_inj i j : at_pe i = at_pe j -> i = j.
Proof. unfold at_pe; intros E; inversion E; lia. Qed.
Lemma link_inj c c' i j : link c i = link c' j -> c = c' /\ i = j.
Proof.
  unfold link, at_pe; intros E; inversion E as [[N P]].
  split; [destruct c, c'; simpl in *; congruence | lia].
Qed.
Lemma in_index_host i : in_index (host_in i) = Some i.
Proof.
  unfold in_index, host_in. destruct (id_dec _ _) as [_|N]; [|congruence].
  rewrite (proj2 (Z.leb_le 0 _)) by lia. rewrite Nat2Z.id; reflexivity.
Qed.
Lemma in_index_inj c i : in_index c = Some i -> c = host_in i.
Proof.
  unfold in_index, host_in; destruct c as [id [|z [|]]|]; try discriminate.
  destruct (id_dec id (named "a_in")) as [->|]; [|discriminate].
  destruct (Z.leb_spec 0 z); [|discriminate]. intros E; inversion E; subst.
  rewrite Z2Nat.id by assumption; reflexivity.
Qed.

Definition east_color K := if Nat.even (K - 1) then Red else Blue.
(** Colour PE [i] sends on / receives from. *)
Definition out_color K i := if Nat.eqb i (K - 1) then east_color K else if Nat.odd i then Blue else Red.
Definition in_color i := if Nat.eqb i 0 then Blue else if Nat.odd i then Red else Blue.

(** Every receiver listens on the colour its east neighbour sends on. *)
Lemma colors_match : forall K i, S i <= K - 1 -> in_color i = out_color K (S i).
Proof.
  intros K i H; unfold in_color, out_color, east_color.
  destruct (Nat.eqb_spec (S i) (K - 1)) as [E|E].
  - rewrite <- E, Nat.even_succ. destruct i as [|i]; [reflexivity|].
    change (Nat.eqb (S i) 0) with false. destruct (Nat.odd (S i)); reflexivity.
  - rewrite Nat.odd_succ, <- Nat.negb_odd. destruct i as [|i]; [reflexivity|].
    change (Nat.eqb (S i) 0) with false. destruct (Nat.odd (S i)); reflexivity.
Qed.

Lemma role_east v K : 2 <= K -> role_body v K (K - 1) = east_body K.
Proof. intros; unfold role_body; rewrite Nat.eqb_refl; reflexivity. Qed.
Lemma role_root v K : 2 <= K -> role_body v K 0 = root_body K.
Proof. intros; unfold role_body. destruct (Nat.eqb_spec 0 (K - 1)); [lia|reflexivity]. Qed.
Lemma role_middle v K i : 0 < i -> i < K - 1 ->
  role_body v K i = relay_body v K (color_name (in_color i)) (color_name (out_color K i)).
Proof.
  intros; unfold role_body, in_color, out_color.
  destruct (Nat.eqb_spec i (K - 1)); [lia|]. destruct (Nat.eqb_spec i 0); [lia|].
  destruct (Nat.odd i); reflexivity.
Qed.

(** Ltac: replace a loop in the goal by its result [R] (equal up to conversion). *)
Ltac use_loop R :=
  match goal with |- context [iter_loop ?run ?e ?k ?src ?zs ?st] =>
    let E := fresh in assert (E : iter_loop run e k src zs st = _) by exact R; rewrite E; clear E
  end.

(** PEs [i, i-1, ..., 0]: each producer before its consumer. *)
Fixpoint down_from (i : nat) : list pe :=
  match i with O => [at_pe 0] | S j => at_pe (S j) :: down_from j end.

Section Correctness.
Context {V : Type} `{data_ops V}.

(** ** How streams resolve *)
Lemma chan_recv m e c i body :
  chan_of false (task_at (V:=V) 2 streams2 i body) m e (EVar (named (color_name c))) = Some (link c (S i)).
Proof.
  destruct c; cbn; unfold link, at_pe; do 3 f_equal; lia.
Qed.
Lemma chan_send m e c i body :
  chan_of true (task_at (V:=V) 2 streams2 i body) m e (EVar (named (color_name c))) = Some (link c i).
Proof. destruct c; reflexivity. Qed.
Lemma chan_east K m e body : 1 <= K ->
  chan_of true (task_at (V:=V) 2 streams2 (K - 1) body) m e
    (Select (EVar (named "red")) (Binary (Binary (int (Z.of_nat K - 1)) Modulo (int 2)) Equal (int 0)) (EVar (named "blue")))
  = Some (link (east_color K) (K - 1)).
Proof.
  intros L. unfold int; cbn [chan_of]. unfold eval_z; cbn [eval is_float]. unfold zbinary; cbn [option_map].
  replace (Z.of_nat K - 1)%Z with (Z.of_nat (K - 1) - 0)%Z by lia.
  rewrite (zparity (K - 1) 0) by lia. unfold east_color; simpl Z.even; cbv iota.
  destruct (Nat.even (K - 1)); reflexivity.
Qed.

Variables (v : variant) (K : nat) (inputs : list (list V)) (init : pe -> @memory V).
Hypothesis K2 : 2 <= K.
Hypothesis LI : List.length inputs = K.
(** The kernel's vectors have [K] elements: [f32[K] a]. *)
Hypothesis LN : Forall (fun a => List.length a = K) inputs.
Hypothesis LA : forall i, i < K -> List.length (init (at_pe i) (named "a")) = K.
Hypothesis LT : forall i, i < K -> List.length (init (at_pe i) (named "t")) = K.

Definition initial_store (c : chan) : list V :=
  match in_index c with Some j => nth j inputs [] | None => [] end.

(** ** Partial sums *)
Definition a i := nth i inputs [].
(** What PE [i] sends west: [a_i + (... + a_{K-1})]. *)
Definition partial i := reduce (skipn i inputs).

Lemma skipn_cons_nth : forall (l : list (list V)) i, i < List.length l ->
  skipn i l = nth i l [] :: skipn (S i) l.
Proof. induction l as [|h t IH]; intros [|i] Hi; simpl in *; try lia; auto. apply IH; lia. Qed.
Lemma a_length i : i < K -> List.length (a i) = K.
Proof. intros; unfold a; rewrite Forall_forall in LN; apply LN, nth_In; lia. Qed.
Lemma partial_step i : S i < K -> partial i = zip_add (a i) (partial (S i)).
Proof.
  intros Hi; unfold partial, a. rewrite (skipn_cons_nth inputs i) by lia.
  destruct (skipn (S i) inputs) eqn:E.
  - apply (f_equal (@List.length _)) in E; rewrite length_skipn in E; simpl in E; lia.
  - reflexivity.
Qed.
Lemma partial_last : partial (K - 1) = a (K - 1).
Proof.
  unfold partial, a. rewrite (skipn_cons_nth inputs (K - 1)) by lia.
  replace (S (K - 1)) with K by lia. rewrite skipn_all2 by lia. reflexivity.
Qed.
Lemma partial_length i : i < K -> List.length (partial i) = K.
Proof.
  intros Hi. remember (K - 1 - i) as d. revert i Hi Heqd.
  induction d; intros i Hi D.
  - replace i with (K - 1) by lia. rewrite partial_last; apply a_length; lia.
  - rewrite partial_step by lia. rewrite zip_add_length, a_length, IHd by lia. lia.
Qed.

(** ** Invariant: streams after PEs [K-1 .. i] have run *)
Definition expected i (c : chan) : list V :=
  if chan_dec c (link (out_color K i) i) then partial i else
  match in_index c with Some j => if j <? i then a j else [] | None => [] end.
Definition Inv i (sto : chan -> list V) := forall c, sto c = expected i c.
Definition Final (sto : chan -> list V) :=
  sto host_out = reduce inputs /\ forall c, c <> host_out -> sto c = [].

Lemma inv_next : forall m sto sto', 1 <= m -> S m <= K - 1 -> Inv (S m) sto ->
  sto' (link (out_color K (S m)) (S m)) = [] ->
  sto' (link (out_color K m) m) = partial m ->
  sto' (host_in m) = [] ->
  (forall c, c <> link (out_color K (S m)) (S m) -> c <> link (out_color K m) m ->
     c <> host_in m -> sto' c = sto c) ->
  Inv m sto'.
Proof.
  intros m sto sto' P L I H1 H2 H3 H4 c. unfold expected.
  destruct (chan_dec c (link (out_color K (S m)) (S m))) as [->|N1].
  { rewrite H1. destruct (chan_dec _ _) as [E|_]; [apply link_inj in E; lia|reflexivity]. }
  destruct (chan_dec c (link (out_color K m) m)) as [->|N2]; [exact H2|].
  destruct (chan_dec c (host_in m)) as [->|N3].
  { rewrite H3, in_index_host, Nat.ltb_irrefl; reflexivity. }
  rewrite H4, I by assumption. unfold expected.
  destruct (chan_dec _ _); [congruence|].
  destruct (in_index c) as [j|] eqn:J; [|reflexivity].
  destruct (Nat.ltb_spec j (S m)), (Nat.ltb_spec j m); auto; [|lia].
  assert (j = m) by lia; subst. apply in_index_inj in J; congruence.
Qed.

(** ** Running one PE *)
Lemma run_phase1 i (st : @state V) :
  List.length (mem st (named "a")) = List.length (store st (host_in i)) ->
  run_task (task_at 1 [] i phase1_body) st =
  Some (set_store (set_mem st (named "a") (store st (host_in i))) (host_in i) []).
Proof.
  intros L. unfold run_task, task_at, phase1_body; cbn [t_body t_env].
  rewrite exec_list_cons, (exec_receive_exact _ _ _ _ _ _ (host_in i)) by (reflexivity || exact L).
  rewrite exec_list_cons, exec_await, exec_list_nil. reflexivity.
Qed.
Lemma run_task_at n ds i body (st : @state V) :
  run_task (task_at n ds i body) st = exec_list (task_at n ds i body) body (coord_env ChainReduce.xy (at_pe i)) st.
Proof. reflexivity. Qed.
Lemma run_two (t1 t2 : @task V) (st st1 : @state V) : run_task t1 st = Some st1 ->
  run_tasks [t1; t2] st = run_task t2 st1.
Proof. intros R; cbn [run_tasks]; rewrite R; destruct (run_task t2 st1); reflexivity. Qed.
Lemma pe_update (ms : pe -> @memory V) i j (m' : @memory V) : j <> i ->
  (fun q => if pe_dec (at_pe i) q then m' else ms q) (at_pe j) = ms (at_pe j).
Proof. intros N; cbn beta; destruct (pe_dec _ _) as [E|]; [apply at_pe_inj in E; lia|reflexivity]. Qed.

(** PE [K-1] receives its input and starts the chain. *)
Lemma step_east : exists ms sto,
  run_pe (kernel v K) (at_pe (K - 1)) init initial_store = Some (ms, sto) /\
  Inv (K - 1) sto /\ (forall j, j <> K - 1 -> ms (at_pe j) = init (at_pe j)).
Proof.
  set (st0 := St (init (at_pe (K - 1))) initial_store).
  assert (R1 := run_phase1 (K - 1) st0).
  assert (Sa : store st0 (host_in (K - 1)) = a (K - 1)).
  { simpl; unfold initial_store; rewrite in_index_host; reflexivity. }
  rewrite Sa in R1. specialize (R1 ltac:(simpl; rewrite LA, a_length by lia; reflexivity)).
  set (st1 := set_store (set_mem st0 (named "a") (a (K - 1))) (host_in (K - 1)) []) in *.
  set (st2 := set_store st1 (link (east_color K) (K - 1))
                (store st1 (link (east_color K) (K - 1)) ++ mem st1 (named "a"))).
  assert (R : run_tasks [task_at 1 [] (K - 1) phase1_body;
                         task_at 2 streams2 (K - 1) (role_body v K (K - 1))] st0 = Some st2).
  { rewrite (run_two _ _ _ _ R1), role_east by lia. unfold run_task, task_at, east_body; cbn [t_body t_env].
    rewrite exec_list_cons, (exec_send_array _ _ _ _ _ _ (link (east_color K) (K - 1))); try reflexivity.
    apply chan_east; lia. }
  eexists _, _; split; [apply (run_pe_result _ _ _ _ _ _ (program_shape v K (K - 1) K2 ltac:(lia)) R)|].
  split.
  - intros c. unfold st2. destruct (chan_dec c (link (east_color K) (K - 1))) as [->|N].
    + autorewrite with df. unfold st1; autorewrite with df.
      rewrite store_set_store_other by discriminate. unfold expected.
      destruct (chan_dec _ _) as [_|E].
      * simpl; unfold initial_store; simpl. rewrite partial_last; reflexivity.
      * exfalso; apply E; unfold out_color; rewrite Nat.eqb_refl; reflexivity.
    + rewrite store_set_store_other by congruence. unfold st1, expected.
      destruct (chan_dec c (host_in (K - 1))) as [->|N2].
      * autorewrite with df. rewrite in_index_host, Nat.ltb_irrefl.
        destruct (chan_dec _ _); [discriminate|reflexivity].
      * rewrite store_set_store_other by congruence. simpl; unfold initial_store.
        destruct (chan_dec _ _) as [E|].
        { exfalso; apply N; rewrite E; unfold out_color; rewrite Nat.eqb_refl; reflexivity. }
        destruct (in_index c) as [j|] eqn:J; [|reflexivity].
        destruct (Nat.ltb_spec j (K - 1)); [reflexivity|].
        assert (j <> K - 1) by (intros ->; apply in_index_inj in J; congruence).
        unfold a; apply nth_overflow; lia.
  - intros j J; apply pe_update; lia.
Qed.

(** A middle PE [m] adds its vector to the incoming partial sum. *)
Lemma step_middle : forall m ms sto, 1 <= m -> S m <= K - 1 -> Inv (S m) sto ->
  ms (at_pe m) = init (at_pe m) ->
  exists ms' sto', run_pe (kernel v K) (at_pe m) ms sto = Some (ms', sto') /\
  Inv m sto' /\ (forall j, j <> m -> ms' (at_pe j) = ms (at_pe j)).
Proof.
  intros m ms sto P L I M.
  set (cin := in_color m). set (cout := out_color K m).
  assert (Cin : cin = out_color K (S m)) by (apply colors_match; lia).
  assert (Dio : link cin (S m) <> link cout m) by (intros E; apply link_inj in E; lia).
  assert (Lp : List.length (partial (S m)) = K) by (apply partial_length; lia).
  assert (La : List.length (a m) = K) by (apply a_length; lia).
  assert (Sin : sto (link cin (S m)) = partial (S m)).
  { rewrite I; unfold expected; rewrite Cin. destruct (chan_dec _ _); [reflexivity|congruence]. }
  assert (Sout : sto (link cout m) = []).
  { rewrite I; unfold expected. destruct (chan_dec _ _) as [E|]; [apply link_inj in E; lia|reflexivity]. }
  assert (Sa : sto (host_in m) = a m).
  { rewrite I; unfold expected. destruct (chan_dec _ _); [discriminate|].
    rewrite in_index_host. destruct (Nat.ltb_spec m (S m)); [reflexivity|lia]. }
  set (st0 := St (ms (at_pe m)) sto).
  assert (R1 := run_phase1 m st0). simpl store in R1. rewrite Sa in R1.
  specialize (R1 ltac:(simpl; rewrite M, LA, La by lia; reflexivity)).
  set (st1 := set_store (set_mem st0 (named "a") (a m)) (host_in m) []) in *.
  assert (S1 : forall c, c <> host_in m -> store st1 c = sto c).
  { intros c C; unfold st1; rewrite store_set_store_other by congruence; reflexivity. }
  assert (M1 : mem st1 (named "a") = a m) by (unfold st1; autorewrite with df; reflexivity).
  assert (T1 : mem st1 (named "t") = init (at_pe m) (named "t")).
  { unfold st1; autorewrite with df; rewrite mem_set_mem_other by discriminate.
    simpl; rewrite M; reflexivity. }
  assert (Prog := program_shape v K m K2 ltac:(lia)).
  rewrite role_middle in Prog by lia. fold cin cout in Prog.
  destruct v.
  - (* Original: foreach receive, add, forward. *)
    destruct (foreach_add_forward (task_at 2 streams2 m (relay_body Original K (color_name cin) (color_name cout)))
                (bind (bind empty (named "x") (VZ (Z.of_nat m))) (named "y") (VZ 0%Z))
                (named "a") (named "k") (named "x") (link cout m) (EVar (named (color_name cout)))
                (partial (S m)) [] (a m) st1 (link cin (S m)))
      as (st2 & R2 & MA & C0 & C1 & Oth & _); auto; try discriminate; try congruence.
    { intros; apply chan_send. }
    rewrite Lp in R2; simpl List.length in R2.
    assert (R : run_tasks [task_at 1 [] m phase1_body;
        task_at 2 streams2 m (relay_body Original K (color_name cin) (color_name cout))] st0 = Some st2).
    { rewrite (run_two _ _ _ _ R1), run_task_at. unfold relay_body, ChainReduce.relay, var, coord, ChainReduce.a_k.
      rewrite exec_list_cons, exec_foreach, range_interval, chan_recv.
      use_loop R2. reflexivity. }
    eexists _, _; split; [apply (run_pe_result _ _ _ _ _ _ Prog R)|]. split.
    + apply (inv_next m sto); auto.
      * rewrite <- Cin; exact C0.
      * fold cout. rewrite C1, S1, Sout by discriminate; simpl.
        rewrite (partial_step m) by lia; reflexivity.
      * rewrite Oth by discriminate. unfold st1; autorewrite with df; reflexivity.
      * intros c N1 N2 N3. rewrite <- Cin in N1. rewrite Oth, S1 by assumption; reflexivity.
    + intros j J; apply pe_update; lia.
  - (* RecvFirst: receive the whole partial sum, map-add, send. *)
    set (t2 := task_at (V:=V) 2 streams2 m (relay_body RecvFirst K (color_name cin) (color_name cout))).
    set (e0 := coord_env (V:=V) ChainReduce.xy (at_pe m)).
    assert (R2 : exec t2 e0 (Receive (EVar (named "t")) (EVar (named (color_name cin))) (Some (named "r"))) st1 =
        Some (set_store (set_mem st1 (named "t") (partial (S m))) (link cin (S m)) [])).
    { rewrite (exec_receive_exact _ _ _ _ _ _ (link cin (S m))); try reflexivity.
      - rewrite S1 by discriminate; rewrite Sin; reflexivity.
      - apply chan_recv.
      - rewrite T1, S1, Sin, LT, Lp by (lia || discriminate); reflexivity. }
    set (st2 := set_store (set_mem st1 (named "t") (partial (S m))) (link cin (S m)) []) in *.
    destruct (map_add t2 e0 (named "a") (named "t") (named "k") (partial (S m)) [] (a m) st2)
      as (st3 & R3 & MA & Sto); auto; try discriminate; try congruence.
    { exists []; unfold st2; autorewrite with df; auto. }
    rewrite Lp in R3; simpl List.length in R3.
    set (st4 := set_store st3 (link cout m) (store st3 (link cout m) ++ mem st3 (named "a"))).
    assert (R : run_tasks [task_at 1 [] m phase1_body; t2] st0 = Some st4).
    { rewrite (run_two _ _ _ _ R1). unfold t2; rewrite run_task_at. fold t2.
      match goal with |- exec_list _ ?b _ _ = _ =>
        change b with [Receive (EVar (named "t")) (EVar (named (color_name cin))) (Some (named "r"));
          Await (named "r");
          Map [Typed (Scalar I32) (named "k")] [interval 0 (Z.of_nat K)]
            [Assign (elem (named "a") (named "k")) (Binary (elem (named "a") (named "k")) Plus (elem (named "t") (named "k")))] None;
          Send (EVar (named "a")) (EVar (named (color_name cout))) None] end.
      rewrite exec_list_cons. fold e0. rewrite R2.
      rewrite exec_list_cons, exec_await, exec_list_cons, exec_map, range_interval.
      use_loop R3. rewrite exec_list_cons, (exec_send_array _ _ _ _ _ _ (link cout m)); try reflexivity.
      apply chan_send. }
    eexists _, _; split; [apply (run_pe_result _ _ _ _ _ _ Prog R)|]. split.
    + apply (inv_next m sto); auto.
      * unfold st4; rewrite store_set_store_other by congruence.
        rewrite Sto; unfold st2; rewrite <- Cin; autorewrite with df; reflexivity.
      * fold cout; unfold st4; autorewrite with df. rewrite Sto, MA; unfold st2.
        rewrite store_set_store_other by congruence. autorewrite with df.
        rewrite S1, Sout by discriminate; simpl. rewrite (partial_step m) by lia; reflexivity.
      * unfold st4; rewrite store_set_store_other by discriminate.
        rewrite Sto; unfold st2; rewrite store_set_store_other by discriminate.
        autorewrite with df; unfold st1; autorewrite with df; reflexivity.
      * intros c N1 N2 N3. rewrite <- Cin in N1. unfold st4. fold cout in N2.
        rewrite store_set_store_other by congruence. rewrite Sto; unfold st2.
        rewrite store_set_store_other by congruence. autorewrite with df.
        rewrite S1 by assumption; reflexivity.
    + intros j J; apply pe_update; lia.
Qed.
(** PE 0 adds its vector and emits the total. *)
Lemma step_root : forall ms sto, Inv 1 sto -> ms (at_pe 0) = init (at_pe 0) ->
  exists ms' sto', run_pe (kernel v K) (at_pe 0) ms sto = Some (ms', sto') /\ Final sto'.
Proof.
  intros ms sto I M.
  assert (Cin : Blue = out_color K 1) by (apply (colors_match K 0); lia).
  assert (Lp : List.length (partial 1) = K) by (apply partial_length; lia).
  assert (La : List.length (a 0) = K) by (apply a_length; lia).
  assert (Sin : sto (link Blue 1) = partial 1).
  { rewrite I; unfold expected; rewrite <- Cin. destruct (chan_dec _ _); [reflexivity|congruence]. }
  assert (Sa : sto (host_in 0) = a 0).
  { rewrite I; unfold expected. destruct (chan_dec _ _); [discriminate|].
    rewrite in_index_host; reflexivity. }
  set (st0 := St (ms (at_pe 0)) sto).
  assert (R1 := run_phase1 0 st0). simpl store in R1. rewrite Sa in R1.
  specialize (R1 ltac:(simpl; rewrite M, LA, La by lia; reflexivity)).
  set (st1 := set_store (set_mem st0 (named "a") (a 0)) (host_in 0) []) in *.
  destruct (foreach_add (task_at (V:=V) 2 streams2 0 (root_body K)) (coord_env ChainReduce.xy (at_pe 0))
              (named "a") (named "k") (named "x") (partial 1) [] (a 0) st1 (link Blue 1))
    as (st2 & R2 & MA & C0 & Oth); try discriminate; try congruence.
  { unfold st1; autorewrite with df; reflexivity. }
  { unfold st1; rewrite store_set_store_other by discriminate; exact Sin. }
  rewrite Lp in R2; simpl List.length in R2.
  set (st3 := set_store st2 host_out (store st2 host_out ++ mem st2 (named "a"))).
  assert (R : run_tasks [task_at 1 [] 0 phase1_body; task_at 2 streams2 0 (role_body v K 0)] st0 = Some st3).
  { rewrite (run_two _ _ _ _ R1), role_root, run_task_at by lia.
    unfold root_body at 2; unfold ChainReduce.a_k, var, coord.
    change (named "blue") with (named (color_name Blue)).
    rewrite exec_list_cons, exec_foreach, range_interval, chan_recv.
    use_loop R2. rewrite exec_list_cons, (exec_send_array _ _ _ _ _ _ host_out); reflexivity. }
  eexists _, _; split; [apply (run_pe_result _ _ _ _ _ _ (program_shape v K 0 K2 ltac:(lia)) R)|]. split.
  - unfold st3; autorewrite with df. rewrite Oth by discriminate. unfold st1.
    rewrite store_set_store_other by discriminate. autorewrite with df.
    rewrite I, MA; unfold expected. destruct (chan_dec _ _); [discriminate|]. simpl.
    replace (zip_add (a 0) (partial 1)) with (partial 0) by (apply partial_step; lia). reflexivity.
  - intros c N. unfold st3; rewrite store_set_store_other by congruence.
    destruct (chan_dec c (link Blue 1)) as [->|N1]; [exact C0|].
    rewrite Oth by assumption. unfold st1.
    destruct (chan_dec c (host_in 0)) as [->|N2]; [autorewrite with df; reflexivity|].
    rewrite store_set_store_other by congruence. simpl. rewrite I; unfold expected.
    destruct (chan_dec _ _) as [E|]; [rewrite <- Cin in E; congruence|].
    destruct (in_index c) as [j|] eqn:J; [|reflexivity].
    destruct (Nat.ltb_spec j 1); [|reflexivity].
    assert (j = 0) by lia; subst. apply in_index_inj in J; congruence.
Qed.

(** ** The whole chain *)
Lemma chain_from : forall m ms sto, S m <= K - 1 -> Inv (S m) sto ->
  (forall j, j <= m -> ms (at_pe j) = init (at_pe j)) ->
  exists ms' sto', run (kernel v K) (down_from m) ms sto = Some (ms', sto') /\ Final sto'.
Proof.
  induction m as [|m IH]; intros ms sto L I M.
  - destruct (step_root ms sto I (M 0 (le_n 0))) as (ms' & sto' & R & F).
    exists ms', sto'; simpl; rewrite R; auto.
  - destruct (step_middle (S m) ms sto ltac:(lia) L I (M _ (le_n _))) as (ms1 & sto1 & R & I1 & U).
    destruct (IH ms1 sto1 ltac:(lia) I1) as (ms' & sto' & R' & F).
    { intros j J; rewrite U by lia; apply M; lia. }
    exists ms', sto'; simpl; rewrite R; auto.
Qed.

(** For any element type and addition, inputs, and initial memories of the
    declared sizes, and either variant: running the IR kernel puts
    [a0 + (a1 + (... + a_{K-1}))] on [out[0]] and drains every other stream. *)
Theorem chain_reduce_correct : exists ms sto,
  run (kernel v K) (down_from (K - 1)) init initial_store = Some (ms, sto) /\
  sto host_out = reduce inputs /\ (forall c, c <> host_out -> sto c = []).
Proof.
  destruct step_east as (ms1 & sto1 & R & I & U).
  replace (K - 1) with (S (K - 2)) in R, I |- * by lia.
  destruct (chain_from (K - 2) ms1 sto1 ltac:(lia) I) as (ms' & sto' & R' & F1 & F2).
  { intros j J; apply U; lia. }
  exists ms', sto'. simpl down_from. cbn [run]. rewrite R; auto.
Qed.
End Correctness.

(** ** Corollaries *)
Section Corollaries.
Context {V : Type} `{data_ops V}.

(** With associative, commutative addition, the order of the PEs' vectors
    does not matter. *)
Corollary chain_reduce_any_order :
  (forall x y z : V, plus x (plus y z) = plus (plus x y) z) ->
  (forall x y : V, plus x y = plus y x) ->
  forall v K (inputs : list (list V)) init order,
  2 <= K -> List.length inputs = K -> Forall (fun a => List.length a = K) inputs ->
  (forall i, i < K -> List.length (init (at_pe i) (named "a")) = K) ->
  (forall i, i < K -> List.length (init (at_pe i) (named "t")) = K) ->
  Permutation inputs order ->
  exists ms sto,
  run (kernel v K) (down_from (K - 1)) init (initial_store inputs) = Some (ms, sto) /\
  sto host_out = reduce order.
Proof.
  intros Assoc Comm v K inputs init order K2 LI LN LA LT P.
  destruct (chain_reduce_correct v K inputs init K2 LI LN LA LT) as (ms & sto & R & O & _).
  exists ms, sto; split; [exact R|]. rewrite O; apply reduce_permutation; assumption.
Qed.

(** With [K = 1], PE 0 is both the east corner and the root: two compute
    blocks in one phase, which SpaDA leaves undefined. *)
Theorem chain_reduce_K1_ill_formed : forall v, pe_program (V:=V) (kernel v 1) (at_pe 0) = None.
Proof. destruct v; reflexivity. Qed.
End Corollaries.
