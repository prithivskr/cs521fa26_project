From Stdlib Require Import List Arith Lia.
From Kahn Require Import Spec.
Import ListNotations.

(** * Kahn-process-network model of SpaDA kernels

    For race-free SpaDA programs, every stream is a single-writer,
    single-reader FIFO, and every PE behaves as a sequential process, so the
    result is independent of the schedule (Kahn's determinacy theorem, trusted
    here). This framework therefore models:

    - a stream as the list of values sent on it ([store : Chan -> list V]);
    - a PE as a sequential program over its private buffers ([mem]);
    - a run as PEs executed one at a time, in an order where each producer
      runs before its consumers. A receive with too little data returns [None].

    Stream, buffer and PE identifiers are parameters; a kernel supplies them. *)

Class Dec (A : Type) := dec : forall x y : A, {x = y} + {x <> y}.
#[export] Instance nat_dec : Dec nat := Nat.eq_dec.

Section Framework.
Context {V Chan Buf PE : Type} `{Plus V} `{Dec Chan} `{Dec Buf} `{Dec PE}.

(** ** State and statements *)
Record state := St { mem : Buf -> list V; store : Chan -> list V }.
Definition set_mem st b l :=
  St (fun b' => if dec b b' then l else mem st b') (store st).
Definition set_store st c l :=
  St (mem st) (fun c' => if dec c c' then l else store st c').
Arguments set_mem : simpl never.
Arguments set_store : simpl never.

(** Loop-body expressions: [b[k]], the received element [x], and [+]. *)
Inductive vexpr := ElemK (b : Buf) | X | Add (e1 e2 : vexpr).
Inductive simple := AssignK (b : Buf) (e : vexpr) | SendExpr (e : vexpr) (c : Chan).
(** [SendBuf]/[RecvBuf] move a whole buffer; [Loop n (Some c)] is a foreach over
    stream [c], and [Loop n None] is a map. *)
Inductive stmt :=
 | SendBuf (b : Buf) (c : Chan)
 | RecvBuf (b : Buf) (c : Chan)
 | Loop (n : nat) (src : option Chan) (body : list simple).

(** ** Execution *)
Fixpoint update_nth (l : list V) (k : nat) (v : V) : option (list V) :=
  match l, k with
  | [], _ => None
  | _ :: t, O => Some (v :: t)
  | h :: t, S k => option_map (cons h) (update_nth t k v)
  end.
Fixpoint eval_v (st : state) (k : nat) (x : option V) (e : vexpr) : option V :=
  match e with
  | ElemK b => nth_error (mem st b) k
  | X => x
  | Add a b => match eval_v st k x a, eval_v st k x b with
               | Some u, Some w => Some (plus u w) | _, _ => None end
  end.
Definition exec_simple (s : simple) k x st : option state :=
  match s with
  | AssignK b e => match eval_v st k x e with
     | Some v => option_map (set_mem st b) (update_nth (mem st b) k v)
     | None => None end
  | SendExpr e c => match eval_v st k x e with
     | Some v => Some (set_store st c (store st c ++ [v]))
     | None => None end
  end.
Fixpoint exec_body (body : list simple) k x st : option state :=
  match body with
  | [] => Some st
  | s :: r => match exec_simple s k x st with
              | Some st' => exec_body r k x st' | None => None end
  end.
Definition fetch (src : option Chan) st : option (option V * state) :=
  match src with
  | None => Some (None, st)
  | Some c => match store st c with
              | [] => None | v :: q => Some (Some v, set_store st c q) end
  end.
(** Iterations [j], [j+1], ... of a loop with [n] iterations left. *)
Fixpoint iter (n j : nat) src body st : option state :=
  match n with
  | O => Some st
  | S n => match fetch src st with
           | None => None
           | Some (x, st1) => match exec_body body j x st1 with
                              | Some st2 => iter n (S j) src body st2
                              | None => None end
           end
  end.
Definition exec (s : stmt) st : option state :=
  match s with
  | SendBuf b c => Some (set_store st c (store st c ++ mem st b))
  | RecvBuf b c =>
      let n := length (mem st b) in
      if n <=? length (store st c)
      then Some (set_store (set_mem st b (firstn n (store st c))) c (skipn n (store st c)))
      else None
  | Loop n src body => iter n 0 src body st
  end.
Fixpoint run_proc (p : list stmt) st : option state :=
  match p with
  | [] => Some st
  | s :: r => match exec s st with Some st' => run_proc r st' | None => None end
  end.

(** ** Networks: per-PE memories and shared stream contents *)
Definition run_pe (procs : PE -> list stmt) (i : PE) (ms : PE -> Buf -> list V)
  (sto : Chan -> list V) : option ((PE -> Buf -> list V) * (Chan -> list V)) :=
  match run_proc (procs i) (St (ms i) sto) with
  | Some st => Some (fun j => if dec i j then mem st else ms j, store st)
  | None => None
  end.
Fixpoint run_net (order : list PE) procs ms sto :=
  match order with
  | [] => Some (ms, sto)
  | i :: rest => match run_pe procs i ms sto with
                 | Some (ms', sto') => run_net rest procs ms' sto'
                 | None => None end
  end.

(** ** State lemmas *)
Lemma mem_set_mem_same st b l : mem (set_mem st b l) b = l.
Proof. unfold set_mem; simpl; destruct (dec b b); congruence. Qed.
Lemma mem_set_mem_other st b b' l : b <> b' -> mem (set_mem st b l) b' = mem st b'.
Proof. intros; unfold set_mem; simpl; destruct (dec b b'); congruence. Qed.
Lemma store_set_mem st b l c : store (set_mem st b l) c = store st c.
Proof. reflexivity. Qed.
Lemma mem_set_store st c l b : mem (set_store st c l) b = mem st b.
Proof. reflexivity. Qed.
Lemma store_set_store_same st c l : store (set_store st c l) c = l.
Proof. unfold set_store; simpl; destruct (dec c c); congruence. Qed.
Lemma store_set_store_other st c c' l : c <> c' -> store (set_store st c l) c' = store st c'.
Proof. intros; unfold set_store; simpl; destruct (dec c c'); congruence. Qed.
#[local] Hint Rewrite mem_set_mem_same store_set_mem mem_set_store store_set_store_same : kahn.

Lemma nth_error_mid (pre rest : list V) r : nth_error (pre ++ r :: rest) (length pre) = Some r.
Proof. induction pre; simpl; auto. Qed.
Lemma update_mid (pre rest : list V) r v :
  update_nth (pre ++ r :: rest) (length pre) v = Some (pre ++ v :: rest).
Proof. induction pre as [|h t IH]; simpl; auto. rewrite IH; reflexivity. Qed.

Lemma run_proc_cons s r st :
  run_proc (s :: r) st = match exec s st with Some st' => run_proc r st' | None => None end.
Proof. reflexivity. Qed.
Lemma recv_exact b c st : length (mem st b) = length (store st c) ->
  exec (RecvBuf b c) st = Some (set_store (set_mem st b (store st c)) c []).
Proof. intros E; simpl. rewrite E, Nat.leb_refl, firstn_all, skipn_all. reflexivity. Qed.
Lemma run_pe_result procs i ms sto st : run_proc (procs i) (St (ms i) sto) = Some st ->
  run_pe procs i ms sto = Some (fun j => if dec i j then mem st else ms j, store st).
Proof. intros E; unfold run_pe; rewrite E; reflexivity. Qed.

(** ** Loop lemmas *)
(** [foreach k, x in receive(cin) { b[k] = b[k] + x; send(b[k], cout) }]. *)
Lemma foreach_add_forward : forall b p pre rest st cin cout,
  cin <> cout -> length rest = length p ->
  mem st b = pre ++ rest -> store st cin = p ->
  exists st', iter (length p) (length pre) (Some cin)
    [AssignK b (Add (ElemK b) X); SendExpr (ElemK b) cout] st = Some st' /\
  mem st' b = pre ++ zip_add rest p /\ store st' cin = [] /\
  store st' cout = store st cout ++ zip_add rest p /\
  (forall c, c <> cin -> c <> cout -> store st' c = store st c) /\
  (forall b', b' <> b -> mem st' b' = mem st b').
Proof.
  intros b; induction p as [|v p IH]; intros pre rest st cin cout D L M Sc.
  - destruct rest; [|discriminate]. exists st; simpl.
    rewrite M; unfold zip_add; simpl; rewrite !app_nil_r; repeat split; auto.
  - destruct rest as [|r rest]; [discriminate|]. simpl in L.
    simpl iter; unfold fetch; rewrite Sc.
    set (st1 := set_store st cin p).
    simpl exec_body; unfold exec_simple; simpl eval_v.
    assert (M1 : mem st1 b = pre ++ r :: rest) by (unfold st1; autorewrite with kahn; auto).
    rewrite M1, nth_error_mid, update_mid; simpl option_map.
    set (st2 := set_mem st1 b (pre ++ plus r v :: rest)); cbv beta iota.
    assert (M2 : mem st2 b = pre ++ plus r v :: rest) by (unfold st2; autorewrite with kahn; auto).
    rewrite M2, nth_error_mid.
    set (st3 := set_store st2 cout (store st2 cout ++ [plus r v])); cbv beta iota.
    destruct (IH (pre ++ [plus r v]) rest st3 cin cout D ltac:(lia))
      as (st' & R & MA & Cin & Cout & Oth & MT).
    + unfold st3; autorewrite with kahn; rewrite M2, <- app_assoc; reflexivity.
    + unfold st3, st2, st1; rewrite store_set_store_other by congruence;
        autorewrite with kahn; reflexivity.
    + rewrite length_app in R; simpl in R; rewrite Nat.add_1_r in R.
      exists st'; split; [exact R|].
      unfold zip_add in *; simpl.
      rewrite MA, <- app_assoc; split; [reflexivity|]. split; [exact Cin|].
      rewrite Cout; unfold st3, st2, st1; autorewrite with kahn.
      rewrite store_set_store_other by congruence; rewrite <- app_assoc; split; [reflexivity|].
      split.
      * intros c C1 C2; rewrite Oth by assumption; unfold st3, st2, st1.
        rewrite store_set_store_other by congruence; autorewrite with kahn.
        apply store_set_store_other; congruence.
      * intros b' B; rewrite MT by assumption; unfold st3, st2, st1; autorewrite with kahn.
        rewrite mem_set_mem_other by congruence; reflexivity.
Qed.

(** [foreach k, x in receive(cin) { b[k] = b[k] + x }]. *)
Lemma foreach_add : forall b p pre rest st cin,
  length rest = length p -> mem st b = pre ++ rest -> store st cin = p ->
  exists st', iter (length p) (length pre) (Some cin)
    [AssignK b (Add (ElemK b) X)] st = Some st' /\
  mem st' b = pre ++ zip_add rest p /\ store st' cin = [] /\
  (forall c, c <> cin -> store st' c = store st c).
Proof.
  intros b; induction p as [|v p IH]; intros pre rest st cin L M Sc.
  - destruct rest; [|discriminate]. exists st; simpl.
    rewrite M; unfold zip_add; simpl; rewrite !app_nil_r; repeat split; auto.
  - destruct rest as [|r rest]; [discriminate|]. simpl in L.
    simpl iter; unfold fetch; rewrite Sc.
    set (st1 := set_store st cin p).
    simpl exec_body; unfold exec_simple; simpl eval_v.
    assert (M1 : mem st1 b = pre ++ r :: rest) by (unfold st1; autorewrite with kahn; auto).
    rewrite M1, nth_error_mid, update_mid; simpl option_map.
    set (st2 := set_mem st1 b (pre ++ plus r v :: rest)); cbv beta iota.
    destruct (IH (pre ++ [plus r v]) rest st2 cin ltac:(lia)) as (st' & R & MA & Cin & Oth).
    + unfold st2; autorewrite with kahn; rewrite <- app_assoc; reflexivity.
    + unfold st2, st1; autorewrite with kahn; reflexivity.
    + rewrite length_app in R; simpl in R; rewrite Nat.add_1_r in R.
      exists st'; split; [exact R|].
      unfold zip_add in *; simpl. rewrite MA, <- app_assoc.
      split; [reflexivity|]. split; [exact Cin|].
      intros c C; rewrite Oth by assumption; unfold st2, st1; autorewrite with kahn.
      apply store_set_store_other; congruence.
Qed.

(** [map k { b[k] = b[k] + t[k] }]. *)
Lemma map_add : forall b t tv pre rest st, b <> t ->
  length rest = length tv -> mem st b = pre ++ rest ->
  (exists tp, mem st t = tp ++ tv /\ length tp = length pre) ->
  exists st', iter (length tv) (length pre) None
    [AssignK b (Add (ElemK b) (ElemK t))] st = Some st' /\
  mem st' b = pre ++ zip_add rest tv /\ store st' = store st.
Proof.
  intros b t tv; induction tv as [|v tv IH]; intros pre rest st D L M (tp & T & LT).
  - destruct rest; [|discriminate]. exists st; simpl.
    rewrite M; unfold zip_add; simpl; rewrite !app_nil_r; repeat split; auto.
  - destruct rest as [|r rest]; [discriminate|]. simpl in L.
    simpl iter; simpl fetch; simpl exec_body; unfold exec_simple; simpl eval_v.
    rewrite M, nth_error_mid, T, <- LT, nth_error_mid, LT, update_mid; simpl option_map.
    set (st2 := set_mem st b (pre ++ plus r v :: rest)); cbv beta iota.
    destruct (IH (pre ++ [plus r v]) rest st2 D ltac:(lia)) as (st' & R & MA & Sto).
    + unfold st2; autorewrite with kahn; rewrite <- app_assoc; reflexivity.
    + exists (tp ++ [v]); unfold st2.
      rewrite mem_set_mem_other by congruence; rewrite T, <- app_assoc.
      split; [reflexivity|]. rewrite !length_app; simpl; lia.
    + rewrite length_app in R; simpl in R; rewrite Nat.add_1_r in R.
      exists st'; split; [exact R|].
      unfold zip_add in *; simpl. rewrite MA, <- app_assoc.
      split; [reflexivity|]. rewrite Sto; reflexivity.
Qed.
End Framework.

Arguments set_mem : simpl never.
Arguments set_store : simpl never.
#[export] Hint Rewrite @mem_set_mem_same @store_set_mem @mem_set_store
  @store_set_store_same : kahn.
