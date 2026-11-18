From Stdlib Require Import ZArith List String Bool Lia.
From SpatialCSL Require Import SpadaIR ReduceSpec.
Import ListNotations Spada.
Open Scope list_scope.

(** * Hardware-agnostic value semantics for SpaDA IR

    This interprets [Spada.kernel] terms directly, following SpaDA's spatial
    spec (irspec/docs/spatial/{spatial,async}.md), not any target. The same
    terms are exported to SpaDA and lowered to CSL.

    - Streams are FIFO edges. A relative stream [s] sent from PE [p] in phase
      [n] is the edge [Edge n s p]; a receive at [q] reads the edge whose
      sender is [q - (dx, dy)]. Argument streams are [Arg a index].
    - Each PE runs its phases in order, with at most one compute block per
      phase (more is undefined behaviour, so [pe_program] rejects it).
    - Statements run in program order. SpaDA lets un-awaited asynchronous
      statements run concurrently, but for a race-free program (races are
      undefined behaviour) program order is one legal schedule, so the values
      computed here are the program's values.
    - [run] executes whole PEs one at a time in a given order, with unbounded
      streams; a receive that finds too little data fails. [run_phased] is
      the same at task granularity: each entry runs a PE's next phase.
    - Scalar fields are one-element lists in memory: [EVar f] reads field [f]
      when no local is named [f], and [Assign (EVar f) e] writes it.

    What this does not model: SpaDA calls a program deadlocked if it can get
    stuck under any progress order, with sends that may stall until the
    receiver is ready. A successful [run] therefore shows the values, not
    deadlock freedom, which is a separate obligation. Not supported (the
    interpreter fails): [MetaFor], multicast and extern streams, [close],
    [foreach] without a range, and multi-index loops.

    Data arithmetic is abstract ([data_ops]); index arithmetic is in [Z]. *)

Definition pe := (Z * Z)%type.

Inductive chan :=
 | Arg (a : identifier) (index : list Z)
 | Edge (phase : nat) (s : identifier) (sender : pe).

Definition id_dec (a b : identifier) : {a = b} + {a <> b}.
Proof.
  destruct a as [n v], b as [n' v'].
  destruct (string_dec n n'), (Nat.eq_dec v v'); [left|right..]; congruence.
Defined.
Definition pe_dec (p q : pe) : {p = q} + {p <> q}.
Proof. unfold pe; decide equality; apply Z.eq_dec. Defined.
Definition chan_dec (a b : chan) : {a = b} + {a <> b}.
Proof.
  decide equality; try apply id_dec; try apply pe_dec; try apply Nat.eq_dec.
  apply (list_eq_dec Z.eq_dec).
Defined.

(** Data arithmetic: any element type with any operations (e.g. IEEE f32). *)
Class data_ops (V : Type) := DataOps {
  data_binary : binary -> V -> V -> V;
  data_literal : scalar -> literal -> V;
  (** [data_fma a b c] is [FusedMultiplyAdd a b c], i.e. [a + b * c] rounded once. *)
  data_fma : V -> V -> V -> V
}.
#[export] Instance data_plus {V} `{data_ops V} : ReduceSpec.Plus V := data_binary Spada.Plus.

Section Semantics.
Context {V : Type} `{data_ops V}.

(** ** Values and expressions *)
Inductive val := VZ (z : Z) | VD (x : V).
Definition env := identifier -> option val.
Definition empty : env := fun _ => None.
Definition bind (e : env) (i : identifier) (v : val) : env :=
  fun j => if id_dec i j then Some v else e j.
Definition memory := identifier -> list V.

Definition is_float (t : scalar) := match t with F16 | F32 | F64 => true | _ => false end.
Definition zbool (b : bool) : Z := if b then 1 else 0.
Definition zbinary (op : binary) (u w : Z) : option Z :=
  match op with
  | Plus => Some (u + w) | Minus => Some (u - w) | Times => Some (u * w)
  | Divide => Some (u / w) | Modulo => Some (u mod w)
  | Equal => Some (zbool (u =? w)) | NotEqual => Some (zbool (negb (u =? w)))
  | Less => Some (zbool (u <? w)) | LessEqual => Some (zbool (u <=? w))
  | Greater => Some (zbool (w <? u)) | GreaterEqual => Some (zbool (w <=? u))
  | LogicalAnd => Some (zbool (negb (u =? 0) && negb (w =? 0)))
  | LogicalOr => Some (zbool (negb (u =? 0) || negb (w =? 0)))
  | _ => None
  end%Z.

(** Variables are locals (coordinates, loop indices, received elements) or,
    when no local has that name, scalar fields (stored as one-element lists);
    arrays are read through [Slice]. *)
Fixpoint eval (m : memory) (e : env) (x : expression) : option val :=
  match x with
  | EVar i => match e i with
              | Some v => Some v
              | None => match m i with [v] => Some (VD v) | _ => None end
              end
  | Constant t l =>
      if is_float t then Some (VD (data_literal t l)) else
      match l with
      | Integer z => Some (VZ z) | BooleanValue b => Some (VZ (zbool b)) | FloatBits _ => None
      end
  | EParam _ (Some z) => Some (VZ z)
  | Unary Negative a => match eval m e a with Some (VZ z) => Some (VZ (- z)) | _ => None end
  | Binary a op b =>
      match eval m e a, eval m e b with
      | Some (VZ u), Some (VZ w) => option_map VZ (zbinary op u w)
      | Some (VD u), Some (VD w) => Some (VD (data_binary op u w))
      | _, _ => None
      end
  | Select a c b =>
      match eval m e c with
      | Some (VZ z) => if (z =? 0)%Z then eval m e b else eval m e a
      | _ => None
      end
  | FusedMultiplyAdd a b c =>
      match eval m e a, eval m e b, eval m e c with
      | Some (VD u), Some (VD v), Some (VD w) => Some (VD (data_fma u v w))
      | _, _, _ => None
      end
  | Slice a [i] =>
      match eval m e i with
      | Some (VZ k) => if (0 <=? k)%Z then option_map VD (nth_error (m a) (Z.to_nat k)) else None
      | _ => None
      end
  | _ => None
  end.
Definition eval_z m e x := match eval m e x with Some (VZ z) => Some z | _ => None end.
Fixpoint eval_zs m e (xs : list expression) : option (list Z) :=
  match xs with
  | [] => Some []
  | x :: r => match eval_z m e x, eval_zs m e r with
              | Some z, Some zs => Some (z :: zs) | _, _ => None end
  end.

(** [lo:hi:step], [hi] exclusive. *)
Definition range_values m e (r : expression) : option (list Z) :=
  match r with
  | Range lo (Some hi) step =>
      match eval_z m e lo, eval_z m e hi,
            match step with None => Some 1%Z | Some s => eval_z m e s end with
      | Some l, Some h, Some s =>
          if (0 <? s)%Z
          then Some (map (fun j => l + Z.of_nat j * s)%Z (seq 0 (Z.to_nat ((h - l + s - 1) / s))))
          else None
      | _, _, _ => None
      end
  | _ => None
  end.

(** ** Which code a PE runs *)
Definition no_memory : memory := fun _ => [].
Definition in_range (r : expression) (z : Z) : bool :=
  match r with
  | Range lo None _ =>
      match eval_z no_memory empty lo with Some l => (z =? l)%Z | None => false end
  | Range lo (Some hi) step =>
      match eval_z no_memory empty lo, eval_z no_memory empty hi with
      | Some l, Some h =>
          ((l <=? z) && (z <? h) &&
           match step with
           | None => true
           | Some s => match eval_z no_memory empty s with
                       | Some s => ((z - l) mod s =? 0) | None => false end
           end)%Z
      | _, _ => false
      end
  | x => match eval_z no_memory empty x with Some l => (z =? l)%Z | None => false end
  end.
Definition in_grid (g : subgrid) (p : pe) := in_range (xrange g) (fst p) && in_range (yrange g) (snd p).

(** One compute block instance: its phase, PE, streams in scope, and
    coordinates. *)
Record task := Task {
  t_phase : nat; t_pe : pe; t_streams : list stream_decl; t_env : env; t_body : list statement
}.
Definition coord_env (cs : list typed_id) (p : pe) : env :=
  match cs with
  | [x; y] => bind (bind empty (ident x) (VZ (fst p))) (ident y) (VZ (snd p))
  | _ => empty
  end.
Definition streams_of (bs : list block) : list stream_decl :=
  flat_map (fun b => match b with Dataflow _ _ ss => ss | _ => [] end) bs.
Definition computes_at (bs : list block) (p : pe) :=
  flat_map (fun b => match b with
    | Compute cs g body => if in_grid g p then [(cs, body)] else []
    | _ => [] end) bs.
Definition flat_block (b : block) :=
  match b with Place _ _ _ | Dataflow _ _ _ | Compute _ _ _ => true | _ => false end.

(** A phase gives PE [p] at most one compute block. *)
Definition phase_task (n : nat) (global : list stream_decl) (bs : list block) (p : pe)
  : option (list task) :=
  if forallb flat_block bs then
    match computes_at bs p with
    | [] => Some []
    | [(cs, body)] => Some [Task n p (streams_of bs ++ global) (coord_env cs p) body]
    | _ => None
    end
  else None.
Fixpoint phase_tasks (n : nat) global (bs : list block) (p : pe) : option (list task) :=
  match bs with
  | [] => Some []
  | Phase body :: rest =>
      match phase_task n global body p, phase_tasks (S n) global rest p with
      | Some ts, Some us => Some (ts ++ us) | _, _ => None
      end
  | Place _ _ _ :: rest | Dataflow _ _ _ :: rest => phase_tasks n global rest p
  | _ => None
  end.
(** Phases are numbered from 1; outer-scope streams are in scope in each. *)
Definition pe_program (k : kernel) (p : pe) : option (list task) :=
  phase_tasks 1 (streams_of (blocks k)) (blocks k) p.

(** ** Streams *)
Fixpoint find_stream (ds : list stream_decl) (s : identifier) : option stream_decl :=
  match ds with
  | [] => None
  | d :: r => if id_dec (stream_id d) s then Some d else find_stream r s
  end.
Fixpoint chan_of (sending : bool) (t : task) (m : memory) (e : env) (x : expression)
  : option chan :=
  match x with
  | EVar s =>
      match find_stream (t_streams t) s with
      | None => Some (Arg s [])
      | Some d =>
          match source d with
          | Relative dx dy _ =>
              if sending then Some (Edge (t_phase t) s (t_pe t)) else
              match eval_z m e dx, eval_z m e dy with
              | Some a, Some b => Some (Edge (t_phase t) s (fst (t_pe t) - a, snd (t_pe t) - b)%Z)
              | _, _ => None
              end
          | _ => None
          end
      end
  | Slice s ix => option_map (Arg s) (eval_zs m e ix)
  | Select a c b =>
      match eval_z m e c with
      | Some z => if (z =? 0)%Z then chan_of sending t m e b else chan_of sending t m e a
      | None => None
      end
  | _ => None
  end.

(** ** Statements *)
Record state := St { mem : memory; store : chan -> list V }.
Definition set_mem st a l := St (fun b => if id_dec a b then l else mem st b) (store st).
Definition set_store st c l := St (mem st) (fun d => if chan_dec c d then l else store st d).

Fixpoint update_nth (l : list V) (k : nat) (v : V) : option (list V) :=
  match l, k with
  | [], _ => None
  | _ :: t, O => Some (v :: t)
  | h :: t, S k => option_map (cons h) (update_nth t k v)
  end.

(** A send's payload: a received element, a whole array, or one element. *)
Definition payload st e (x : expression) : option (list V) :=
  match x with
  | EVar a => match e a with Some (VD v) => Some [v] | Some (VZ _) => None | None => Some (mem st a) end
  | _ => match eval (mem st) e x with Some (VD v) => Some [v] | _ => None end
  end.

Definition fetch (src : option (identifier * chan)) (e : env) (st : state) : option (env * state) :=
  match src with
  | None => Some (e, st)
  | Some (x, c) => match store st c with
                   | [] => None
                   | v :: q => Some (bind e x (VD v), set_store st c q)
                   end
  end.
(** A loop over index values [zs]; with [src], each iteration first receives
    one element into [x]. *)
Fixpoint iter_loop (run : env -> state -> option state) (e : env) (k : identifier)
  (src : option (identifier * chan)) (zs : list Z) (st : state) : option state :=
  match zs with
  | [] => Some st
  | z :: zs =>
      match fetch src (bind e k (VZ z)) st with
      | None => None
      | Some (e1, st1) => match run e1 st1 with
                          | Some st2 => iter_loop run e k src zs st2
                          | None => None
                          end
      end
  end.

Section Exec.
Variable t : task.
Fixpoint exec (e : env) (s : statement) (st : state) {struct s} : option state :=
  let fix exec_body (ss : list statement) (e : env) (st : state) : option state :=
    match ss with
    | [] => Some st
    | s :: r => match exec e s st with Some st' => exec_body r e st' | None => None end
    end in
  match s with
  | Assign (Slice a [i]) src =>
      match eval_z (mem st) e i, eval (mem st) e src with
      | Some k, Some (VD v) =>
          if (0 <=? k)%Z then option_map (set_mem st a) (update_nth (mem st a) (Z.to_nat k) v)
          else None
      | _, _ => None
      end
  | Assign (EVar f) src =>
      match e f, mem st f, eval (mem st) e src with
      | None, [_], Some (VD v) => Some (set_mem st f [v])
      | _, _, _ => None
      end
  | Send x c _ =>
      match payload st e x, chan_of true t (mem st) e c with
      | Some vs, Some ch => Some (set_store st ch (store st ch ++ vs))
      | _, _ => None
      end
  | Receive (EVar a) c _ =>
      match e a, chan_of false t (mem st) e c with
      | None, Some ch =>
          let n := List.length (mem st a) in
          if Nat.leb n (List.length (store st ch))
          then Some (set_store (set_mem st a (firstn n (store st ch))) ch (skipn n (store st ch)))
          else None
      | _, _ => None
      end
  | Foreach [Typed _ k] [r] (Typed _ x) c body _ =>
      match range_values (mem st) e r, chan_of false t (mem st) e c with
      | Some zs, Some ch => iter_loop (exec_body body) e k (Some (x, ch)) zs st
      | _, _ => None
      end
  | Map [Typed _ k] [r] body _ | For [Typed _ k] [r] body =>
      match range_values (mem st) e r with
      | Some zs => iter_loop (exec_body body) e k None zs st
      | None => None
      end
  | Async body _ => exec_body body e st
  | Await _ | AwaitAll => Some st
  | _ => None
  end.
Fixpoint exec_list (ss : list statement) (e : env) (st : state) : option state :=
  match ss with
  | [] => Some st
  | s :: r => match exec e s st with Some st' => exec_list r e st' | None => None end
  end.
End Exec.

(** ** Kernels *)
Definition run_task (t : task) (st : state) := exec_list t (t_body t) (t_env t) st.
Fixpoint run_tasks (ts : list task) (st : state) : option state :=
  match ts with
  | [] => Some st
  | t :: r => match run_task t st with Some st' => run_tasks r st' | None => None end
  end.
Definition run_pe (k : kernel) (p : pe) (ms : pe -> memory) (sto : chan -> list V)
  : option ((pe -> memory) * (chan -> list V)) :=
  match pe_program k p with
  | None => None
  | Some ts =>
      match run_tasks ts (St (ms p) sto) with
      | Some st => Some (fun q => if pe_dec p q then mem st else ms q, store st)
      | None => None
      end
  end.
(** Run whole PEs in [order]; [ms] are the initial memories and [sto] the
    initial stream contents (argument inputs). *)
Fixpoint run (k : kernel) (order : list pe) (ms : pe -> memory) (sto : chan -> list V) :=
  match order with
  | [] => Some (ms, sto)
  | p :: rest => match run_pe k p ms sto with
                 | Some (ms', sto') => run k rest ms' sto'
                 | None => None
                 end
  end.

(** ** Phase-granular scheduling

    [run] executes whole PEs. In kernels whose PEs swap roles across phases
    (e.g. SUMMA, where a PE sends in one phase and receives in another) no
    whole-PE order works, so [run_phased] interleaves at task granularity:
    each entry [p] of the order runs PE [p]'s next task (compute block
    instance). [pc p] counts the tasks PE [p] has run; an entry for a PE with
    no task left fails. *)
Definition run_next (k : kernel) (p : pe) (ms : pe -> memory) (pc : pe -> nat)
  (sto : chan -> list V) : option ((pe -> memory) * (pe -> nat) * (chan -> list V)) :=
  match pe_program k p with
  | None => None
  | Some ts =>
      match nth_error ts (pc p) with
      | None => None
      | Some t =>
          match run_task t (St (ms p) sto) with
          | Some st => Some (fun q => if pe_dec p q then mem st else ms q,
                             fun q => if pe_dec p q then S (pc p) else pc q, store st)
          | None => None
          end
      end
  end.
Fixpoint run_phased (k : kernel) (order : list pe) (ms : pe -> memory) (pc : pe -> nat)
  (sto : chan -> list V) :=
  match order with
  | [] => Some (ms, pc, sto)
  | p :: rest => match run_next k p ms pc sto with
                 | Some (ms', pc', sto') => run_phased k rest ms' pc' sto'
                 | None => None
                 end
  end.
End Semantics.

Arguments set_mem : simpl never.
Arguments set_store : simpl never.

(** * Reusable lemmas *)
Section Lemmas.
Context {V : Type} `{data_ops V}.

(** ** State *)
Lemma mem_set_mem_same (st : @state V) a l : mem (set_mem st a l) a = l.
Proof. unfold set_mem; simpl; destruct (id_dec a a); congruence. Qed.
Lemma mem_set_mem_other (st : @state V) a b l : a <> b -> mem (set_mem st a l) b = mem st b.
Proof. intros; unfold set_mem; simpl; destruct (id_dec a b); congruence. Qed.
Lemma store_set_mem (st : @state V) a l c : store (set_mem st a l) c = store st c.
Proof. reflexivity. Qed.
Lemma mem_set_store (st : @state V) c l a : mem (set_store st c l) a = mem st a.
Proof. reflexivity. Qed.
Lemma store_set_store_same (st : @state V) c l : store (set_store st c l) c = l.
Proof. unfold set_store; simpl; destruct (chan_dec c c); congruence. Qed.
Lemma store_set_store_other (st : @state V) c d l : c <> d -> store (set_store st c l) d = store st d.
Proof. intros; unfold set_store; simpl; destruct (chan_dec c d); congruence. Qed.
Lemma bind_same (e : @env V) i v : bind e i v i = Some v.
Proof. unfold bind; destruct (id_dec i i); congruence. Qed.
Lemma bind_other (e : @env V) i j v : i <> j -> bind e i v j = e j.
Proof. intros; unfold bind; destruct (id_dec i j); congruence. Qed.

Lemma nth_error_mid (pre rest : list V) r : nth_error (pre ++ r :: rest) (List.length pre) = Some r.
Proof. induction pre; simpl; auto. Qed.
Lemma update_mid (pre rest : list V) r v :
  update_nth (pre ++ r :: rest) (List.length pre) v = Some (pre ++ v :: rest).
Proof. induction pre as [|h t IH]; simpl; auto. rewrite IH; reflexivity. Qed.

(** ** Statements *)
Lemma exec_list_cons t s r e (st : @state V) : exec_list t (s :: r) e st =
  match exec t e s st with Some st' => exec_list t r e st' | None => None end.
Proof. reflexivity. Qed.
Lemma exec_list_nil t e (st : @state V) : exec_list t [] e st = Some st.
Proof. reflexivity. Qed.
Lemma exec_await t e c (st : @state V) : exec t e (Await c) st = Some st.
Proof. reflexivity. Qed.
Lemma exec_foreach t e ty k r ty' x c body d (st : @state V) :
  exec t e (Foreach [Typed ty k] [r] (Typed ty' x) c body d) st =
  match range_values (mem st) e r, chan_of false t (mem st) e c with
  | Some zs, Some ch => iter_loop (exec_list t body) e k (Some (x, ch)) zs st
  | _, _ => None
  end.
Proof. reflexivity. Qed.
Lemma exec_map t e ty k r body d (st : @state V) :
  exec t e (Map [Typed ty k] [r] body d) st =
  match range_values (mem st) e r with
  | Some zs => iter_loop (exec_list t body) e k None zs st
  | None => None
  end.
Proof. reflexivity. Qed.
Lemma exec_send_array t e a c d (st : @state V) ch : e a = None ->
  chan_of true t (mem st) e c = Some ch ->
  exec t e (Send (EVar a) c d) st = Some (set_store st ch (store st ch ++ mem st a)).
Proof. intros A C. simpl. rewrite A, C. reflexivity. Qed.
(** A whole-array receive when exactly the array's worth of data is waiting. *)
Lemma exec_receive_exact t e a c d (st : @state V) ch : e a = None ->
  chan_of false t (mem st) e c = Some ch ->
  List.length (mem st a) = List.length (store st ch) ->
  exec t e (Receive (EVar a) c d) st = Some (set_store (set_mem st a (store st ch)) ch []).
Proof.
  intros A C L. simpl. rewrite A, C, L, Nat.leb_refl, firstn_all, skipn_all. reflexivity.
Qed.

Lemma range_interval m e n :
  range_values m e (interval 0 (Z.of_nat n)) = Some (map Z.of_nat (seq 0 n)).
Proof.
  unfold range_values, interval, int, eval_z; simpl.
  replace ((Z.of_nat n - 0 + 1 - 1) / 1)%Z with (Z.of_nat n) by (rewrite Z.div_1_r; lia).
  rewrite Nat2Z.id. f_equal. apply map_ext; intros; lia.
Qed.

Definition elem a k := Slice a [EVar k].

(** Reading [a[k]] where [k] is bound to position [length pre]. *)
Lemma eval_elem m (e : @env V) a k pre r rest :
  e k = Some (VZ (Z.of_nat (List.length pre))) -> m a = pre ++ r :: rest ->
  eval m e (elem a k) = Some (VD r).
Proof.
  intros K M; unfold elem; simpl. rewrite K.
  rewrite (proj2 (Z.leb_le 0 _)) by lia. rewrite Nat2Z.id, M, nth_error_mid. reflexivity.
Qed.
Lemma exec_assign_elem t (e : @env V) a k src (st : @state V) pre r rest v :
  e k = Some (VZ (Z.of_nat (List.length pre))) -> mem st a = pre ++ r :: rest ->
  eval (mem st) e src = Some (VD v) ->
  exec t e (Assign (elem a k) src) st = Some (set_mem st a (pre ++ v :: rest)).
Proof.
  intros K M S. unfold elem. simpl exec. unfold eval_z; simpl eval at 1. rewrite K, S.
  rewrite (proj2 (Z.leb_le 0 _)) by lia. rewrite Nat2Z.id, M, update_mid. reflexivity.
Qed.
Lemma exec_send_elem t (e : @env V) a k c (st : @state V) ch pre r rest :
  e k = Some (VZ (Z.of_nat (List.length pre))) -> mem st a = pre ++ r :: rest ->
  chan_of true t (mem st) e c = Some ch ->
  exec t e (Send (elem a k) c None) st = Some (set_store st ch (store st ch ++ [r])).
Proof.
  intros K M C. cbn [exec]. unfold payload. rewrite (eval_elem _ _ _ _ _ _ _ K M), C.
  reflexivity.
Qed.

Lemma eval_var m (e : @env V) x v : e x = Some v -> eval m e (EVar x) = Some v.
Proof. intros E; simpl; rewrite E; reflexivity. Qed.
Lemma eval_data_binary m (e : @env V) x y op u w :
  eval m e x = Some (VD u) -> eval m e y = Some (VD w) ->
  eval m e (Binary x op y) = Some (VD (data_binary op u w)).
Proof. intros X Y; simpl; rewrite X, Y; reflexivity. Qed.

#[local] Hint Rewrite mem_set_mem_same store_set_mem mem_set_store store_set_store_same : df.

(** ** Loops *)

(** [foreach k, x in [..], receive(cin) { a[k] = a[k] + x; send(a[k], cout) }] *)
Lemma foreach_add_forward : forall t e a k x cout sout p pre rest (st : @state V) cin,
  x <> k -> cin <> cout -> (forall m e', chan_of true t m e' sout = Some cout) ->
  List.length rest = List.length p -> mem st a = pre ++ rest -> store st cin = p ->
  exists st', iter_loop (exec_list t [Assign (elem a k) (Binary (elem a k) Spada.Plus (EVar x));
                                      Send (elem a k) sout None])
    e k (Some (x, cin)) (map Z.of_nat (seq (List.length pre) (List.length p))) st = Some st' /\
  mem st' a = pre ++ zip_add rest p /\ store st' cin = [] /\
  store st' cout = store st cout ++ zip_add rest p /\
  (forall c, c <> cin -> c <> cout -> store st' c = store st c) /\
  (forall b, b <> a -> mem st' b = mem st b).
Proof.
  intros t e a k x cout sout p; induction p as [|v p IH];
    intros pre rest st cin XK D So L M Sc.
  - destruct rest; [|discriminate]. exists st; simpl.
    rewrite M; unfold zip_add; simpl; rewrite !app_nil_r; repeat split; auto.
  - destruct rest as [|r rest]; [discriminate|]. simpl in L.
    cbn [Datatypes.length seq map iter_loop fetch]. rewrite Sc; cbv beta iota.
    set (e2 := bind (bind e k (VZ (Z.of_nat (List.length pre)))) x (VD v)).
    assert (Ek : e2 k = Some (VZ (Z.of_nat (List.length pre))))
      by (unfold e2; rewrite bind_other, bind_same by assumption; reflexivity).
    assert (Ex : e2 x = Some (VD v)) by apply bind_same.
    set (st1 := set_store st cin p).
    assert (M1 : mem st1 a = pre ++ r :: rest) by (unfold st1; autorewrite with df; auto).
    rewrite exec_list_cons.
    rewrite (exec_assign_elem _ _ _ _ _ _ _ _ _ (plus r v) Ek M1)
      by (apply eval_data_binary; [exact (eval_elem _ _ _ _ _ _ _ Ek M1) | exact (eval_var _ _ _ _ Ex)]).
    set (st2 := set_mem st1 a (pre ++ plus r v :: rest)).
    assert (M2 : mem st2 a = pre ++ plus r v :: rest) by (unfold st2; autorewrite with df; auto).
    rewrite exec_list_cons, (exec_send_elem _ _ _ _ _ _ _ _ _ _ Ek M2 (So _ _)), exec_list_nil.
    set (st3 := set_store st2 cout (store st2 cout ++ [plus r v])).
    destruct (IH (pre ++ [plus r v]) rest st3 cin XK D So ltac:(lia)) as (st' & R & MA & Cin & Cout & Oth & MT).
    + unfold st3; autorewrite with df; rewrite M2, <- app_assoc; reflexivity.
    + unfold st3, st2, st1; rewrite store_set_store_other by congruence;
        autorewrite with df; reflexivity.
    + rewrite length_app in R; simpl in R; rewrite Nat.add_1_r in R.
      exists st'; split; [exact R|].
      unfold zip_add in *; simpl.
      rewrite MA, <- app_assoc; split; [reflexivity|]. split; [exact Cin|].
      rewrite Cout; unfold st3, st2, st1; autorewrite with df.
      rewrite store_set_store_other by congruence; rewrite <- app_assoc; split; [reflexivity|].
      split.
      * intros c C1 C2; rewrite Oth by assumption; unfold st3, st2, st1.
        rewrite store_set_store_other by congruence; autorewrite with df.
        apply store_set_store_other; congruence.
      * intros b B; rewrite MT by assumption; unfold st3, st2, st1; autorewrite with df.
        rewrite mem_set_mem_other by congruence; reflexivity.
Qed.

(** [foreach k, x in [..], receive(cin) { a[k] = a[k] + x }] *)
Lemma foreach_add : forall t e a k x p pre rest (st : @state V) cin,
  x <> k -> List.length rest = List.length p -> mem st a = pre ++ rest -> store st cin = p ->
  exists st', iter_loop (exec_list t [Assign (elem a k) (Binary (elem a k) Spada.Plus (EVar x))])
    e k (Some (x, cin)) (map Z.of_nat (seq (List.length pre) (List.length p))) st = Some st' /\
  mem st' a = pre ++ zip_add rest p /\ store st' cin = [] /\
  (forall c, c <> cin -> store st' c = store st c).
Proof.
  intros t e a k x p; induction p as [|v p IH]; intros pre rest st cin XK L M Sc.
  - destruct rest; [|discriminate]. exists st; simpl.
    rewrite M; unfold zip_add; simpl; rewrite !app_nil_r; repeat split; auto.
  - destruct rest as [|r rest]; [discriminate|]. simpl in L.
    cbn [Datatypes.length seq map iter_loop fetch]; rewrite Sc; cbv beta iota.
    set (e2 := bind (bind e k (VZ (Z.of_nat (List.length pre)))) x (VD v)).
    assert (Ek : e2 k = Some (VZ (Z.of_nat (List.length pre))))
      by (unfold e2; rewrite bind_other, bind_same by assumption; reflexivity).
    assert (Ex : e2 x = Some (VD v)) by apply bind_same.
    set (st1 := set_store st cin p).
    assert (M1 : mem st1 a = pre ++ r :: rest) by (unfold st1; autorewrite with df; auto).
    rewrite exec_list_cons.
    rewrite (exec_assign_elem _ _ _ _ _ _ _ _ _ (plus r v) Ek M1)
      by (apply eval_data_binary; [exact (eval_elem _ _ _ _ _ _ _ Ek M1) | exact (eval_var _ _ _ _ Ex)]).
    rewrite exec_list_nil.
    set (st2 := set_mem st1 a (pre ++ plus r v :: rest)).
    destruct (IH (pre ++ [plus r v]) rest st2 cin XK ltac:(lia)) as (st' & R & MA & Cin & Oth).
    + unfold st2; autorewrite with df; rewrite <- app_assoc; reflexivity.
    + unfold st2, st1; autorewrite with df; reflexivity.
    + rewrite length_app in R; simpl in R; rewrite Nat.add_1_r in R.
      exists st'; split; [exact R|].
      unfold zip_add in *; simpl. rewrite MA, <- app_assoc.
      split; [reflexivity|]. split; [exact Cin|].
      intros c C; rewrite Oth by assumption; unfold st2, st1; autorewrite with df.
      apply store_set_store_other; congruence.
Qed.

(** [map k in [..] { a[k] = a[k] + b[k] }] *)
Lemma map_add : forall t e a b k bv pre rest (st : @state V), a <> b ->
  List.length rest = List.length bv -> mem st a = pre ++ rest ->
  (exists bp, mem st b = bp ++ bv /\ List.length bp = List.length pre) ->
  exists st', iter_loop (exec_list t [Assign (elem a k) (Binary (elem a k) Spada.Plus (elem b k))])
    e k None (map Z.of_nat (seq (List.length pre) (List.length bv))) st = Some st' /\
  mem st' a = pre ++ zip_add rest bv /\ store st' = store st.
Proof.
  intros t e a b k bv; induction bv as [|v bv IH]; intros pre rest st D L M (bp & B & LB).
  - destruct rest; [|discriminate]. exists st; simpl.
    rewrite M; unfold zip_add; simpl; rewrite !app_nil_r; repeat split; auto.
  - destruct rest as [|r rest]; [discriminate|]. simpl in L.
    cbn [Datatypes.length seq map iter_loop fetch].
    set (e1 := bind e k (VZ (Z.of_nat (List.length pre)))).
    assert (Ek : e1 k = Some (VZ (Z.of_nat (List.length pre)))) by apply bind_same.
    assert (Ekb : e1 k = Some (VZ (Z.of_nat (List.length bp)))) by (rewrite LB; exact Ek).
    rewrite exec_list_cons.
    rewrite (exec_assign_elem _ _ _ _ _ _ _ _ _ (plus r v) Ek M)
      by (apply eval_data_binary; [exact (eval_elem _ _ _ _ _ _ _ Ek M) | exact (eval_elem _ _ _ _ _ _ _ Ekb B)]).
    rewrite exec_list_nil.
    set (st2 := set_mem st a (pre ++ plus r v :: rest)).
    destruct (IH (pre ++ [plus r v]) rest st2 D ltac:(lia)) as (st' & R & MA & Sto).
    + unfold st2; autorewrite with df; rewrite <- app_assoc; reflexivity.
    + exists (bp ++ [v]); unfold st2.
      rewrite mem_set_mem_other by congruence; rewrite B, <- app_assoc.
      split; [reflexivity|]. rewrite !length_app; simpl; lia.
    + rewrite length_app in R; simpl in R; rewrite Nat.add_1_r in R.
      exists st'; split; [exact R|].
      unfold zip_add in *; simpl. rewrite MA, <- app_assoc.
      split; [reflexivity|]. rewrite Sto; reflexivity.
Qed.

(** ** Kernels *)
Lemma run_tasks_app ts us (st : @state V) :
  run_tasks (ts ++ us) st = match run_tasks ts st with Some st' => run_tasks us st' | None => None end.
Proof.
  revert st; induction ts as [|t ts IH]; intros st; simpl; auto.
  destruct (run_task t st); auto.
Qed.
Lemma run_pe_result k p ts (ms : pe -> @memory V) sto st : pe_program k p = Some ts ->
  run_tasks ts (St (ms p) sto) = Some st ->
  run_pe k p ms sto = Some (fun q => if pe_dec p q then mem st else ms q, store st).
Proof. intros P R; unfold run_pe; rewrite P, R; reflexivity. Qed.
End Lemmas.

Arguments set_mem : simpl never.
Arguments set_store : simpl never.
#[export] Hint Rewrite @mem_set_mem_same @store_set_mem @mem_set_store
  @store_set_store_same : df.
