From Stdlib Require Import ZArith List String Bool Arith Lia.
From SpatialCSL Require Import SpadaIR.
Import ListNotations Spada.
Open Scope Z_scope.
Open Scope list_scope.

Module SpatialSemantics.
Record atom := Atom { atom_type : scalar; atom_bits : Z }.
Record tensor := Tensor { shape : list nat; elements : list atom }.
Definition singleton (v : atom) := Tensor [] [v].
Definition scalar_value (v : tensor) : option atom :=
  match shape v, elements v with [], [a] => Some a | _, _ => None end.
Definition environment := identifier -> option tensor.
Definition id_eqb (a b : identifier) :=
  (String.eqb (name a) (name b) && Nat.eqb (version a) (version b))%bool.
Definition bind (env : environment) (id : identifier) (v : tensor) : environment :=
  fun x => if id_eqb x id then Some v else env x.
Definition pe := (Z * Z)%type.
Definition pe_eqb (a b : pe) := (Z.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b))%bool.
Definition memory := pe -> environment.
Definition put (m : memory) (p : pe) (id : identifier) (v : tensor) : memory :=
  fun q => if pe_eqb q p then bind (m q) id v else m q.

(** Numeric operations are an explicit parameter of the semantics, rather than
    silently treating f32 as reals or making fmac equal to two roundings.
    Atoms store bits, so a model can preserve signed zero and NaN payloads. *)
Record arithmetic := Arithmetic {
  literal_value : scalar -> literal -> option atom;
  unary_value : unary -> atom -> option atom;
  binary_value : binary -> atom -> atom -> option atom;
  fma_value : atom -> atom -> atom -> option atom;
  cast_value : scalar -> atom -> option atom;
  truth_value : atom -> bool;
  index_value : atom -> option Z
}.
Definition obind {A B} (v : option A) (f : A -> option B) :=
  match v with Some x => f x | None => None end.
Notation "x <- a ;; b" := (obind a (fun x => b)) (at level 100, a at next level, right associativity).
Fixpoint traverse {A B} (f : A -> option B) (xs : list A) : option (list B) :=
 match xs with [] => Some [] | x :: xs => y <- f x ;; ys <- traverse f xs ;; Some (y :: ys) end.
Definition dims_eqb (a b : list nat) := if list_eq_dec Nat.eq_dec a b then true else false.
Definition broadcast (a b : tensor) : option (list nat * list (atom * atom)) :=
 if dims_eqb (shape a) (shape b) then
   if Nat.eqb (List.length (elements a)) (List.length (elements b))
   then Some (shape a, combine (elements a) (elements b)) else None
 else match scalar_value a, scalar_value b with
 | Some x, _ => Some (shape b, map (fun y => (x,y)) (elements b))
 | _, Some y => Some (shape a, map (fun x => (x,y)) (elements a))
 | _, _ => None end.
Definition lift1 (f : atom -> option atom) (a : tensor) :=
 xs <- traverse f (elements a) ;; Some (Tensor (shape a) xs).
Definition lift2 (f : atom -> atom -> option atom) (a b : tensor) :=
 pair <- broadcast a b ;;
 xs <- traverse (fun xy => f (fst xy) (snd xy)) (snd pair) ;;
 Some (Tensor (fst pair) xs).
Definition lift3 (f : atom -> atom -> atom -> option atom) (a b c : tensor) :=
 ab <- broadcast a b ;;
 let dummy := Tensor (fst ab) (map fst (snd ab)) in
 ac <- broadcast dummy c ;;
 (* Broadcasting the first pair along a scalar third operand preserves length. *)
 if Nat.eqb (List.length (snd ab)) (List.length (snd ac)) then
   xs <- traverse (fun xy => f (fst (fst xy)) (snd (fst xy)) (snd (snd xy)))
     (combine (snd ab) (snd ac)) ;; Some (Tensor (fst ac) xs)
 else match scalar_value a, scalar_value b with
 | Some x, Some y => lift1 (fun z => f x y z) c
 | _, _ => None end.

Definition range_values (lo hi stride : Z) : option (list Z) :=
 if Z.eqb stride 0 then None else
 let distance := if Z.ltb 0 stride then hi-lo else lo-hi in
 let count := Z.to_nat (Z.max 0 ((distance + Z.abs stride - 1) / Z.abs stride)) in
 Some (map (fun n => lo + Z.of_nat n * stride) (seq 0 count)).
Fixpoint cartesian (xs : list (list Z)) : list (list Z) :=
 match xs with [] => [[]] | x :: rest =>
 flat_map (fun i => map (cons i) (cartesian rest)) x end.
Fixpoint offset (dims : list nat) (ix : list Z) : option nat :=
 match dims, ix with
 | [], [] => Some 0%nat
 | d :: ds, i :: is =>
   if (Z.leb 0 i && Z.ltb i (Z.of_nat d))%bool then
     rest <- offset ds is ;;
     Some ((Z.to_nat i * fold_right Nat.mul 1 ds + rest)%nat)
   else None
 | _, _ => None end.
Definition sliced (a : tensor) (indices : list tensor) (ops : arithmetic) :=
 choices <- traverse (fun t => traverse (index_value ops) (elements t)) indices ;;
 offsets <- traverse (offset (shape a)) (cartesian choices) ;;
 values <- traverse (fun i => nth_error (elements a) i) offsets ;;
 Some (Tensor (flat_map shape indices) values).

Fixpoint evaluate (ops : arithmetic) (env : environment) (e : expression) : option tensor :=
 match e with
 | EVar id => env id
 | Constant ty v => a <- literal_value ops ty v ;; Some (singleton a)
 | EParam p v => match env (named p) with
   | Some value => Some value
   | None => match v with
     | Some z => a <- literal_value ops I32 (Integer z) ;; Some (singleton a)
     | None => None end end
 | Unary op a => v <- evaluate ops env a ;; lift1 (unary_value ops op) v
 | Binary a op b => x <- evaluate ops env a ;; y <- evaluate ops env b ;;
   lift2 (binary_value ops op) x y
 | Select yes cond no => c <- evaluate ops env cond ;; a <- scalar_value c ;;
   evaluate ops env (if truth_value ops a then yes else no)
 | FusedMultiplyAdd a b c => x <- evaluate ops env a ;; y <- evaluate ops env b ;;
   z <- evaluate ops env c ;; lift3 (fma_value ops) x y z
 | Slice id indices => a <- env id ;; ix <- traverse (evaluate ops env) indices ;;
   sliced a ix ops
 | Range lo hi stride =>
   l <- evaluate ops env lo ;; la <- scalar_value l ;; start <- index_value ops la ;;
   match hi with
   | None => Some (singleton la)
   | Some hi => h <- evaluate ops env hi ;; ha <- scalar_value h ;; stop <- index_value ops ha ;;
     step <- match stride with None => Some 1 | Some s =>
       t <- evaluate ops env s ;; sa <- scalar_value t ;; index_value ops sa end ;;
     zs <- range_values start stop step ;;
     vs <- traverse (fun z => literal_value ops I32 (Integer z)) zs ;;
     Some (Tensor [List.length vs] vs)
   end
 end.
Definition local_environment (m : memory) (p : pe) (locals : environment) : environment :=
 fun id => match locals id with Some v => Some v | None => m p id end.
Definition eval_at ops m p locals := evaluate ops (local_environment m p locals).
Definition selections ops env dst : option (identifier * list nat) :=
 match dst with
 | EVar id => a <- env id ;; Some (id, seq 0 (List.length (elements a)))
 | Slice id indices => a <- env id ;; ix <- traverse (evaluate ops env) indices ;;
   zs <- traverse (fun t => traverse (index_value ops) (elements t)) ix ;;
   positions <- traverse (offset (shape a)) (cartesian zs) ;; Some (id, positions)
 | _ => None end.
Fixpoint update_nth {A} (n : nat) (v : A) (xs : list A) :=
 match n, xs with
 | O, _ :: tail => v :: tail | S n, h :: tail => h :: update_nth n v tail
 | _, [] => [] end.
Definition write_selected (old : tensor) (positions : list nat) (values : list atom) :=
 Tensor (shape old) (fold_left (fun xs iv => update_nth (fst iv) (snd iv) xs)
   (combine positions values) (elements old)).
Definition converted ops targets values :=
 if Nat.eqb (List.length targets) (List.length values) then
 traverse (fun pair => cast_value ops (atom_type (fst pair)) (snd pair)) (combine targets values)
 else None.
Definition assign ops m p locals dst value : option memory :=
 match dst with
 | EVar id => match m p id with
   | Some old =>
     let values := match scalar_value value with
       | Some v => repeat v (List.length (elements old)) | None => elements value end in
     if (dims_eqb (shape old) (shape value) ||
       match scalar_value value with Some _ => true | None => false end)%bool then
       vs <- converted ops (elements old) values ;;
       Some (put m p id (Tensor (shape old) vs)) else None
   | None => Some (put m p id value) end
 | _ => selection <- selections ops (local_environment m p locals) dst ;;
   old <- m p (fst selection) ;;
   let values := match scalar_value value with
     | Some v => repeat v (List.length (snd selection)) | None => elements value end in
   targets <- traverse (fun i => nth_error (elements old) i) (snd selection) ;;
   vs <- converted ops targets values ;;
   Some (put m p (fst selection) (write_selected old (snd selection) vs)) end.
Definition iterations ops env (base : environment) (ids : list typed_id) (ranges : list expression) :=
 tensors <- traverse (evaluate ops env) ranges ;;
 let choices := map elements tensors in
 let fix product (xs : list (list atom)) := match xs with
   | [] => [[]] | x :: tail => flat_map (fun v => map (cons v) (product tail)) x end in
 if Nat.eqb (List.length ids) (List.length ranges) then
 Some (map (fun vs => fold_left (fun e iv => bind e (ident (fst iv)) (singleton (snd iv)))
   (combine ids vs) base) (product choices)) else None.

(** Streams are resolved from declarations to directed FIFO edges. An edge may
    have a host endpoint; multicast has several outgoing edges. Physical route
    correctness is a separate obligation, not an assumption of global barriers. *)
Definition stream_ref := (identifier * list Z)%type.
Fixpoint resolve_stream ops env e : option stream_ref := match e with
 | EVar id => Some (id, [])
 | Slice id ix => tensors <- traverse (evaluate ops env) ix ;;
   atoms <- traverse scalar_value tensors ;; zs <- traverse (index_value ops) atoms ;;
   Some (id,zs)
 | Select a cond b => c <- evaluate ops env cond ;; v <- scalar_value c ;;
   if truth_value ops v then resolve_stream ops env a else resolve_stream ops env b
 | _ => None end.
Record network := Network {
 outgoing : pe -> stream_ref -> list nat;
 incoming : pe -> stream_ref -> option nat;
 edge_bound : nat -> option nat;
 edge_capacity : nat -> nat;
 host_input : nat -> bool;
 host_output : nat -> bool
}.
Inductive instruction :=
 | Execute (s : statement)
 | Spawn (body : list instruction) (done : completion)
 | StartSend (payload stream : expression)
 | StartReceive (destination stream : expression)
 | Release (stream : expression)
 | ReleaseIfOpen (stream : expression)
 | ResetHandles
 | StartEach (ids : list typed_id) (ranges : list expression)
     (element : typed_id) (stream : expression) (body : list statement)
 | Restore (locals : environment)
 | Wait (task : nat)
 | WaitChildren
 | Transmit (stream : stream_ref) (values : list atom)
 | Collect (dst : expression) (stream : stream_ref) (count : nat) (values : list atom)
 | Each (stream : stream_ref) (element : typed_id) (body : list statement)
     (remaining : option (list environment)).
Record task := Task {
 task_id : nat; parent_id : option nat; location : pe;
 locals : environment; handles : identifier -> option nat;
 code : list instruction
}.
Definition with_code t c := Task (task_id t) (parent_id t) (location t) (locals t) (handles t) c.
Definition with_locals t env c := Task (task_id t) (parent_id t) (location t) env (handles t) c.
Definition instructions body := map Execute body.
Definition no_environment : environment := fun _ => None.
Definition no_handles : identifier -> option nat := fun _ => None.
Record state := State {
 tasks : list task; contents : memory; next_id : nat;
 queues : nat -> list atom; counts : nat -> nat;
 closed : nat -> bool;
 endpoint_closed : pe -> stream_ref -> bool
}.
Definition alive s id := exists t, In t (tasks s) /\ task_id t = id.
Definition has_child s id := exists t, In t (tasks s) /\ parent_id t = Some id.
Definition replace_task (s : state) (before : list task) (t : task) (after : list task) :=
 State (before ++ t :: after) (contents s) (next_id s) (queues s) (counts s) (closed s) (endpoint_closed s).
Definition set_queue (qs : nat -> list atom) edge values :=
 fun e => if Nat.eqb e edge then values else qs e.
Definition set_closed (cl : nat -> bool) edge := fun e => if Nat.eqb e edge then true else cl e.
Definition count_sent (net : network) (s : state) (edge : nat) :=
 match edge_bound net edge with Some n => Nat.leb n (counts s edge) | None => false end.
Definition eof net s edge := (closed s edge || count_sent net s edge)%bool.
Definition receive_ready net s edge := queues s edge <> [] \/ eof net s edge = true.
Inductive observation := Input (edge : nat) (v : atom) | Output (edge : nat) (v : atom) | EndInput (edge : nat).
Definition label := option observation.

(** Small-step scheduling. Every task, including a bulk transfer, may be
    preempted between rules; no fairness or cross-PE barrier is introduced. *)
Inductive step (ops : arithmetic) (net : network) : state -> label -> state -> Prop :=
 | StepRestore : forall s pre t post env rest,
   tasks s = pre ++ t :: post -> code t = Restore env :: rest ->
   step ops net s None (replace_task s pre (with_locals t env rest) post)
 | StepAssign : forall s pre t post rest dst src v m,
   tasks s = pre ++ t :: post -> code t = Execute (Assign dst src) :: rest ->
   eval_at ops (contents s) (location t) (locals t) src = Some v ->
   assign ops (contents s) (location t) (locals t) dst v = Some m ->
   step ops net s None (State (pre ++ with_code t rest :: post) m (next_id s)
     (queues s) (counts s) (closed s) (endpoint_closed s))
 | StepFor : forall s pre t post rest ids ranges body envs,
   tasks s = pre ++ t :: post -> code t = Execute (For ids ranges body) :: rest ->
   iterations ops (local_environment (contents s) (location t) (locals t)) (locals t) ids ranges = Some envs ->
   step ops net s None (replace_task s pre
     (with_code t (flat_map (fun env => Restore env :: instructions body ++
       [WaitChildren; Restore (locals t)]) envs ++ rest)) post)
 | StepSpawn : forall s pre t post rest body done,
   tasks s = pre ++ t :: post -> code t = Spawn body done :: rest ->
   let child := Task (next_id s) (Some (task_id t)) (location t) (locals t) (handles t) body in
   let hs := match done with None => handles t | Some id =>
     fun x => if id_eqb x id then Some (next_id s) else handles t x end in
   let continuation := match done with None => Wait (next_id s) :: rest | Some _ => rest end in
   step ops net s None (State
     (pre ++ Task (task_id t) (parent_id t) (location t) (locals t) hs continuation :: child :: post)
     (contents s) (S (next_id s)) (queues s) (counts s) (closed s) (endpoint_closed s))
 | StepAwait : forall s pre t post rest id child,
   tasks s = pre ++ t :: post -> code t = Execute (Await id) :: rest -> handles t id = Some child ->
   step ops net s None (replace_task s pre (with_code t (Wait child :: rest)) post)
 | StepAwaitAll : forall s pre t post rest,
   tasks s = pre ++ t :: post -> code t = Execute AwaitAll :: rest ->
   step ops net s None (replace_task s pre (with_code t (WaitChildren :: rest)) post)
 | StepWait : forall s pre t post rest child,
   tasks s = pre ++ t :: post -> code t = Wait child :: rest -> ~ alive s child ->
   step ops net s None (replace_task s pre (with_code t rest) post)
 | StepWaitChildren : forall s pre t post rest,
   tasks s = pre ++ t :: post -> code t = WaitChildren :: rest -> ~ has_child s (task_id t) ->
   step ops net s None (replace_task s pre (with_code t rest) post)
 | StepFinish : forall s pre t post,
   tasks s = pre ++ t :: post -> code t = [] -> ~ has_child s (task_id t) ->
   step ops net s None (State (pre ++ post) (contents s) (next_id s)
     (queues s) (counts s) (closed s) (endpoint_closed s))
 | StepResetHandles : forall s pre t post rest,
   tasks s = pre ++ t :: post -> code t = ResetHandles :: rest ->
   step ops net s None (replace_task s pre
     (Task (task_id t) (parent_id t) (location t) (locals t) no_handles rest) post)
 | StepReleaseIfClosed : forall s pre t post rest stream ref,
   tasks s = pre ++ t :: post -> code t = ReleaseIfOpen stream :: rest ->
   resolve_stream ops (local_environment (contents s) (location t) (locals t)) stream = Some ref ->
   endpoint_closed s (location t) ref = true ->
   step ops net s None (replace_task s pre (with_code t rest) post)
 | StepReleaseIfOpen : forall s pre t post rest stream ref,
   tasks s = pre ++ t :: post -> code t = ReleaseIfOpen stream :: rest ->
   resolve_stream ops (local_environment (contents s) (location t) (locals t)) stream = Some ref ->
   endpoint_closed s (location t) ref = false ->
   step ops net s None (replace_task s pre (with_code t (Release stream :: rest)) post)
 | StepAsync : forall s pre t post rest body done,
   tasks s = pre ++ t :: post -> code t = Execute (Async body done) :: rest ->
   step ops net s None (replace_task s pre (with_code t (Spawn (instructions body) done :: rest)) post)
 | StepMap : forall s pre t post rest ids ranges body done envs,
   tasks s = pre ++ t :: post -> code t = Execute (Map ids ranges body done) :: rest ->
   iterations ops (local_environment (contents s) (location t) (locals t)) (locals t) ids ranges = Some envs ->
   step ops net s None (replace_task s pre (with_code t
     (Spawn (map (fun env => Spawn (Restore env :: instructions body)
       (Some (named "$iteration"))) envs ++ [WaitChildren]) done :: rest)) post)
 | StepSend : forall s pre t post rest payload stream done,
   tasks s = pre ++ t :: post -> code t = Execute (Send payload stream done) :: rest ->
   step ops net s None (replace_task s pre (with_code t (Spawn [StartSend payload stream] done :: rest)) post)
 | StepReceive : forall s pre t post rest dst stream done,
   tasks s = pre ++ t :: post -> code t = Execute (Receive dst stream done) :: rest ->
   step ops net s None (replace_task s pre (with_code t (Spawn [StartReceive dst stream] done :: rest)) post)
 | StepClose : forall s pre t post rest stream done,
   tasks s = pre ++ t :: post -> code t = Execute (Close stream done) :: rest ->
   step ops net s None (replace_task s pre (with_code t (Spawn [Release stream] done :: rest)) post)
 | StepForeach : forall s pre t post rest ids ranges element stream body done,
   tasks s = pre ++ t :: post -> code t = Execute (Foreach ids ranges element stream body done) :: rest ->
   step ops net s None (replace_task s pre (with_code t
     (Spawn [StartEach ids ranges element stream body] done :: rest)) post)
 | StepStartSend : forall s pre t post rest payload stream v ref,
   tasks s = pre ++ t :: post -> code t = StartSend payload stream :: rest ->
   eval_at ops (contents s) (location t) (locals t) payload = Some v ->
   resolve_stream ops (local_environment (contents s) (location t) (locals t)) stream = Some ref ->
   endpoint_closed s (location t) ref = false ->
   outgoing net (location t) ref <> [] ->
   step ops net s None (replace_task s pre (with_code t (Transmit ref (elements v) :: rest)) post)
 | StepTransmit : forall s pre t post rest ref v vs edges,
   tasks s = pre ++ t :: post -> code t = Transmit ref (v :: vs) :: rest ->
   outgoing net (location t) ref = edges -> edges <> [] ->
   endpoint_closed s (location t) ref = false ->
   (forall e, In e edges -> eof net s e = false /\
     (List.length (queues s e) < edge_capacity net e)%nat) ->
   step ops net s None (State (pre ++ with_code t (Transmit ref vs :: rest) :: post)
     (contents s) (next_id s)
     (fun e => if in_dec Nat.eq_dec e edges then queues s e ++ [v] else queues s e)
     (fun e => if in_dec Nat.eq_dec e edges then S (counts s e) else counts s e)
     (closed s) (endpoint_closed s))
 | StepTransmitDone : forall s pre t post rest ref,
   tasks s = pre ++ t :: post -> code t = Transmit ref [] :: rest ->
   step ops net s None (replace_task s pre (with_code t rest) post)
 | StepStartReceive : forall s pre t post rest dst stream v ref,
   tasks s = pre ++ t :: post -> code t = StartReceive dst stream :: rest ->
   eval_at ops (contents s) (location t) (locals t) dst = Some v ->
   resolve_stream ops (local_environment (contents s) (location t) (locals t)) stream = Some ref ->
   endpoint_closed s (location t) ref = false ->
   step ops net s None (replace_task s pre (with_code t
     (Collect dst ref (List.length (elements v)) [] :: rest)) post)
 | StepCollect : forall s pre t post rest dst ref n values edge v vs,
   tasks s = pre ++ t :: post -> code t = Collect dst ref (S n) values :: rest ->
   incoming net (location t) ref = Some edge -> queues s edge = v :: vs ->
   endpoint_closed s (location t) ref = false ->
   step ops net s None (State
     (pre ++ with_code t (Collect dst ref n (values ++ [v]) :: rest) :: post)
     (contents s) (next_id s) (set_queue (queues s) edge vs) (counts s) (closed s) (endpoint_closed s))
 | StepCollectDone : forall s pre t post rest dst ref values old m,
   tasks s = pre ++ t :: post -> code t = Collect dst ref O values :: rest ->
   eval_at ops (contents s) (location t) (locals t) dst = Some old ->
   assign ops (contents s) (location t) (locals t) dst (Tensor (shape old) values) = Some m ->
   step ops net s None (State (pre ++ with_code t rest :: post) m (next_id s)
     (queues s) (counts s) (closed s) (endpoint_closed s))
 | StepRelease : forall s pre t post rest stream ref,
   tasks s = pre ++ t :: post -> code t = Release stream :: rest ->
   resolve_stream ops (local_environment (contents s) (location t) (locals t)) stream = Some ref ->
   endpoint_closed s (location t) ref = false ->
   step ops net s None (State (pre ++ with_code t rest :: post) (contents s) (next_id s)
     (queues s) (counts s)
     (fun e => if in_dec Nat.eq_dec e (outgoing net (location t) ref) then true else closed s e)
     (fun p r => if pe_eqb p (location t) then
       if (id_eqb (fst r) (fst ref) &&
         (if list_eq_dec Z.eq_dec (snd r) (snd ref) then true else false))%bool
       then true else endpoint_closed s p r else endpoint_closed s p r))
 | StepStartEach : forall s pre t post rest ids ranges element stream body ref envs,
   tasks s = pre ++ t :: post -> code t = StartEach ids ranges element stream body :: rest ->
   resolve_stream ops (local_environment (contents s) (location t) (locals t)) stream = Some ref ->
   (match ranges with [] => Some [] | _ =>
      iterations ops (local_environment (contents s) (location t) (locals t)) (locals t) ids ranges end) = Some envs ->
   step ops net s None (replace_task s pre (with_code t
     (Each ref element body (match ranges with [] => None | _ => Some envs end) :: rest)) post)
 | StepEach : forall s pre t post rest ref element body remaining edge v vs env tail,
   tasks s = pre ++ t :: post -> code t = Each ref element body remaining :: rest ->
   incoming net (location t) ref = Some edge -> queues s edge = v :: vs ->
   endpoint_closed s (location t) ref = false ->
   (match remaining with None => Some (locals t, None)
      | Some [] => None | Some (e :: es) => Some (e, Some es) end) = Some (env,tail) ->
   step ops net s None (State (pre ++ with_locals t (bind env (ident element) (singleton v))
     (instructions body ++ [WaitChildren; Restore (locals t); Each ref element body tail] ++ rest) :: post)
     (contents s) (next_id s) (set_queue (queues s) edge vs) (counts s) (closed s) (endpoint_closed s))
 | StepEachDone : forall s pre t post rest ref element body,
   tasks s = pre ++ t :: post -> code t = Each ref element body (Some []) :: rest ->
   step ops net s None (replace_task s pre (with_code t rest) post)
 | StepEachEnd : forall s pre t post rest ref element body edge,
   tasks s = pre ++ t :: post -> code t = Each ref element body None :: rest ->
   incoming net (location t) ref = Some edge -> queues s edge = [] -> eof net s edge = true ->
   step ops net s None (replace_task s pre (with_code t rest) post)
 | StepHostInput : forall s edge v,
   host_input net edge = true -> eof net s edge = false ->
   (List.length (queues s edge) < edge_capacity net edge)%nat ->
   step ops net s (Some (Input edge v)) (State (tasks s) (contents s) (next_id s)
     (set_queue (queues s) edge (queues s edge ++ [v]))
     (fun e => if Nat.eqb e edge then S (counts s e) else counts s e)
     (closed s) (endpoint_closed s))
 | StepHostOutput : forall s edge v vs,
   host_output net edge = true -> queues s edge = v :: vs ->
   step ops net s (Some (Output edge v)) (State (tasks s) (contents s) (next_id s)
     (set_queue (queues s) edge vs) (counts s) (closed s) (endpoint_closed s))
 | StepHostEnd : forall s edge,
   host_input net edge = true -> eof net s edge = false ->
   step ops net s (Some (EndInput edge)) (State (tasks s) (contents s) (next_id s)
     (queues s) (counts s) (set_closed (closed s) edge) (endpoint_closed s)).
End SpatialSemantics.
