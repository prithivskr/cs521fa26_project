From Stdlib Require Import ZArith List String Bool DecimalString.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaEquivalence.
Import ListNotations Spada SpatialSemantics.
Open Scope string_scope.
Open Scope nat_scope.

Module SpatialElaboration.
Inductive located_kind :=
 | Fields (decls : list field)
 | Streams (decls : list stream_decl)
 | Body (statements : list statement).
Record located := Located {
 scope : option nat; position : pe; constants : environment; kind : located_kind
}.
Definition phase_number (s : option nat) := match s with None => 0 | Some n => n end.
Definition same_scope a b := Nat.eqb (phase_number a) (phase_number b).
Definition visible (current declared : option nat) :=
 match declared with None => true | Some _ => same_scope current declared end.
Definition decimal n := NilZero.string_of_uint (Nat.to_uint n).
Definition scoped (prefix : string) (s : option nat) (id : identifier) :=
 Id ("/" ++ prefix ++ "/" ++ decimal (phase_number s) ++ "/" ++ name id) (version id).
Definition scope_of (r : located) := scope r.

Fixpoint stateful_flatmap {A B} (f : nat -> A -> option (list B * nat)) n xs :=
 match xs with
 | [] => Some ([],n)
 | x :: tail => obind (f n x) (fun first =>
   obind (stateful_flatmap f (snd first) tail) (fun rest =>
   Some ((fst first ++ fst rest)%list, snd rest))) end.
Definition grid_environments ops env ids (g : subgrid) :=
 iterations ops env env ids [xrange g; yrange g].
Definition coordinate ops env (v : typed_id) :=
 obind (env (ident v)) (fun t => obind (scalar_value t) (index_value ops)).
Definition locate_region ops env ids grid current payload :=
 match ids with
 | [x;y] => obind (grid_environments ops env ids grid) (fun envs =>
   traverse (fun env => obind (coordinate ops env x) (fun x =>
     obind (coordinate ops env y) (fun y => Some (Located current (x,y) env payload)))) envs)
 | _ => None end.
(** Fuel bounds nesting depth, not execution time or stream extent. A caller
    can increase it without truncating a successful elaboration. *)
Fixpoint expand_block fuel ops current next env (b : block) : option (list located * nat) :=
 match fuel with
 | O => None
 | S fuel => match b with
   | Place ids g fields => obind (locate_region ops env ids g current (Fields fields))
       (fun rs => Some (rs,next))
   | Dataflow ids g streams => obind (locate_region ops env ids g current (Streams streams))
       (fun rs => Some (rs,next))
   | Compute ids g body => obind (locate_region ops env ids g current (Body body))
       (fun rs => Some (rs,next))
   | Phase body => match current with
     | Some _ => None
     | None => stateful_flatmap (fun n b => expand_block fuel ops (Some next) n env b)
         (S next) body end
   | MetaFor ids ranges body =>
     obind (iterations ops env env ids ranges) (fun envs =>
       stateful_flatmap (fun n env => stateful_flatmap
         (fun n b => expand_block fuel ops current n env b) n body) next envs)
   end
 end.
Definition bind_parameter ops env (p : string * option Z) :=
 match snd p with None => match env (named (fst p)) with Some _ => Some env | None => None end
 | Some z => match env (named (fst p)) with
   | Some _ => Some env
   | None => obind (literal_value ops I32 (Integer z))
       (fun v => Some (bind env (named (fst p)) (singleton v))) end end.
Fixpoint bind_parameters ops env ps := match ps with
 | [] => Some env | p :: ps => obind (bind_parameter ops env p) (fun env => bind_parameters ops env ps) end.
Definition elaborate fuel ops env (k : kernel) :=
 obind (bind_parameters ops env (parameters k)) (fun env =>
   obind (stateful_flatmap (fun n b => expand_block fuel ops None n env b) 1 (blocks k))
     (fun rs => Some (fst rs))).

Definition field_names rs p current := flat_map (fun r =>
 if (pe_eqb p (position r) && visible current (scope r))%bool then
   match kind r with Fields fs => map (fun f => (field_id f,scope r)) fs | _ => [] end
 else []) rs.
Definition stream_names rs p current := flat_map (fun r =>
 if (pe_eqb p (position r) && visible current (scope r))%bool then
   match kind r with Streams ss => map stream_id ss | _ => [] end
 else []) rs.
Definition stream_arguments k := fold_right (fun a ids =>
 let fix is_stream t := match t with Stream _ _ => true | Array t _ => is_stream t | _ => false end in
 if is_stream (argument_type a) then argument_id a :: ids else ids) [] (arguments k).
Definition resolve_name rs k p current id :=
 if existsb (id_eqb id) ((stream_names rs p current ++ stream_arguments k)%list)
 then scoped "stream" current id else
 match find (fun entry => (id_eqb id (fst entry) && same_scope current (snd entry))%bool)
   (field_names rs p current) with
 | Some entry => scoped "field" (snd entry) id
 | None => match find (fun entry => id_eqb id (fst entry)) (field_names rs p current) with
   | Some entry => scoped "field" (snd entry) id | None => id end end.
Definition hide (f : identifier -> identifier) (ids : list identifier) :=
 fun id => if existsb (id_eqb id) ids then id else f id.
Fixpoint rename_expression (f : identifier -> identifier) e := match e with
 | EVar id => EVar (f id) | Constant t v => Constant t v | EParam p v => EParam p v
 | Unary op a => Unary op (rename_expression f a)
 | Binary a op b => Binary (rename_expression f a) op (rename_expression f b)
 | Select a c b => Select (rename_expression f a) (rename_expression f c) (rename_expression f b)
 | FusedMultiplyAdd a b c => FusedMultiplyAdd (rename_expression f a) (rename_expression f b) (rename_expression f c)
 | Slice id ix => Slice (f id) (map (rename_expression f) ix)
 | Range lo hi stride => Range (rename_expression f lo)
   (option_map (rename_expression f) hi) (option_map (rename_expression f) stride) end.
Fixpoint rename_statement f s :=
 let e := rename_expression f in match s with
 | Assign dst src => Assign (e dst) (e src)
 | Send payload stream done => Send (e payload) (e stream) done
 | Receive dst stream done => Receive (e dst) (e stream) done
 | Close stream done => Close (e stream) done
 | Async body done => Async (map (rename_statement f) body) done
 | For ids ranges body => For ids (map e ranges)
     (map (rename_statement (hide f (map ident ids))) body)
 | Map ids ranges body done => Map ids (map e ranges)
     (map (rename_statement (hide f (map ident ids))) body) done
 | Foreach ids ranges element stream body done => Foreach ids (map e ranges) element (e stream)
     (map (rename_statement (hide f (ident element :: map ident ids))) body) done
 | Await id => Await id | AwaitAll => AwaitAll end.
Definition argument_streams ops env k := flat_map (fun a =>
 let fix is_stream t := match t with Stream _ _ => true | Array t _ => is_stream t | _ => false end in
 match argument_type a with
 | Stream _ _ => [EVar (argument_id a)]
 | Array base dims => if is_stream base then
   match traverse (fun e => obind (evaluate ops env e) (fun t =>
     obind (scalar_value t) (index_value ops))) dims with
   | Some ds => map (fun ix => Slice (argument_id a) (map int ix))
       (cartesian (map (fun d => map Z.of_nat (seq 0 (Z.to_nat d))) ds))
   | None => [] end else []
 | _ => [] end) (arguments k).
Definition region_code ops rs k (r : located) := match kind r with
 | Body body =>
   let f := resolve_name rs k (position r) (scope r) in
   let streams := (map EVar (stream_names rs (position r) (scope r)) ++
      argument_streams ops (constants r) k)%list in
   (Restore (constants r) :: instructions (map (rename_statement f) body) ++
     [WaitChildren] ++ map (fun e => ReleaseIfOpen (rename_expression f e)) streams ++ [ResetHandles])%list
 | _ => [] end.
Definition pe_eq_dec (a b : pe) : {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition locations rs := nodup pe_eq_dec (map position rs).
Definition pe_code ops rs k p := flat_map (fun r => if pe_eqb p (position r) then region_code ops rs k r else []) rs.
Definition initial_tasks ops rs k := map (fun ip =>
 Task (fst ip) None (snd ip) no_environment no_handles (pe_code ops rs k (snd ip)))
 (combine (seq 0 (List.length (locations rs))) (locations rs)).
Definition initial_state ops rs k m initial_queues :=
 State (initial_tasks ops rs k) m (List.length (locations rs)) initial_queues
   (fun e => List.length (initial_queues e)) (fun _ => false) (fun _ _ => false).

(** Each canonical edge carries its semantic endpoints and the source stream.
    Edges with a missing endpoint cross the host boundary. A deployment provides
    a wiring witness; physical colors/switch configurations are backend data. *)
Record wire := Wire {
 wire_id : nat; sender : option pe; receiver : option pe;
 wire_stream : identifier; wire_indices : list Z; wire_scope : option nat;
 bound : option nat; capacity : nat
}.
Definition ref_matches w ref :=
 (id_eqb (scoped "stream" (wire_scope w) (wire_stream w)) (fst ref) &&
  if list_eq_dec Z.eq_dec (wire_indices w) (snd ref) then true else false)%bool.
Definition to_network ws := Network
 (fun p ref => map wire_id (filter (fun w =>
    match sender w with Some q => (pe_eqb p q && ref_matches w ref)%bool | None => false end) ws))
 (fun p ref => option_map wire_id (find (fun w =>
    match receiver w with Some q => (pe_eqb p q && ref_matches w ref)%bool | None => false end) ws))
 (fun e => match find (fun w => Nat.eqb e (wire_id w)) ws with Some w => bound w | None => None end)
 (fun e => match find (fun w => Nat.eqb e (wire_id w)) ws with Some w => capacity w | None => 0 end)
 (fun e => existsb (fun w => (Nat.eqb e (wire_id w) && match sender w with None => true | _ => false end)%bool) ws)
 (fun e => existsb (fun w => (Nat.eqb e (wire_id w) && match receiver w with None => true | _ => false end)%bool) ws).
Definition declared_stream rs p current id :=
 exists r ss s, In r rs /\ position r = p /\ visible current (scope r) = true /\
 kind r = Streams ss /\ In s ss /\ stream_id s = id.
Definition expected_offset ops env e :=
 obind (evaluate ops env e) (fun t =>
   traverse (index_value ops) (elements t)).
Definition source_destinations ops env p source := match source with
 | Relative dx dy _ | Multicast dx dy _ =>
   obind (expected_offset ops env dx) (fun xs =>
   obind (expected_offset ops env dy) (fun ys =>
   Some (flat_map (fun x => map (fun y => ((fst p+x)%Z,(snd p+y)%Z)) ys) xs)))
 | _ => None end.
(** A wire must agree with source-level geometry. This rules out proving a
    communication kernel under an arbitrary, unrelated network. Completeness
    additionally requires exactly the edges used by matched send/receives. *)
Definition declared_external rs p current id (input : bool) : Prop :=
 exists r ss s route, In r rs /\ position r = p /\ visible current (scope r) = true /\
 kind r = Streams ss /\ In s ss /\ stream_id s = id /\
 source s = (if input then ExternalInput route else ExternalOutput route).
Definition argument_external k id (input : bool) : Prop :=
 exists a, In a (arguments k) /\ argument_id a = id /\
 (let fix is_stream ty := match ty with Stream _ _ => true | Array t _ => is_stream t | _ => false end
  in is_stream (argument_type a)) = true /\
 (if input then writeonly a else readonly a) = false.
Definition wire_agrees ops rs k w := match sender w,receiver w with
 | Some p,Some q => exists r ss s targets,
   In r rs /\ position r = p /\ visible (wire_scope w) (scope r) = true /\
   kind r = Streams ss /\ In s ss /\ stream_id s = wire_stream w /\
   source_destinations ops (constants r) p (source s) = Some targets /\ In q targets
 | None,Some p => declared_external rs p (wire_scope w) (wire_stream w) true \/
                    argument_external k (wire_stream w) true
 | Some p,None => declared_external rs p (wire_scope w) (wire_stream w) false \/
                    argument_external k (wire_stream w) false
 | None,None => False end.
End SpatialElaboration.

Module KernelEquivalence.



Import SpatialElaboration.
(** Initial memories are supplied explicitly. In particular, proofs quantify
    over scratch contents rather than silently assuming they start at zero.
    The observer can select exported fields and ignore private scratch. *)
Definition kernel_equivalent {O} fuel ops
 (observe : memory -> O) (k1 k2 : kernel) :=
 forall env regions1 regions2,
 elaborate fuel ops env k1 = Some regions1 ->
 elaborate fuel ops env k2 = Some regions2 ->
 locations regions1 = locations regions2 /\
 forall (m : memory) (queues : nat -> list atom) (net : network),
 total_equivalent ops net (fun s => observe (contents s))
   (initial_state ops regions1 k1 m queues) (initial_state ops regions2 k2 m queues).
Definition with_name name k := Kernel name (parameters k) (arguments k) (blocks k).
Lemma kernel_name_irrelevant : forall O fuel ops (observe : memory -> O) k name,
 kernel_equivalent fuel ops observe k (with_name name k).
Proof.
 intros O fuel ops observe k name env r1 r2 A B.
 assert (r1 = r2) as E.
 { change (elaborate fuel ops env k = Some r2) in B.
   rewrite A in B; inversion B; reflexivity. }
 subst r2; split; [reflexivity |].
 intros m qs net; unfold total_equivalent; split.
 - assert (initial_state ops r1 k m qs = initial_state ops r1 (with_name name k) m qs) as E.
   { unfold initial_state, initial_tasks, pe_code, region_code, resolve_name, stream_arguments, argument_streams, with_name; reflexivity. }
   rewrite E; apply equivalent_refl.
 - assert (initial_state ops r1 k m qs = initial_state ops r1 (with_name name k) m qs) as E.
   { unfold initial_state, initial_tasks, pe_code, region_code, resolve_name, stream_arguments, argument_streams, with_name; reflexivity. }
   rewrite E; reflexivity.
Qed.
End KernelEquivalence.
