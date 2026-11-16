From Stdlib Require Import ZArith List Bool.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaElaboration SpadaRouting SpadaKernelProofs.
Import ListNotations Spada SpatialSemantics SpatialElaboration Routing.
Open Scope Z_scope.
Open Scope list_scope.

Module Deployment.
Record use := Use { at_pe : pe; phase : option nat; context : environment;
 reference : stream_ref; sending : bool }.
Definition resolved_use ops p ph env e send :=
 option_map (fun ref => Use p ph env ref send) (resolve_stream ops env e).
Fixpoint collect fuel ops p ph env body : option (list use) :=
 match fuel with O => None | S fuel =>
 let one s := match s with
 | Send _ e _ => option_map (fun u => [u]) (resolved_use ops p ph env e true)
 | Receive _ e _ => option_map (fun u => [u]) (resolved_use ops p ph env e false)
 | Async body _ => collect fuel ops p ph env body
 | For ids ranges body | Map ids ranges body _ =>
   obind (iterations ops env env ids ranges) (fun envs =>
    option_map (@concat use) (traverse (fun env => collect fuel ops p ph env body) envs))
 | Foreach ids ranges _ stream body _ =>
   obind (resolved_use ops p ph env stream false) (fun u =>
   obind (match ranges with [] => Some [env] | _ => iterations ops env env ids ranges end) (fun envs =>
   obind (traverse (fun env => collect fuel ops p ph env body) envs) (fun us => Some (u :: concat us))))
 | _ => Some [] end in
 option_map (@concat use) (traverse one body) end.
Definition collect_regions fuel ops rs := option_map (@concat use)
 (traverse (fun r => match kind r with
 | Body body => collect fuel ops (position r) (scope r) (constants r) body
 | _ => Some [] end) rs).
Definition ref_eqb a b := (id_eqb (fst a) (fst b) &&
 if list_eq_dec Z.eq_dec (snd a) (snd b) then true else false)%bool.
Definition use_eqb a b := (pe_eqb (at_pe a) (at_pe b) && same_scope (phase a) (phase b) &&
 ref_eqb (reference a) (reference b) && Bool.eqb (sending a) (sending b))%bool.
Fixpoint distinct_uses us := match us with
 | [] => [] | u :: tail => let rest := distinct_uses tail in
 if existsb (use_eqb u) rest then rest else u :: rest end.
Definition declaration rs u :=
 let choose (local : bool) := fold_right (fun r rest =>
   if (pe_eqb (at_pe u) (position r) &&
       if local then same_scope (phase u) (scope r) else
         match scope r with None => true | _ => false end)%bool then
     match kind r with Streams ss => match find (fun s => id_eqb (fst (reference u)) (stream_id s)) ss with
       Some s => Some (r,s) | None => rest end | _ => rest end
   else rest) None rs in
 match choose true with Some d => Some d | None => choose false end.
Fixpoint stream_bound t := match t with
 | Stream _ b => Some b | Array base _ => stream_bound base | _ => None end.
Definition bound_value ops env ty := obind (stream_bound ty) (fun b =>
 match b with None => Some None | Some e => option_map (@Some nat) (eval_nat ops env e) end).
Definition route_of s := match s with
 | Relative _ _ r | Multicast _ _ r | ExternalInput r | ExternalOutput r => r end.
Definition external_flow ops cap u ty source :=
 let allowed := match source with ExternalInput _ => negb (sending u)
   | ExternalOutput _ => sending u | _ => false end in
 if allowed then obind (bound_value ops (context u) ty) (fun b =>
 obind (channel_value ops (context u) (route_channel (route_of source))) (fun channel =>
 Some [Flow (Wire 0 (if sending u then Some (at_pe u) else None)
   (if sending u then None else Some (at_pe u)) (fst (reference u)) (snd (reference u))
   (phase u) b cap) [at_pe u] channel])) else None.
Definition matching_receive uses u q := existsb (fun v =>
 (negb (sending v) && pe_eqb (at_pe v) q && same_scope (phase u) (phase v) &&
   ref_eqb (reference u) (reference v))%bool) uses.
Definition flows_for ops cap rs k uses u :=
 match declaration rs u with
 | Some (r,s) => match source s with
   | ExternalInput _ | ExternalOutput _ => external_flow ops cap u (stream_type s) (source s)
   | src => if sending u then
     obind (source_destinations ops (constants r) (at_pe u) src) (fun targets =>
     if Nat.eqb (List.length targets) 0 then None else
     obind (bound_value ops (constants r) (stream_type s)) (fun b =>
     obind (channel_value ops (constants r) (route_channel (route_of src))) (fun channel =>
     traverse (fun q => if matching_receive uses u q then
       obind (match src with Multicast _ _ _ => plan_prefix (at_pe u) q (route_hops (route_of src))
          | _ => plan_path (at_pe u) q (route_hops (route_of src)) end) (fun ps =>
       Some (Flow (Wire 0 (Some (at_pe u)) (Some q) (fst (reference u)) (snd (reference u))
         (phase u) b cap) ps channel)) else None) targets)))
     else Some [] end
 | None => match find (fun a => id_eqb (argument_id a) (fst (reference u))) (arguments k) with
   | None => None
   | Some a => if (if sending u then readonly a else writeonly a) then None else
     external_flow ops cap u (argument_type a)
       (if sending u then ExternalOutput auto_route else ExternalInput auto_route) end end.
Definition number_flows fs := map (fun nf => let f := snd nf in let w := edge f in
 Flow (Wire (fst nf) (sender w) (receiver w) (wire_stream w) (wire_indices w)
   (wire_scope w) (bound w) (capacity w)) (path f) (logical_channel f))
 (combine (seq 0 (List.length fs)) fs).
Definition covers fs u := existsb (fun f => let w := edge f in
 (same_scope (phase u) (wire_scope w) &&
 id_eqb (fst (reference u)) (wire_stream w) &&
 (if list_eq_dec Z.eq_dec (snd (reference u)) (wire_indices w) then true else false) &&
 match (if sending u then sender w else receiver w) with
 | Some p => pe_eqb p (at_pe u) | None => false end)%bool) fs.
Definition infer_flows fuel ops cap rs k :=
 if Nat.ltb 0 cap then obind (collect_regions fuel ops rs) (fun us =>
 let us := distinct_uses us in
 obind (traverse (flows_for ops cap rs k us) us) (fun groups =>
 let fs := number_flows (concat groups) in
 if (forallb (covers fs) us && wire_table_ok (map edge fs))%bool then Some fs else None)) else None.
Record compiled := Compiled { regions : list located; flows : list flow; routes : list colored }.
Definition compile_routes fuel ops env cap palette separated k :=
 obind (elaborate fuel ops env k) (fun rs =>
 obind (infer_flows fuel ops cap rs k) (fun fs =>
 option_map (Compiled rs fs) (checked_allocate separated palette fs))).
Definition deployed_network p := to_network (map edge (flows p)).
Definition start ops p k memory queues := initial_state ops (regions p) k memory queues.
Theorem inference_covers_uses : forall fuel ops cap rs k fs,
 infer_flows fuel ops cap rs k = Some fs -> exists us,
 collect_regions fuel ops rs = Some us /\ forallb (covers fs) (distinct_uses us) = true /\
 wire_table_ok (map edge fs) = true.
Proof.
 intros fuel ops cap rs k fs H; unfold infer_flows, obind in H.
 destruct (Nat.ltb 0 cap); try discriminate.
 destruct (collect_regions fuel ops rs) as [us|] eqn:E; try discriminate.
 destruct (traverse (flows_for ops cap rs k (distinct_uses us)) (distinct_uses us)) as [gs|]; try discriminate.
 destruct (forallb (covers (number_flows (concat gs))) (distinct_uses us) &&
   wire_table_ok (map edge (number_flows (concat gs))))%bool eqn:C; inversion H; subst.
 apply andb_true_iff in C as [A B]; exists us; auto.
Qed.
End Deployment.
