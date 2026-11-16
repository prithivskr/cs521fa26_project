From Stdlib Require Import ZArith List String Bool DecimalString.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaElaboration SpadaRouting.
Import ListNotations Spada SpatialSemantics SpatialElaboration Routing.
Open Scope string_scope.
Module RoutingCSL.
Record entry := Entry { node : pe; entry_color : nat; inputs : list string; outputs : list string }.
Definition direction p q :=
 if Z.ltb (fst p) (fst q) then "EAST" else if Z.ltb (fst q) (fst p) then "WEST"
 else if Z.ltb (snd p) (snd q) then "SOUTH" else "NORTH".
Fixpoint vertices previous points c := match points with
 | [] => [] | p :: tail =>
 Entry p c [match previous with None => "RAMP" | Some q => direction p q end]
   [match tail with [] => "RAMP" | q :: _ => direction p q end] ::
 vertices (Some p) tail c end.
Definition contributions c := match sender (edge (connection c)),receiver (edge (connection c)) with
 | Some _,Some _ => vertices None (path (connection c)) (color c)
 | _,_ => [] end.
Definition distinct xs := nodup string_dec xs.
Fixpoint insert e entries := match entries with
 | [] => [e] | h :: rest =>
 if (pe_eqb (node e) (node h) && Nat.eqb (entry_color e) (entry_color h))%bool then
   Entry (node h) (entry_color h) (distinct (inputs e ++ inputs h)%list)
     (distinct (outputs e ++ outputs h)%list) :: rest
 else h :: insert e rest end.
Definition table cs := fold_left (fun entries e => insert e entries) (flat_map contributions cs) [].
Definition entry_ok e :=
 (Z.leb 0 (fst (node e)) && Z.leb 0 (snd (node e)) &&
 Nat.eqb (List.length (inputs e)) 1 && negb (Nat.eqb (List.length (outputs e)) 0))%bool.
Definition zdecimal z := NilZero.string_of_int (Z.to_int z).
Definition print_entry e :=
 "  @set_color_config(" ++ zdecimal (fst (node e)) ++ ", " ++ zdecimal (snd (node e)) ++
 ", @get_color(" ++ decimal (entry_color e) ++ "), .{ .routes = .{ .rx = .{" ++
 String.concat ", " (inputs e) ++ "}, .tx = .{" ++ String.concat ", " (outputs e) ++ "} } });
".
(** Static configurations only. Conflicting receive ports require a real router
    epoch/switch schedule and are rejected, even when color reuse is certified. *)
Definition emit cs := let rows := table cs in
 if forallb entry_ok rows then Some (String.concat "" (map print_entry rows)) else None.
Theorem emitted_rows_valid : forall cs text,
 emit cs = Some text -> forall e, In e (table cs) -> entry_ok e = true.
Proof.
 intros cs text H e I; unfold emit in H.
 destruct (forallb entry_ok (table cs)) eqn:E; try discriminate.
 rewrite forallb_forall in E; apply E; exact I.
Qed.
End RoutingCSL.
