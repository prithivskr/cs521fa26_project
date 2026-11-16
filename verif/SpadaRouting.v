From Stdlib Require Import ZArith List Bool Lia.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaElaboration.
Import ListNotations Spada SpatialSemantics SpatialElaboration.
Open Scope Z_scope.
Open Scope list_scope.

Module Routing.
Record flow := Flow {
 edge : wire; path : list pe; logical_channel : option nat
}.
Record colored := Colored { connection : flow; color : nat }.
Definition point_add (p d : pe) := (fst p + fst d, snd p + snd d).
Definition unit (d : pe) := Z.eqb (Z.abs (fst d) + Z.abs (snd d)) 1.
Fixpoint walk p ds := match ds with
 | [] => [p] | d :: tail => p :: walk (point_add p d) tail end.
Definition axis_steps delta (horizontal : bool) :=
 repeat (if horizontal then (Z.sgn delta,0) else (0,Z.sgn delta)) (Z.to_nat (Z.abs delta)).
Definition manhattan p q := walk p
 (axis_steps (fst q-fst p) true ++ axis_steps (snd q-snd p) false).
Fixpoint prefix_to q ps := match ps with
 | [] => None | p :: tail => if pe_eqb p q then Some [p] else
   obind (prefix_to q tail) (fun rest => Some (p :: rest)) end.
Fixpoint simple_path ps := match ps with [] => true | p :: tail =>
 (negb (existsb (pe_eqb p) tail) && simple_path tail)%bool end.
Definition path_ok p q ps := match ps with
 | [] => false | h :: _ => (pe_eqb h p && pe_eqb (last ps h) q && simple_path ps &&
   forallb unit (map (fun ab => (fst (snd ab)-fst (fst ab), snd (snd ab)-snd (fst ab)))
     (combine ps (tl ps))))%bool end.
Definition eval_nat ops env e := obind (evaluate ops env e) (fun t =>
 obind (scalar_value t) (fun a => obind (index_value ops a) (fun z =>
 if Z.leb 0 z then Some (Z.to_nat z) else None))).
Definition channel_value ops env c := match c with
 | AutoChannel => Some None | Channel e => option_map (@Some nat) (eval_nat ops env e) end.
Definition plan_prefix p q hs := match hs with
 | AutoHops => let ps := manhattan p q in if path_ok p q ps then Some ps else None
 | Hops ds => if forallb unit ds then
   obind (prefix_to q (walk p ds)) (fun ps => if path_ok p q ps then Some ps else None)
   else None end.
Definition plan_path p q hs := match hs with
 | AutoHops => plan_prefix p q hs
 | Hops ds => let ps := walk p ds in
   if (forallb unit ds && path_ok p q ps)%bool then Some ps else None end.
Definition overlap a b := existsb (fun p => existsb (pe_eqb p) (path b)) (path a).
Definition multicast_group a b :=
 (match sender (edge a), sender (edge b) with
 | Some p,Some q => pe_eqb p q | _,_ => false end &&
 id_eqb (wire_stream (edge a)) (wire_stream (edge b)) &&
 same_scope (wire_scope (edge a)) (wire_scope (edge b)) &&
 if list_eq_dec Z.eq_dec (wire_indices (edge a)) (wire_indices (edge b)) then true else false)%bool.
(** A reuse certificate is explicit. Merely appearing in different phases is
    not sufficient evidence: PEs advance between phases independently. *)
Definition compatible (separated : flow -> flow -> bool) a b :=
 (negb (overlap a b) || multicast_group a b || separated a b)%bool.
Definition requested_together a b := match logical_channel a,logical_channel b with
 | Some x,Some y => Nat.eqb x y | _,_ => multicast_group a b end.
Definition candidate separated (placed : list colored) f c := forallb (fun old =>
 (if requested_together f (connection old) then Nat.eqb c (color old) else true) &&
 (if Nat.eqb c (color old) then compatible separated f (connection old) else true)) placed.
Fixpoint allocate separated palette placed remaining : option (list colored) :=
 match remaining with
 | [] => Some placed
 | f :: rest => match find (candidate separated placed f) palette with
   | None => None | Some c => allocate separated palette (Colored f c :: placed) rest end end.
Definition pair_ok separated a b :=
 ((if requested_together (connection a) (connection b) then Nat.eqb (color a) (color b) else true) &&
  (if Nat.eqb (color a) (color b) then compatible separated (connection a) (connection b) else true))%bool.
(** Check only distinct allocated entries; one route is compatible with itself. *)
Fixpoint coloring_ok separated palette cs := match cs with
 | [] => true | c :: rest =>
 (existsb (Nat.eqb (color c)) palette &&
  forallb (pair_ok separated c) rest && coloring_ok separated palette rest)%bool end.
Definition checked_allocate separated palette fs :=
 obind (allocate separated palette [] fs) (fun cs =>
 if coloring_ok separated palette cs then Some cs else None).
Theorem allocated_checked : forall separated palette fs cs,
 checked_allocate separated palette fs = Some cs -> coloring_ok separated palette cs = true.
Proof.
 intros separated palette fs cs H; unfold checked_allocate, obind in H.
 destruct (allocate separated palette [] fs) as [xs|]; try discriminate.
 destruct (coloring_ok separated palette xs) eqn:E; inversion H; subst; exact E.
Qed.
Theorem checked_colors_in_palette : forall sep palette cs,
 coloring_ok sep palette cs = true -> forall c, In c cs -> In (color c) palette.
Proof.
 intros sep palette cs; induction cs as [|a tail IH]; intros H c I; [contradiction|].
 simpl in H; apply andb_true_iff in H as [H T]; apply andb_true_iff in H as [P _].
 destruct I as [I|I].
 - subst c; apply existsb_exists in P as [n [N E]]; apply Nat.eqb_eq in E; subst; exact N.
 - eapply IH; eauto.
Qed.
Theorem checked_pair_constraints : forall sep palette a tail,
 coloring_ok sep palette (a :: tail) = true -> forall b, In b tail -> pair_ok sep a b = true.
Proof.
 intros sep palette a tail H b I; simpl in H.
 apply andb_true_iff in H as [H _]; apply andb_true_iff in H as [_ H].
 rewrite forallb_forall in H; apply H; exact I.
Qed.
Theorem overlapping_independent_routes_have_different_colors : forall sep a b,
 pair_ok sep a b = true -> overlap (connection a) (connection b) = true ->
 multicast_group (connection a) (connection b) = false ->
 sep (connection a) (connection b) = false -> color a <> color b.
Proof.
 intros sep a b H O M S E; unfold pair_ok in H; rewrite E, Nat.eqb_refl in H.
 apply andb_true_iff in H as [_ H]; unfold compatible in H.
 rewrite O, M, S in H; discriminate.
Qed.
End Routing.
