From Stdlib Require Import ZArith List String Bool Lia.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaArithmetic SpadaEquivalence
 SpadaElaboration SpadaRefinement SpadaExamples.
Import ListNotations Spada SpatialSemantics ReferenceArithmetic SpatialElaboration.
Open Scope Z_scope.

(** Validate the finite wire table before constructing its functional maps.
    These checks address indexing/ambiguity, not physical router conflicts. *)
Fixpoint unique_ids (ids : list nat) := match ids with
 | [] => true | id :: tail => negb (existsb (Nat.eqb id) tail) && unique_ids tail end.
Definition same_receiver a b := match receiver a, receiver b with
 | Some p,Some q => (pe_eqb p q &&
    id_eqb (scoped "stream" (wire_scope a) (wire_stream a))
           (scoped "stream" (wire_scope b) (wire_stream b)) &&
    if list_eq_dec Z.eq_dec (wire_indices a) (wire_indices b) then true else false)%bool
 | _,_ => false end.
Definition wire_table_ok ws :=
 (unique_ids (map wire_id ws) &&
 forallb (fun w => Nat.ltb 0 (capacity w) &&
   match sender w, receiver w with None,None => false | _,_ => true end) ws &&
 forallb (fun a => forallb (fun b =>
   if same_receiver a b then Nat.eqb (wire_id a) (wire_id b) else true) ws) ws)%bool.
Lemma checked_wires_have_capacity : forall ws, wire_table_ok ws = true ->
 forall w, In w ws -> (0 < capacity w)%nat.
Proof.
 intros ws H w I; unfold wire_table_ok in H.
 apply andb_true_iff in H as [H _]; apply andb_true_iff in H as [_ H].
 rewrite forallb_forall in H; specialize (H w I).
 apply andb_true_iff in H as [H _]; apply Nat.ltb_lt; exact H.
Qed.
(** Source-level endpoints are explicit. Geometry agreement is required;
    completeness, field initialization, race freedom and physical routing
    remain separate source well-formedness obligations. *)
Definition deployment ops fuel env k m queues (net : network) s :=
 exists regions wires, elaborate fuel ops env k = Some regions /\
 wire_table_ok wires = true /\
 (forall w, In w wires -> wire_agrees ops regions k w) /\
 net = to_network wires /\ s = initial_state ops regions k m queues.
Definition deployed_equivalent {O} ops (observeA observeB : state -> O)
 netA netB a b := across_equivalent ops netA netB observeA observeB a b.
Theorem certify_deployed_kernels : forall O ops fuel env kA kB mA mB queuesA queuesB
 netA netB a b (observeA observeB : state -> O) R,
 deployment ops fuel env kA mA queuesA netA a ->
 deployment ops fuel env kB mB queuesB netB b ->
 weak_certificate ops netA netB observeA observeB R -> R a b ->
 deployed_equivalent ops observeA observeB netA netB a b.
Proof. intros; eapply weak_certificate_sound; eauto. Qed.

(** Route selection is a compiler choice. Functional equivalence is conditional
    on both choices realizing the same logical FIFO network. This proves no
    physical color allocation or router safety fact. *)
Definition manual_east := StreamDecl (Stream F32 (Some (int 4))) (named "east")
 (Relative (int 1) (int 0) (Route (Hops [(1,0)]) (Channel (int 0)))).
Definition manual_ping := Kernel "rocq_ping_manual" [] [] [
 Place xy grid2 [buf "a";buf "b"];
 Dataflow xy grid2 [manual_east];
 Phase [
  Compute xy left [Send (var "a") (var "east") (Some (named "sent")); Await (named "sent")];
  Compute xy right [Receive (var "b") (var "east") None]]].
Definition prepared k m queues :=
 option_map (fun rs => initial_state reference rs k m queues)
   (elaborate 8 reference no_environment k).
Theorem automatic_and_manual_routes_same_machine : forall m queues,
 prepared ping m queues = prepared manual_ping m queues.
Proof. intros; reflexivity. Qed.
Theorem communicating_kernels_equivalent : forall O (observe : state -> O) m queues a b net,
 prepared ping m queues = Some a -> prepared manual_ping m queues = Some b ->
 total_equivalent reference net observe a b.
Proof.
 intros O observe m queues a b net A B.
 rewrite <- automatic_and_manual_routes_same_machine in B.
 rewrite A in B; inversion B; subst; split.
 - apply equivalent_refl.
 - reflexivity.
Qed.

(** Use a real sender/receiver edge, capacity one, with exactly four elements.
    Capacity one retains backpressure instead of assuming unbounded buffering. *)
Definition ping_wire := Wire 0 (Some (0,0)) (Some (1,0)) (named "east") []
 (Some 1%nat) (Some 4%nat) 1.
Definition ping_network := to_network [ping_wire].
Example sender_has_one_fifo :
 outgoing ping_network (0,0) (scoped "stream" (Some 1%nat) (named "east"),[]) = [0%nat].
Proof. vm_compute; reflexivity. Qed.
Example receiver_has_the_same_fifo :
 incoming ping_network (1,0) (scoped "stream" (Some 1%nat) (named "east"),[]) = Some 0%nat.
Proof. vm_compute; reflexivity. Qed.
Example ping_fifo_is_bounded : edge_capacity ping_network 0 = 1%nat /\
 edge_bound ping_network 0 = Some 4%nat.
Proof. split; reflexivity. Qed.
Print Assumptions communicating_kernels_equivalent.
Print Assumptions certify_deployed_kernels.

Example rejects_zero_capacity :
 wire_table_ok [Wire 0 (Some (0,0)) (Some (1,0)) (named "east") []
   (Some 1%nat) (Some 4%nat) 0] = false.
Proof. vm_compute; reflexivity. Qed.
Example rejects_duplicate_ids : wire_table_ok [ping_wire;ping_wire] = false.
Proof. vm_compute; reflexivity. Qed.
Example accepts_ping_wiring : wire_table_ok [ping_wire] = true.
Proof. vm_compute; reflexivity. Qed.

Definition manual_ping_json := export manual_ping.
