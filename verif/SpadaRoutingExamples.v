From Stdlib Require Import ZArith List String.
From SpatialCSL Require Import SpadaIR SpadaSemantics SpadaArithmetic SpadaElaboration
 SpadaEquivalence SpadaRouting SpadaRoutingCSL SpadaDeployment SpadaExamples SpadaKernelProofs.
Import ListNotations Spada SpatialSemantics ReferenceArithmetic SpatialElaboration Routing Deployment.
Open Scope Z_scope.
Definition no_reuse (_ _ : flow) := false.
Definition palette := [2%nat;3%nat;4%nat;5%nat;6%nat;7%nat].
Definition plan k := compile_routes 16 ReferenceArithmetic.reference no_environment 1 palette no_reuse k.
Definition counts k := option_map (fun p => (List.length (flows p),List.length (routes p))) (plan k).
Example infer_point_to_point : counts ping = Some (1%nat,1%nat).
Proof. vm_compute; reflexivity. Qed.
Example infer_multicast : counts multicast = Some (2%nat,2%nat).
Proof. vm_compute; reflexivity. Qed.
Example multicast_shares_color : option_map (fun p => map color (routes p)) (plan multicast) =
 Some [2%nat;2%nat].
Proof. vm_compute; reflexivity. Qed.
Example infer_host_streams : counts host_streaming = Some (2%nat,2%nat).
Proof. vm_compute; reflexivity. Qed.
Example infer_bounded_array_arguments : counts bounded_host = Some (4%nat,4%nat).
Proof. vm_compute; reflexivity. Qed.
Example infer_explicit_external_streams : counts external_streams = Some (2%nat,2%nat).
Proof. vm_compute; reflexivity. Qed.
Example infer_multiphase_pipeline : counts pipeline = Some (1%nat,1%nat).
Proof. vm_compute; reflexivity. Qed.
Example inference_rejects_exhausted_palette :
 compile_routes 16 ReferenceArithmetic.reference no_environment 1 [] no_reuse ping = None.
Proof. vm_compute; reflexivity. Qed.
Example invalid_hop_rejected : plan_path (0,0) (2,0) (Hops [(2,0)]) = None.
Proof. vm_compute; reflexivity. Qed.
Example wrong_destination_rejected : plan_path (0,0) (2,0) (Hops [(1,0)]) = None.
Proof. vm_compute; reflexivity. Qed.
Example automatic_multi_hop : plan_path (0,0) (2,1) AutoHops = Some [(0,0);(1,0);(2,0);(2,1)].
Proof. vm_compute; reflexivity. Qed.
Definition conflicting := Kernel "bad" [] [] [
 Place xy grid2 [buf "a";buf "b"];
 Dataflow xy grid2 [east]; Phase [Compute xy left [Send (var "a") (var "east") None]]].
Example unmatched_send_rejected : plan conflicting = None.
Proof. vm_compute; reflexivity. Qed.
Example inferred_fifo_is_executable :
 option_map (fun p => outgoing (deployed_network p) (0,0)
  (scoped "stream" (Some 1%nat) (named "east"),[])) (plan ping) = Some [0%nat].
Proof. vm_compute; reflexivity. Qed.
Print Assumptions allocated_checked.
Print Assumptions checked_colors_in_palette.
Print Assumptions inference_covers_uses.

Example inference_matches_manual_network :
 option_map deployed_network (plan ping) = Some ping_network.
Proof. vm_compute; reflexivity. Qed.
Definition ping_routing_text := obind (plan ping) (fun p => RoutingCSL.emit (routes p)).
Definition multicast_routing_text := obind (plan multicast) (fun p => RoutingCSL.emit (routes p)).
Example static_ping_configurations :
 option_map (fun p => List.length (RoutingCSL.table (routes p))) (plan ping) = Some 2%nat.
Proof. vm_compute; reflexivity. Qed.
Example multicast_router_delivers_and_forwards :
 option_map (fun p => map RoutingCSL.outputs (RoutingCSL.table (routes p))) (plan multicast) =
 Some [["EAST"];["RAMP";"EAST"];["RAMP"]]%string.
Proof. vm_compute; reflexivity. Qed.

Definition second_flow := Flow
 (Wire 1 (Some (1,0)) (Some (2,0)) (named "other") [] (Some 1%nat) None 1)
 [(1,0);(2,0)] None.
Definition first_flow := Flow ping_wire [(0,0);(1,0)] None.
Example overlapping_flows_need_distinct_colors :
 option_map (map color) (checked_allocate no_reuse [2%nat;3%nat] [first_flow;second_flow]) =
 Some [3%nat;2%nat].
Proof. vm_compute; reflexivity. Qed.
Example conflicting_single_color_is_rejected :
 checked_allocate no_reuse [2%nat] [first_flow;second_flow] = None.
Proof. vm_compute; reflexivity. Qed.
Example static_switch_conflict_is_rejected :
 RoutingCSL.emit [Colored first_flow 2;Colored second_flow 2] = None.
Proof. vm_compute; reflexivity. Qed.

Definition inferred_start k m qs := option_map
 (fun p => start ReferenceArithmetic.reference p k m qs) (plan k).
Theorem inference_preserves_ping_initial_state : forall m qs,
 inferred_start ping m qs = prepared ping m qs.
Proof. intros; reflexivity. Qed.
Theorem inferred_stream_kernel_equivalent : forall O (observe : state -> O) m qs a b,
 inferred_start ping m qs = Some a -> prepared ping m qs = Some b ->
 total_equivalent ReferenceArithmetic.reference ping_network observe a b.
Proof.
 intros O observe m qs a b A B; rewrite inference_preserves_ping_initial_state in A.
 rewrite A in B; inversion B; subst; split; [apply equivalent_refl | reflexivity].
Qed.
Print Assumptions inferred_stream_kernel_equivalent.
