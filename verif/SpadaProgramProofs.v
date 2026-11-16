From Stdlib Require Import ZArith List String Bool.
From SpatialCSL Require Import SpadaIR SpadaExamples SpadaSemantics SpadaArithmetic SpadaEquivalence SpadaElaboration.
Import ListNotations Spada SpatialSemantics ReferenceArithmetic SpatialElaboration.
Open Scope Z_scope.

Example ping_places_two_pes :
 option_map (fun rs => List.length (locations rs)) (elaborate 8 reference no_environment ping) = Some 2%nat.
Proof. vm_compute; reflexivity. Qed.
Example pipeline_has_two_local_phases :
 option_map (fun rs => map (fun r => phase_number (scope r))
   (filter (fun r => match kind r with Body _ => true | _ => false end) rs))
   (elaborate 8 reference no_environment pipeline) = Some [1%nat;1%nat;2%nat;2%nat].
Proof. vm_compute; reflexivity. Qed.
Definition meta_kernel := Kernel "meta" [] [] [
 MetaFor [coord "stage"] [interval 0 3] [Phase [Compute xy left [
   Assign (var "a") (var "stage")]]]].
Example metaprogramming_instantiates_three_phases :
 option_map (fun rs => map (fun r => phase_number (scope r)) rs)
   (elaborate 8 reference no_environment meta_kernel) = Some [1%nat;2%nat;3%nat].
Proof. vm_compute; reflexivity. Qed.
Definition scratch_shadow := Kernel "shadow" [] [] [
 Place xy left [Field (Scalar I32) (named "a") false];
 Phase [Place xy left [Field (Scalar I32) (named "a") false];
        Compute xy left [Assign (var "a") (int 1)]];
 Phase [Compute xy left [Assign (var "a") (int 2)]]].
Example local_field_shadows_global_only_in_its_phase :
 option_map (fun rs =>
   (name (resolve_name rs scratch_shadow (0,0) (Some 1%nat) (named "a")),
    name (resolve_name rs scratch_shadow (0,0) (Some 2%nat) (named "a"))))
   (elaborate 8 reference no_environment scratch_shadow) =
 Some ("/field/1/a", "/field/0/a")%string.
Proof. vm_compute; reflexivity. Qed.
Example stream_epochs_are_distinct :
 scoped "stream" (Some 1%nat) (named "east") <>
 scoped "stream" (Some 2%nat) (named "east").
Proof. discriminate. Qed.
Example integer_assignment_converts_to_float :
 converted reference [Atom F32 0] [Atom I32 2] = Some [Atom F32 1073741824].
Proof. vm_compute; reflexivity. Qed.
Example multidimensional_slice :
 evaluate reference (fun id => if id_eqb id (named "a") then
   Some (Tensor [2%nat;2%nat] [Atom I32 1;Atom I32 2;Atom I32 3;Atom I32 4]) else None)
   (Slice (named "a") [int 1; interval 0 2]) =
 Some (Tensor [2%nat] [Atom I32 3;Atom I32 4]).
Proof. vm_compute; reflexivity. Qed.
Example broadcast_preserves_placed_shape :
 option_map (fun m => m (0,0) (named "a"))
 (assign reference (fun _ _ => Some (Tensor [2%nat] [Atom I32 9;Atom I32 9]))
   (0,0) no_environment (var "a") (singleton (Atom I32 3))) =
 Some (Some (Tensor [2%nat] [Atom I32 3;Atom I32 3])).
Proof. vm_compute; reflexivity. Qed.

(** A semantic expression rewrite can be used under any assignment, including
    in asynchronous tasks. It does not require equality of source syntax. *)
Definition expression_equivalent ops a b :=
 forall env, evaluate ops env a = evaluate ops env b.
Theorem assignment_rewrite : forall ops a b,
 expression_equivalent ops a b -> forall m p locals dst,
 obind (eval_at ops m p locals a) (assign ops m p locals dst) =
 obind (eval_at ops m p locals b) (assign ops m p locals dst).
Proof. intros ops a b E m p locals dst; unfold eval_at; rewrite E; reflexivity. Qed.
Example constant_folding : expression_equivalent reference
 (Binary (Constant F32 (FloatBits 1065353216)) Plus (Constant F32 (FloatBits 1065353216)))
 (Constant F32 (FloatBits 1073741824)).
Proof. intros env; vm_compute; reflexivity. Qed.

(** Relational proof infrastructure has no assumptions about real arithmetic,
    scheduler determinism, fairness, or backpressure-free communication. *)
Print Assumptions assignment_rewrite.
Print Assumptions bisimulation_sound.
Print Assumptions bisimulation_divergence.
Print Assumptions KernelEquivalence.kernel_name_irrelevant.

Definition quiet_network := Network (fun _ _ => []) (fun _ _ => None)
 (fun _ => None) (fun _ => 1%nat) (fun _ => false) (fun _ => false).
Definition assignment_task dst src := Task 0 None (0,0) no_environment no_handles [Execute (Assign dst src)].
Definition assignment_state m dst src := State [assignment_task dst src] m 1
 (fun _ => []) (fun _ => 0%nat) (fun _ => false) (fun _ _ => false).
Lemma singleton_task_split : forall (only : task) before chosen after,
 [only] = (before ++ chosen :: after)%list -> before = [] /\ chosen = only /\ after = [].
Proof.
 intros only before chosen after E; destruct before as [|h before]; simpl in E.
 - inversion E; subst; auto.
 - inversion E as [[F G]]; symmetry in G; apply app_eq_nil in G as [_ G]; discriminate.
Qed.
Lemma assignment_step_inverse : forall ops m dst src label next,
 step ops quiet_network (assignment_state m dst src) label next ->
 exists value m', label = None /\
 evaluate ops (local_environment m (0,0) no_environment) src = Some value /\
 assign ops m (0,0) no_environment dst value = Some m' /\
 next = State [with_code (assignment_task dst src) []] m' 1
   (fun _ => []) (fun _ => 0%nat) (fun _ => false) (fun _ _ => false).
Proof.
 intros ops m dst src label next H; inversion H; subst; simpl in *;
 try match goal with
 | K : [_] = (_ ++ _ :: _)%list |- _ =>
   apply singleton_task_split in K; destruct K as [? [? ?]]; subst
 end; simpl in *; try discriminate.
 inversion H1; subst.
 exists v, m0; repeat split; auto.
Qed.

Lemma assignment_step_rewrite : forall ops a b,
 expression_equivalent ops a b -> forall m dst label next,
 step ops quiet_network (assignment_state m dst a) label next ->
 step ops quiet_network (assignment_state m dst b) label next.
Proof.
 intros ops a b E m dst label next H.
 destruct (assignment_step_inverse _ _ _ _ _ _ H) as [v [m' [L [V [W N]]]]]; subst.
 eapply StepAssign with (pre:=[]) (post:=[]) (t:=assignment_task dst b) (rest:=[]) (v:=v).
 - reflexivity.
 - reflexivity.
 - change (evaluate ops (local_environment m (0,0) no_environment) b = Some v).
   rewrite <- E; exact V.
 - exact W.
Qed.
Theorem assignment_program_equivalent : forall O ops (observe : memory -> O) a b,
 expression_equivalent ops a b -> forall m dst,
 total_equivalent ops quiet_network (fun s => observe (contents s))
   (assignment_state m dst a) (assignment_state m dst b).
Proof.
 intros O ops observe a b E m dst.
 set (A := assignment_state m dst a).
 set (B := assignment_state m dst b).
 set (R := fun s t => s = t \/ (s = A /\ t = B)).
 assert (Bisim : bisimulation ops quiet_network R).
 { constructor.
   - intros s t [K|[K L]] label next H; subst.
     + exists next; split; [exact H | left; reflexivity].
     + exists next; split; [eapply assignment_step_rewrite; eauto | left; reflexivity].
   - intros s t [K|[K L]] label next H; subst.
     + exists next; split; [exact H | left; reflexivity].
     + exists next; split; [|left; reflexivity].
       eapply assignment_step_rewrite; [|exact H].
       intros env; symmetry; apply E.
   - intros s t [K|[K L]]; subst; [reflexivity |].
     unfold terminal, A, B, assignment_state; simpl; split; discriminate. }
 eapply bisimulation_total_sound with (R:=R); [exact Bisim| |].
 - intros s t [K|[K L]]; subst; reflexivity.
 - right; split; reflexivity.
Qed.
Example f32_folded_programs_equivalent : forall m dst,
 total_equivalent reference quiet_network contents
 (assignment_state m dst (Binary (Constant F32 (FloatBits 1065353216)) Plus
                                (Constant F32 (FloatBits 1065353216))))
 (assignment_state m dst (Constant F32 (FloatBits 1073741824))).
Proof. intros; exact (assignment_program_equivalent memory reference (fun x => x) _ _ constant_folding m dst). Qed.
Print Assumptions assignment_program_equivalent.

Example explicit_parameter_value_overrides_default :
 evaluate reference (bind no_environment (named "N") (singleton (Atom I32 8)))
   (EParam "N" (Some 4)) = Some (singleton (Atom I32 8)).
Proof. vm_compute; reflexivity. Qed.
Example indexed_stream_array_closes_every_element :
 List.length (argument_streams reference no_environment bounded_host) = 4%nat.
Proof. vm_compute; reflexivity. Qed.
