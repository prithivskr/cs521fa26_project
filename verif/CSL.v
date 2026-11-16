From Stdlib Require Import ZArith List Bool String DecimalString Lia.
From SpatialCSL Require Import Spatial.
Import ListNotations.
Open Scope string_scope.

(** The scalar assignment fragment of CSL, with explicit u32 semantics.
    This is an executable model, not a formalization of Cerebras' compiler. *)
Inductive cexpr :=
| CWord (v : Z) | CRead (slot : nat)
| CAdd (a b : cexpr) | CMul (a b : cexpr).
Fixpoint ceval (e : cexpr) (m : memory) : Z :=
  match e with
  | CWord v => word v | CRead i => word (m i)
  | CAdd a b => word (ceval a m + ceval b m)
  | CMul a b => word (ceval a m * ceval b m)
  end.
Record instruction := { destination : nat; value : cexpr }.
Definition step (i : instruction) (m : memory) :=
  write m (destination i) (ceval (value i) m).
Fixpoint interpret (code : list instruction) (m : memory) : memory :=
  match code with [] => m | i :: tail => interpret tail (step i m) end.
Lemma interpret_app : forall a b m,
  interpret (a ++ b) m = interpret b (interpret a m).
Proof. induction a; intros b m; simpl; auto. Qed.

Fixpoint lower_expr (e : expr) : cexpr :=
  match e with
  | Lit v => CWord (word v) | Load i => CRead i
  | Add a b => CAdd (lower_expr a) (lower_expr b)
  | Mul a b => CMul (lower_expr a) (lower_expr b)
  end.
Lemma word_idempotent : forall z, word (word z) = word z.
Proof. intros; unfold word; apply Z.mod_mod; discriminate. Qed.
Theorem lower_expr_correct : forall e m, ceval (lower_expr e) m = eval e m.
Proof.
  induction e; intros m; simpl; try rewrite IHe1, IHe2; auto.
  apply word_idempotent.
Qed.
Fixpoint copies (n : nat) (code : list instruction) : list instruction :=
  match n with O => [] | S n => code ++ copies n code end.
Fixpoint lower (c : command) : list instruction :=
  match c with
  | Skip => []
  | Store i e => [{| destination := i; value := lower_expr e |}]
  | Seq a b => lower a ++ lower b
  | Repeat n b => copies n (lower b)
  end.
Lemma interpret_copies : forall n code m,
  interpret (copies n code) m = iterate n (interpret code) m.
Proof.
  induction n; intros code m; simpl; auto.
  rewrite interpret_app; apply IHn.
Qed.
Theorem lower_correct : forall c m, interpret (lower c) m = execute c m.
Proof.
  induction c; intros m; simpl; auto.
  - unfold step; simpl; rewrite lower_expr_correct; reflexivity.
  - rewrite interpret_app, IHc1, IHc2; reflexivity.
  - rewrite interpret_copies.
    apply iterate_ext; apply IHc.
Qed.

Record program := {
  columns : nat; rows : nat; buffer_size : nat;
  tile : nat -> nat -> list instruction
}.
Definition lower_kernel (k : kernel) : program :=
  {| columns := width k; rows := height k; buffer_size := slots k;
     tile := fun x y => lower (compute k x y) |}.
Definition run_program (p : program) (s : fabric) : fabric := fun x y =>
  if (Nat.ltb x (columns p) && Nat.ltb y (rows p))%bool
  then interpret (tile p x y) (s x y) else s x y.
Theorem lower_kernel_correct : forall k s x y,
  run_program (lower_kernel k) s x y = run k s x y.
Proof.
  intros; unfold run_program, run, lower_kernel; simpl.
  destruct (Nat.ltb x (width k) && Nat.ltb y (height k))%bool;
    [apply lower_correct | reflexivity].
Qed.
Theorem equivalence_preserved : forall a b,
  kernel_equivalent a b -> forall s x y,
  run_program (lower_kernel a) s x y = run_program (lower_kernel b) s x y.
Proof.
  intros a b [_ [_ [_ E]]] s x y; rewrite !lower_kernel_correct; apply E.
Qed.

Theorem observational_equivalence_preserved : forall outputs a b,
  observationally_equivalent outputs a b -> forall s x y i,
  In i outputs ->
  run_program (lower_kernel a) s x y i =
  run_program (lower_kernel b) s x y i.
Proof.
  intros outputs a b [_ [_ E]] s x y i I.
  rewrite !lower_kernel_correct; apply E; exact I.
Qed.

Definition coordinates (w h : nat) : list (nat * nat) :=
  flat_map (fun y => map (fun x => (x, y)) (seq 0 w)) (seq 0 h).
Definition valid (k : kernel) : bool :=
  (Nat.ltb 0 (width k) && Nat.leb (width k) 32767 &&
   Nat.ltb 0 (height k) && Nat.leb (height k) 32767 &&
   Nat.ltb 0 (slots k) && Nat.leb (slots k) 8192 &&
   forallb (fun xy => command_ok (slots k) (compute k (fst xy) (snd xy)))
     (coordinates (width k) (height k)))%bool.
Definition compile (k : kernel) : option program :=
  if valid k then Some (lower_kernel k) else None.
Theorem compile_correct : forall k p, compile k = Some p ->
  forall s x y, run_program p s x y = run k s x y.
Proof.
  intros k p H; unfold compile in H; destruct (valid k); inversion H; subst.
  apply lower_kernel_correct.
Qed.

Lemma coordinates_complete : forall w h x y,
  (x < w)%nat -> (y < h)%nat -> In (x, y) (coordinates w h).
Proof.
  intros w h x y X Y; unfold coordinates; apply in_flat_map.
  exists y; split.
  - apply in_seq; lia.
  - apply in_map_iff; exists x; split; [reflexivity | apply in_seq; lia].
Qed.
Theorem valid_commands : forall k x y,
  valid k = true -> (x < width k)%nat -> (y < height k)%nat ->
  command_ok (slots k) (compute k x y) = true.
Proof.
  intros k x y V X Y; unfold valid in V.
  apply andb_true_iff in V as [_ V].
  rewrite forallb_forall in V.
  apply (V (x, y)); apply coordinates_complete; assumption.
Qed.
Theorem compile_storage_safe : forall k p, compile k = Some p ->
  forall s x y j, (slots k <= j)%nat -> run_program p s x y j = s x y j.
Proof.
  intros k p C s x y j J; rewrite (compile_correct k p C).
  unfold compile in C; destruct (valid k) eqn:V; try discriminate.
  unfold run; destruct (Nat.ltb x (width k) && Nat.ltb y (height k))%bool eqn:B;
    [|reflexivity].
  apply andb_true_iff in B as [X Y].
  apply Nat.ltb_lt in X; apply Nat.ltb_lt in Y.
  apply execute_frame with (slots k); auto.
  apply valid_commands; assumption.
Qed.

(** Rendering is kept separate from the proved AST lowering. Names are generated
    from naturals, so user strings cannot inject CSL syntax. *)
Definition decimal (n : nat) := NilZero.string_of_uint (Nat.to_uint n).
Definition word_decimal (z : Z) := NilZero.string_of_int (Z.to_int (word z)).
Fixpoint print_expr (e : cexpr) : string :=
  match e with
  | CWord v => "@as(u32, " ++ word_decimal v ++ ")"
  | CRead i => "buffer[" ++ decimal i ++ "]"
  | CAdd a b => "(" ++ print_expr a ++ " + " ++ print_expr b ++ ")"
  | CMul a b => "(" ++ print_expr a ++ " * " ++ print_expr b ++ ")"
  end.
Definition print_instruction (i : instruction) :=
  "  buffer[" ++ decimal (destination i) ++ "] = " ++ print_expr (value i) ++ ";
".
Definition tile_name (x y : nat) :=
  "pe_" ++ decimal x ++ "_" ++ decimal y ++ ".csl".
Definition print_tile (p : program) (x y : nat) :=
  "param memcpy_params;
const sys = @import_module(""<memcpy/memcpy>"", memcpy_params);
var buffer: [" ++ decimal (buffer_size p) ++ "]u32;
var buffer_ptr: [*]u32 = &buffer;
fn run() void {
" ++ String.concat "" (map print_instruction (tile p x y)) ++
  "  sys.unblock_cmd_stream();
}
comptime {
  @export_symbol(buffer_ptr, ""buffer"");
  @export_symbol(run);
}
".
Definition print_placement (xy : nat * nat) :=
  let '(x, y) := xy in
  "  @set_tile_code(" ++ decimal x ++ ", " ++ decimal y ++ ", """ ++
  tile_name x y ++ """, .{ .memcpy_params = memcpy.get_params(" ++
  decimal x ++ ") });
".
Definition print_layout (p : program) :=
  "const memcpy = @import_module(""<memcpy/get_params>"", .{
  .width = " ++ decimal (columns p) ++ ", .height = " ++ decimal (rows p) ++ "
});
layout {
  @set_rectangle(" ++ decimal (columns p) ++ ", " ++ decimal (rows p) ++ ");
" ++ String.concat "" (map print_placement (coordinates (columns p) (rows p))) ++
  "  @export_name(""buffer"", [*]u32, true);
  @export_name(""run"", fn()void);
}
".
Definition file := (string * string)%type.
Definition render (p : program) : list file :=
  ("layout.csl", print_layout p) ::
  map (fun xy => (tile_name (fst xy) (snd xy), print_tile p (fst xy) (snd xy)))
      (coordinates (columns p) (rows p)).
Definition compile_files (k : kernel) : option (list file) :=
  option_map render (compile k).
