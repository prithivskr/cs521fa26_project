From Stdlib Require Import ZArith List Ascii String Bool DecimalString.
Import ListNotations.
Open Scope string_scope.

(** Surface AST of the checked-out SpaDA Spatial IR. This module has no Python,
    parser, or CSL dependency: kernels are constructed as ordinary Rocq values. *)
Module Spada.
Inductive scalar := I8 | I16 | I32 | U8 | U16 | U32 | F16 | F32 | F64 | Bool.
Record identifier := Id { name : string; version : nat }.
Definition named (s : string) := Id s 0.
Inductive unary := Positive | Negative | LogicalNot | BitNot.
Inductive binary := Plus | Minus | Times | Divide | Modulo
 | Equal | NotEqual | Less | LessEqual | Greater | GreaterEqual | ShiftLeft | ShiftRight | BitAnd | BitOr | BitXor | LogicalAnd | LogicalOr | Power.
(** Floating literals carry exact IEEE bit patterns, preserving -0, infinity,
    and NaNs. Integer literals are arbitrary precision before target checking. *)
Inductive literal := Integer (z : Z) | FloatBits (bits : Z) | BooleanValue (value : bool).
Inductive expression :=
 | EVar (id : identifier)
 | Constant (ty : scalar) (v : literal)
 | EParam (param : string) (value : option Z)
 | Unary (op : unary) (value : expression)
 | Binary (a : expression) (op : binary) (b : expression)
 | Select (yes condition no : expression)
 | FusedMultiplyAdd (a b c : expression)
 | Slice (array : identifier) (indices : list expression)
 | Range (start : expression) (stop stride : option expression).
Definition int (z : Z) := Constant I32 (Integer z).
Definition var (s : string) := EVar (named s).
Definition interval (lo hi : Z) := Range (int lo) (Some (int hi)) None.
Inductive dtype :=
 | Scalar (ty : scalar)
 | Stream (ty : scalar) (bound : option expression)
 | Array (base : dtype) (shape : list expression).
Record typed_id := Typed { typ : dtype; ident : identifier }.
Definition coord (s : string) := Typed (Scalar I32) (named s).
Record subgrid := Grid { xrange : expression; yrange : expression }.
Definition rectangle (w h : Z) := Grid (interval 0 w) (interval 0 h).
Record field := Field { field_type : dtype; field_id : identifier; external : bool }.
Inductive channel := AutoChannel | Channel (number : expression).
Inductive hops := AutoHops | Hops (offsets : list (Z * Z)).
Record routing := Route { route_hops : hops; route_channel : channel }.
Definition auto_route := Route AutoHops AutoChannel.
Inductive stream_source :=
 | Relative (dx dy : expression) (route : routing)
 | Multicast (dx dy : expression) (route : routing)
 | ExternalInput (route : routing) | ExternalOutput (route : routing).
Record stream_decl := StreamDecl {
  stream_type : dtype; stream_id : identifier; source : stream_source
}.
(** None means immediate await, Some id introduces a completion. *)
Definition completion := option identifier.
Inductive statement :=
 | Assign (destination source : expression)
 | Send (payload stream : expression) (done : completion)
 | Receive (destination stream : expression) (done : completion)
 | Close (stream : expression) (done : completion)
 | Foreach (indices : list typed_id) (ranges : list expression)
     (element : typed_id) (stream : expression)
     (body : list statement) (done : completion)
 | Map (indices : list typed_id) (ranges : list expression)
     (body : list statement) (done : completion)
 | For (indices : list typed_id) (ranges : list expression) (body : list statement)
 | Async (body : list statement) (done : completion)
 | Await (done : identifier)
 | AwaitAll.
Inductive block :=
 | Place (coords : list typed_id) (grid : subgrid) (fields : list field)
 | Dataflow (coords : list typed_id) (grid : subgrid) (streams : list stream_decl)
 | Compute (coords : list typed_id) (grid : subgrid) (body : list statement)
 | Phase (body : list block)
 | MetaFor (indices : list typed_id) (ranges : list expression) (body : list block).
Record argument := Argument {
  argument_type : dtype; argument_id : identifier;
  readonly : bool; writeonly : bool; compiletime : bool
}.
Record kernel := Kernel {
  kernel_name : string;
  parameters : list (string * option Z);
  arguments : list argument;
  blocks : list block
}.

(** Lossless, data-only interchange AST. It is also useful as a compact target
    for a future verified routing backend. No code strings or eval hooks. *)
Inductive tree :=
 | Object (tag : string) (fields : list (string * tree))
 | Sequence (elements : list tree)
 | Text (value : string) | Number (value : Z) | Boolean (value : bool) | Null.
Definition node := Object.
Definition scalar_name (ty : scalar) := match ty with
 | I8 => "i8" | I16 => "i16" | I32 => "i32"
 | U8 => "u8" | U16 => "u16" | U32 => "u32"
 | F16 => "f16" | F32 => "f32" | F64 => "f64" | Bool => "bool" end.
Definition unary_name (op : unary) := match op with Positive => "+" | Negative => "-" | LogicalNot => "not" | BitNot => "~" end.
Definition binary_name (op : binary) := match op with
 | Plus => "+" | Minus => "-" | Times => "*" | Divide => "/" | Modulo => "%"
 | Equal => "==" | NotEqual => "!=" | Less => "<" | LessEqual => "<="
 | Greater => ">" | GreaterEqual => ">=" | ShiftLeft => "<<" | ShiftRight => ">>"
 | BitAnd => "&" | BitOr => "|" | BitXor => "^" | LogicalAnd => "and" | LogicalOr => "or" | Power => "**" end.
Definition encode_option {A} (f : A -> tree) (x : option A) :=
 match x with None => Null | Some v => f v end.
Definition encode_list {A} (f : A -> tree) (xs : list A) := Sequence (map f xs).
Definition encode_scalar (ty : scalar) := node "$scalar" [("name", Text (scalar_name ty))].
Definition encode_id (id : identifier) := node "Identifier"
 [("name", Text (name id)); ("version", Number (Z.of_nat (version id)))].
Definition encode_param (p : string * option Z) := node "Parameter"
 [("name", Text (fst p)); ("value", encode_option Number (snd p))].
Fixpoint encode_expression (e : expression) : tree :=
 match e with
 | Range lo hi step => node "RangeExpression"
   [("start", encode_expression lo); ("stop", encode_option encode_expression hi);
    ("step", encode_option encode_expression step)]
 | _ => node "Expression" [("value",
   match e with
   | EVar id => encode_id id
   | EParam p v => encode_param (p,v)
   | Constant ty v => node "ConstantLiteral"
     [("value", match v with Integer z => Number z | BooleanValue b => Boolean b | FloatBits bits =>
       node "$float_bits" [("type", Text (scalar_name ty)); ("bits", Number bits)] end);
      ("dtype", encode_scalar ty)]
   | Unary op v => node "UnaryOperator"
     [("op", Text (unary_name op)); ("value", encode_expression v)]
   | Binary a op b => node "BinaryOperator"
     [("left", encode_expression a); ("op", Text (binary_name op)); ("right", encode_expression b)]
   | Select a c b => node "TernaryOperator"
     [("if_true", encode_expression a); ("cond", encode_expression c); ("if_false", encode_expression b)]
   | FusedMultiplyAdd a b c => node "MultiplyAccumulateOperator"
     [("a", encode_expression a); ("b", encode_expression b); ("c", encode_expression c)]
   | Slice a idx => node "ArraySlice"
     [("array", encode_id a); ("indices", encode_list encode_expression idx)]
   | Range _ _ _ => Null
   end)]
 end.
(** SpaDA uses unwrapped operands for send/receive destinations and streams. *)
Definition encode_operand (e : expression) :=
 match encode_expression e with
 | Object _ [("value", v)] => v
 | other => other
 end.
Fixpoint encode_type (ty : dtype) : tree := match ty with
 | Scalar t => encode_scalar t
 | Stream t n => node "StreamType"
   [("element_type", encode_scalar t); ("buffer_size", encode_option encode_expression n)]
 | Array t dims => node "ArrayType"
   [("base_type", encode_type t); ("shape", encode_list encode_expression dims)] end.
Definition encode_typed (v : typed_id) := node "TypedIdentifier"
 [("dtype", encode_type (typ v)); ("identifier", encode_id (ident v))].
Definition encode_grid (g : subgrid) := node "SubgridExpression"
 [("x_range", encode_expression (xrange g)); ("y_range", encode_expression (yrange g))].
Definition encode_field (f : field) := node "FieldDeclaration"
 [("dtype", encode_type (field_type f)); ("field_name", encode_id (field_id f));
  ("is_extern", Boolean (external f))].
Definition encode_hop (p : Z * Z) := node "RoutingHop"
 [("offset", node "$tuple" [("items", Sequence [Number (fst p); Number (snd p)])])].
Definition encode_route (r : routing) := node "RoutingDeclaration"
 [("hops", match route_hops r with AutoHops => Text "auto"
    | Hops hs => encode_list encode_hop hs end);
  ("channel", match route_channel r with AutoChannel => Text "auto"
    | Channel n => encode_expression n end)].
Definition encode_source (s : stream_source) := match s with
 | Relative x y r => node "RelativeStreamDeclaration"
   [("dx", encode_expression x); ("dy", encode_expression y); ("routing", encode_route r)]
 | Multicast x y r => node "MulticastRangeStreamDeclaration"
   [("dx", encode_expression x); ("dy", encode_expression y); ("routing", encode_route r)]
 | ExternalInput r => node "ExternStreamDeclaration"
   [("direction", Text "in"); ("routing", encode_route r)]
 | ExternalOutput r => node "ExternStreamDeclaration"
   [("direction", Text "out"); ("routing", encode_route r)] end.
Definition encode_stream (s : stream_decl) := node "StreamDeclaration"
 [("dtype", encode_type (stream_type s)); ("stream_name", encode_id (stream_id s));
  ("stream", encode_source (source s))].
Definition encode_completion := encode_option (fun id => node "Completion" [("name", encode_id id)]).
Fixpoint encode_statement (s : statement) : tree := match s with
 | Assign dst src => node "AssignmentStatement"
   [("destination", encode_operand dst); ("source", encode_expression src)]
 | Send payload stream done => node "SendStatement"
   [("local_array", encode_operand payload); ("stream_name", encode_operand stream);
    ("completion_name", encode_completion done)]
 | Receive dst stream done => node "ReceiveStatement"
   [("local_array", encode_operand dst); ("stream_name", encode_operand stream);
    ("completion_name", encode_completion done)]
 | Close stream done => node "CloseStatement"
   [("stream_name", encode_operand stream); ("completion_name", encode_completion done)]
 | Foreach ids ranges element stream body done => node "ForeachStatement"
   [("variables", encode_list encode_typed ids); ("parameter_range", encode_list encode_expression ranges);
    ("stream_variable", encode_typed element);
    ("receive_stream", node "ReceiveGenerator" [("stream_name", encode_operand stream)]);
    ("body", encode_list encode_statement body); ("completion_name", encode_completion done)]
 | Map ids ranges body done => node "MapStatement"
   [("variables", encode_list encode_typed ids); ("range_expression", encode_list encode_expression ranges);
    ("body", encode_list encode_statement body); ("completion_name", encode_completion done)]
 | For ids ranges body => node "ForStatement"
   [("variables", encode_list encode_typed ids); ("range_expression", encode_list encode_expression ranges);
    ("body", encode_list encode_statement body)]
 | Async body done => node "AsyncBlock"
   [("body", encode_list encode_statement body); ("completion_name", encode_completion done)]
 | Await id => node "AwaitCompletionStatement" [("completion_name", encode_id id)]
 | AwaitAll => node "AwaitAllStatement" [] end.
Definition block_tag (b : block) : string := match b with
 | Place _ _ _ => "place" | Dataflow _ _ _ => "dataflow" | Compute _ _ _ => "compute"
 | Phase _ => "phase" | MetaFor _ _ _ => "meta" end.
Fixpoint encode_block (b : block) : tree := match b with
 | Place ids g fields => node "PlaceBlock"
   [("variables", encode_list encode_typed ids); ("subgrid", encode_grid g);
    ("statements", encode_list encode_field fields)]
 | Dataflow ids g streams => node "DataflowBlock"
   [("variables", encode_list encode_typed ids); ("subgrid", encode_grid g);
    ("statements", encode_list encode_stream streams)]
 | Compute ids g body => node "ComputeBlock"
   [("variables", encode_list encode_typed ids); ("subgrid", encode_grid g);
    ("statements", encode_list encode_statement body)]
 | Phase body => if existsb (fun b => match b with Phase _ => true | _ => false end) body
   then node "$invalid_nested_phase" [] else node "Phase"
   (map (fun tag => (fst tag, Sequence (fold_right (fun b acc =>
       if String.eqb (block_tag b) (snd tag) then encode_block b :: acc else acc) [] body)))
      [("place", "place"); ("dataflow", "dataflow"); ("compute", "compute");
       ("metaprogramming_blocks", "meta")])
 | MetaFor ids ranges body => node "MetaForBlock"
   [("variables", encode_list encode_typed ids); ("range_expression", encode_list encode_expression ranges);
    ("body", encode_list encode_block body)] end.
Definition encode_argument (a : argument) := node "KernelArgument"
 [("dtype", encode_type (argument_type a)); ("identifier", encode_id (argument_id a));
  ("readonly", Boolean (readonly a)); ("writeonly", Boolean (writeonly a));
  ("compiletime", Boolean (compiletime a))].
Definition encode_kernel (k : kernel) := node "Kernel"
 [("name", Text (kernel_name k)); ("parameters", encode_list encode_param (parameters k));
  ("arguments", encode_list encode_argument (arguments k));
  ("body", encode_list encode_block (blocks k))].

Definition quote := String (Ascii.ascii_of_nat 34) EmptyString.
Definition slash := String (Ascii.ascii_of_nat 92) EmptyString.
Definition hex (n : nat) : ascii := Ascii.ascii_of_nat (if Nat.ltb n 10 then 48+n else 87+n).
Definition escape_char (c : ascii) : string :=
 let n := Ascii.nat_of_ascii c in
 if (Nat.ltb n 32 || Nat.eqb n 34 || Nat.eqb n 92)%bool
 then slash ++ "u00" ++ String (hex (Nat.div n 16)) (String (hex (Nat.modulo n 16)) "")
 else String c "".
Fixpoint escape (s : string) := match s with
 | EmptyString => EmptyString | String c tail => escape_char c ++ escape tail end.
Definition quoted (s : string) := quote ++ escape s ++ quote.
Fixpoint json (t : tree) : string := match t with
 | Null => "null" | Text s => quoted s | Number n => NilZero.string_of_int (Z.to_int n)
 | Boolean b => if b then "true" else "false"
 | Sequence xs => "[" ++ String.concat "," (map json xs) ++ "]"
 | Object tag fields => "{" ++ quoted "$node" ++ ":" ++ quoted tag ++
   String.concat "" (map (fun kv => "," ++ quoted (fst kv) ++ ":" ++ json (snd kv)) fields) ++ "}"
 end.
Definition export (k : kernel) := json (encode_kernel k).
End Spada.
