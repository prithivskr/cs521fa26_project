From Stdlib Require Import ZArith List String.
From SpatialCSL Require Import SpadaIR.
Import ListNotations Spada.
Open Scope string_scope.
Open Scope Z_scope.


Definition xy := [coord "x"; coord "y"].
Definition grid2 := rectangle 2 1.
Definition left := Grid (Range (int 0) None None) (Range (int 0) None None).
Definition right := Grid (Range (int 1) None None) (Range (int 0) None None).
Definition farray (n : Z) := Array (Scalar F32) [int n].
Definition index (s : string) (i : expression) := Slice (named s) [i].
Definition buf (s : string) := Field (farray 4) (named s) true.
Definition east := StreamDecl (Stream F32 (Some (int 4))) (named "east")
  (Relative (int 1) (int 0) auto_route).

(** Genuine routed communication, not a PE-local simulation. *)
Definition ping : kernel := Kernel "rocq_ping" [] [] [
  Place xy grid2 [buf "a"; buf "b"];
  Dataflow xy grid2 [east];
  Phase [
    Compute xy left [Send (var "a") (var "east") (Some (named "sent")); Await (named "sent")];
    Compute xy right [Receive (var "b") (var "east") None]
  ]].
Definition ping_json := export ping.

Definition scatter := StreamDecl (Stream F32 (Some (int 4))) (named "scatter")
  (Multicast (interval 1 3) (int 0) auto_route).
Definition multicast : kernel := Kernel "rocq_multicast" [] [] [
  Place xy (rectangle 3 1) [buf "a"; buf "b"];
  Dataflow xy (rectangle 3 1) [scatter];
  Phase [
    Compute xy left [Send (var "a") (var "scatter") None];
    Compute xy (Grid (interval 1 3) (Range (int 0) None None))
      [Receive (var "b") (var "scatter") None]
  ]].
Definition multicast_json := export multicast.

(** Two phases, dynamic indexed arithmetic, map/for/async/foreach/completions. *)
Definition pipeline : kernel := Kernel "rocq_pipeline" [] [] [
  Place xy grid2 [buf "a"; buf "b"];
  Dataflow xy grid2 [east];
  Phase [
    Compute xy left [
      Async [For [coord "k"] [interval 0 4]
        [Assign (index "a" (var "k")) (Binary (index "a" (var "k")) Times (Constant F32 (Integer 2)))]]
        (Some (named "prepared"));
      Await (named "prepared"); Send (var "a") (var "east") None];
    Compute xy right [Foreach [coord "k"] [interval 0 4]
      (Typed (Scalar F32) (named "value")) (var "east")
      [Assign (index "b" (var "k")) (var "value")] None]
  ];
  Phase [Compute xy grid2 [Map [coord "k"] [interval 0 4]
    [Assign (index "b" (var "k")) (Binary (index "b" (var "k")) Plus (Constant F32 (Integer 1)))] None]]
].
Definition pipeline_json := export pipeline.

(** Unbounded host streaming, including range-free foreach. *)
Definition host_streaming : kernel := Kernel "rocq_streaming" [] [
  Argument (Stream F32 None) (named "input") true false false;
  Argument (Stream F32 None) (named "output") false true false
] [
  Phase [Compute xy (rectangle 1 1) [
    Foreach [] [] (Typed (Scalar F32) (named "value")) (var "input")
      [Send (var "value") (var "output") None] None
  ]]
].
Definition host_json := export host_streaming.

(** A data-only fixture exercises every public concrete constructor, including
    features that cannot all coexist in one well-formed executable kernel. *)
Definition every_expression := [
  var "a"; Constant Bool (BooleanValue true); Constant F32 (FloatBits 1065353216); EParam "N" (Some 4);
  Unary Negative (int 3); Binary (int 2) ShiftLeft (int 1);
  Select (var "a") (Binary (int 0) Equal (int 0)) (var "b");
  FusedMultiplyAdd (var "a") (var "b") (var "c");
  Slice (named "a") [Range (int 0) (Some (int 4)) (Some (int 2))]
].
Definition manual := Route (Hops [(1,0)%Z]) (Channel (int 0)).
Definition fixtures : list tree :=
  map encode_scalar [I8; I16; I32; U8; U16; U32; F16; F32; F64; Bool] ++
  map encode_expression every_expression ++
  map (fun op => encode_expression (Binary (int 1) op (int 2)))
    [Plus; Minus; Times; Divide; Modulo; Equal; NotEqual; Less; LessEqual;
     Greater; GreaterEqual; ShiftLeft; ShiftRight; BitAnd; BitOr; BitXor; LogicalAnd; LogicalOr; Power] ++
  [encode_expression (Unary Positive (int 2));
   encode_expression (Unary LogicalNot (int 2)); encode_expression (Unary BitNot (int 2));
   encode_kernel ping; encode_kernel pipeline; encode_kernel multicast;
   encode_kernel host_streaming;
   encode_type (Array (Stream F32 (Some (int 4))) [int 2; int 2]);
   encode_source (Relative (int 1) (int 0) manual);
   encode_source (ExternalInput auto_route); encode_source (ExternalOutput auto_route);
   encode_statement (Close (var "east") (Some (named "closed")));
   encode_statement AwaitAll;
   encode_block (MetaFor [coord "stage"] [interval 0 2] [Phase []]);
   encode_argument (Argument (Scalar I32) (named "alpha") false false true)].
Definition fixtures_json := json (Sequence fixtures).

Definition channel_zero := Route (Hops [(1,0)]) (Channel (int 0)).
Definition epochs : kernel := Kernel "rocq_epochs" [] [] [
 Place xy grid2 [buf "a"; buf "b"];
 Dataflow xy grid2 [
   StreamDecl (Stream F32 None) (named "first") (Relative (int 1) (int 0) channel_zero);
   StreamDecl (Stream F32 None) (named "second") (Relative (int 1) (int 0) channel_zero)];
 Phase [
   Compute xy left [Send (var "a") (var "first") None; Close (var "first") None;
     Send (var "a") (var "second") None; Close (var "second") None];
   Compute xy right [Receive (var "b") (var "first") None; Close (var "first") None;
     Receive (var "b") (var "second") None; Close (var "second") None]]].
Definition epochs_json := export epochs.
Definition meta : kernel := Kernel "rocq_meta" [("N",Some 4)] [] [
 Place xy (rectangle 1 1) [buf "a"];
 MetaFor [coord "stage"] [interval 0 2] [
   Phase [Compute xy (rectangle 1 1) [For [coord "k"]
     [Range (int 0) (Some (EParam "N" None)) None]
     [Assign (index "a" (var "k")) (Constant F32 (Integer 1))]]]]].
Definition meta_json := export meta.
Definition bounded_host : kernel := Kernel "rocq_bounded" [] [
 Argument (Array (Stream F32 (Some (int 4))) [int 2; int 1]) (named "input") true false false;
 Argument (Array (Stream F32 (Some (int 4))) [int 2; int 1]) (named "output") false true false
] [
 Place xy grid2 [buf "a"];
 Phase [Compute xy grid2 [
   Receive (var "a") (Slice (named "input") [var "x";var "y"]) None;
   Send (var "a") (Slice (named "output") [var "x";var "y"]) None]]].
Definition bounded_json := export bounded_host.

Definition external_streams : kernel := Kernel "rocq_extern" [] [] [
 Dataflow xy (rectangle 1 1) [
   StreamDecl (Stream F32 None) (named "input") (ExternalInput auto_route);
   StreamDecl (Stream F32 None) (named "output") (ExternalOutput auto_route)];
 Phase [Compute xy (rectangle 1 1) [Foreach [] []
   (Typed (Scalar F32) (named "value")) (var "input")
   [Send (var "value") (var "output") None] None]]].
Definition external_json := export external_streams.
