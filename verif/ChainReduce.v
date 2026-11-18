From Stdlib Require Import ZArith List String.
From SpatialCSL Require Import SpadaIR.
Import ListNotations Spada.
Open Scope string_scope.
Open Scope Z_scope.

(** Chain reduction from the SpaDA paper (its [N] read as [K]).
    Proof: ../kahn/ChainReduceProof.v. *)
Module ChainReduce.
Definition xy := [coord "x"; coord "y"].
Definition row (lo hi : Z) := Grid (interval lo hi) (Range (int 0) None None).
Definition strided (lo hi step : Z) :=
  Grid (Range (int lo) (Some (int hi)) (Some (int step))) (Range (int 0) None None).
Definition at_x (x : Z) := Grid (Range (int x) None None) (Range (int 0) None None).
Definition a_k := Slice (named "a") [var "k"].
Definition west (s : string) :=
  StreamDecl (Stream F32 None) (named s) (Relative (int (-1)) (int 0) auto_route).
(** One chain step: add the incoming partial sum, then forward it. *)
Definition relay (K : Z) (input output : string) :=
  [Foreach [coord "k"] [interval 0 K] (Typed (Scalar F32) (named "x")) (var input)
    [Assign a_k (Binary a_k Plus (var "x")); Send a_k (var output) None] None].

Definition kernel (K : Z) : Spada.kernel := Kernel "chain_reduce" [] [
  Argument (Array (Stream F32 (Some (int K))) [int K]) (named "a_in") true false false;
  Argument (Array (Stream F32 (Some (int K))) [int 1]) (named "out") false true false
] [
  Place xy (row 0 K) [Field (Array (Scalar F32) [int K]) (named "a") false];
  (* Phase 1: read argument stream *)
  Phase [Compute xy (row 0 K)
    [Receive (var "a") (Slice (named "a_in") [var "x"]) (Some (named "got"));
     Await (named "got")]];
  (* Phase 2: reduction *)
  Phase [
    Dataflow xy (row 0 K) [west "red"; west "blue"];
    Compute xy (at_x (K-1))
      [Send (var "a") (Select (var "red")
         (Binary (Binary (int (K-1)) Modulo (int 2)) Equal (int 0)) (var "blue")) None];
    Compute xy (strided 1 (K-1) 2) (relay K "red" "blue");
    Compute xy (strided 2 (K-1) 2) (relay K "blue" "red");
    Compute xy (at_x 0)
      [Foreach [coord "k"] [interval 0 K] (Typed (Scalar F32) (named "x")) (var "blue")
         [Assign a_k (Binary a_k Plus (var "x"))] None;
       Send (var "a") (Slice (named "out") [var "x"]) None]]].

Definition K4 := kernel 4.
Definition K4_json := export K4.
End ChainReduce.
