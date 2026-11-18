From Stdlib Require Import ZArith List String.
From SpatialCSL Require Import SpadaIR ChainReduce.
Import ListNotations Spada.
Open Scope string_scope.
Open Scope Z_scope.

(** Receive-first relay: avoids a SpaDA switch-ordering bug that stalls
    [ChainReduce] in the simulator. Proof: ChainReduceProof.v. *)
Module ChainReduceRecvFirst.
Import ChainReduce.
Definition t_k := Slice (named "t") [var "k"].
Definition relay (K : Z) (input output : string) :=
  [Receive (var "t") (var input) (Some (named "r"));
   Await (named "r");
   Map [coord "k"] [interval 0 K] [Assign a_k (Binary a_k Plus t_k)] None;
   Send (var "a") (var output) None].

Definition kernel (K : Z) : Spada.kernel := Kernel "chain_reduce" [] [
  Argument (Array (Stream F32 (Some (int K))) [int K]) (named "a_in") true false false;
  Argument (Array (Stream F32 (Some (int K))) [int 1]) (named "out") false true false
] [
  Place xy (row 0 K) [Field (Array (Scalar F32) [int K]) (named "a") false;
                      Field (Array (Scalar F32) [int K]) (named "t") false];
  Phase [Compute xy (row 0 K)
    [Receive (var "a") (Slice (named "a_in") [var "x"]) (Some (named "got"));
     Await (named "got")]];
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
End ChainReduceRecvFirst.
