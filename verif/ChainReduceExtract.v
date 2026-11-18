From Stdlib Require Import ZArith String Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From SpatialCSL Require Import SpadaIR ChainReduce ChainReduceVariant.
Extraction Language OCaml.
(** K-parametric generator for the receive-first kernel (for scaling sweeps).
    [nat] extracts to OCaml [int], so the driver can pass K directly. *)
Definition recvfirst_json (K : nat) : string :=
  Spada.export (ChainReduceRecvFirst.kernel (Z.of_nat K)).
Extraction "_build/chain_generated.ml"
  ChainReduce.K4_json ChainReduceRecvFirst.K4_json recvfirst_json.
