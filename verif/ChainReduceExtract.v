From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From SpatialCSL Require Import ChainReduce ChainReduceVariant.
Extraction Language OCaml.
Extraction "_build/chain_generated.ml" ChainReduce.K4_json ChainReduceRecvFirst.K4_json.
