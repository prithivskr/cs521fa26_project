From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From SpatialCSL Require Import Summa.
Extraction Language OCaml.
Extraction "_build/summa_generated.ml" Summa.baseline_json Summa.optimized_json.
