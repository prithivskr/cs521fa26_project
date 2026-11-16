From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From SpatialCSL Require Import SpadaArithmetic.
Extraction Language OCaml.
Extraction "_build/spada_numeric.ml" ReferenceArithmetic.binary_reference ReferenceArithmetic.fma_reference.
