From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From SpatialCSL Require Import Examples.
Extraction Language OCaml.
(** Keep Z in its exact binary representation; extracting it to machine ints
    would silently overflow when multiplying two u32 values. *)
Extraction "_build/generated.ml" example_files.
