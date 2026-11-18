From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From SpatialCSL Require Import SpadaIR Summa.
Extraction Language OCaml.
(** Dimension-parametric generator (for scaling sweeps). [nat] extracts to
    OCaml [int], so the driver passes P, Mt, Kt, Nt directly. *)
Definition summa_json (p m k n : nat) (cached : bool) : String.string :=
  Spada.export (Summa.lower (Summa.Gemm (Summa.Dims p m k n)
    (if cached then Summa.Cached else Summa.Baseline))).
Extraction "_build/summa_generated.ml" Summa.baseline_json Summa.optimized_json summa_json.
