Require Export Coq.extraction.Extraction.
From Coq.extraction Require Export ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt ExtrOcamlZInt.

Require Koika.Circuits
        Koika.Types.

(* The following commands work around problems due to incorrect extraction: *)
Extraction Inline Koika.Circuits.retVal.
Extraction Inline Types.argTypes Types.argSizes.

(* This command makes extraction a bit more predictable *)
Global Set Extraction KeepSingleton.

(* The following commands make these functions much easier to use from the OCaml
   side by removing unnecessary arguments. *)
Extraction Implicit TypedSyntaxTools.AnyAction [sig tau].
Extraction Implicit TypedSyntaxTools.action_footprint [R Sigma sig tau].
Extraction Implicit TypedSyntaxTools.action_footprint' [R Sigma sig tau].
Extraction Implicit TypedSyntaxTools.action_mentions_var [R Sigma sig tau].
Extraction Implicit TypedSyntaxTools.action_mentions_shadowed_var [R Sigma sig tau].
Extraction Implicit TypedSyntaxTools.existsb_subterm [R Sigma sig tau].
