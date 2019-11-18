Require Export Coq.extraction.Extraction.
From Coq.extraction Require Export ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt ExtrOcamlZInt.

Require Koika.Circuits
        Koika.Types.

(* The following commands work around problems due to incorrect extraction: *)
Extraction Inline Koika.Circuits.retVal.
Extraction Inline Types.argTypes Types.argSizes.

Extract Constant Vect.index => int.
Extract Inductive Vect.index' => int [ "0" "Pervasives.succ" ]
  "(fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))".
Extract Constant Vect.index_of_nat => "fun sz x -> if x < sz then Some x else None".
Extract Constant Vect.index_to_nat => "fun _ x -> x".
Extract Constant Vect.largest_index => "fun x -> x".

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
Extraction Implicit TypedSyntaxTools.is_const_zero [R Sigma sig tau].
