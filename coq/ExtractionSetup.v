(*! Interop | Custom extraction settings (also used by external Kôika programs !*)
Require Export Coq.extraction.Extraction.
From Coq.extraction Require Export ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt ExtrOcamlZInt.

Require Koika.Types
        Koika.TypedSyntaxFunctions
        Koika.CircuitGeneration
        Koika.CircuitOptimization.

(* The following commands work around problems due to incorrect extraction: *)
Extraction Inline Koika.CircuitGeneration.retVal.
Extraction Inline Types.argSigs.

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
Extraction Implicit CircuitOptimization.unannot [CR CSigma rwdata].
Extraction Implicit CircuitOptimization.lco_iter [csigma].
Extraction Implicit CircuitOptimization.lco_compose [csigma].
Extraction Implicit CircuitOptimization.lco_constprop [csigma].
Extraction Implicit CircuitOptimization.lco_identical [csigma].
Extraction Implicit CircuitOptimization.lco_muxelim [csigma].
Extraction Implicit CircuitOptimization.lco_simplify [csigma].
Extraction Implicit CircuitOptimization.lco_all [csigma].
Extraction Implicit CircuitOptimization.lco_all_iterated [csigma].
Extraction Implicit CircuitOptimization.unannot [CR CSigma rwdata].
Extraction Implicit TypedSyntaxFunctions.unannot [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.AnyAction [sig tau].
Extraction Implicit TypedSyntaxFunctions.action_footprint [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.action_footprint' [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.action_mentions_var [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.annotate_action_register_histories [Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.annotate_rule_register_histories [Sigma].
Extraction Implicit TypedSyntaxFunctions.compute_register_histories [Sigma].
Extraction Implicit TypedSyntaxFunctions.rule_max_log_size [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.action_mentions_shadowed_var [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.existsb_subterm [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.returns_zero [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.is_pure [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.is_tt [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.action_type [R Sigma sig tau].
Extraction Implicit TypedSyntaxFunctions.interp_arithmetic [R Sigma sig tau].
Extraction Implicit LoweredSyntaxFunctions.action_footprint [R Sigma sig tau].
Extraction Implicit LoweredSyntaxFunctions.action_footprint' [R Sigma sig tau].
