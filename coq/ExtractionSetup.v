Require Export Coq.extraction.Extraction.
From Coq.extraction Require Export ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt ExtrOcamlZInt.

Require Koika.Circuits
        Koika.Types.

(* The following commands work around problems due to incorrect extraction: *)
Extraction Inline Koika.Circuits.retVal.
Extraction Inline Types.argTypes Types.argSizes.

(* This command makes extraction a bit more predictable *)
Global Set Extraction KeepSingleton.
