Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlString Coq.extraction.ExtrOcamlNatInt.

Require Import SGA.Common SGA.Environments SGA.TypedSyntax SGA.Demo.

Extract Inductive list => "list" [ "[]" "(::)" ].
(* This prevents an assertion error: *)
Extraction Inline Circuits.retVal.
(*
  | Bind (sig0, tau, var, ex, body) ->
    let ex0 = compile_expr r sigma rEnv r0 cLog sig0 gamma tau ex clog in
    compile_rule r sigma rEnv r0 cLog ((var, tau)::sig0) (CtxCons (sig0, (var, tau),
      (Obj.magic retVal (assert false (* Proj Args *)) (assert false (* Proj Args *)) (assert false (* Proj Args *))
        (assert false (* Proj Args *)) ex0), gamma)) body ex0.erwc
 *)

Extraction "sga.ml" to_list vect_to_list Bits.to_nat index_to_nat Collatz.package.
