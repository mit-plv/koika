Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlString Coq.extraction.ExtrOcamlNatInt.

Require SGA.Common SGA.Environments SGA.TypedSyntax SGA.TypeInference SGA.Circuits SGA.Interop SGA.Demo.

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

Extraction "SGA.ml"
           Common.EqDec
           Environments.FiniteType Environments.mem Environments.ContextEnv
           Syntax.uscheduler Syntax.urule Syntax.uexpr
           TypeInference.type_scheduler
           Circuits.compile_scheduler
           Primitives.prim_Sigma
           Interop.interop_fn_t

           Interop.VerilogPackage
           Environments.to_list Vect.vect_to_list Vect.Bits.to_nat Vect.index_to_nat
           Demo.Collatz.package.
