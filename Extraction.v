Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlString Coq.extraction.ExtrOcamlNatInt.

Require SGA.Common
        SGA.Environments
        SGA.TypedSyntax
        SGA.TypeInference
        SGA.SyntaxTools
        SGA.Circuits
        SGA.Interop
        SGA.Demo.

(* This prevents an assertion error: *)
Extraction Inline Circuits.retVal.
(*
  | Bind (sig0, tau, var, ex, body) ->
    let ex0 = compile_expr r sigma rEnv r0 cLog sig0 gamma tau ex clog in
    compile_rule r sigma rEnv r0 cLog ((var, tau)::sig0) (CtxCons (sig0, (var, tau),
      (Obj.magic retVal (assert false (* Proj Args *)) (assert false (* Proj Args *)) (assert false (* Proj Args *))
        (assert false (* Proj Args *)) ex0), gamma)) body ex0.erwc
 *)

Set Extraction KeepSingleton.

Extraction "SGA.ml"
           EqDec.EqDec
           FiniteType.FiniteType Member.mem
           IndexUtils.List_nth
           Environments.ContextEnv Environments.to_list
           Vect.vect_to_list Vect.vect_of_list Vect.Bits.to_nat Vect.index_to_nat Vect.vect_zip
           Syntax.uscheduler
           TypeInference.type_action TypeInference.type_rule TypeInference.type_scheduler
           SyntaxTools.action_mentions_var SyntaxTools.member_mentions_shadowed_binding
           Circuits.compile_scheduler
           Interop.sga_package_t Interop.circuit_package_t Interop.sim_package_t
           Interop.struct_of_list Interop.struct_to_list
           Interop.compile_sga_package
           Demo.demo_packages.
