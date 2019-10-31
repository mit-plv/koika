Require Import Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlString Coq.extraction.ExtrOcamlNatInt.

Require Koika.Common
        Koika.Environments
        Koika.TypedSyntax
        Koika.TypeInference
        Koika.TypedSyntaxTools
        Koika.Circuits
        Koika.Interop
        Koika.Demo.

(* These prevent assertion errors: *)
Extraction Inline Circuits.retVal.
Extraction Inline Types.argTypes Types.argSizes.
(*
  CBinop ((PrimTyped.Concat ((sub width sz0),
    (type_sz
      (vect_hd 0
        (Obj.magic argTypes (assert false (* Proj Args *))
          (PrimSignatures.coq_Sigma1 (PrimTyped.Bits1 (PrimTyped.ZExtL
            (sz0, width))))))))), (CConst

  | Bind (sig0, tau, var, ex, body) ->
    let ex0 = compile_expr r sigma rEnv r0 cLog sig0 gamma tau ex clog in
    compile_rule r sigma rEnv r0 cLog ((var, tau)::sig0) (CtxCons (sig0, (var, tau),
      (Obj.magic retVal (assert false (* Proj Args *)) (assert false (* Proj Args *)) (assert false (* Proj Args *))
        (assert false (* Proj Args *)) ex0), gamma)) body ex0.erwc
 *)

Set Extraction KeepSingleton.

Extraction "extracted.ml"
           EqDec.EqDec
           FiniteType.FiniteType Member.mem Member.mmap
           IndexUtils.List_nth
           Environments.ContextEnv Environments.to_list
           Vect.vect_to_list Vect.vect_of_list Vect.Bits.to_nat Vect.index_to_nat Vect.vect_zip
           Syntax.uscheduler
           Desugaring.desugar_action
           TypeInference.type_action TypeInference.type_rule TypeInference.type_scheduler
           TypedSyntaxTools.action_mentions_var TypedSyntaxTools.member_mentions_shadowed_binding
           TypedSyntaxTools.action_footprint
           Circuits.compile_scheduler
           Interop.koika_package_t Interop.circuit_package_t Interop.sim_package_t Interop.verilog_package_t Interop.demo_package_t
           Interop.struct_of_list Interop.struct_to_list
           Interop.compile_koika_package
           Demo.demo_packages.
