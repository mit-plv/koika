Require Import Koika.ExtractionSetup.

Require Koika.Common
        Koika.Environments
        Koika.TypedSyntax
        Koika.TypeInference
        Koika.TypedSyntaxTools
        Koika.Circuits
        Koika.Interop.

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
           Circuits.lco_opt_compose Circuits.opt_constprop Circuits.opt_muxelim
           Interop.koika_package_t Interop.circuit_package_t Interop.sim_package_t Interop.verilog_package_t Interop.interop_package_t
           Interop.struct_of_list Interop.struct_to_list
           Interop.compile_koika_package.
