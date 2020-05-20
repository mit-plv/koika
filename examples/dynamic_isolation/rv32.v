Require Import Koika.Frontend.

Require Import DynamicIsolation.External.
Require Import DynamicIsolation.Interfaces.
Require Import DynamicIsolation.Memory.
Require Import DynamicIsolation.RVCore.
Require Import DynamicIsolation.TrivialCore.

Module Params0 <: CoreParameters.
  Definition core_id := Ob~0.
  Definition initial_pc := EnclaveParams.enclave_base Common.Enclave0.
End Params0.

Module Params1 <: CoreParameters.
  Definition core_id := Ob~1.
  Definition initial_pc := EnclaveParams.enclave_base Common.Enclave1.
End Params1.

Module Core0:= RV32I EnclaveParams Params0.
(* Module Core0_rv32e := RV32E EnclaveParams Params0. *)
(* Module Core1 := EmptyCore External EnclaveParams Params1.  *)
Module Core1:= RV32I EnclaveParams Params1.
Module Mem := WIPMemory.

(* TODO: modularize *)

Module Machine_rv32i := Machine External EnclaveParams Params0 Params1
                        Core0 Core1 Mem.
(*
Module Machine_rv32e := Machine External EnclaveParams Params0 Params1
                        Core0_rv32e Core1 Mem.
*)

Module Package_rv32i.
  Include Machine_rv32i.
  Definition external (rl: rule_name_t) := false.

  Definition circuits :=
    compile_scheduler rules external schedule.

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r;
       koika_ext_fn_types := Sigma;
       koika_rules := rules;
       koika_rule_external := external;
       koika_scheduler := schedule;
       koika_module_name := "rv32" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_ext_fn_names fn := show fn;
                   sp_extfuns := None |};
       ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End Package_rv32i.

(*
Module Package_rv32e.
  Include Machine_rv32e.
  Instance Show_reg_t : Show reg_t := _.

  Definition external (rl: rule_name_t) := false.

  Definition circuits :=
    compile_scheduler rules external schedule.

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r;
       koika_ext_fn_types := Sigma;
       koika_rules := rules;
       koika_rule_external := external;
       koika_scheduler := schedule;
       koika_module_name := "rv32" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_ext_fn_names fn := show fn;
                    sp_extfuns := None |};
       ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.

End Package_rv32e.
*)
