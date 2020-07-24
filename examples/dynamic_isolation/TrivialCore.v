Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import dynamic_isolation.External.
Require Import dynamic_isolation.Interfaces.
Require Import dynamic_isolation.Interp.

Module EmptyCore (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters)
                 <: Core_sig External Params CoreParams.
  Import Common.

  Inductive private_reg_t : Type :=
  | Foo | Bar.

  Definition R_private (idx: private_reg_t) : type :=
    match idx with
    | _ => bits_t 1
    end.

  Definition r_private (idx: private_reg_t) : R_private idx :=
    match idx with
    | _ => Bits.zero
    end.

  Instance FiniteType_private_reg_t : FiniteType private_reg_t := _.

  Definition private_params : private_module_sig :=
    {| _private_reg_t := private_reg_t;
       _R_private := R_private;
       _r_private := r_private;
       _FiniteType_private_reg_t := FiniteType_private_reg_t
    |}.

  Definition reg_t := @Core_Common.reg_t private_params.
  Definition r := @Core_Common.r CoreParams.core_id CoreParams.initial_pc private_params.
  Definition R := @Core_Common.R private_params.
  Definition rule := @Core_Common.rule private_params External.ext.
  Definition sigma := @Core_Common.sigma External.ext.
  Definition Sigma := @Core_Common.Sigma External.ext.
  Definition ext_fn_t := @Core_Common.ext_fn_t External.ext.

  Inductive rule_name_t' : Type := DoNothing | StillDoNothing.
  Definition rule_name_t := rule_name_t'.

  (* TOOD: Silly workaround due to extraction issues: https://github.com/coq/coq/issues/12124 *)
  Definition do_nothing : uaction reg_t ext_fn_t :=
    {{ pass }}.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | _ => tc_rule R Sigma do_nothing
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t := done.

  Instance FiniteType_reg_t : FiniteType reg_t := @Core_Common.FiniteType_reg_t private_params.

  (* TODO: clean up instantiation *)
  Parameter output_correctness :
    @Core_Common.P_output_correctness CoreParams.core_id CoreParams.initial_pc
                                      private_params External.ext
                                      rule_name_t rules schedule.
  Parameter correctness : @Core_Common.P_correctness CoreParams.core_id CoreParams.initial_pc
                                                     private_params External.ext
                                                     rule_name_t rules schedule.
  Parameter compliance : @Core_Common.P_compliance CoreParams.core_id CoreParams.initial_pc
                                                   private_params External.ext
                                                   rule_name_t rules schedule.

End EmptyCore.
