Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import dynamic_isolation.External.
Require Import dynamic_isolation.Interfaces.
Require Import dynamic_isolation.Interp.

Module EmptyCore (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters)
                 <: Core_sig External Params CoreParams.
  Import Common.

  Inductive internal_reg_t : Type :=
  | Foo | Bar.

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | _ => bits_t 1
    end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with
    | _ => Bits.zero
    end.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.

  Definition internal_params : internal_module_sig :=
    {| _internal_reg_t := internal_reg_t;
       _R_internal := R_internal;
       _r_internal := r_internal;
       _FiniteType_internal_reg_t := FiniteType_internal_reg_t
    |}.

  Definition reg_t := @Core_Common.reg_t internal_params.
  Definition r := @Core_Common.r CoreParams.core_id CoreParams.initial_pc internal_params.
  Definition R := @Core_Common.R internal_params.
  Definition rule := @Core_Common.rule internal_params External.ext.
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

  Instance FiniteType_reg_t : FiniteType reg_t := @Core_Common.FiniteType_reg_t internal_params.

  (* TODO: clean up instantiation *)
  Parameter output_correctness :
    @Core_Common.P_output_correctness CoreParams.core_id CoreParams.initial_pc
                                      internal_params External.ext
                                      rule_name_t rules schedule.
  Parameter correctness : @Core_Common.P_correctness CoreParams.core_id CoreParams.initial_pc
                                                     internal_params External.ext
                                                     rule_name_t rules schedule.
  Parameter compliance : @Core_Common.P_compliance CoreParams.core_id CoreParams.initial_pc
                                                   internal_params External.ext
                                                   rule_name_t rules schedule.

End EmptyCore.
