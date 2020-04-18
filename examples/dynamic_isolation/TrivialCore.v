Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import DynamicIsolation.External.
Require Import DynamicIsolation.Interfaces.


Module EmptyCore (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters) 
                 <: Core_sig External Params CoreParams.
  Import Common.

  Inductive internal_reg_t' : Type := .
  Definition internal_reg_t := internal_reg_t'.
  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with end.

  Inductive reg_t :=
  | core_id
  | pc
  | toIMem (state: MemReq.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) : type :=
   match idx with
   | core_id => bits_t 1
   | pc => addr_t
   | toIMem r => MemReq.R r
   | toDMem r => MemReq.R r
   | fromIMem  r => MemResp.R r
   | fromDMem  r => MemResp.R r
   | internal r => R_internal r
   end.

  Definition r idx : R idx :=
    match idx with
    | core_id => CoreParams.core_id
    | pc => Bits.zero
    | toIMem s => MemReq.r s
    | fromIMem s => MemResp.r s
    | toDMem s => MemReq.r s
    | fromDMem s => MemResp.r s
    | internal s => r_internal s
    end.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  Definition sigma := External.sigma.

  Inductive rule_name_t' : Type := .
  Definition rule_name_t := rule_name_t'.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t := done.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.

End EmptyCore.
