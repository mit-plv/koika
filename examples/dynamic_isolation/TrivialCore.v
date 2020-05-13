Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import DynamicIsolation.External.
Require Import DynamicIsolation.Interfaces.

Module EmptyCore (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters)
                 <: Core_sig External Params CoreParams.
  Import Common.

  Inductive internal_reg_t' : Type :=
  | Foo | Bar.

  Definition internal_reg_t := internal_reg_t'.

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | _ => bits_t 1
    end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with
    | _ => Bits.zero
    end.

  Inductive reg_t :=
  | core_id
  | toIMem (state: MemReq.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | rf (state: Rf.reg_t)
  | purge
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) : type :=
   match idx with
   | core_id => bits_t 1
   | toIMem r => MemReq.R r
   | toDMem r => MemReq.R r
   | fromIMem  r => MemResp.R r
   | fromDMem  r => MemResp.R r
   | rf r => Rf.R r 
   | purge => enum_t purge_state
   | internal r => R_internal r
   end.

  Definition r idx : R idx :=
    match idx with
    | core_id => CoreParams.core_id
    | toIMem s => MemReq.r s
    | fromIMem s => MemResp.r s
    | toDMem s => MemReq.r s
    | fromDMem s => MemResp.r s
    | rf r => Rf.r r 
    | purge => value_of_bits (Bits.zero)
    | internal s => r_internal s
    end.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)

  Inductive rule_name_t' : Type := DoNothing | StillDoNothing.
  Definition rule_name_t := rule_name_t'.

  (* TOOD: Silly workaround due to extraction issues: https://github.com/coq/coq/issues/12124 *)
  Definition do_nothing : uaction reg_t ext_fn_t :=
    {{ pass  }}.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | _ => tc_rule R Sigma do_nothing
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t := done.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.

End EmptyCore.
