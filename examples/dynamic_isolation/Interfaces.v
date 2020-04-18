Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import DynamicIsolation.Lift.
Require Import DynamicIsolation.Tactics.
Require Import DynamicIsolation.Scoreboard.

Definition post_t := unit.
Definition var_t := string.
Definition fn_name_t := string.

(* Our machine consists of two cores, a security monitor, a memory hierarchy, and external memory modules.
 * We have a well-defined interface to each component.
 *)

Module Common.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := [("byte_en" , bits_t 4);
                         ("addr"     , bits_t 32);
                         ("data"     , bits_t 32)] |}.
  Definition mem_resp :=
    {| struct_name := "mem_resp";
       struct_fields := [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)] |}.

  Module FifoMemReq <: Fifo.
    Definition T:= struct_t mem_req.
  End FifoMemReq.
  Module MemReq := Fifo1Bypass FifoMemReq.

  Module FifoMemResp <: Fifo.
    Definition T:= struct_t mem_resp.
  End FifoMemResp.
  Module MemResp := Fifo1 FifoMemResp.

  Instance FiniteType_MemReq : FiniteType MemReq.reg_t := _.
  Instance FiniteType_MemResp : FiniteType MemResp.reg_t := _.

  Definition addr_t := bits_t 32.
  Definition data_t := bits_t 32.

  (* Alignment *)
  Definition addr_index_t := bits_t 30.

  Definition initial_mem_t := addr_index_t -> data_t.

  Definition mem_input :=
    {| struct_name := "mem_input";
       struct_fields := [("get_ready", bits_t 1);
                        ("put_valid", bits_t 1);
                        ("put_request", struct_t mem_req)] |}.

  Definition mem_output :=
    {| struct_name := "mem_output";
       struct_fields := [("get_valid", bits_t 1);
                        ("put_ready", bits_t 1);
                        ("get_response", struct_t mem_resp)] |}.

End Common.

Module Type EnclaveParameters.

End EnclaveParameters.

Module Type CoreParameters.
  Parameter core_id : bits_t 1.
End CoreParameters.

Module Type External_sig.
  Parameter ext_fn_t : Type.
  Parameter Sigma : ext_fn_t -> ExternalSignature.
  Parameter sigma : (forall fn: ext_fn_t, Sig_denote (Sigma fn)).
  Parameter ext_fn_specs : ext_fn_t -> ext_fn_spec.

End External_sig.

Module Type Core_sig (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters).
  Import Common.
  Parameter internal_reg_t : Type.
  Parameter R_internal : internal_reg_t -> type.
  Parameter r_internal : forall (idx: internal_reg_t), R_internal idx.
  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

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


  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  Definition sigma := External.sigma.

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Axiom schedule : Syntax.scheduler pos_t rule_name_t.

End Core_sig.

Module SecurityMonitor (External: External_sig) (Params: EnclaveParameters).
  Inductive internal_reg_t := .
  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with end.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.

  Import Common.

  Inductive reg_t : Type :=
  | fromCore0_IMem (state: MemReq.reg_t)
  | fromCore0_DMem (state: MemReq.reg_t)
  | toCore0_IMem (state: MemResp.reg_t)
  | toCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | fromCore1_IMem (state: MemReq.reg_t)
  | fromCore1_DMem (state: MemReq.reg_t)
  | toCore1_IMem (state: MemResp.reg_t)
  | toCore1_DMem (state: MemResp.reg_t)
  (* SM <-> Mem *)
  | toMem0_IMem (state: MemReq.reg_t)
  | toMem0_DMem (state: MemReq.reg_t)
  | toMem1_IMem (state: MemReq.reg_t)
  | toMem1_DMem (state: MemReq.reg_t)
  | fromMem0_IMem (state: MemResp.reg_t)
  | fromMem0_DMem (state: MemResp.reg_t)
  | fromMem1_IMem (state: MemResp.reg_t)
  | fromMem1_DMem (state: MemResp.reg_t)
  | internal (idx: internal_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | fromCore0_IMem st => MemReq.R st
    | fromCore0_DMem st => MemReq.R st
    | toCore0_IMem st => MemResp.R st
    | toCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | fromCore1_IMem st => MemReq.R st
    | fromCore1_DMem st => MemReq.R st
    | toCore1_IMem st => MemResp.R st
    | toCore1_DMem st => MemResp.R st
    (* SM <-> Mem *)
    | toMem0_IMem st => MemReq.R st
    | toMem0_DMem st => MemReq.R st
    | toMem1_IMem st => MemReq.R st
    | toMem1_DMem st => MemReq.R st
    | fromMem0_IMem st => MemResp.R st
    | fromMem0_DMem st => MemResp.R st
    | fromMem1_IMem st => MemResp.R st
    | fromMem1_DMem st => MemResp.R st
    | internal st => R_internal st
    end.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition Sigma := External.Sigma.
  Definition ext_fn_t := External.ext_fn_t.
  Definition state := env_t ContextEnv (fun idx : reg_t => R idx).

  (* Placeholder rule; do nothing *)
  Definition forward : uaction reg_t ext_fn_t :=
    {{ (when (fromCore0_IMem.(MemReq.can_deq)() &&
              toMem0_IMem.(MemReq.can_enq)()) do
         let req := fromCore0_IMem.(MemReq.deq)() in
         toMem0_IMem.(MemReq.enq)(req)
       );
       (when (fromCore1_IMem.(MemReq.can_deq)() &&
              toMem1_IMem.(MemReq.can_enq)()) do
         let req := fromCore1_IMem.(MemReq.deq)() in
         toMem1_IMem.(MemReq.enq)(req)
       );
       (when (fromCore0_DMem.(MemReq.can_deq)() &&
              toMem0_DMem.(MemReq.can_enq)()) do
         let req := fromCore0_DMem.(MemReq.deq)() in
         toMem0_DMem.(MemReq.enq)(req)
       );
       (when (fromCore1_DMem.(MemReq.can_deq)() &&
              toMem1_DMem.(MemReq.can_enq)()) do
         let req := fromCore1_DMem.(MemReq.deq)() in
         toMem1_DMem.(MemReq.enq)(req)
       );
       (when (fromMem0_IMem.(MemResp.can_deq)() &&
              toCore0_IMem.(MemResp.can_enq)()) do
         let req := fromMem0_IMem.(MemResp.deq)() in
         toCore0_IMem.(MemResp.enq)(req)
       );
       (when (fromMem1_IMem.(MemResp.can_deq)() &&
              toCore1_IMem.(MemResp.can_enq)()) do
         let req := fromMem1_IMem.(MemResp.deq)() in
         toCore1_IMem.(MemResp.enq)(req)
       );
       (when (fromMem0_DMem.(MemResp.can_deq)() &&
              toCore0_DMem.(MemResp.can_enq)()) do
         let req := fromMem0_DMem.(MemResp.deq)() in
         toCore0_DMem.(MemResp.enq)(req)
       );
       (when (fromMem1_DMem.(MemResp.can_deq)() &&
              toCore1_DMem.(MemResp.can_enq)()) do
         let req := fromMem1_DMem.(MemResp.deq)() in
         toCore1_DMem.(MemResp.enq)(req)
       )
    }}.

  Definition tc_forward := tc_rule R Sigma forward <: rule R Sigma.

  Inductive rule_name_t := | Forward.

  Definition rules (rl : rule_name_t) : rule R Sigma :=
    match rl with
    | Forward => tc_forward
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Forward |> done.

End SecurityMonitor.

Module Type Memory_sig (External: External_sig).
  Parameter internal_reg_t : Type.
  Parameter R_internal : internal_reg_t -> type.
  Parameter r_internal : (forall (idx: internal_reg_t), R_internal idx).

  Import Common.

  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

  Inductive reg_t :=
  | toIMem0 (state: MemReq.reg_t)
  | toIMem1 (state: MemReq.reg_t)
  | toDMem0 (state: MemReq.reg_t)
  | toDMem1 (state: MemReq.reg_t)
  | fromIMem0 (state: MemResp.reg_t)
  | fromIMem1 (state: MemResp.reg_t)
  | fromDMem0 (state: MemResp.reg_t)
  | fromDMem1 (state: MemResp.reg_t)
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | toIMem0 st => MemReq.R st
    | toIMem1 st => MemReq.R st
    | toDMem0 st => MemReq.R st
    | toDMem1 st => MemReq.R st
    | fromIMem0 st => MemResp.R st
    | fromIMem1 st => MemResp.R st
    | fromDMem0 st => MemResp.R st
    | fromDMem1 st => MemResp.R st
    | internal st => R_internal st
    end.

  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  Definition sigma := External.sigma.

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Axiom schedule : Syntax.scheduler pos_t rule_name_t.

End Memory_sig.

Module Type Machine_sig.
  Parameter reg_t : Type.
  Parameter ext_fn_t : Type.
  Parameter R : reg_t -> type.
  Parameter Sigma : ext_fn_t -> ExternalSignature.
  Parameter r : forall reg, R reg.
  Parameter rule_name_t : Type.
  Parameter rules : rule_name_t -> rule R Sigma.
  Parameter ext_fn_specs : ext_fn_t -> ext_fn_spec.
  Parameter FiniteType_reg_t : FiniteType reg_t.
  Parameter schedule : Syntax.scheduler pos_t rule_name_t.
End Machine_sig.

Module Machine (External: External_sig) (EnclaveParams: EnclaveParameters)
               (Params0: CoreParameters) (Params1: CoreParameters)
               (Core0: Core_sig External EnclaveParams Params0)
               (Core1: Core_sig External EnclaveParams Params1)
               (Memory: Memory_sig External) <: Machine_sig.

  Module SM := SecurityMonitor External EnclaveParams.

  Include Common.

  Inductive reg_t' : Type :=
  | core_id0
  | core_id1
  | pc0
  | pc1
  (* TODO: reset memory *)
  (* Core0 <-> SM *)
  | Core0ToSM_IMem (state: MemReq.reg_t)
  | Core0ToSM_DMem (state: MemReq.reg_t)
  | SMToCore0_IMem (state: MemResp.reg_t)
  | SMToCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | Core1ToSM_IMem (state: MemReq.reg_t)
  | Core1ToSM_DMem (state: MemReq.reg_t)
  | SMToCore1_IMem (state: MemResp.reg_t)
  | SMToCore1_DMem (state: MemResp.reg_t)
  (* SM <-> Mem *)
  | SMToMem0_IMem (state: MemReq.reg_t)
  | SMToMem0_DMem (state: MemReq.reg_t)
  | SMToMem1_IMem (state: MemReq.reg_t)
  | SMToMem1_DMem (state: MemReq.reg_t)
  | MemToSM0_IMem (state: MemResp.reg_t)
  | MemToSM0_DMem (state: MemResp.reg_t)
  | MemToSM1_IMem (state: MemResp.reg_t)
  | MemToSM1_DMem (state: MemResp.reg_t)
  (* Internal registers *)
  | Core0_internal (state: Core0.internal_reg_t)
  | Core1_internal (state: Core1.internal_reg_t)
  | SM_internal (state: SM.internal_reg_t)
  | Mem_internal (state: Memory.internal_reg_t)
  .

  Definition reg_t := reg_t'.

  Definition R (idx: reg_t) : type :=
    match idx with
    | core_id0 => bits_t 1
    | core_id1 => bits_t 1
    | pc0 => bits_t 32
    | pc1 => bits_t 32
    (* TODO: reset memory *)
    (* Core0 <-> SM *)
    | Core0ToSM_IMem st => MemReq.R st
    | Core0ToSM_DMem st => MemReq.R st
    | SMToCore0_IMem st => MemResp.R st
    | SMToCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | Core1ToSM_IMem st => MemReq.R st
    | Core1ToSM_DMem st => MemReq.R st
    | SMToCore1_IMem st => MemResp.R st
    | SMToCore1_DMem st => MemResp.R st
    (* SM <-> Mem *)
    | SMToMem0_IMem st => MemReq.R st
    | SMToMem0_DMem st => MemReq.R st
    | SMToMem1_IMem st => MemReq.R st
    | SMToMem1_DMem st => MemReq.R st
    | MemToSM0_IMem st => MemResp.R st
    | MemToSM0_DMem st => MemResp.R st
    | MemToSM1_IMem st => MemResp.R st
    | MemToSM1_DMem st => MemResp.R st
    (* Internal registers *)
    | Core0_internal st => Core0.R_internal st
    | Core1_internal st => Core1.R_internal st
    | SM_internal st => SM.R_internal st
    | Mem_internal st => Memory.R_internal st
    end.

  Definition r (idx: reg_t) : R idx :=
    match idx with
    | core_id0 => Params0.core_id
    | core_id1 => Params1.core_id
    | pc0 => Bits.zero
    | pc1 => Bits.zero
    (* TODO: reset memory *)
    (* Core0 <-> SM *)
    | Core0ToSM_IMem st => MemReq.r st
    | Core0ToSM_DMem st => MemReq.r st
    | SMToCore0_IMem st => MemResp.r st
    | SMToCore0_DMem st => MemResp.r st
    (* Core1 <-> SM *)
    | Core1ToSM_IMem st => MemReq.r st
    | Core1ToSM_DMem st => MemReq.r st
    | SMToCore1_IMem st => MemResp.r st
    | SMToCore1_DMem st => MemResp.r st
    (* SM <-> Mem *)
    | SMToMem0_IMem st => MemReq.r st
    | SMToMem0_DMem st => MemReq.r st
    | SMToMem1_IMem st => MemReq.r st
    | SMToMem1_DMem st => MemReq.r st
    | MemToSM0_IMem st => MemResp.r st
    | MemToSM0_DMem st => MemResp.r st
    | MemToSM1_IMem st => MemResp.r st
    | MemToSM1_DMem st => MemResp.r st
    (* Internal registers *)
    | Core0_internal st => Core0.r_internal st
    | Core1_internal st => Core1.r_internal st
    | SM_internal st => SM.r_internal st
    | Mem_internal st => Memory.r_internal st
    end.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition ext_fn_specs := External.ext_fn_specs.
  Definition rule : Type := rule R Sigma.

  (* TODO: 40s *)
  (* Instance FiniteType_reg_t : FiniteType reg_t := _. *)
  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Instance EqDec_reg_t : EqDec reg_t := _.

  Inductive rule_name_t' :=
  | Core0Rule (r: Core0.rule_name_t)
  | Core1Rule (r: Core1.rule_name_t)
  | SmRule   (r: SM.rule_name_t)
  | MemRule  (r: Memory.rule_name_t)
  .

  Definition rule_name_t := rule_name_t'.

  Section Core0_Lift.
    Definition core0_lift (reg: Core0.reg_t) : reg_t :=
      match reg with
      | Core0.core_id => core_id0
      | Core0.pc => pc0
      | Core0.toIMem s => Core0ToSM_IMem s
      | Core0.toDMem s => Core0ToSM_DMem s
      | Core0.fromIMem s => SMToCore0_IMem s
      | Core0.fromDMem s => SMToCore0_DMem s
      | Core0.internal s => Core0_internal s
      end.

    Definition Lift_core0 : RLift _ Core0.reg_t reg_t Core0.R R := ltac:(mk_rlift core0_lift).
    Definition FnLift_core0 : RLift _ Core0.ext_fn_t ext_fn_t Core0.Sigma Sigma := ltac:(lift_auto).

  End Core0_Lift.

  Section Core1_Lift.
    Definition core1_lift (reg: Core1.reg_t) : reg_t :=
      match reg with
      | Core1.core_id => core_id1
      | Core1.pc => pc1
      | Core1.toIMem s => Core1ToSM_IMem s
      | Core1.toDMem s => Core1ToSM_DMem s
      | Core1.fromIMem s => SMToCore1_IMem s
      | Core1.fromDMem s => SMToCore1_DMem s
      | Core1.internal s => Core1_internal s
      end.

    Definition Lift_core1 : RLift _ Core1.reg_t reg_t Core1.R R := ltac:(mk_rlift core1_lift).
    Definition FnLift_core1 : RLift _ Core1.ext_fn_t ext_fn_t Core1.Sigma Sigma := ltac:(lift_auto).

  End Core1_Lift.

  Section SM_Lift.

    Definition sm_lift (reg: SM.reg_t) : reg_t :=
      match reg with
      | SM.fromCore0_IMem st => Core0ToSM_IMem st
      | SM.fromCore0_DMem st => Core0ToSM_DMem st
      | SM.toCore0_IMem st => SMToCore0_IMem st
      | SM.toCore0_DMem st => SMToCore0_DMem st
      (* Core1 <-> SM *)
      | SM.fromCore1_IMem st => Core1ToSM_IMem st
      | SM.fromCore1_DMem st => Core1ToSM_DMem st
      | SM.toCore1_IMem st => SMToCore1_IMem st
      | SM.toCore1_DMem st => SMToCore1_DMem st
      (* SM <-> Mem *)
      | SM.toMem0_IMem st => SMToMem0_IMem st
      | SM.toMem0_DMem st => SMToMem0_DMem st
      | SM.toMem1_IMem st => SMToMem1_IMem st
      | SM.toMem1_DMem st => SMToMem1_DMem st
      | SM.fromMem0_IMem st => MemToSM0_IMem st
      | SM.fromMem0_DMem st => MemToSM0_DMem st
      | SM.fromMem1_IMem st => MemToSM1_IMem st
      | SM.fromMem1_DMem st => MemToSM1_DMem st
      | SM.internal st => SM_internal st
      end.

    Definition Lift_sm : RLift _ SM.reg_t reg_t SM.R R := ltac:(mk_rlift sm_lift).
    Definition FnLift_sm : RLift _ SM.ext_fn_t ext_fn_t SM.Sigma Sigma := ltac:(lift_auto).

  End SM_Lift.

  Section Mem_Lift.
    Definition mem_lift (reg: Memory.reg_t) : reg_t :=
      match reg with
      | Memory.toIMem0 st => SMToMem0_IMem st
      | Memory.toIMem1 st => SMToMem1_IMem st
      | Memory.toDMem0 st => SMToMem0_DMem st
      | Memory.toDMem1 st => SMToMem1_DMem st
      | Memory.fromIMem0 st => MemToSM0_IMem st
      | Memory.fromIMem1 st => MemToSM1_IMem st
      | Memory.fromDMem0 st => MemToSM0_DMem st
      | Memory.fromDMem1 st => MemToSM1_DMem st
      | Memory.internal st => Mem_internal st
      end.

    Definition Lift_mem : RLift _ Memory.reg_t reg_t Memory.R R := ltac:(mk_rlift mem_lift).
    Definition FnLift_mem : RLift _ Memory.ext_fn_t ext_fn_t Memory.Sigma Sigma := ltac:(lift_auto).

  End Mem_Lift.

  Section Rules.
    Definition core0_rule_name_lift (rl: Core0.rule_name_t) : rule_name_t :=
      Core0Rule rl.
    Definition core1_rule_name_lift (rl: Core1.rule_name_t) : rule_name_t :=
      Core1Rule rl.
    Definition sm_rule_name_lift (rl: SM.rule_name_t) : rule_name_t :=
      SmRule rl.
    Definition mem_rule_name_lift (rl: Memory.rule_name_t) : rule_name_t :=
      MemRule rl.

    Definition core0_rules (rl: Core0.rule_name_t) : rule :=
      lift_rule Lift_core0 FnLift_core0 (Core0.rules rl).
    Definition core1_rules (rl: Core1.rule_name_t) : rule :=
      lift_rule Lift_core1 FnLift_core1 (Core1.rules rl).
    Definition sm_rules (rl: SM.rule_name_t) : rule :=
      lift_rule Lift_sm FnLift_sm (SM.rules rl).
    Definition mem_rules (rl: Memory.rule_name_t) : rule :=
      lift_rule Lift_mem FnLift_mem (Memory.rules rl).

    Definition rules (rl: rule_name_t) : rule :=
      match rl with
      | Core0Rule r => core0_rules r
      | Core1Rule r => core1_rules r
      | SmRule r => sm_rules r
      | MemRule r => mem_rules r
      end.

  End Rules.

  Section Schedule.
    Definition core0_schedule := lift_scheduler core0_rule_name_lift Core0.schedule.
    Definition core1_schedule := lift_scheduler core1_rule_name_lift Core1.schedule.
    Definition sm_schedule := lift_scheduler sm_rule_name_lift SM.schedule.
    Definition mem_schedule := lift_scheduler mem_rule_name_lift Memory.schedule.

    Definition schedule :=
      schedule_app (schedule_app (schedule_app core0_schedule core1_schedule) sm_schedule) mem_schedule.

  End Schedule.

End Machine.
