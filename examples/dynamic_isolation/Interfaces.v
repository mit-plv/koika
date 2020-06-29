Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import dynamic_isolation.Lift.
Require Import dynamic_isolation.LogHelpers.
Require Import dynamic_isolation.Tactics.
Require Import dynamic_isolation.Scoreboard.

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
                         ("addr"    , bits_t 32);
                         ("data"    , bits_t 32)] |}.
  
  (* TODO *)
  Definition mem_req_get_addr (req: struct_t mem_req) : bits_t 32 :=
    let '(_, (addr, (_, _))) := req in
    addr.


  Definition mem_resp :=
    {| struct_name := "mem_resp";
       struct_fields := [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)] |}.

  Inductive enclave_id :=
  | Enclave0
  | Enclave1
  | Enclave2
  | Enclave3.

  Definition enclave_req :=
    {| struct_name := "enclave_req";
       struct_fields := [("eid", bits_t 32)]
    |}.

  Module FifoMemReq <: Fifo.
    Definition T:= struct_t mem_req.
  End FifoMemReq.
  Module MemReq := Fifo1Bypass FifoMemReq.

  Module FifoMemResp <: Fifo.
    Definition T:= struct_t mem_resp.
  End FifoMemResp.
  Module MemResp := Fifo1 FifoMemResp.

  Module FifoEnclaveReq <: Fifo.
    Definition T := struct_t enclave_req.
  End FifoEnclaveReq.
  Module EnclaveReq := Fifo1Bypass FifoEnclaveReq.

  Instance FiniteType_MemReq : FiniteType MemReq.reg_t := _.
  Instance FiniteType_MemResp : FiniteType MemResp.reg_t := _.
  Instance FiniteType_FifoEnclaveReq : FiniteType EnclaveReq.reg_t := _.

  Inductive ind_core_id :=
  | CoreId0
  | CoreId1
  .

  Inductive ind_cache_type :=
  | CacheType_Imem
  | CacheType_Dmem
  .

  Definition addr_t := bits_t 32.
  Definition data_t := bits_t 32.
  Definition core_id_t := bits_t 1.

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

  Definition ENUM_purge_restart := Ob~0~0.
  Definition ENUM_purge_ready := Ob~0~1.
  Definition ENUM_purge_purging := Ob~1~0.
  Definition ENUM_purge_purged := Ob~1~1.

  Definition purge_state :=
    {| enum_name := "purge_state";
       enum_members := vect_of_list ["Restart"; "Ready"; "Purging"; "Purged"];
       enum_bitpatterns := vect_of_list [ENUM_purge_restart; ENUM_purge_ready; 
                                         ENUM_purge_purging; ENUM_purge_purged] |}.

  Module RfParams <: RfPow2_sig.
    Definition idx_sz := log2 32.
    Definition T := bits_t 32.
    Definition init := Bits.zeroes 32.
    Definition read_style := Scoreboard.read_style 32.
    Definition write_style := Scoreboard.write_style.
  End RfParams.
  Module Rf := RfPow2 RfParams.

  Instance FiniteType_rf : FiniteType Rf.reg_t := _.
   
End Common.

(* TODO: need a well-formed predicate *)
Module Type EnclaveParameters.
  Parameter enclave_base : Common.enclave_id -> Common.addr_t.
  Parameter enclave_size : Common.enclave_id -> bits_t 32.
  Parameter enclave_bootloader_addr : Common.enclave_id -> Common.addr_t.
  Parameter shared_mem_base : Common.addr_t.
  Parameter shared_mem_size : bits_t 32.
End EnclaveParameters.

Module Type CoreParameters.
  Parameter core_id : Common.core_id_t.
  Parameter initial_pc : Common.addr_t.
End CoreParameters.

Module Type External_sig.
  Parameter ext_fn_t : Type.
  Parameter Sigma : ext_fn_t -> ExternalSignature.
  (* TODO: for later *)
  (* Parameter sigma : (forall fn: ext_fn_t, Sig_denote (Sigma fn)). *)
  Parameter ext_fn_specs : ext_fn_t -> ext_fn_spec.

End External_sig.

Module Type Core_sig (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters).
  Import Common.
  Parameter internal_reg_t : Type.
  Parameter R_internal : internal_reg_t -> type.
  Parameter r_internal : forall (idx: internal_reg_t), R_internal idx.
  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

  Inductive external_reg_t :=
  | core_id
  | toIMem (state: MemReq.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | toSMEnc (state: EnclaveReq.reg_t)
  | rf (state: Rf.reg_t) 
  | pc
  | purge
  .

  Definition R_external (idx: external_reg_t) : type :=
    match idx with
    | core_id => core_id_t
    | toIMem r => MemReq.R r
    | toDMem r => MemReq.R r
    | fromIMem  r => MemResp.R r
    | fromDMem  r => MemResp.R r
    | toSMEnc r => EnclaveReq.R r
    | rf r => Rf.R r  
    | pc => bits_t 32
    | purge => enum_t purge_state
    end.  

  Definition r_external (idx: external_reg_t) : R_external idx :=
    match idx with
    | core_id => CoreParams.core_id
    | toIMem s => MemReq.r s
    | fromIMem s => MemResp.r s
    | toDMem s => MemReq.r s
    | fromDMem s => MemResp.r s
    | toSMEnc s => EnclaveReq.r s
    | rf r => Rf.r r  
    | pc => CoreParams.initial_pc
    | purge => value_of_bits (Bits.zero)
    end.

  Inductive reg_t :=
  | external (r: external_reg_t)
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) : type :=
    match idx with
    | external r => R_external r
    | internal r => R_internal r
    end.

  Definition r idx : R idx :=
    match idx with
    | external s => r_external s
    | internal s => r_internal s
    end.                              

  (* TODO: recompile Tactics.v and this should work *)
  Declare Instance FiniteType_ext_reg_t : FiniteType external_reg_t. 
  Declare Instance FiniteType_reg_t : FiniteType reg_t.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Parameter schedule : Syntax.scheduler pos_t rule_name_t.

  Section CycleSemantics.
    Definition state := env_t ContextEnv (fun idx : reg_t => R idx).
    Definition empty_log : Log R ContextEnv := log_empty.

    Definition initial_state := ContextEnv.(create) r.

    Parameter update_function : state -> Log R ContextEnv -> Log R ContextEnv.
      (* interp_scheduler' st ? rules log scheduler. *)

    Record step_io :=
      { step_input : Log R_external ContextEnv;
        step_feedback: Log R_external ContextEnv
      }.

    Definition lift_ext_log (log: Log R_external ContextEnv) : Log R ContextEnv :=
      ContextEnv.(create) (fun reg => match reg return (RLog (R reg)) with
                                   | external s => ContextEnv.(getenv) log s
                                   | _ => []
                                   end).

    Definition do_step__koika (st: state) (step: step_io)
                            : state * Log R ContextEnv :=
      let input := lift_ext_log step.(step_input) in
      let output := update_function st input in
      let final := log_app (lift_ext_log step.(step_feedback)) (log_app output input) in
      (commit_update st final, output).

    Definition do_steps__koika (steps: list step_io) 
                             : state * list (Log R ContextEnv) :=
      fold_left (fun '(st, evs) step =>
                   let '(st', ev) := do_step__koika st step in
                   (st', evs ++ [ev]))
                steps (initial_state, []).

  End CycleSemantics.

  Section Interface.
    Definition proj_log__ext (log: Log R ContextEnv) : Log R_external ContextEnv :=
      ContextEnv.(create) (fun reg => ContextEnv.(getenv) log (external reg)).

      Definition tau := Log R_external ContextEnv.
      Definition trace := list tau.
  End Interface.

  Section TODO_MOVE.

    Definition AND (Ps: list Prop) : Prop :=
      List.fold_left and Ps True.

    Definition bits_eqb {sz} (v1: bits_t sz) (v2: bits_t sz) : bool :=
      N.eqb (Bits.to_N v1) (Bits.to_N v2).


  End TODO_MOVE.

  Section Spec.

    Record props_t :=
      { P_input : Prop;
        P_output : Prop;
        P_feedback: Prop
      }.

    Definition valid_inputs (props: list props_t) :=
      AND (List.map P_input props).
    Definition valid_feedback (props: list props_t) :=
      AND (List.map P_feedback props).
    Definition valid_output (props: list props_t) :=
      AND (List.map P_output props).

    Definition trivial_props : props_t :=
      {| P_input := True;
         P_output := True;
         P_feedback := True
      |}.

    Definition is_external_log (log: Log R ContextEnv) : Prop :=
      forall reg, match reg with
             | external r => True
             | internal r => ContextEnv.(getenv) log reg = []
             end.

    (* TODO: to simplify for now, we say that the Core executes first *)
    Definition valid_input_log__common (input_log: Log R_external ContextEnv) : Prop :=
      input_log = log_empty.

    Definition valid_output_log__common (output_log: Log R_external ContextEnv) : Prop :=
      True.
    
    Definition valid_feedback_log__common (log: Log R_external ContextEnv) : Prop :=
      (* Writeback to external registers only *)
      latest_write log core_id = None /\
      (* TODO: Register file is really internal... we just wanted to be able to talk about it *)
      (forall s, latest_write log (rf s) = None).
    (*
      (latest_write log (external (toIMem MemReq.valid0)) = None \/
      latest_write log (external (toIMem MemReq.valid0)) = Some Ob~0).
      *)
    
    (* - While running, SM only gets to write purging (which doesn't change anything)
     * - Only Core writes purged, transitioning from running -> waiting
     * - Here, Core promises to not change external state
     * - Supposing that SM writes restart only when external state is cleared (apart from certain regs),
     * - Then simulation of resetting holds.
     *)
    Inductive ghost_state :=
    | SpecSt_Running
    | SpecSt_Waiting (rf: env_t ContextEnv Rf.R)
    .

    Definition spec_state_t : Type := state * ghost_state.

    Definition initial_spec_state : spec_state_t := (initial_state, SpecSt_Running).

    Definition only_write_ext_purge (log: Log R_external ContextEnv) (v: bits_t 2) : Prop :=
      latest_write log purge = Some v \/ latest_write log purge = None.

    Definition only_write_purge (log: Log R ContextEnv) (v: bits_t 2) : Prop :=
      latest_write log (external purge) = Some v \/ latest_write log (external purge) = None.

    Definition extract_rf (st: state) : env_t ContextEnv Rf.R :=
      ContextEnv.(create) (fun reg => ContextEnv.(getenv) st (external (rf reg))).
    
    Definition initialise_with_rf (initial_rf: env_t ContextEnv Rf.R) (initial_pc: bits_t 32) : state :=
      ContextEnv.(create) (fun reg => match reg return R reg with
                                   | external (rf s) => ContextEnv.(getenv) initial_rf s
                                   | external pc => initial_pc
                                   | s => r s
                                   end).
    
    (* TODO: should really be inductive probably or option type? But too much effort to specify everything. *)
    Definition do_step_trans__spec (spec_st: spec_state_t) (step: step_io)
                                 : spec_state_t * Log R_external ContextEnv :=
      let '(st, ghost) := spec_st in
      let '(st', output) := do_step__koika st step in
      let ext_output := proj_log__ext output in 
      match ghost with
      | SpecSt_Running =>
          let continue := ((st', SpecSt_Running), ext_output) in
          match latest_write output (external purge) with
          | Some v => if bits_eqb v ENUM_purge_purged 
                     then ((st', SpecSt_Waiting (extract_rf st')), ext_output)
                     else continue
          | None => continue
          end
      | SpecSt_Waiting _rf => 
         let continue := ((st', SpecSt_Waiting _rf), ext_output) in
         match latest_write step.(step_feedback) purge,
               latest_write step.(step_feedback) pc with
         | Some v, Some _pc => 
             if bits_eqb v ENUM_purge_restart then
               (((initialise_with_rf _rf _pc), SpecSt_Running), ext_output)
             else (* don't care *) continue
         | _, _ => continue
         end
      end.

    (* Behaves nicely with enq/deqs *)
    Definition valid_interface_log (st: state) (init_log: Log R_external ContextEnv) 
                                   (log: Log R_external ContextEnv) : Prop. Admitted.

    Definition no_writes (log: Log R_external ContextEnv) : Prop :=
      forall r, latest_write log r = None.

    Definition valid_step_output__spec (spec_st: spec_state_t) (step: step_io) : Prop :=
      let '(st, ghost) := spec_st in
      let '(st', log) := do_step_trans__spec spec_st step in
      valid_output_log__common log /\
      valid_interface_log st log_empty log  /\
        (match ghost with
        | SpecSt_Running => True
        | SpecSt_Waiting _ =>
            no_writes log
        end).

    Definition reset_external_state (st: state) : Prop :=
      forall reg, match reg with
             | rf _ => True
             | pc => True
             | purge => True
             | s => ContextEnv.(getenv) st (external s) = r_external s
             end.

    Definition valid_step_feedback__spec (spec_st: spec_state_t) (step: step_io) : Prop :=
      let '(st, ghost) := spec_st in
      let '(st', output) := do_step_trans__spec spec_st step in
      let feedback := step.(step_feedback) in

      valid_feedback_log__common step.(step_feedback) /\
      valid_interface_log st (log_app output step.(step_input)) feedback /\
      match ghost with
      | SpecSt_Running =>
          only_write_ext_purge feedback ENUM_purge_purging
      | SpecSt_Waiting _  =>
          only_write_ext_purge feedback ENUM_purge_restart /\
          (latest_write feedback purge = Some ENUM_purge_restart ->
           latest_write feedback pc <> None /\
           reset_external_state (fst st') (* TODO: whose responsibility to clear FIFOs? *)
          )
      end.

    Definition do_step__spec (spec_st: spec_state_t) (step: step_io)
                           : spec_state_t * Log R_external ContextEnv * props_t :=
      let '(st', log) := do_step_trans__spec spec_st step in
      let props' := {| P_input := valid_input_log__common step.(step_input);
                       P_output := valid_step_output__spec spec_st step;
                       P_feedback := valid_step_feedback__spec spec_st step
                    |} in
      (st', log, props').

    Definition do_steps__spec (steps: list step_io) 
                            : spec_state_t * list (Log R_external ContextEnv) * list props_t :=
      fold_left (fun '(st, evs, props) step => 
                   let '(st', ev, prop) := do_step__spec st step in
                   (st', evs ++ [ev], props ++ [prop]))
                steps (initial_spec_state, [], []).
     
  End Spec.

  Section Correctness.

    (* TODO: clean *)
    Definition log_equivalent (koika_log: Log R ContextEnv) (spec_log: Log R_external ContextEnv) : Prop :=
      forall (reg: external_reg_t), 
        latest_write koika_log (external reg) = latest_write spec_log reg /\
        (forall port, may_read koika_log port (external reg) = may_read spec_log port reg) /\
        (forall port, may_write koika_log log_empty port (external reg) =
                 may_write spec_log log_empty port reg).

    Definition trace_equivalent (koika_tr: list (Log R ContextEnv)) 
                                (spec_tr: list (Log R_external ContextEnv)) : Prop :=
      Forall2 log_equivalent koika_tr spec_tr.

    Axiom correctness :
      forall (steps: list step_io) 
        (spec_st: spec_state_t) (spec_tr: list (Log R_external ContextEnv)) (props: list props_t)
        (koika_st: state) (koika_tr: list (Log R ContextEnv)),
      valid_inputs props ->
      valid_feedback props ->
      do_steps__spec steps = (spec_st, spec_tr, props) ->
      do_steps__koika steps = (koika_st, koika_tr) ->
      trace_equivalent koika_tr spec_tr.

  End Correctness.

  Section Compliance.
    Axiom compliance:
      forall (steps: list step_io) 
        (spec_st: spec_state_t) (spec_tr: list (Log R_external ContextEnv)) (props: list props_t)
        (koika_st: state) (koika_tr: list (Log R ContextEnv)),
      valid_inputs props ->
      valid_feedback props ->
      do_steps__spec steps = (spec_st, spec_tr, props) ->
      do_steps__koika steps = (koika_st, koika_tr) ->
      valid_output props.

  End Compliance.

  (*
  Section LogHelpers.
    Definition update_no_writes_to_reg (st: state) (log: Log R ContextEnv) (reg: reg_t) : Prop :=
      latest_write (update_function st log) reg = latest_write log reg.

  End LogHelpers.


  Section CoreAxioms.
    (* TODO: rf *)
    Definition internal_reg_reset (st: state) (reg: internal_reg_t) : Prop :=
      ContextEnv.(getenv) st (internal reg) = r (internal reg).

    Definition reg_reset (st: state) (reg: reg_t) : Prop :=
      match reg with
      | pc => True (* don't care *)
      | purge => True (* don't care *)
      | internal s => internal_reg_reset st s
      | _ => ContextEnv.(getenv) st reg = r reg
      end.

    Definition valid_reset_state (st: state) : Prop :=
      forall reg, reg_reset st reg.

    (* If in Ready/Purged state, not allowed to write to purge *)
    Inductive purge_state_machine (st: state) (log: Log R ContextEnv): Prop :=
    | PurgeRestart :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_restart)
          (no_writes_or_write_ready: 
             update_no_writes_to_reg st log purge \/
             latest_write (update_function st log) purge = Some ENUM_purge_ready),
          purge_state_machine st log
    | PurgeReady :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_ready)
          (no_writes: update_no_writes_to_reg st log purge),
          purge_state_machine st log
    | PurgePurging :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purging)
          (no_writes_or_write_purged: 
             update_no_writes_to_reg st log purge \/
             latest_write (update_function st log) purge = Some ENUM_purge_purged
          ),
          purge_state_machine st log
    | PurgePurged :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purged)
          (no_writes_to_any_reg: forall reg, update_no_writes_to_reg st log reg),
          purge_state_machine st log
    .

    Definition valid_core_id (st: state) : Prop :=
      ContextEnv.(getenv) st core_id = r core_id.

    Definition valid_state_by_purge (st: state) : Prop :=
      ContextEnv.(getenv) st purge = ENUM_purge_restart \/
      ContextEnv.(getenv) st purge = ENUM_purge_purged ->
      valid_reset_state st.

    Axiom valid_internal_state : state -> Prop.

    Definition valid_input_log (log: Log R ContextEnv) :=
      log = empty_log.

    Definition valid_state (st: state) : Prop :=
      valid_core_id st /\
      valid_state_by_purge st /\
      valid_internal_state st.

    Axiom valid_state_preserved: 
      forall (st: state) (log: Log R ContextEnv),
      valid_state st ->
      valid_input_log log ->
      valid_state (commit_update st (update_function st log)).

    (* TODO: and valid_state_preserved after external world effects on FIFO? *)

    (* Core_id is unchanged *)
    Axiom core_id_unchanged : 
      forall (st: state) (log: Log R ContextEnv),
      latest_write (update_function st log) core_id = latest_write log core_id.

    Axiom valid_purge_state_machine :
      forall (st: state) (log: Log R ContextEnv),
        purge_state_machine st log.

    (* If we are in a valid state and write Purging->Purged, then we promise to be in a reset state.
     * This is a stronger statement that we ultimately need, but is easier to phrase/work with.
     * I think with modules (/being written in a more modular way without register sharing) this will be easier.
     *)
    (* TODO: this is wrong right now b/c of FIFOs *)
    Axiom write_purged_impl_in_reset_state :
      forall (st: state) (log: Log R ContextEnv),
      latest_write (update_function st log) purge = Some ENUM_purge_purged ->
      latest_write log purge <> Some ENUM_purge_purged ->
      valid_reset_state (commit_update st (update_function st log)).
    *)

    (*
    | ValidSt_Restart :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_restart)
          (reset_st: valid_reset_state st),
        valid_state st
    | ValidSt_Ready :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_ready),
        valid_state st
    | ValidSt_Purging :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purging),
        valid_state st
    | ValidSt_Purged :
        forall (purge_state_eq: ContextEnv.(getenv) st purge = ENUM_purge_purged)
          (reset_st: valid_reset_state st),
        valid_state st.
    *)
  (* End CoreAxioms. *)

End Core_sig.

Module EnclaveInterface.
  Import Common.

  Definition enclave_data :=
    {| struct_name := "enclave_data";
       struct_fields := [("eid", bits_t 32);
                         ("addr_min", bits_t 32);
                         ("size", bits_t 32);
                         ("shared_page", bits_t 1);
                         ("valid", bits_t 1)
                        ]
    |}.

  Record struct_enclave_data :=
    { enclave_data_eid : bits_t 32;
      enclave_data_addr_min : bits_t 32;
      enclave_data_size : bits_t 32;
      enclave_data_shared_page : bits_t 1;
      enclave_data_valid : bits_t 1;
    }.

  Inductive mem_region :=
  | MemRegion_Enclave (eid: enclave_id)
  | MemRegion_Shared
  | MemRegion_Other
  .

  Scheme Equality for mem_region.

  Definition mk_enclave_data (data: struct_enclave_data) : struct_t enclave_data :=
    (data.(enclave_data_eid),
     (data.(enclave_data_addr_min), (data.(enclave_data_size), 
                                     (data.(enclave_data_shared_page), (data.(enclave_data_valid), tt))))).

  (* TODO: generalize this. *)
  Definition extract_enclave_data (data: struct_t enclave_data) : struct_enclave_data :=
      let '(eid, (addr_min, (size, (shared_page, (valid, _))))) := data in
      {| enclave_data_eid := eid;
         enclave_data_addr_min := addr_min;
         enclave_data_size := size;
         enclave_data_shared_page := shared_page;
         enclave_data_valid := valid;
      |}.

  Definition bits_id_to_ind_id (eid: bits_t 32) : option enclave_id :=
    match Bits.to_nat eid with
    | 0 => Some Enclave0
    | 1 => Some Enclave1
    | 2 => Some Enclave2
    | 3 => Some Enclave3
    | _ => None
    end.

  Definition enclave_id_to_bits (eid: enclave_id) : bits_t 32 :=
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1
    end.

  Record enclave_config :=
    { eid : Common.enclave_id;
      shared_page : bool;
    }.

End EnclaveInterface.

(* NOTE: in our model we say this is fixed, so we can talk about the internal registers. *)
Module SecurityMonitor (External: External_sig) (Params: EnclaveParameters).
  Import Common.
  Import EnclaveInterface.

  Definition ENUM_CORESTATE_RUNNING := Ob~0~0.
  Definition ENUM_CORESTATE_PURGING:= Ob~0~0.
  Definition ENUM_CORESTATE_WAITING:= Ob~0~0.

  Definition core_state :=
    {| enum_name := "core_states";
       enum_members := vect_of_list ["Running"; "Purging"; "Waiting"];
       enum_bitpatterns := vect_of_list [ENUM_CORESTATE_RUNNING; ENUM_CORESTATE_PURGING; ENUM_CORESTATE_WAITING]
    |}.

  (* Note: somewhat redundant registers *)
  Inductive internal_reg_t' :=
  | state0
  | state1
  | enc_data0
  | enc_data1
  | enc_req0
  | enc_req1
  | clk
  .

  Definition internal_reg_t := internal_reg_t'.

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | state0 => enum_t core_state
    | state1 => enum_t core_state
    | enc_data0 => struct_t enclave_data
    | enc_data1 => struct_t enclave_data
    | enc_req0 => struct_t enclave_data
    | enc_req1 => struct_t enclave_data
    | clk => bits_t 1
    end.


  Definition eid_to_initial_enclave_data (eid: enclave_id) : struct_t enclave_data :=
    mk_enclave_data {| enclave_data_eid := enclave_id_to_bits eid;
                       enclave_data_addr_min := Params.enclave_base eid;
                       enclave_data_size := Params.enclave_size eid;
                       enclave_data_shared_page := Ob~0;
                       enclave_data_valid := Ob~1
                    |}.


  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with
    | state0 => Bits.zero
    | state1 => Bits.zero
    | enc_data0 => eid_to_initial_enclave_data Enclave0
    | enc_data1 => eid_to_initial_enclave_data Enclave1
    | enc_req0 => value_of_bits Bits.zero
    | enc_req1 => value_of_bits Bits.zero
    | clk => Bits.zero
    end.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.

  Inductive external_reg_t :=
  | fromCore0_IMem (state: MemReq.reg_t)
  | fromCore0_DMem (state: MemReq.reg_t)
  | fromCore0_Enc (state: EnclaveReq.reg_t)
  | toCore0_IMem (state: MemResp.reg_t)
  | toCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | fromCore1_IMem (state: MemReq.reg_t)
  | fromCore1_DMem (state: MemReq.reg_t)
  | fromCore1_Enc (state: EnclaveReq.reg_t)
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
  | pc_core0
  | pc_core1
  | purge_core0
  | purge_core1
  | purge_mem0
  | purge_mem1
  .

  Definition R_external (idx: external_reg_t) : type :=
    match idx with
    | fromCore0_IMem st => MemReq.R st
    | fromCore0_DMem st => MemReq.R st
    | fromCore0_Enc st => EnclaveReq.R st
    | toCore0_IMem st => MemResp.R st
    | toCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | fromCore1_IMem st => MemReq.R st
    | fromCore1_DMem st => MemReq.R st
    | fromCore1_Enc st => EnclaveReq.R st
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
    | pc_core0 => bits_t 32
    | pc_core1 => bits_t 32
    | purge_core0 => enum_t purge_state
    | purge_core1 => enum_t purge_state
    | purge_mem0 => enum_t purge_state
    | purge_mem1 => enum_t purge_state
    end.

  Definition r_external (idx: external_reg_t) : R_external idx :=
    match idx with
    | fromCore0_IMem st => MemReq.r st
    | fromCore0_DMem st => MemReq.r st
    | fromCore0_Enc st => EnclaveReq.r st
    | toCore0_IMem st => MemResp.r st
    | toCore0_DMem st => MemResp.r st
    (* Core1 <-> SM *)
    | fromCore1_IMem st => MemReq.r st
    | fromCore1_DMem st => MemReq.r st
    | fromCore1_Enc st => EnclaveReq.r st
    | toCore1_IMem st => MemResp.r st
    | toCore1_DMem st => MemResp.r st
    (* SM <-> Mem *)
    | toMem0_IMem st => MemReq.r st
    | toMem0_DMem st => MemReq.r st
    | toMem1_IMem st => MemReq.r st
    | toMem1_DMem st => MemReq.r st
    | fromMem0_IMem st => MemResp.r st
    | fromMem0_DMem st => MemResp.r st
    | fromMem1_IMem st => MemResp.r st
    | fromMem1_DMem st => MemResp.r st
    | pc_core0 => Bits.zero
    | pc_core1 => Bits.zero
    | purge_core0 => value_of_bits (Bits.zero)
    | purge_core1 => value_of_bits (Bits.zero)
    | purge_mem0 => value_of_bits (Bits.zero)
    | purge_mem1 => value_of_bits (Bits.zero)
    end.

  Inductive reg_t : Type :=
  | external (idx: external_reg_t)
  | internal (idx: internal_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | external st => R_external st
    | internal st => R_internal st
    end.

  Definition r (idx: reg_t) : R idx :=
    match idx with
    | external st => r_external st
    | internal st => r_internal st
    end.

  Instance FiniteType_external_reg_t : FiniteType external_reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition Sigma := External.Sigma.
  Definition ext_fn_t := External.ext_fn_t.
  Definition state := env_t ContextEnv (fun idx : reg_t => R idx).

  Definition eid_to_enc_data : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun eid_to_enc_data (eid: bits_t 32) : struct_t enclave_data =>
         match eid with
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 =>
             `UConst (tau := struct_t enclave_data) (eid_to_initial_enclave_data Enclave0)`
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 =>
             `UConst (tau := struct_t enclave_data) (eid_to_initial_enclave_data Enclave1)`
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0 =>
             `UConst (tau := struct_t enclave_data) (eid_to_initial_enclave_data Enclave2)`
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1 =>
             `UConst (tau := struct_t enclave_data) (eid_to_initial_enclave_data Enclave3)`
         return default : `UConst (tau := struct_t enclave_data) (value_of_bits (Bits.zero))`
         end
    }}.

  Definition lookup_reg_state (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => internal state0
    | CoreId1 => internal state1
    end.

  Definition lookup_reg_enc_data (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => internal enc_data0
    | CoreId1 => internal enc_data1
    end.

  Definition lookup_reg_enc_req (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => internal enc_req0
    | CoreId1 => internal enc_req1
    end.

  Definition lookup_reg_proc_reset (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => external purge_core0
    | CoreId1 => external purge_core1
    end.

  Definition lookup_reg_mem_reset (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => external purge_mem0
    | CoreId1 => external purge_mem1
    end.

  Definition lookup_reg_pc (core: ind_core_id) : reg_t :=
    match core with
    | CoreId0 => external pc_core0
    | CoreId1 => external pc_core1
    end.

  (* TODO: This is wrong. While in a limbo state, other core can't switch into old enclave until done reset *)
  Definition canSwitchToEnc (core: ind_core_id) : UInternalFunction reg_t empty_ext_fn_t :=
    let other_core := match core with CoreId0 => CoreId1 | CoreId1 => CoreId0 end in
    let reg_other_enc := lookup_reg_enc_data other_core in
    {{ fun canSwitchToEnc (eid: bits_t 32) : bits_t 1 =>
         let other_enc_data := read0(reg_other_enc) in
         get(other_enc_data, eid) != eid
    }}.

  Notation "'__external__' instance " :=
    (fun reg => external ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  (* TODO: shared page *)
  Definition sm_update_enclave (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let reg_state := lookup_reg_state core in
    let reg_enc_req := lookup_reg_enc_req core in
    let reg_proc_reset := lookup_reg_proc_reset core in
    let reg_mem_reset := lookup_reg_mem_reset core in
    let fromCore :=
        match core with
        | CoreId0 => fromCore0_Enc
        | CoreId1 => fromCore1_Enc
        end in
    {{ when (read0(reg_state) == enum core_state { Running }) do (
         let max_eid := |32`d3| in
         let enclaveRequest := (__external__ fromCore).(EnclaveReq.deq)() in
         let eid := get(enclaveRequest, eid) in
         if (eid <= max_eid) then
           write0(reg_state, enum core_state { Purging });
           write0(reg_enc_req, eid_to_enc_data(eid));
           write1(reg_proc_reset, enum purge_state { Purging });
           write1(reg_mem_reset, enum purge_state { Purging })
         else (* drop it *)
           pass
       )
    }}.

  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

  Definition sm_filter_reqs (core: ind_core_id) (cache: ind_cache_type) : uaction reg_t ext_fn_t :=
    let reg_state := lookup_reg_state core in
    let reg_enc := lookup_reg_enc_data core in
    let '(fromCore, toMem) :=
        match core, cache with
        | CoreId0, CacheType_Imem => (fromCore0_IMem, toMem0_IMem)
        | CoreId0, CacheType_Dmem => (fromCore0_DMem, toMem0_DMem)
        | CoreId1, CacheType_Imem => (fromCore1_IMem, toMem1_IMem)
        | CoreId1, CacheType_Dmem => (fromCore1_DMem, toMem1_DMem)
        end in
    {{ when (read0(reg_state) == enum core_state { Running }) do
         let request := (__external__ fromCore).(MemReq.deq)() in
         let address := get(request, addr) in
         let enc_data := read0(reg_enc) in
         let addr_min := get(enc_data, addr_min) in
         let addr_max := get(enc_data, size) + addr_min in
         let TODO_temp_bypass := address >= #(MMIO_UART_ADDRESS) in
         if ((addr_min <= address && address < addr_max) ||  TODO_temp_bypass) then
           (__external__ toMem).(MemReq.enq)(request)
         else pass
    }}.

  Definition sm_filter_resps (core: ind_core_id) (cache: ind_cache_type) : uaction reg_t ext_fn_t :=
    let reg_state := lookup_reg_state core in
    let reg_enc := lookup_reg_enc_data core in
    let '(fromMem, toCore) :=
        match core, cache with
        | CoreId0, CacheType_Imem => (fromMem0_IMem, toCore0_IMem)
        | CoreId0, CacheType_Dmem => (fromMem0_DMem, toCore0_DMem)
        | CoreId1, CacheType_Imem => (fromMem1_IMem, toCore1_IMem)
        | CoreId1, CacheType_Dmem => (fromMem1_DMem, toCore1_DMem)
        end in
    {{ when (read0(reg_state) == enum core_state { Running }) do
         let response:= (__external__ fromMem).(MemResp.deq)() in
         let address := get(response, addr) in
         let enc_data := read0(reg_enc) in
         let addr_min := get(enc_data, addr_min) in
         let addr_max := get(enc_data, size) + addr_min in
         let TODO_temp_bypass := address >= #(MMIO_UART_ADDRESS) in
         if (addr_min <= address && address < addr_max) || TODO_temp_bypass then
           (__external__ toCore).(MemResp.enq)(response)
         else pass
    }}.

  (*
  Definition sm_reset_processor_and_memory (core: ind_core_id): uaction reg_t ext_fn_t :=
    let reg_limbo := lookup_reg_limbo core in
    let reg_proc_reset := lookup_reg_proc_reset core in
    let reg_mem_reset := lookup_reg_mem_reset core in
    {{ (if (read0(reg_limbo) && read0(reg_proc_reset) == enum purge_state { Ready }) then
         write0(reg_proc_reset, enum purge_state { Purging })
        else pass);
       if (read0(reg_limbo) && read0(reg_mem_reset) == enum purge_state { Ready }) then
         write0(reg_mem_reset, enum purge_state { Purging })
       else pass
    }}.
    *)

  Definition eid_to_bootloader_addr : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun eid_to_bootloader_addr (eid: bits_t 32) : bits_t 32 =>
         match eid with
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 =>
             #(Params.enclave_bootloader_addr Enclave0)
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 =>
             #(Params.enclave_bootloader_addr Enclave1)
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0 =>
             #(Params.enclave_bootloader_addr Enclave2)
         | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1 =>
             #(Params.enclave_bootloader_addr Enclave3)
         return default : |32`d0|
         end
    }}.
  Definition reset_fifos : UInternalFunction reg_t ext_fn_t :=
    {{ fun reset_fifos () : bits_t 0 =>
         (__external__ fromCore0_IMem).(MemReq.reset)();
         (__external__ fromCore0_DMem).(MemReq.reset)();
         (__external__ fromCore0_Enc).(EnclaveReq.reset)();
         (__external__ toCore0_IMem).(MemResp.reset)();
         (__external__ toCore0_DMem).(MemResp.reset)();
         (__external__ fromCore1_IMem).(MemReq.reset)();
         (__external__ fromCore1_DMem).(MemReq.reset)();
         (__external__ fromCore1_Enc).(EnclaveReq.reset)();
         (__external__ toCore1_IMem).(MemResp.reset)();
         (__external__ toCore1_DMem).(MemResp.reset)();
         (__external__ toMem0_IMem).(MemReq.reset)();
         (__external__ toMem0_DMem).(MemReq.reset)();
         (__external__ toMem1_IMem).(MemReq.reset)();
         (__external__ toMem1_DMem).(MemReq.reset)();
         (__external__ fromMem0_IMem).(MemResp.reset)();
         (__external__ fromMem0_DMem).(MemResp.reset)();
         (__external__ fromMem1_IMem).(MemResp.reset)();
         (__external__ fromMem1_DMem).(MemResp.reset)()
    }}.

  Definition sm_exit_enclave (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let reg_state := lookup_reg_state core in
    let reg_enc_data := lookup_reg_enc_data core in
    let reg_proc_reset := lookup_reg_proc_reset core in
    let reg_mem_reset := lookup_reg_mem_reset core in
    {{ if (read0(reg_state) == enum core_state { Purging } &&
           read0(reg_proc_reset) == enum purge_state { Purged } &&
           read0(reg_mem_reset) == enum purge_state { Purged }) then
          (* Do resets *)
          reset_fifos();
          (* Exit enclave *)
          write0(reg_state, enum core_state { Waiting });
          write0(reg_enc_data, `UConst (tau := struct_t enclave_data) (value_of_bits (Bits.zero))`)
       else fail
    }}.

  (* TODO: avoiding dealing with semantics of valid bits... *)
  Definition sm_enter_enclave (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let reg_state := lookup_reg_state core in
    let reg_enc_data := lookup_reg_enc_data core in
    let reg_enc_req := lookup_reg_enc_req core in
    let reg_proc_reset := lookup_reg_proc_reset core in
    let reg_mem_reset := lookup_reg_mem_reset core in
    let valid_clk := match core with | CoreId0 => Ob~0 | CoreId1 => Ob~1 end in
    let reg_pc := lookup_reg_pc core in
    {{  if (read0(reg_state) == enum core_state { Waiting } &&
            read0(internal clk) == #valid_clk) then
         let enc_req := read0(reg_enc_req) in
         let eid := get(enc_req,eid) in
         (* Check for permission to enter by reading other core's enclave data *)
         if ({canSwitchToEnc core}(eid)) then
           (* Set up new enclave *)
           write0(reg_enc_data, enc_req);
           write0(reg_enc_req, `UConst (tau := struct_t enclave_data) (value_of_bits (Bits.zero))`);
           (* Restart *)
           write0(reg_state, enum core_state { Running });
           write0(reg_proc_reset, enum purge_state { Restart });
           write0(reg_mem_reset, enum purge_state { Restart });
           (* Set initial pc *)
           write0(reg_pc, eid_to_bootloader_addr(eid))
         else fail
        else fail
    }}.


  (*
  Definition sm_restart_pipeline (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let reg_limbo := lookup_reg_limbo core in
    let reg_enc := lookup_reg_enc_data core in
    let reg_proc_reset := lookup_reg_proc_reset core in
    let reg_mem_reset := lookup_reg_mem_reset core in
    let reg_pc := lookup_reg_pc core in
    {{ if (read0(reg_limbo) && read0(reg_proc_reset) == enum purge_state { Purged } &&
           read0(reg_mem_reset) == enum purge_state { Purged }) then
         (* Do resets *)
         reset_fifos();
         (* Restart *)
         write0(reg_limbo, Ob~0);
         write0(reg_proc_reset, enum purge_state { Restart });
         write0(reg_mem_reset, enum purge_state { Restart });
         let enc_data := read0(reg_enc) in
         let max_eid := |32`d3| in
         let eid := get(enc_data,eid) in
         if (eid <= max_eid) then
           write0(reg_pc, eid_to_bootloader_addr(eid))
         else
           fail
       else fail
    }}.
    *)

  Definition do_clk : uaction reg_t ext_fn_t :=
    {{ write0 (internal clk, !read0(internal clk)) }}.


  Definition tc_update_enclave0 := tc_rule R Sigma (sm_update_enclave CoreId0) <: rule R Sigma.
  Definition tc_update_enclave1 := tc_rule R Sigma (sm_update_enclave CoreId1) <: rule R Sigma.

  Definition tc_filter_reqs_imem0 := tc_rule R Sigma (sm_filter_reqs CoreId0 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_reqs_dmem0 := tc_rule R Sigma (sm_filter_reqs CoreId0 CacheType_Dmem) <: rule R Sigma.
  Definition tc_filter_reqs_imem1 := tc_rule R Sigma (sm_filter_reqs CoreId1 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_reqs_dmem1 := tc_rule R Sigma (sm_filter_reqs CoreId1 CacheType_Dmem) <: rule R Sigma.

  Definition tc_filter_resps_imem0 := tc_rule R Sigma (sm_filter_resps CoreId0 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_resps_dmem0 := tc_rule R Sigma (sm_filter_resps CoreId0 CacheType_Dmem) <: rule R Sigma.
  Definition tc_filter_resps_imem1 := tc_rule R Sigma (sm_filter_resps CoreId1 CacheType_Imem) <: rule R Sigma.
  Definition tc_filter_resps_dmem1 := tc_rule R Sigma (sm_filter_resps CoreId1 CacheType_Dmem) <: rule R Sigma.

  (*
  Definition tc_reset_proc_and_mem0 := tc_rule R Sigma (sm_reset_processor_and_memory CoreId0) <: rule R Sigma.
  Definition tc_reset_proc_and_mem1 := tc_rule R Sigma (sm_reset_processor_and_memory CoreId1) <: rule R Sigma.

  Definition tc_restart_pipeline0 := tc_rule R Sigma (sm_restart_pipeline CoreId0) <: rule R Sigma.
  Definition tc_restart_pipeline1 := tc_rule R Sigma (sm_restart_pipeline CoreId1) <: rule R Sigma.
  *)
  Definition tc_exit_enclave0 := tc_rule R Sigma (sm_exit_enclave CoreId0) <: rule R Sigma.
  Definition tc_exit_enclave1 := tc_rule R Sigma (sm_exit_enclave CoreId1) <: rule R Sigma.

  Definition tc_enter_enclave0 := tc_rule R Sigma (sm_enter_enclave CoreId0) <: rule R Sigma.
  Definition tc_enter_enclave1 := tc_rule R Sigma (sm_enter_enclave CoreId1) <: rule R Sigma.

  Definition tc_clk := tc_rule R Sigma do_clk <: rule R Sigma.

  (* Definition tc_forward := tc_rule R Sigma forward <: rule R Sigma. *)

  Inductive rule_name_t' :=
  | UpdateEnclave0
  | UpdateEnclave1
  | FilterReqsIMem0
  | FilterReqsDMem0
  | FilterReqsIMem1
  | FilterReqsDMem1
  | FilterRespsIMem0
  | FilterRespsDMem0
  | FilterRespsIMem1
  | FilterRespsDMem1
  (*
  | ResetProcAndMem0
  | ResetProcAndMem1
  | RestartPipeline0
  | RestartPipeline1
  *)
  | ExitEnclave0
  | ExitEnclave1
  | EnterEnclave0
  | EnterEnclave1
  | DoClk
  .

  Definition rule_name_t := rule_name_t'.

  Definition rules (rl : rule_name_t) : rule R Sigma :=
    match rl with
    | UpdateEnclave0 => tc_update_enclave0
    | UpdateEnclave1 => tc_update_enclave1
    | FilterReqsIMem0 => tc_filter_reqs_imem0
    | FilterReqsDMem0 => tc_filter_reqs_dmem0
    | FilterReqsIMem1 => tc_filter_reqs_imem1
    | FilterReqsDMem1 => tc_filter_reqs_dmem1
    | FilterRespsIMem0 => tc_filter_resps_imem0
    | FilterRespsDMem0 => tc_filter_resps_dmem0
    | FilterRespsIMem1 => tc_filter_resps_imem1
    | FilterRespsDMem1 => tc_filter_resps_dmem1
    (*
    | ResetProcAndMem0 => tc_reset_proc_and_mem0
    | ResetProcAndMem1 => tc_reset_proc_and_mem1
    | RestartPipeline0 => tc_restart_pipeline0
    | RestartPipeline1 => tc_restart_pipeline1
    *)
    | ExitEnclave0 => tc_exit_enclave0
    | ExitEnclave1 => tc_exit_enclave1
    | EnterEnclave0 => tc_enter_enclave0
    | EnterEnclave1 => tc_enter_enclave1
    | DoClk => tc_clk
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    UpdateEnclave0 |> UpdateEnclave1
                   |> FilterReqsIMem0 |> FilterReqsDMem0 |> FilterReqsIMem1 |> FilterReqsDMem1
                   |> FilterRespsIMem0 |> FilterRespsDMem0 |> FilterRespsIMem1 |> FilterRespsDMem1
                   (* |> ResetProcAndMem0 |> ResetProcAndMem1 *)
                   (* |> RestartPipeline0 |> RestartPipeline1 *)
                   |> ExitEnclave0 |> ExitEnclave1
                   |> EnterEnclave0 |> EnterEnclave1
                   |> DoClk
                   |> done.

  Section CycleSemantics.
    Parameter update_function : state -> Log R ContextEnv -> Log R ContextEnv.

    Record step_io :=
      { step_input : Log R_external ContextEnv;
        step_feedback : Log R_external ContextEnv
      }.



  End CycleSemantics.

End SecurityMonitor.

Module Type Machine_sig.
  Parameter reg_t : Type.
  Parameter ext_fn_t : Type.
  Parameter R : reg_t -> type.
  Parameter Sigma : ext_fn_t -> ExternalSignature.
  Parameter r : forall reg, R reg.
  Parameter rule_name_t : Type.
  Parameter rules : rule_name_t -> rule R Sigma.
  Parameter FiniteType_reg_t : FiniteType reg_t.
  Parameter schedule : Syntax.scheduler pos_t rule_name_t.
  Parameter ext_fn_specs : ext_fn_t -> ext_fn_spec.

End Machine_sig.

Module Type Memory_sig (External: External_sig) (EnclaveParams: EnclaveParameters).
  Parameter internal_reg_t : Type.
  Parameter R_internal : internal_reg_t -> type.
  Parameter r_internal : (forall (idx: internal_reg_t), R_internal idx).

  Import Common.

  Declare Instance FiniteType_internal_reg_t : FiniteType internal_reg_t.

  Inductive external_reg_t :=
  | toIMem0 (state: MemReq.reg_t)
  | toIMem1 (state: MemReq.reg_t)
  | toDMem0 (state: MemReq.reg_t)
  | toDMem1 (state: MemReq.reg_t)
  | fromIMem0 (state: MemResp.reg_t)
  | fromIMem1 (state: MemResp.reg_t)
  | fromDMem0 (state: MemResp.reg_t)
  | fromDMem1 (state: MemResp.reg_t)
  | purge0
  | purge1
  .

  Definition R_external (idx: external_reg_t) : type :=
    match idx with
    | toIMem0 st => MemReq.R st
    | toIMem1 st => MemReq.R st
    | toDMem0 st => MemReq.R st
    | toDMem1 st => MemReq.R st
    | fromIMem0 st => MemResp.R st
    | fromIMem1 st => MemResp.R st
    | fromDMem0 st => MemResp.R st
    | fromDMem1 st => MemResp.R st
    | purge0 => enum_t purge_state
    | purge1 => enum_t purge_state
    end.

  Definition r_external (idx: external_reg_t) : R_external idx :=
    match idx with
    | toIMem0 st => MemReq.r st
    | toIMem1 st => MemReq.r st
    | toDMem0 st => MemReq.r st
    | toDMem1 st => MemReq.r st
    | fromIMem0 st => MemResp.r st
    | fromIMem1 st => MemResp.r st
    | fromDMem0 st => MemResp.r st
    | fromDMem1 st => MemResp.r st
    | purge0 => value_of_bits (Bits.zero)
    | purge1 => value_of_bits (Bits.zero)
    end.

  Inductive reg_t :=
  | external (r: external_reg_t)
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) : type :=
    match idx with
    | external r => R_external r
    | internal r => R_internal r
    end.

  Definition r idx : R idx :=
    match idx with
    | external s => r_external s
    | internal s => r_internal s
    end.

  Instance FiniteType_ext_reg_t : FiniteType external_reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)

  Parameter rule_name_t : Type.
  Parameter rules  : rule_name_t -> rule.

  Axiom schedule : Syntax.scheduler pos_t rule_name_t.

  Import EnclaveInterface.

  Scheme Equality for ind_core_id.

  Section Taint.

    Definition external_reg_to_taint (reg: external_reg_t) : ind_core_id:=
      match reg with
      | toIMem0 st => CoreId0
      | toIMem1 st => CoreId1
      | toDMem0 st => CoreId0
      | toDMem1 st => CoreId1
      | fromIMem0 st => CoreId0
      | fromIMem1 st => CoreId1
      | fromDMem0 st => CoreId0
      | fromDMem1 st => CoreId1
      | purge0 => CoreId0
      | purge1 => CoreId1
      end.

  End Taint.

  Section Interface.
    Definition proj_log__ext (log: Log R ContextEnv) : Log R_external ContextEnv :=
      ContextEnv.(create) (fun reg => ContextEnv.(getenv) log (external reg)).

    Definition lift_ext_log (log: Log R_external ContextEnv) : Log R ContextEnv :=
      ContextEnv.(create) (fun reg => match reg return (RLog (R reg)) with
                                   | external s => ContextEnv.(getenv) log s
                                   | _ => []
                                   end).

    Definition filter_ext_log (log: Log R_external ContextEnv) (core: ind_core_id) : Log R_external ContextEnv :=
      ContextEnv.(create) (fun reg => if ind_core_id_beq (external_reg_to_taint reg) core
                                   then ContextEnv.(getenv) log reg
                                   else []).

    Definition tau := Log R_external ContextEnv.
    Definition trace := list tau.
  End Interface.

  Section CycleSemantics.
    Definition koika_state_t : Type := env_t ContextEnv (fun idx: reg_t => R idx).
    Definition dram_t : Type := nat -> option data_t.

    Parameter internal_external_state_t : Type.
    Parameter initial_internal_external_state : internal_external_state_t.
    Definition external_state_t : Type := dram_t * internal_external_state_t.

    Definition initial_external_state (initial_dram: dram_t) : external_state_t :=
      (initial_dram, initial_internal_external_state).

    Definition state : Type := koika_state_t * external_state_t.
    Definition initial_state (initial_dram: dram_t) : state :=
      (ContextEnv.(create) r, initial_external_state initial_dram).
    Definition empty_log : Log R ContextEnv := log_empty.

    Definition koika_update_function : koika_state_t -> Log R ContextEnv -> Log R ContextEnv. Admitted.
      (* interp_scheduler' st ? rules log scheduler. *)
    Definition external_update_function : state -> Log R ContextEnv -> Log R ContextEnv * external_state_t.
      Admitted.
    
    Definition update_function (st: state) (input_log: Log R ContextEnv) : Log R ContextEnv * external_state_t :=
      let '(koika_st, ext_st) := st in
      let koika_log := koika_update_function koika_st input_log in
      external_update_function (koika_st, ext_st) koika_log.

    Record step_io :=
      { step_input : Log R_external ContextEnv;
        step_feedback : Log R_external ContextEnv
      }.

    Record ifc_io :=
      { ifc_step : step_io;
        ifc_input_config0 : option EnclaveInterface.enclave_config;
        ifc_input_config1 : option EnclaveInterface.enclave_config;
      }.

    Definition get_input_config (step: ifc_io) (core: ind_core_id) : option EnclaveInterface.enclave_config :=
      match core with
      | CoreId0 => step.(ifc_input_config0)
      | CoreId1 => step.(ifc_input_config1)
      end.

    Definition do_step__impl (st: state) (step: step_io) : state * Log R ContextEnv :=
      let input := lift_ext_log step.(step_input) in
      let '(output, ext_st') := update_function st input in
      let final := log_app (lift_ext_log step.(step_feedback)) (log_app output input) in
      ((commit_update (fst st) final, ext_st'), output).

    Definition do_steps__impl (initial_dram: dram_t) (steps: list step_io)
                             : state * list (Log R ContextEnv) :=
      fold_left (fun '(st, evs) step =>
                   let '(st', ev) := do_step__impl st step in
                   (st', evs ++ [ev]))
                steps (initial_state initial_dram, []).

  End CycleSemantics.

  Section TODO_MOVE.

    Definition AND (Ps: list Prop) : Prop :=
      List.fold_left and Ps True.

    Definition bits_eqb {sz} (v1: bits_t sz) (v2: bits_t sz) : bool :=
      N.eqb (Bits.to_N v1) (Bits.to_N v2).

    Definition initial_enclave_config0 : enclave_config :=
      {| eid := Enclave0;
         shared_page  := false
      |}.
    Definition initial_enclave_config1 : enclave_config :=
      {| eid := Enclave1;
         shared_page  := false
      |}.

  End TODO_MOVE.

  Section TODO_dram.
    Definition enclave_base enc_id := Bits.to_nat (EnclaveParams.enclave_base enc_id).
    Definition enclave_max enc_id := Bits.to_nat (Bits.plus (EnclaveParams.enclave_base enc_id)
                                                            (EnclaveParams.enclave_size enc_id)).
    Definition shared_base := Bits.to_nat EnclaveParams.shared_mem_base.
    Definition shared_max := Bits.to_nat (Bits.plus EnclaveParams.shared_mem_base EnclaveParams.shared_mem_size).

    Definition memory_map : Type := EnclaveInterface.mem_region -> dram_t.

    Import EnclaveInterface.

    Definition addr_in_region (region: mem_region) (addr: nat): bool :=
      match region with
      | MemRegion_Enclave eid =>
          (enclave_base eid <=? addr) && (addr <? (enclave_max eid))
      | MemRegion_Shared =>
          (shared_base <=? addr) && (addr <? shared_max)
      | MemRegion_Other => false
      end.

    Definition filter_dram : dram_t -> mem_region -> dram_t :=
      fun dram region addr =>
        if addr_in_region region addr then
          dram addr
        else None.

    (* NOTE: the current representation of memory regions is probably non-ideal... *)
    Definition get_dram : memory_map -> enclave_config -> dram_t :=
      fun mem_map enclave_config addr =>
        let enclave_region := MemRegion_Enclave enclave_config.(eid) in
        if addr_in_region enclave_region addr then
          (mem_map enclave_region) addr
        else if enclave_config.(shared_page) && (addr_in_region MemRegion_Shared addr) then
          (mem_map MemRegion_Shared) addr
        else None.

    Definition update_regions (config: enclave_config) (dram: dram_t)
                              (regions: memory_map)
                              : memory_map :=
      fun region =>
        if mem_region_beq region MemRegion_Shared && config.(shared_page) then
          filter_dram dram MemRegion_Shared
        else if mem_region_beq region (MemRegion_Enclave config.(eid)) then
          filter_dram dram region
        else regions region.

  End TODO_dram.

  Section Spec.

    Record props_t :=
      { P_input : Prop;
        P_output : Prop;
        P_feedback: Prop
      }.
    Definition valid_inputs (props: list props_t) :=
      AND (List.map P_input props).
    Definition valid_feedback (props: list props_t) :=
      AND (List.map P_feedback props).
    Definition valid_output (props: list props_t) :=
      AND (List.map P_output props).

    Definition trivial_props : props_t :=
      {| P_input := True;
         P_output := True;
         P_feedback := True
      |}.


    (* Interface properties *)
    Definition valid_input_log__common (input_log: Log R_external ContextEnv) : Prop.
    Admitted.

    Definition valid_output_log__common (output_log: Log R_external ContextEnv) : Prop.
    Admitted.

    Definition valid_feedback_log__common (log: Log R_external ContextEnv) : Prop :=
      log = log_empty.

    Import EnclaveInterface.

    Inductive state_phase :=
    | SpecSt_Running (config: enclave_config)
    | SpecSt_Waiting.

    Definition local_spec_state_t : Type := state * state_phase.

    Record spec_state_t :=
      { machine0 : local_spec_state_t;
        machine1 : local_spec_state_t;
        regions: memory_map;
      }.

    Definition initial_regions initial_dram : memory_map :=
      fun region => filter_dram initial_dram region.

    Definition initial_spec_state (initial_dram: dram_t) : spec_state_t :=
      let mem0 := initial_state (initial_regions initial_dram (MemRegion_Enclave Enclave0)) in
      let mem1 := initial_state (initial_regions initial_dram (MemRegion_Enclave Enclave1)) in
      {| machine0 := (mem0, SpecSt_Running initial_enclave_config0);
         machine1 := (mem1, SpecSt_Running initial_enclave_config1);
         regions := initial_regions initial_dram
      |}.

    Definition external_state_is_reset (st: state) (core_id: ind_core_id): Prop :=
      forall reg, external_reg_to_taint reg = core_id ->
             ContextEnv.(getenv) (fst st) (external reg) = r_external reg.

    Definition output_t := Log R_external ContextEnv.

    Definition get_purge_reg (core: ind_core_id) : external_reg_t :=
      match core with
      | CoreId0 => purge0
      | CoreId1 => purge1
      end.

    Definition get_dram_from_state (st: state) : dram_t :=
      let '(_, (dram, _)) := st in dram.

    (* TODO: infer this *)
    Definition pf_R_ext_purge_reg: forall core,
        (R (external (get_purge_reg core))) = enum_t purge_state.
    Proof.
      destruct core; reflexivity.
    Defined.

    Definition filter_step (step: step_io) (core: ind_core_id) : step_io :=
      {| step_input := filter_ext_log (step_input step) core;
         step_feedback := filter_ext_log (step_feedback step) core
      |}.

    Definition proj_ifc_io (step: ifc_io) (core: ind_core_id) : step_io * option enclave_config :=
      (filter_step step.(ifc_step) core, get_input_config step core).

    Definition do_local_step_trans__spec (machine: local_spec_state_t)
                                       (core: ind_core_id)
                                       (step: step_io)
                                       (opt_config: option enclave_config)
                                       (mem_map: memory_map)
                                       : local_spec_state_t * output_t * memory_map :=
      let '(st, phase) := machine in
      let '(st', output) := do_step__impl st step in
      let ext_output := proj_log__ext output in
      let purge_reg := get_purge_reg core in
      match phase with
      | SpecSt_Running config =>
          let continue := ((st', phase), ext_output, mem_map) in
          let ext_st' := get_dram_from_state st' in
          match rew_latest_write output (external purge_reg) (pf_R_ext_purge_reg core) with
          | Some v => if bits_eqb v ENUM_purge_purged
                     then ((st', SpecSt_Waiting), ext_output, update_regions config ext_st' mem_map)
                     else continue
          | None => continue
          end
      | SpecSt_Waiting =>
          let continue := ((st', SpecSt_Waiting), ext_output, mem_map) in
          let input_log := step.(step_input) in
          match rew_latest_write input_log purge_reg (pf_R_ext_purge_reg core), opt_config with
          | Some v, Some config =>
             if bits_eqb v ENUM_purge_restart then
               let dram := get_dram mem_map config in
               ((initial_state dram, SpecSt_Running config), ext_output, mem_map)
             else (* don't care *) continue
          | _, _ => continue
          end
      end.

    Definition do_step_trans__spec (spec_st: spec_state_t) (step: ifc_io)
                                 : spec_state_t * output_t * output_t :=
      let '(step0, config0) := proj_ifc_io step CoreId0 in
      let '(step1, config1) := proj_ifc_io step CoreId1 in
      let '(machine0', output0, mem_map') :=
          do_local_step_trans__spec (machine0 spec_st) CoreId0 step0 config0 (regions spec_st) in
      let '(machine1', output1, mem_map'') :=
          do_local_step_trans__spec (machine1 spec_st) CoreId1 step1 config1 mem_map' in
      ({| machine0 := machine0';
          machine1 := machine1';
          regions := mem_map'' |}, output0, output1).

    Definition only_write_ext_purge (log: Log R_external ContextEnv) (core: ind_core_id) (v: bits_t 2) : Prop :=
      let purge_reg := get_purge_reg core in
         rew_latest_write log purge_reg (pf_R_ext_purge_reg core) = Some v
      \/ latest_write log purge_reg = None.

    (* addr req are in range *)
    Definition mem_reqs_in_config (log: Log R_external ContextEnv) (config: enclave_config) (core: ind_core_id)
                                  : Prop.
    Admitted.

    Definition disjoint_configs (opt_config0: option enclave_config) (opt_config1: option enclave_config) : Prop :=
      match opt_config0, opt_config1 with
      | Some config0, Some config1 =>
          config0.(eid) <> config1.(eid) /\ (config0.(shared_page) && config1.(shared_page) = false)
      | _, _ => True
      end.

    Definition valid_local_step_input (local_st: local_spec_state_t)
                                      (core: ind_core_id)
                                      (step: step_io)
                                      (opt_config: option enclave_config)
                                      (mem_map: memory_map)
                                      : Prop :=
      let '(st, phase) := local_st in
      let '(st', output, _) := do_local_step_trans__spec local_st core step opt_config mem_map in
      let purge := get_purge_reg core in
      let input := step.(step_input) in
      valid_input_log__common input /\
      match phase with
      | SpecSt_Running config =>
          (* TODO: inputs belong to the enclave *)
          only_write_ext_purge input core ENUM_purge_purging /\
          opt_config = Some config /\
          mem_reqs_in_config input config core
      | SpecSt_Waiting =>
          only_write_ext_purge input core ENUM_purge_restart /\
          (rew_latest_write input purge (pf_R_ext_purge_reg core) = Some ENUM_purge_restart ->
           opt_config <> None /\
           external_state_is_reset (fst st') core (* TODO: whose responsibility to clear FIFOs? *)
          )
      end.

    Definition valid_step_input__spec (spec_st: spec_state_t) (step: ifc_io) : Prop :=
      let '(step0, config0) := proj_ifc_io step CoreId0 in
      let '(step1, config1) := proj_ifc_io step CoreId1 in
      let '(_, _, mem_map') :=
          do_local_step_trans__spec (machine0 spec_st) CoreId0 step0 config0 (regions spec_st) in
      valid_local_step_input (machine0 spec_st) CoreId0 step0 config0 (regions spec_st) /\
      valid_local_step_input (machine1 spec_st) CoreId1 step1 config1 mem_map' /\
      (* not same config *)
      disjoint_configs config0 config1 /\
      (* only one restart at a time *)
      (not (latest_write step0.(step_input) purge0 = Some ENUM_purge_restart /\
          latest_write step1.(step_input) purge1 = Some ENUM_purge_restart)) /\
      valid_input_log__common step.(ifc_step).(step_input). (* TODO *)

    (* Not very interesting: machine0 only outputs to external0; behaves like interface *)
    Definition valid_step_output__spec (spec_st: spec_state_t) (step: ifc_io) : Prop.
    Admitted.

    Definition spec_output_t : Type := output_t * output_t.

    Definition do_step__spec (spec_st: spec_state_t) (step: ifc_io)
                           : spec_state_t * spec_output_t * props_t :=
      let '(st', log0, log1) := do_step_trans__spec spec_st step in
      let props' := {| P_input := valid_step_input__spec spec_st step;
                       P_output := valid_step_output__spec spec_st step;
                       P_feedback := valid_feedback_log__common step.(ifc_step).(step_feedback)
                    |} in
      (st', (log0, log1), props').

    Definition do_steps__spec (initial_dram: dram_t) (steps: list ifc_io)
                            : spec_state_t * list spec_output_t * list props_t :=
      fold_left (fun '(st, evs0, props) step =>
                   let '(st', ev0, prop) := do_step__spec st step in
                   (st', evs0 ++ [ev0], props ++ [prop]))
                steps (initial_spec_state initial_dram, [], []).

  End Spec.

  Section Correctness.

    (* TODO: clean *)
    Definition log_equivalent (koika_log: Log R ContextEnv) (spec_log: Log R_external ContextEnv) : Prop :=
      forall (reg: external_reg_t),
        latest_write koika_log (external reg) = latest_write spec_log reg /\
        (forall port, may_read koika_log port (external reg) = may_read spec_log port reg) /\
        (forall port, may_write koika_log log_empty port (external reg) =
                 may_write spec_log log_empty port reg).

    Definition tau_equivalent (impl_tau: Log R ContextEnv) (spec_tau: spec_output_t) : Prop :=
      let (log0, log1) := spec_tau in
      let spec_ext_log := ContextEnv.(create)
                            (fun reg => match external_reg_to_taint reg with
                                     | CoreId0 => ContextEnv.(getenv) log0 reg
                                     | CoreId1 => ContextEnv.(getenv) log1 reg
                                     end) in
      log_equivalent impl_tau spec_ext_log.

    Definition trace_equivalent (koika_tr: list (Log R ContextEnv))
                                (spec_tr: list spec_output_t) : Prop :=
      Forall2 tau_equivalent koika_tr spec_tr.

    Axiom correctness :
      forall (initial_dram: dram_t)
        (steps: list ifc_io)
        (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
        (koika_st: state) (koika_tr: list (Log R ContextEnv)),
      valid_inputs props ->
      valid_feedback props ->
      do_steps__spec initial_dram steps = (spec_st, spec_tr, props) ->
      do_steps__impl initial_dram (List.map ifc_step steps) = (koika_st, koika_tr) ->
      trace_equivalent koika_tr spec_tr.

  End Correctness.

  Section Compliance.
    Axiom compliance:
      forall (initial_dram: dram_t)
        (steps: list ifc_io)
        (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
        (koika_st: state) (koika_tr: list (Log R ContextEnv)),
      valid_inputs props ->
      valid_feedback props ->
      do_steps__spec initial_dram steps = (spec_st, spec_tr, props) ->
      do_steps__impl initial_dram (List.map ifc_step steps) = (koika_st, koika_tr) ->
      valid_output props.

  End Compliance.

  (*
  Section Taint.
    Inductive taint_t :=
    | TaintCore (id: ind_core_id)
    | Bottom. 

    Definition external_reg_to_taint (st: state) (reg: reg_t) : option taint_t :=
      match reg with
      | toIMem0 st => Some (TaintCore CoreId0)
      | toIMem1 st => Some (TaintCore CoreId1)
      | toDMem0 st => Some (TaintCore CoreId0)
      | toDMem1 st => Some (TaintCore CoreId1)
      | fromIMem0 st => Some (TaintCore CoreId0)
      | fromIMem1 st => Some (TaintCore CoreId1)
      | fromDMem0 st => Some (TaintCore CoreId0)
      | fromDMem1 st => Some (TaintCore CoreId1)
      | purge0 => Some (TaintCore CoreId0)
      | purge1 => Some (TaintCore CoreId1)
      | internal st => None (* not external *)
      end.

    Definition reg_to_taint (reg: reg_t) (st: state) : option ind_core_id. Admitted.

  End Taint.

  Section Valid.
    Definition valid_input_log (st: state) (log: Log R ContextEnv) : Prop. Admitted.
    Definition valid_input_state (st: state) : Prop. Admitted.

    Definition valid_reset_state (st: state) (core_id: ind_core_id): Prop :=
      forall reg, reg_to_taint reg st = Some core_id ->
             ContextEnv.(getenv) (fst st) reg = r reg.

    Parameter (initial_dram: dram_t).
    Definition valid_initial_state (st: state) : Prop. Admitted.
  End Valid.
  
  Section GhostState.

    Record ghost_state :=
      { ghost_taint0 : EnclaveInterface.mem_region -> bool;
        ghost_taint1 : EnclaveInterface.mem_region -> bool;
        hist0 : list (Log R ContextEnv);
        hist1 : list (Log R ContextEnv);
      }.

    Definition initial_ghost_st : ghost_state :=
      {| ghost_taint0 := fun _ => false;
         ghost_taint1 := fun _ => false;
         hist0 := [];
         hist1 := [];
      |}.

k    Definition bits_eqb {sz} (v1: bits_t sz) (v2: bits_t sz) : bool :=
      N.eqb (Bits.to_N v1) (Bits.to_N v2).

    Definition observe_imem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toIMem0 MemReq.valid0) eq_refl
                   (toIMem0 MemReq.data0) eq_refl log.

    Definition observe_imem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toIMem1 MemReq.valid0) eq_refl
                   (toIMem1 MemReq.data0) eq_refl log.

    Definition observe_imem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) 
      :=
      match core_id with
      | CoreId0 => observe_imem_reqs_to_mem0 log
      | CoreId1 => observe_imem_reqs_to_mem1 log
      end.

    Definition observe_dmem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toDMem0 MemReq.valid0) eq_refl
                   (toDMem0 MemReq.data0) eq_refl log.

    Definition observe_dmem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toDMem1 MemReq.valid0) eq_refl
                   (toDMem1 MemReq.data0) eq_refl log.

    Definition observe_dmem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_dmem_reqs_to_mem0 log
      | CoreId1 => observe_dmem_reqs_to_mem1 log
      end.

    Definition addr_to_mem_region (addr: bits_t 32) : EnclaveInterface.mem_region. Admitted.

    Definition update_taint_fn (core_id: ind_core_id) (input_log: Log R ContextEnv) 
                               (taint_fn : EnclaveInterface.mem_region -> bool)
                               : EnclaveInterface.mem_region -> bool :=
      let imem_reqs_opt := observe_imem_reqs_to_mem input_log core_id in
      let dmem_reqs_opt := observe_dmem_reqs_to_mem input_log core_id in
      let fn' := match imem_reqs_opt with
                 | Some req => let req_region := addr_to_mem_region (mem_req_get_addr req) in
                              (fun region => if EnclaveInterface.mem_region_beq region req_region then true
                                          else taint_fn region)
                 | None => taint_fn
                 end in
      match dmem_reqs_opt with
      | Some req => let req_region := addr_to_mem_region (mem_req_get_addr req) in
                   (fun region => if EnclaveInterface.mem_region_beq region req_region then true
                               else fn' region)
      | None => taint_fn
      end.

    Definition filter_external_log (input: Log R ContextEnv) (core: ind_core_id) : Log R ContextEnv. Admitted.

    Definition get_dram (st: state) : dram_t. Admitted.

    (* TODO: code duplication *)
    Section Dram.
      Definition memory_map : Type := EnclaveInterface.mem_region -> dram_t.
      Definition enclave_base enc_id := Bits.to_nat (EnclaveParams.enclave_base enc_id).
      Definition enclave_max enc_id := Bits.to_nat (Bits.plus (EnclaveParams.enclave_base enc_id)
                                                              (EnclaveParams.enclave_size enc_id)).

      Definition shared_base := Bits.to_nat EnclaveParams.shared_mem_base.
      Definition shared_max := Bits.to_nat (Bits.plus EnclaveParams.shared_mem_base EnclaveParams.shared_mem_size).

      Import EnclaveInterface.

      Definition addr_in_region (region: mem_region) (addr: nat): bool :=
        match region with
        | MemRegion_Enclave eid =>
            (enclave_base eid <=? addr) && (addr <? (enclave_max eid))
        | MemRegion_Shared =>
            (shared_base <=? addr) && (addr <? shared_max)
        | MemRegion_Other => false
        end.

      Definition filter_dram : dram_t -> mem_region -> dram_t :=
        fun dram region addr =>
          if addr_in_region region addr then
            dram addr
          else None.

      (* NOTE: the current representation of memory regions is probably non-ideal... *)
      Definition get_dram_from_mem_map : memory_map -> enclave_config -> dram_t :=
        fun mem_map enclave_config addr =>
          let enclave_region := MemRegion_Enclave enclave_config.(eid) in
          if addr_in_region enclave_region addr then
            (mem_map enclave_region) addr
          else if enclave_config.(shared_page) && (addr_in_region MemRegion_Shared addr) then
            (mem_map MemRegion_Shared) addr
          else None.

      (* Copy back relevant regions of dram *)
      Definition update_regions (config: enclave_config) (dram: dram_t)
                                (regions: memory_map)
                                : memory_map :=
        fun region =>
          if mem_region_beq region MemRegion_Shared && config.(shared_page) then
            filter_dram dram MemRegion_Shared
          else if mem_region_beq region (MemRegion_Enclave config.(eid)) then
            filter_dram dram region
          else regions region.

    End Dram.

    Section IsolationSpec.

      Inductive MemoryState :=
      | MemoryState_Running (config: EnclaveInterface.enclave_config) (st: state)
      | MemoryState_Waiting
      . 

      (* IDEA!: isolation as piecewise simulation? *)
      Record isolated_state :=
        { machine0: MemoryState;
          machine1: MemoryState;
          regions : memory_map;
        }.

    Definition update_ghost_state (ghost: ghost_state) (st: state) (input: Log R ContextEnv)
                                  (final: Log R ContextEnv) : ghost_state :=
      let post_inputs := {| ghost_taint0 := update_taint_fn CoreId0 input ghost.(ghost_taint0);
                            ghost_taint1 := update_taint_fn CoreId1 input ghost.(ghost_taint1);
                            hist0 := ghost.(hist0) ++ [filter_external_log input CoreId0];
                            hist1 := ghost.(hist1) ++ [filter_external_log input CoreId1];
                         |} in
      let do_resets := {| ghost_taint0 := match latest_write final purge0 with
                                          | None => post_inputs.(ghost_taint0)
                                          | Some v => if bits_eqb v ENUM_purge_purged
                                                     then (fun _ => false)
                                                     else post_inputs.(ghost_taint0)
                                          end;
                          ghost_taint1 := match latest_write final purge1 with
                                          | None => post_inputs.(ghost_taint1)
                                          | Some v => if bits_eqb v ENUM_purge_purged
                                                     then (fun _ => false)
                                                     else post_inputs.(ghost_taint1)
                                          end;
                          (* TODO: ugly; move to above *)
                          hist0 := match latest_write input purge0 with
                                   | None => post_inputs.(hist0)
                                   | Some v => if bits_eqb v ENUM_purge_restart
                                              then []
                                              else post_inputs.(hist0)
                                   end;
                          hist1 := match latest_write input purge1 with
                                   | None => post_inputs.(hist1)
                                   | Some v => if bits_eqb v ENUM_purge_restart
                                              then []
                                              else post_inputs.(hist1)
                                   end;
                       |} in
      ghost.

  End GhostState.

  (* Cheating: no feedback *)
  Section CycleModel.
    Definition prop_holds_about_step (st: state) (input: Log R ContextEnv)
                                     (P: state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> Prop) : Prop :=
      let '(update, ext_st') := update_function st input in
      P st input update ext_st'.


    Definition ghost_prop_holds_about_step (st: state) (ghost: ghost_state) (input: Log R ContextEnv)
               (P: state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> Prop) : Prop :=
      let '(update, ext_st') := update_function st input in
      P st ghost input update ext_st'.

    Fixpoint prop_holds_for_steps (inputs: list (Log R ContextEnv)) (st: state) 
                                  (P: state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> Prop) : Prop :=
      match inputs with
      | [] => True
      | input :: inputs =>
        let state' := do_step st input in
        prop_holds_about_step st input P /\
        prop_holds_for_steps inputs state' P
      end.

    Definition do_step_with_ghost (st: state) (ghost: ghost_state) (input: Log R ContextEnv): state * ghost_state :=
      let '(update, ext_st') := update_function st input in
      (do_step st input, update_ghost_state ghost st input update).

    Fixpoint ghost_prop_holds_for_steps (inputs: list (Log R ContextEnv)) (st: state) (ghost: ghost_state)
                                  (P: state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> Prop) : Prop :=
      match inputs with
      | [] => True
      | input :: inputs =>
        let (state',ghost') := do_step_with_ghost st ghost input in
        ghost_prop_holds_about_step st ghost input P /\
        ghost_prop_holds_for_steps inputs state' ghost' P
      end.

      (* If we never reset, partitioning is fine: run on disjoint machines with the same initial relevant dram.
       * (More specifically, the outputs at each step for a core are the same as if we ran with filtered inputs)
       * Whenever we reset, we want to say that until the next reset, the outputs are the same as if we ran with
       * a new machine with the relevant dram.
       * - And when we are in the process of resetting, there are no outputs.
       *)
    Definition disjoint_taints (ghost: ghost_state) : Prop :=
      forall (region: EnclaveInterface.mem_region), (ghost.(ghost_taint0) region && ghost.(ghost_taint1) region) = false.

    Definition P_disjoint_taints (core_id: ind_core_id)
               : state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> Prop :=
      fun st ghost input_log output_log _ =>
      disjoint_taints ghost.

    Definition P_valid_input : state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> Prop.
    Admitted.

    Definition output_state_for_step (st: state) (input: Log R ContextEnv) 
                                     {T: Type} (O: state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> T)
                                     : T :=
      let '(update, ext_st') := update_function st input in
      O st input update ext_st'.

    Fixpoint output_state_for_steps (inputs: list (Log R ContextEnv)) (st: state) {T: Type}
                                    (O: state -> Log R ContextEnv -> Log R ContextEnv -> external_state_t -> T) 
                                    : list T :=
      match inputs with
      | [] => []
      | input :: inputs =>
          let state' := do_step st input in
          let output := output_state_for_step st input O in
          let outputs := output_state_for_steps inputs state' O in
          output :: outputs 
      end.

    Axiom partitioned_from_creation:
      forall (core_id: ind_core_id) (st: state),
      valid_initial_state st ->
      forall (inputs: list (Log R ContextEnv)),
      prop_holds_for_steps inputs st P_valid_input ->
      ghost_prop_holds_for_steps inputs st initial_ghost_st (P_disjoint_taints core_id).


  End CycleModel.
  *)
    (*
  Section Semantics.
    Definition state := env_t ContextEnv (fun idx : reg_t => R idx).
    Definition empty_log : Log R ContextEnv := log_empty.

    Parameter update_function : state -> Log R ContextEnv -> Log R ContextEnv.
      (* interp_scheduler' st ? rules log scheduler. *)
  End Semantics.

  Section Valid.
    Definition valid_input_log (st: state) (log: Log R ContextEnv) : Prop. Admitted.
    Definition valid_input_state (st: state) : Prop. Admitted.
    Definition valid_feedback_log : state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      fun st input_log output_log => input_log = output_log.

    Inductive taint_t :=
    | TaintCore (id: ind_core_id)
    | Bottom. 

    Definition external_reg_to_taint (st: state) (reg: reg_t) : option taint_t :=
      match reg with
      | toIMem0 st => Some (TaintCore CoreId0)
      | toIMem1 st => Some (TaintCore CoreId1)
      | toDMem0 st => Some (TaintCore CoreId0)
      | toDMem1 st => Some (TaintCore CoreId1)
      | fromIMem0 st => Some (TaintCore CoreId0)
      | fromIMem1 st => Some (TaintCore CoreId1)
      | fromDMem0 st => Some (TaintCore CoreId0)
      | fromDMem1 st => Some (TaintCore CoreId1)
      | purge0 => Some (TaintCore CoreId0)
      | purge1 => Some (TaintCore CoreId1)
      | internal st => None (* not external *)
      end.

    Definition reg_to_taint (reg: reg_t) (st: state) : option ind_core_id. Admitted.

    (* TODO *)
    Definition valid_reset_state (st: state) (core_id: ind_core_id): Prop :=
      forall reg, reg_to_taint reg st = Some core_id ->
             ContextEnv.(getenv) st reg = r reg.

  End Valid.

  Section CycleModel.

    Axiom partitioned : 
      forall (core_id: ind_core_id) (st: state),
      valid_initial_state st ->
      forall (inputs: list Log R ContextEnv)
        (outputs: list Log R ContextEnv)
        (

    (*
    Variable input_fn : state -> Log R ContextEnv.
    Variable pf_input_fn_generates_valid_log : forall (st: state), valid_input_log st (input_fn st).
    Variable feedback_fn : state -> Log R ContextEnv -> Log R ContextEnv.
    Variable pf_feedback_fn_generates_valid_log
      : forall (st: state) (log: Log R ContextEnv), valid_feedback_log st log (feedback_fn st log).
      *)

    Record ghost_state :=
      { ghost_taint0 : EnclaveInterface.mem_region -> bool;
        ghost_taint1 : EnclaveInterface.mem_region -> bool
      }.

    Definition initial_ghost_st : ghost_state :=
      {| ghost_taint0 := fun _ => false;
         ghost_taint1 := fun _ => false
      |}.

    Definition bits_eqb {sz} (v1: bits_t sz) (v2: bits_t sz) : bool :=
      N.eqb (Bits.to_N v1) (Bits.to_N v2).

    Definition observe_imem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toIMem0 MemReq.valid0) eq_refl
                   (toIMem0 MemReq.data0) eq_refl log.

    Definition observe_imem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toIMem1 MemReq.valid0) eq_refl
                   (toIMem1 MemReq.data0) eq_refl log.

    Definition observe_imem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) 
      :=
      match core_id with
      | CoreId0 => observe_imem_reqs_to_mem0 log
      | CoreId1 => observe_imem_reqs_to_mem1 log
      end.

    Definition observe_dmem_reqs_to_mem0 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toDMem0 MemReq.valid0) eq_refl
                   (toDMem0 MemReq.data0) eq_refl log.

    Definition observe_dmem_reqs_to_mem1 (log: Log R ContextEnv) : option (struct_t mem_req) :=
      observe_enq0 (toDMem1 MemReq.valid0) eq_refl
                   (toDMem1 MemReq.data0) eq_refl log.

    Definition observe_dmem_reqs_to_mem (log: Log R ContextEnv) (core_id: ind_core_id) : option (struct_t mem_req) :=
      match core_id with
      | CoreId0 => observe_dmem_reqs_to_mem0 log
      | CoreId1 => observe_dmem_reqs_to_mem1 log
      end.

    Definition addr_to_mem_region (addr: bits_t 32) : EnclaveInterface.mem_region. Admitted.

    Definition update_taint_fn (core_id: ind_core_id) (input_log: Log R ContextEnv) 
                               (taint_fn : EnclaveInterface.mem_region -> bool)
                               : EnclaveInterface.mem_region -> bool :=
      let imem_reqs_opt := observe_imem_reqs_to_mem input_log core_id in
      let dmem_reqs_opt := observe_dmem_reqs_to_mem input_log core_id in
      let fn' := match imem_reqs_opt with
                 | Some req => let req_region := addr_to_mem_region (mem_req_get_addr req) in
                              (fun region => if EnclaveInterface.mem_region_beq region req_region then true
                                          else taint_fn region)
                 | None => taint_fn
                 end in
      match dmem_reqs_opt with
      | Some req => let req_region := addr_to_mem_region (mem_req_get_addr req) in
                   (fun region => if EnclaveInterface.mem_region_beq region req_region then true
                               else fn' region)
      | None => taint_fn
      end.

    (* Bits equality? *)
    (* input log and output log? *)
    Definition update_ghost_state (ghost: ghost_state) (st: state) (input: Log R ContextEnv)
                                  (final: Log R ContextEnv) : ghost_state :=
      let post_inputs := {| ghost_taint0 := update_taint_fn CoreId0 input ghost.(ghost_taint0);
                            ghost_taint1 := update_taint_fn CoreId1 input ghost.(ghost_taint1)
                         |} in
      let do_resets := {| ghost_taint0 := match latest_write final purge0 with
                                          | None => post_inputs.(ghost_taint0)
                                          | Some v => if bits_eqb v ENUM_purge_purged
                                                     then (fun _ => false)
                                                     else post_inputs.(ghost_taint0)
                                          end;
                          ghost_taint1 := match latest_write final purge1 with
                                          | None => post_inputs.(ghost_taint1)
                                          | Some v => if bits_eqb v ENUM_purge_purged
                                                     then (fun _ => false)
                                                     else post_inputs.(ghost_taint1)
                                          end |} in
      ghost.

    Definition do_step (st: state) : state :=
      let input := input_fn st in
      let update := update_function st input in
      let final := feedback_fn st update in
      commit_update st final.

    Definition do_step_with_ghost (st: state) (ghost: ghost_state) : state * ghost_state :=
      let input := input_fn st in
      let update := update_function st input in
      let final := feedback_fn st update in
      (commit_update st final, update_ghost_state ghost st input final).

    Definition prop_holds_about_step (st: state) (P: state -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
      let input := input_fn st in
      let update := update_function st input in
      P st input update.

    Definition ghost_prop_holds_about_step (st: state) (ghost: ghost_state)
               (P: state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
      let input := input_fn st in
      let update := update_function st input in
      P st ghost input update.

    Fixpoint prop_holds_for_n_steps (n: nat) (st: state)
             (P: state -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
      match n with
      | 0 => True
      | S n' =>
        let state' := do_step st in
        prop_holds_about_step st P /\
        prop_holds_for_n_steps n' state' P
      end.

    Fixpoint ghost_prop_holds_for_n_steps (n: nat) (st: state) (ghost: ghost_state)
             (P: state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> Prop) : Prop :=
      match n with
      | 0 => True
      | S n' =>
        let (state', ghost') := do_step_with_ghost st ghost in
        ghost_prop_holds_about_step st ghost P /\
        ghost_prop_holds_for_n_steps n' state' ghost' P
      end.


    (* Properties:
     * - Reset model like in Core_sig
     * - Property of both traces: compute taint per core. While memory requests are "disjoint"/not tainted,
     *   output is ok.
     * - Extending multicycle framework with state will help
     *)

    Definition disjoint_taints (ghost: ghost_state) : Prop :=
      forall (region: EnclaveInterface.mem_region), (ghost.(ghost_taint0) region && ghost.(ghost_taint1) region) = false.

    (* TODO: this is tricky; equiv_st_for_core is too complex
     *)
    (*Definition equiv_st_for_core : ind_core_id -> state -> state -> Prop. Admitted.*)
    (* TODO: separate input/output? But need to reason about intermediate states... *)
    (*Definition equiv_log_for_core : ind_core_id -> Log R ContextEnv -> Log R ContextEnv -> Prop. Admitted.*)
    Definition equiv_input_log_for_core : ind_core_id -> Log R ContextEnv -> Log R ContextEnv -> Prop. Admitted.
    Definition equiv_output_log_for_core : ind_core_id -> Log R ContextEnv -> Log R ContextEnv -> Prop. Admitted.

    (* TODO: assert validity? *)
    (*
    Definition P_disjoint_taint_implies_partition (core_id: ind_core_id)
      : state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      fun st ghost input_log output_log =>
      disjoint_taints ghost ->
      forall st' log',
      equiv_st_for_core core_id st st' ->
      equiv_input_log_for_core core_id input_log log' ->
      equiv_output_log_for_core core_id output_log (update_function st' log').
    *)

    (* We can represent the state of memory as the history of inputs per core (interactions with external state).
     * We want to say: forall n,
     * - if we have disjoint taints (as defined by ghost state)
     * - then over n steps from an initial state, the per-cycle outputs from the combined inputs are the same 
     *   as from a different input function where we filter out the other inputs (or something like that?)
     * - Furthermore, we maintain the invariant that if we are in a purge state
     *   + we do nothing output-wise
     *   + the state after a write restart behaves as if it were an initial state
     *)
    Definition P_disjoint_taints (core_id: ind_core_id)
               : state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      fun st ghost input_log output_log =>
      disjoint_taints ghost.
    
    Scheme Equality for ind_core_id.

    (* Not a function of state b/c input is statically partitioned here *)
    Definition filter_input_log (st: state) (log: Log R ContextEnv) (core_id: ind_core_id) : Log R ContextEnv :=
      ContextEnv.(create)
        (fun reg => match external_reg_to_taint st reg with
                 | None => []
                 | Some (TaintCore core) => if ind_core_id_beq core core_id 
                                           then ContextEnv.(getenv) log reg
                                           else []
                 | Some (Bottom) => ContextEnv.(getenv) log reg
                 end).

    Definition do_transformed_step (input_transform: state -> Log R ContextEnv -> Log R ContextEnv) 
                                   (st: state) : state :=
      let input := input_transform st (input_fn st) in
      let update := update_function st input in
      let final := feedback_fn st update in
      commit_update st final.

    Definition do_filtered_step (core_id: ind_core_id) (st: state) : state :=
      do_transformed_step (fun st input_log => filter_input_log st input_log core_id) st.

    
    

    Axiom partitioned_from_creation:
      forall (core_id: ind_core_id) (st: state),
      valid_initial_state st ->
      forall (n: nat),
      ghost_prop_holds_for_n_steps n st initial_ghost_st (P_disjoint_taints core_id) ->
      


      prop_holds_for_n_steps n st (P_partition core_id).


    Definition P_partition (core_id: ind_core_id)
      : state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      fun st input_log output_log =>
      forall log',
      equiv_input_log_for_core core_id input_log log' ->
      equiv_output_log_for_core core_id output_log (update_function st log').


    (* TODO: external state? *)
    Definition valid_initial_state (st: state) :=
      forall reg, ContextEnv.(getenv) st reg = r reg.

    (* TODO: not enough to deal with resets, but it handles partitioning *)
    Axiom partitioned_from_creation:
      forall (core_id: ind_core_id) (st: state),
      valid_initial_state st ->
      forall (n: nat),
      ghost_prop_holds_for_n_steps n st initial_ghost_st (P_disjoint_taints core_id) ->
      prop_holds_for_n_steps n st (P_partition core_id).

    (* We know that as long as the taints are partitioned as defined with reset ghost state,
     * then when the input log is equivalent, the output log for that core is also equivalent.
     * Now we have to deal with
     * - Resets/Invariants about purge
     *   + Similar ones to Core
     *   + More specifically, when memory system writes purged (from a valid initial state),
     *     then at the next write of restart (barring valid inputs in the meantime), it should behave like
     *     a reset system at the partitioned interface
     * - Note: We will have to expose the clock here
     *)

    Definition purge_reg (core_id: ind_core_id) : reg_t :=
      match core_id with
      | CoreId0 => purge0
      | CoreId1 => purge1
      end.

    Lemma pf_R_purge_reg (core_id: ind_core_id) : R (purge_reg core_id) = enum_t purge_state.
    Proof. destruct core_id; reflexivity. Qed.

    Definition get_purge_reg (st: state) (core_id: ind_core_id) : enum_t purge_state :=
      match core_id with
      | CoreId0 => ContextEnv.(getenv) st purge0
      | CoreId1 => ContextEnv.(getenv) st purge1
      end.

    Definition update_no_writes_to_reg (st: state) (log: Log R ContextEnv) (reg: reg_t) : Prop :=
      latest_write (update_function st log) reg = latest_write log reg.

    (* What's the point of a restart state? Useful invariant for semantics? Really pointless... *)
    Inductive purge_state_machine (st: state) (log: Log R ContextEnv) (core_id: ind_core_id): Prop :=
    | PurgeRestart :
        forall (purge_state_eq: get_purge_reg st core_id = ENUM_purge_restart)
          (no_writes_or_write_ready: 
           update_no_writes_to_reg st log (purge_reg core_id) \/
           rew_latest_write (update_function st log) 
                            (purge_reg core_id) (pf_R_purge_reg core_id) = Some ENUM_purge_ready),
          purge_state_machine st log core_id
    | PurgeReady :
        forall (purge_state_eq: get_purge_reg st core_id = ENUM_purge_ready)
          (no_writes: update_no_writes_to_reg st log (purge_reg core_id)),
          purge_state_machine st log core_id
    | PurgePurging :
        forall (purge_state_eq: get_purge_reg st core_id = ENUM_purge_purging)
          (no_writes_or_write_purged: 
             update_no_writes_to_reg st log (purge_reg core_id) \/
             rew_latest_write (update_function st log) 
                              (purge_reg core_id) (pf_R_purge_reg core_id) = Some ENUM_purge_purged),
          purge_state_machine st log core_id
    | PurgePurged :
        forall (purge_state_eq: get_purge_reg st core_id = ENUM_purge_purged)
          (*(no_writes_to_any_reg: forall reg, update_no_writes_to_reg st log reg)*),
          purge_state_machine st log core_id
    .

    Definition P_purge_state_machine (core_id: ind_core_id)
               : state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      fun st input_log output_log =>
      purge_state_machine st input_log core_id.

    Axiom valid_purge_state_machine :
      forall (st: state) (log: Log R ContextEnv) (core_id: ind_core_id),
        valid_initial_state st ->
        forall (n: nat),
        prop_holds_for_n_steps n st (P_purge_state_machine core_id).

     * Given an n-step trace where the input taints are always partitioned,
     * - It's the same as 
     *)

    (* Partition
     * (x,y): 
     * + step 1: (input_x = input_x' -> output_x = output_x') -> (impl_st, spec_st')
     * + step 2: (same_input -> same_output) but now we are in different states, so that's not great       
     *)
  (*
    Definition P_
               : state -> ghost_state -> Log R ContextEnv -> Log R ContextEnv -> Prop :=
      fun st ghost input_log output_log =>
        

      (* st = purged => no output *)

      (* st = purged /\ latest_write is  *)

      forall st', valid_initial_state state' ->

      equiv_output_log_for_core core_id ? ?.

  End CycleModel.
*)

End Memory_sig.


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
  (* State purging *)
  | purge_core0
  | purge_core1
  | purge_mem0
  | purge_mem1
  (* Program counter? Doesn't /need/ to be here, but let's us avoid reasoning about Core code *)
  | pc0
  | pc1
  (* Register files *)
      (*
  | core0_rf (state: Rf.reg_t)
  | core1_rf (state: Rf.reg_t) 
  *)
  (* Core0 <-> SM *)
  | Core0ToSM_IMem (state: MemReq.reg_t)
  | Core0ToSM_DMem (state: MemReq.reg_t)
  | Core0ToSM_Enc (state: EnclaveReq.reg_t)
  | SMToCore0_IMem (state: MemResp.reg_t)
  | SMToCore0_DMem (state: MemResp.reg_t)
  (* Core1 <-> SM *)
  | Core1ToSM_IMem (state: MemReq.reg_t)
  | Core1ToSM_DMem (state: MemReq.reg_t)
  | Core1ToSM_Enc (state: EnclaveReq.reg_t)
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
    (* State purging*)
    | purge_core0 => enum_t purge_state
    | purge_core1 => enum_t purge_state
    | purge_mem0 => enum_t purge_state
    | purge_mem1 => enum_t purge_state
    | pc0 => bits_t 32
    | pc1 => bits_t 32
    (* Register files *)
    (*
    | core0_rf st => Rf.R st
    | core1_rf st => Rf.R st
    *)
    (* Core0 <-> SM *)
    | Core0ToSM_IMem st => MemReq.R st
    | Core0ToSM_DMem st => MemReq.R st
    | Core0ToSM_Enc st => EnclaveReq.R st
    | SMToCore0_IMem st => MemResp.R st
    | SMToCore0_DMem st => MemResp.R st
    (* Core1 <-> SM *)
    | Core1ToSM_IMem st => MemReq.R st
    | Core1ToSM_DMem st => MemReq.R st
    | Core1ToSM_Enc st => EnclaveReq.R st
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
    (* Purge state *)
    | purge_core0 => value_of_bits (Bits.zero)
    | purge_core1 => value_of_bits (Bits.zero)
    | purge_mem0 => value_of_bits (Bits.zero)
    | purge_mem1 => value_of_bits (Bits.zero)
    | pc0 => Params0.initial_pc
    | pc1 => Params1.initial_pc
    (* Register files *)
    (*
    | core0_rf st => Rf.r st
    | core1_rf st => Rf.r st
    *)
    (* Core0 <-> SM *)
    | Core0ToSM_IMem st => MemReq.r st
    | Core0ToSM_DMem st => MemReq.r st
    | Core0ToSM_Enc st => EnclaveReq.r st
    | SMToCore0_IMem st => MemResp.r st
    | SMToCore0_DMem st => MemResp.r st
    (* Core1 <-> SM *)
    | Core1ToSM_IMem st => MemReq.r st
    | Core1ToSM_DMem st => MemReq.r st
    | Core1ToSM_Enc st => EnclaveReq.r st
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
  Instance FiniteType_reg_t : FiniteType reg_t := _.
  (* Declare Instance FiniteType_reg_t : FiniteType reg_t.   *)

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
      | Core0.toIMem s => Core0ToSM_IMem s
      | Core0.toDMem s => Core0ToSM_DMem s
      | Core0.toSMEnc s => Core0ToSM_Enc s
      | Core0.fromIMem s => SMToCore0_IMem s
      | Core0.fromDMem s => SMToCore0_DMem s
      (* | Core0.rf s => core0_rf s *)
      | Core0.pc => pc0
      | Core0.purge => purge_core0
      | Core0.internal s => Core0_internal s
      end.

    Definition Lift_core0 : RLift _ Core0.reg_t reg_t Core0.R R := ltac:(mk_rlift core0_lift).
    Definition FnLift_core0 : RLift _ Core0.ext_fn_t ext_fn_t Core0.Sigma Sigma := ltac:(lift_auto).

  End Core0_Lift.

  Section Core1_Lift.
    Definition core1_lift (reg: Core1.reg_t) : reg_t :=
      match reg with
      | Core1.core_id => core_id1
      | Core1.toIMem s => Core1ToSM_IMem s
      | Core1.toDMem s => Core1ToSM_DMem s
      | Core1.toSMEnc s => Core1ToSM_Enc s
      | Core1.fromIMem s => SMToCore1_IMem s
      | Core1.fromDMem s => SMToCore1_DMem s
      (* | Core1.rf s => core1_rf s *)
      | Core1.pc => pc1
      | Core1.purge => purge_core1
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
      | SM.fromCore0_Enc st => Core0ToSM_Enc st
      | SM.toCore0_IMem st => SMToCore0_IMem st
      | SM.toCore0_DMem st => SMToCore0_DMem st
      (* Core1 <-> SM *)
      | SM.fromCore1_IMem st => Core1ToSM_IMem st
      | SM.fromCore1_DMem st => Core1ToSM_DMem st
      | SM.fromCore1_Enc st => Core1ToSM_Enc st
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
      (* pc *)
      | SM.pc_core0 => pc0
      | SM.pc_core1 => pc1
      (* purge *)
      | SM.purge_core0 => purge_core0
      | SM.purge_core1 => purge_core1
      | SM.purge_mem0 => purge_mem0
      | SM.purge_mem1 => purge_mem1
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
      | Memory.purge0 => purge_mem0
      | Memory.purge1 => purge_mem1
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
      core0_schedule ||> core1_schedule ||> sm_schedule ||> mem_schedule.

  End Schedule.

  Definition reg_state : Type := env_t ContextEnv (fun idx: reg_t => R idx).

End Machine.
