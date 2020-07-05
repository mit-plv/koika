Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import dynamic_isolation.External.
Require Import dynamic_isolation.Interfaces.

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

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  Definition sigma := External.sigma.

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

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.
  Instance FiniteType_ext_reg_t : FiniteType external_reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Section CycleSemantics.
    Definition state := env_t ContextEnv (fun idx : reg_t => R idx).
    Definition empty_log : Log R ContextEnv := log_empty.

    Definition initial_state := ContextEnv.(create) r.

    Parameter update_function : state -> Log R ContextEnv -> Log R ContextEnv.
      (* interp_scheduler' st ? rules log scheduler. *)

    Definition log_t := Log R ContextEnv.
    Definition input_t := Log R_external ContextEnv.
    Definition output_t := Log R ContextEnv.
    Definition feedback_t := Log R_external ContextEnv.

    Record step_io :=
      { step_input : input_t;
        step_feedback: feedback_t
      }.

    Definition lift_ext_log (log: Log R_external ContextEnv) : Log R ContextEnv :=
      ContextEnv.(create) (fun reg => match reg return (RLog (R reg)) with
                                   | external s => ContextEnv.(getenv) log s
                                   | _ => []
                                   end).

    Definition do_step_input__koika (st: state) (ext_input: input_t) : output_t * log_t :=
       let input := lift_ext_log ext_input in
       let output := update_function st input in
       (output, log_app output input).

    Definition do_step__koika (st: state) (step: step_io)
                            : state * Log R ContextEnv :=
      let '(output, acc) := do_step_input__koika st step.(step_input) in
      let final := log_app (lift_ext_log step.(step_feedback)) acc in
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

  Section Spec.

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
    Inductive phase_state :=
    | SpecSt_Running
    | SpecSt_Waiting (rf: env_t ContextEnv Rf.R)
    .

    Definition spec_state_t : Type := state * phase_state.

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

    Definition do_step_trans_input__spec (spec_st: spec_state_t) (ext_input: input_t) : output_t * log_t :=
      do_step_input__koika (fst spec_st) ext_input.
    
    (* TODO: should really be inductive probably or option type? But too much effort to specify everything. *)
    Definition do_step_trans__spec (spec_st: spec_state_t) (step: step_io)
                           : spec_state_t * Log R_external ContextEnv :=
      let '(st, phase) := spec_st in
      let '(st', output) := do_step__koika st step in
      let ext_output := proj_log__ext output in 
      let final_st :=
        match phase with
        | SpecSt_Running =>
            let continue := (st', SpecSt_Running) in
            match latest_write output (external purge) with
            | Some v => if bits_eqb v ENUM_purge_purged
                       then (st', SpecSt_Waiting (extract_rf st'))
                       else continue
            | None => continue
            end
        | SpecSt_Waiting _rf =>
           let continue := (st', SpecSt_Waiting _rf) in
           match latest_write step.(step_feedback) purge,
                 latest_write step.(step_feedback) pc with
           | Some v, Some _pc =>
               if bits_eqb v ENUM_purge_restart then
                 ((initialise_with_rf _rf _pc), SpecSt_Running)
               else (* don't care *) continue
           | _, _ => continue
           end
        end in
      (final_st, ext_output).

    (* Behaves nicely with enq/deqs *)
    Definition valid_interface_log (st: state) (init_log: Log R_external ContextEnv) 
                                   (log: Log R_external ContextEnv) : Prop. Admitted.

    Definition no_writes (log: Log R_external ContextEnv) : Prop :=
      forall r, latest_write log r = None.

    Definition valid_step_output__spec (spec_st: spec_state_t) (step: step_io) : Prop :=
      let '(st, phase) := spec_st in
      let '(st', log) := do_step_trans__spec spec_st step in
      valid_output_log__common log /\
      valid_interface_log st log_empty log  /\
        (match phase with
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
      let '(st, phase) := spec_st in
      let '(st', output) := do_step_trans__spec spec_st step in
      let feedback := step.(step_feedback) in

      valid_feedback_log__common step.(step_feedback) /\
      valid_interface_log st (log_app output step.(step_input)) feedback /\
      match phase with
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

    Definition ext_log_equivalent (log0 log1: Log R_external ContextEnv) : Prop.
    Admitted.

    Definition log_equivalent (koika_log: Log R ContextEnv) (spec_log: Log R_external ContextEnv) : Prop :=
      forall (reg: external_reg_t), 
        latest_write koika_log (external reg) = latest_write spec_log reg /\
        (forall port, may_read koika_log port (external reg) = may_read spec_log port reg) /\
        (forall port, may_write koika_log log_empty port (external reg) =
                 may_write spec_log log_empty port reg).

    Definition trace_equivalent (koika_tr: list (Log R ContextEnv)) 
                                (spec_tr: list (Log R_external ContextEnv)) : Prop :=
      Forall2 log_equivalent koika_tr spec_tr.

    Axiom output_correctness:
      forall (steps: list step_io)
        (spec_st: spec_state_t) (spec_tr: list (Log R_external ContextEnv)) (props: list props_t)
        (koika_st: state) (koika_tr: list (Log R ContextEnv))
        (input: input_t) (output0 output1: output_t),
        valid_inputs props ->
        valid_feedback props ->
        do_steps__spec steps = (spec_st, spec_tr, props) ->
        do_steps__koika steps = (koika_st, koika_tr) ->
        fst (do_step_input__koika koika_st input) = output0 ->
        fst (do_step_trans_input__spec spec_st input) = output1 ->
        ext_log_equivalent (proj_log__ext output0) (proj_log__ext output1).

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

  (* TODO: code duplication *)

  (*
  Section Constraints.
    Definition state := env_t ContextEnv (fun idx : reg_t => R idx).
    Definition empty_log : Log R ContextEnv := log_empty.

    Definition update_function : state -> Log R ContextEnv -> Log R ContextEnv. Admitted.

    Definition update_no_writes_to_reg (st: state) (log: Log R ContextEnv) (reg: reg_t) : Prop :=
      latest_write (update_function st log) reg = latest_write log reg.

    Definition internal_reg_reset (st: state) (reg: internal_reg_t) : Prop :=
      ContextEnv.(getenv) st (internal reg) = r (internal reg).


    Definition reg_reset (st: state) (reg: reg_t) : Prop :=
      match reg with
      | external pc => True (* don't care *)
      | external purge => True (* don't care *)
      | external internal s => internal_reg_reset st s
      | _ => ContextEnv.(getenv) st reg = r reg
      end.

    Definition valid_reset_state (st: state) : Prop :=
      forall reg, reg_reset st reg.

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

    Definition valid_internal_state : state -> Prop. Admitted.

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
    Axiom write_purged_impl_in_reset_state :
      forall (st: state) (log: Log R ContextEnv),
      latest_write (update_function st log) purge = Some ENUM_purge_purged ->
      latest_write log purge <> Some ENUM_purge_purged ->
      valid_reset_state (commit_update st (update_function st log)).


  End Constraints.
  *)

End EmptyCore.
