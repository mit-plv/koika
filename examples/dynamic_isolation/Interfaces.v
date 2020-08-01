Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.

Require Import dynamic_isolation.FiniteType.
Require Import dynamic_isolation.Interp.
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

(* ======================= Contract between modules =================================
 * (Goal: chain outputs/inputs/feedback)
 *
 * Cores:
 * - inputs are empty
 * - outputs
 *   + obeys FIFO output interface (enqs/deqs, read only/write only registers)
 *   + Start in waiting state ==> no writes
 * - feedback
 *    + obeys FIFO interface
 *    + While Core running, SM only gets to write purging
 *    + Core waiting: SM only writes restart when public state is cleared (apart from, e.g., register file)
 *
 * SM
 * - input
 *   + obeys FIFO input interface (enq/deqs, read only/write only registers)
 *   + In switching state (for core) -> no writes from core
 * - output
 *   + obeys FIFO output interface (enq/deqs, read only/write only registers)
 *   + requests to memory are in the given enclave config
 * - feedback
 *   + Core/Mem in waiting state => no writes
 *   + obeys FIFO interface
 *
 * Mem
 * - inputs
 *   + While running, SM only gets to write purging
 *   + While waiting, SM only writes restart when public state is cleared
 *   + Inputs are in the allowed enclave configuration
 * - outputs
 *   + In Waiting state => no writes
 * - feedback is empty
 *
 * ======================= State simulation between modules =================================
 *
 *)

Section Util.
  Definition AND (Ps: list Prop) : Prop :=
    List.fold_left and Ps True.

  Definition bits_eqb {sz} (v1: bits_t sz) (v2: bits_t sz) : bool :=
    N.eqb (Bits.to_N v1) (Bits.to_N v2).

  Record props_t :=
    { P_input : Prop;
      P_output : Prop;
      P_feedback: Prop
    }.

  Definition valid_inputs (props: list props_t) :=
    AND (List.map P_input props).
  Definition valid_feedbacks (props: list props_t) :=
    AND (List.map P_feedback props).
  Definition valid_outputs (props: list props_t) :=
    AND (List.map P_output props).

  Definition trivial_props : props_t :=
    {| P_input := True;
       P_output := True;
       P_feedback := True
    |}.

End Util.

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

  (* TODO: do this better *)
  Inductive shared_id :=
  | Shared01
  | Shared02
  | Shared03
  | Shared12
  | Shared13
  | Shared23
  .

  Definition enclave_req :=
    {| struct_name := "enclave_req";
       struct_fields := [("eid", bits_t 32);
                         ("shared_regions", bits_t 6)]
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

  Scheme Equality for ind_core_id.

  (* TODO: rename to ind_cache_t *)
  Inductive ind_cache_type :=
  | CacheType_Imem
  | CacheType_Dmem
  .

  Scheme Equality for ind_cache_type.

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

  Record external_sig :=
    { _ext_fn_t : Type
    ; _Sigma : _ext_fn_t -> ExternalSignature
    ; _sigma :  (forall fn: _ext_fn_t, Sig_denote (_Sigma fn))
    ; _ext_fn_specs : _ext_fn_t -> ext_fn_spec
    }.

  Record private_module_sig :=
    { _private_reg_t : Type
    ; _R_private : _private_reg_t -> type
    ; _r_private : forall (idx: _private_reg_t), _R_private idx
    ; _FiniteType_private_reg_t : FiniteType _private_reg_t
    }.

  Record schedule_sig {rule_t: Type} :=
    { _rule_name_t: Type;
      _rules : _rule_name_t -> rule_t;
      _schedule : Syntax.scheduler pos_t _rule_name_t
    }.

  Record enclave_params_sig :=
    { _enclave_base : enclave_id -> addr_t
    ; _enclave_size : enclave_id -> bits_t 32
    ; _enclave_bootloader_addr : enclave_id -> addr_t
    ; _shared_region_base : shared_id -> addr_t
    ; _shared_region_size : bits_t 32
    }.

End Common.

(* TODO: need a well-formed predicate about address regions being disjoint *)
Module Type EnclaveParameters.
  Parameter params : Common.enclave_params_sig.
End EnclaveParameters.

Module Type CoreParameters.
  Parameter core_id : Common.core_id_t.
  Parameter initial_pc : Common.addr_t.
End CoreParameters.

Module Type External_sig.
  Parameter ext: Common.external_sig.

End External_sig.

Module Core_Common.
  Import Common.
  Inductive public_reg_t :=
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

  Instance FiniteType_public_reg_t : FiniteType public_reg_t := ltac:(FiniteTypeHelpers.FiniteType_t'').

  Definition R_public (idx: public_reg_t) : type :=
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

  Section Parameterised.
    Context {param_core_id: Common.core_id_t}.
    Context {initial_pc: addr_t}.
    Context {private_sig: private_module_sig}.
    Context {ext_sig: external_sig}.

    Definition private_reg_t := _private_reg_t private_sig.
    Definition R_private := _R_private private_sig.
    Definition r_private : forall (idx: private_reg_t), R_private idx := _r_private private_sig.
    Instance FiniteType_private_reg_t : FiniteType private_reg_t := _FiniteType_private_reg_t private_sig.

    Definition r_public (idx: public_reg_t) : R_public idx :=
      match idx with
      | core_id => param_core_id
      | toIMem s => MemReq.r s
      | fromIMem s => MemResp.r s
      | toDMem s => MemReq.r s
      | fromDMem s => MemResp.r s
      | toSMEnc s => EnclaveReq.r s
      | rf r => Rf.r r
      | pc => initial_pc
      | purge => value_of_bits (Bits.zero)
      end.

    Inductive reg_t :=
    | public (r: public_reg_t)
    | private (r: private_reg_t)
    .

    Definition R (idx: reg_t) : type :=
      match idx with
      | public r => R_public r
      | private r => R_private r
      end.

    Definition r idx : R idx :=
      match idx with
      | public s => r_public s
      | private s => r_private s
      end.

    Instance FiniteType_reg_t : FiniteType reg_t := _.

    Instance EqDec_reg_t : EqDec reg_t := _. (* a few seconds *)

    Definition ext_fn_t := _ext_fn_t ext_sig.
    Definition Sigma := _Sigma ext_sig.
    Definition rule := rule R Sigma.
    Definition sigma := _sigma ext_sig.

    Context {rule_name_t : Type}.
    Context {rules: rule_name_t -> rule}.
    Context {schedule: Syntax.scheduler pos_t rule_name_t}.

    Section CycleSemantics.
      Definition state := env_t ContextEnv (fun idx : reg_t => R idx).
      Definition empty_log : Log R ContextEnv := log_empty.

      Definition initial_state := ContextEnv.(create) r.

      Definition update_function : state -> Log R ContextEnv -> Log R ContextEnv :=
        fun st log => interp_scheduler_delta st sigma rules log schedule.

      Definition log_t := Log R ContextEnv.
      Definition input_t := Log R_public ContextEnv.
      Definition output_t := Log R ContextEnv.
      Definition feedback_t := Log R_public ContextEnv.

      Record step_io :=
        { step_input : input_t;
          step_feedback: feedback_t
        }.

      Definition lift_ext_log (log: Log R_public ContextEnv) : Log R ContextEnv :=
        ContextEnv.(create) (fun reg => match reg return (RLog (R reg)) with
                                     | public s => ContextEnv.(getenv) log s
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
      Definition proj_log__pub (log: Log R ContextEnv) : Log R_public ContextEnv :=
        ContextEnv.(create) (fun reg => ContextEnv.(getenv) log (public reg)).

        Definition tau := Log R_public ContextEnv.
        Definition trace := list tau.
    End Interface.

    Section Spec.

      Definition is_public_log (log: Log R ContextEnv) : Prop :=
        forall reg, match reg with
               | public r => True
               | private r => ContextEnv.(getenv) log reg = []
               end.

      (* TODO: to simplify for now, we say that the Core executes first *)

      Definition valid_input_log__common (input_log: Log R_public ContextEnv) : Prop :=
        input_log = log_empty.

      Definition valid_output_log__common (output_log: Log R ContextEnv) : Prop :=
        True.

      Definition valid_feedback_log__common (log: Log R_public ContextEnv) : Prop :=
        (* Writeback to public registers only *)
        latest_write log core_id = None /\
        (* TODO: Register file is really internal... we just wanted to be able to talk about it *)
        (forall s, latest_write log (rf s) = None).
      (*
        (latest_write log (public (toIMem MemReq.valid0)) = None \/
        latest_write log (public (toIMem MemReq.valid0)) = Some Ob~0).
        *)

      (* - While running, SM only gets to write purging (which doesn't change anything)
       * - Only Core writes purged, transitioning from running -> waiting
       * - Here, Core promises to not change public state
       * - Supposing that SM writes restart only when public state is cleared (apart from certain regs),
       * - Then simulation of resetting holds.
       *)
      Inductive phase_state :=
      | SpecSt_Running
      | SpecSt_Waiting (rf: env_t ContextEnv Rf.R)
      .

      Definition spec_state_t : Type := state * phase_state.

      Definition initial_spec_state : spec_state_t := (initial_state, SpecSt_Running).

      Definition only_write_ext_purge (log: Log R_public ContextEnv) (v: bits_t 2) : Prop :=
        latest_write log purge = Some v \/ latest_write log purge = None.

      Definition only_write_purge (log: Log R ContextEnv) (v: bits_t 2) : Prop :=
        latest_write log (public purge) = Some v \/ latest_write log (public purge) = None.

      Definition extract_rf (st: state) : env_t ContextEnv Rf.R :=
        ContextEnv.(create) (fun reg => ContextEnv.(getenv) st (public (rf reg))).

      Definition initialise_with_rf (initial_rf: env_t ContextEnv Rf.R) (initial_pc: bits_t 32) : state :=
        ContextEnv.(create) (fun reg => match reg return R reg with
                                     | public (rf s) => ContextEnv.(getenv) initial_rf s
                                     | public pc => initial_pc
                                     | s => r s
                                     end).

      Definition do_step_trans_input__spec (spec_st: spec_state_t) (ext_input: input_t) : output_t * log_t :=
        do_step_input__koika (fst spec_st) ext_input.

      (* TODO: should really be inductive probably or option type? But too much effort to specify everything. *)
      Definition do_step_trans__spec (spec_st: spec_state_t) (step: step_io)
                             : spec_state_t * Log R ContextEnv :=
        let '(st, phase) := spec_st in
        let '(st', output) := do_step__koika st step in
        let final_st :=
          match phase with
          | SpecSt_Running =>
              let continue := (st', SpecSt_Running) in
              match latest_write output (public purge) with
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
        (final_st, output).

      (* Behaves nicely with enq/deqs *)
      Definition valid_interface_log (st: state) (init_log: Log R_public ContextEnv)
                                     (log: Log R_public ContextEnv) : Prop. Admitted.

      Definition no_writes (log: Log R_public ContextEnv) : Prop :=
        forall r, latest_write log r = None.

      Definition valid_output  (spec_st: spec_state_t) (input: input_t) (output_log: output_t) : Prop.
      Admitted.

      (* Definition valid_step_output__spec (spec_st: spec_state_t) (step: step_io) : Prop := *)
      (*   let '(st, phase) := spec_st in *)
      (*   let '(st', log) := do_step_trans__spec spec_st step in *)
      (*   valid_output_log__common log /\ *)
      (*   valid_interface_log st log_empty (proj_log__pub log) /\ *)
      (*     (match phase with *)
      (*     | SpecSt_Running => True *)
      (*     | SpecSt_Waiting _ => *)
      (*         no_writes (proj_log__pub log) *)
      (*     end). *)

      Definition reset_public_state (st: state) : Prop :=
        forall reg, match reg with
               | rf _ => True
               | pc => True
               | purge => True
               | s => ContextEnv.(getenv) st (public s) = r_public s
               end.

      Definition valid_feedback (spec_st: spec_state_t) (input: input_t) (feedback: feedback_t) : Prop.
      Admitted.

      (* Definition valid_step_feedback__spec (spec_st: spec_state_t) (step: step_io) : Prop := *)
      (*   let '(st, phase) := spec_st in *)
      (*   let '(st', output) := do_step_trans__spec spec_st step in *)
      (*   let feedback := step.(step_feedback) in *)

      (*   valid_feedback_log__common step.(step_feedback) /\ *)
      (*   valid_interface_log st (log_app (proj_log__pub output) step.(step_input)) feedback /\ *)
      (*   match phase with *)
      (*   | SpecSt_Running => *)
      (*       only_write_ext_purge feedback ENUM_purge_purging *)
      (*   | SpecSt_Waiting _  => *)
      (*       only_write_ext_purge feedback ENUM_purge_restart /\ *)
      (*       (latest_write feedback purge = Some ENUM_purge_restart -> *)
      (*        latest_write feedback pc <> None /\ *)
      (*        reset_public_state (fst st') (* TODO: whose responsibility to clear FIFOs? *) *)
      (*       ) *)
      (*   end. *)

      Definition valid_input (spec_st: spec_state_t) (log: input_t) : Prop := valid_input_log__common log.

      Definition do_step__spec (spec_st: spec_state_t) (step: step_io)
                             : spec_state_t * Log R ContextEnv * props_t :=
        let '(st', log) := do_step_trans__spec spec_st step in
        let props' := {| P_input := valid_input spec_st step.(step_input);
                         P_output := valid_output spec_st step.(step_input) log;
                         P_feedback := valid_feedback spec_st step.(step_input) step.(step_feedback)
                      |} in
        (st', log, props').

      Definition do_steps__spec (steps: list step_io)
                              : spec_state_t * list (Log R ContextEnv) * list props_t :=
        fold_left (fun '(st, evs, props) step =>
                     let '(st', ev, prop) := do_step__spec st step in
                     (st', evs ++ [ev], props ++ [prop]))
                  steps (initial_spec_state, [], []).

    End Spec.

    Section Correctness.

      (* TODO: clean *)

      (* Potentially too strong *)
      Definition ext_log_equivalent (log0 log1: Log R_public ContextEnv) : Prop :=
        log0 = log1.

      Definition log_equivalent (koika_log: Log R ContextEnv) (spec_log: Log R ContextEnv) : Prop :=
        forall (reg: public_reg_t),
          latest_write koika_log (public reg) = latest_write spec_log (public reg) /\
          (forall port, may_read koika_log port (public reg) = may_read spec_log port (public reg)) /\
          (forall port, may_write koika_log log_empty port (public reg) =
                   may_write spec_log log_empty port (public reg)).

      Definition trace_equivalent (koika_tr: list (Log R ContextEnv))
                                  (spec_tr: list (Log R ContextEnv)) : Prop :=
        Forall2 log_equivalent koika_tr spec_tr.


      Definition output_log_equivalent (output0 output1 : Log R ContextEnv) : Prop :=
        ext_log_equivalent (proj_log__pub output0) (proj_log__pub output1).

      Definition P_output_correctness :=
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list (Log R ContextEnv)) (props: list props_t)
          (koika_st: state) (koika_tr: list (Log R ContextEnv))
          (input: input_t) (output0 output1: output_t),
          valid_inputs props ->
          valid_feedbacks props ->
          do_steps__spec steps = (spec_st, spec_tr, props) ->
          do_steps__koika steps = (koika_st, koika_tr) ->
          valid_input spec_st input ->
          fst (do_step_input__koika koika_st input) = output0 ->
          fst (do_step_trans_input__spec spec_st input) = output1 ->
          output_log_equivalent output0 output1.

      Definition P_correctness :=
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list (Log R ContextEnv)) (props: list props_t)
          (koika_st: state) (koika_tr: list (Log R ContextEnv)),
        valid_inputs props ->
        valid_feedbacks props ->
        do_steps__spec steps = (spec_st, spec_tr, props) ->
        do_steps__koika steps = (koika_st, koika_tr) ->
        trace_equivalent koika_tr spec_tr.

    End Correctness.

    Section Compliance.
      Definition P_output_compliance :=
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list (Log R ContextEnv)) (props: list props_t)
          (input: input_t) (output: output_t) (prop: props_t),
          valid_inputs props ->
          valid_feedbacks props ->
          do_steps__spec steps = (spec_st, spec_tr, props) ->
          valid_input spec_st input ->
          fst (do_step_trans_input__spec spec_st input) = output ->
          valid_output spec_st input output.

      Definition P_compliance :=
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list (Log R ContextEnv)) (props: list props_t),
        valid_inputs props ->
        valid_feedbacks props ->
        do_steps__spec steps = (spec_st, spec_tr, props) ->
        valid_outputs props.

    End Compliance.

    Section Lemmas.

      Lemma do_steps__koika_app__state:
        forall ios io,
        fst (do_steps__koika (ios ++ [io])) =
        fst (do_step__koika (fst (do_steps__koika ios)) io).
      Proof.
        intros. consider do_steps__koika.
        rewrite fold_left_app.
        unfold fold_left at 1.
        fast_destruct_goal_matches.
        unfold fst. rewrite_solve.
      Qed.

      Lemma do_step_rel_do_step_input__koika :
        forall st io,
        snd (do_step__koika st io) =
        fst (do_step_input__koika st (io.(step_input))).
      Proof.
        auto.
      Qed.

      Lemma do_steps__koika_app__trace :
        forall ios io,
        snd (do_steps__koika ios) ++ [fst (do_step_input__koika (fst (do_steps__koika ios)) (io.(step_input)) )] =
        snd (do_steps__koika (ios ++ [io])).
      Proof.
        intros. consider do_steps__koika.
        repeat rewrite fold_left_app.
        unfold fold_left at 3.
        fast_destruct_goal_matches.
        unfold snd.
        simpl fst at 2.
        rewrite<-do_step_rel_do_step_input__koika.
        rewrite_solve.
      Qed.

      Lemma do_steps__spec_app__state:
        forall ios io,
        fst (fst (do_steps__spec (ios ++ [io]))) =
        fst (fst (do_step__spec (fst (fst (do_steps__spec ios))) io)).
      Proof.
        intros. consider do_steps__spec.
        rewrite fold_left_app.
        unfold fold_left at 1.
        fast_destruct_goal_matches.
        unfold fst. rewrite_solve.
      Qed.

      Lemma do_step_rel_do_step_input__spec :
        forall st io,
        snd (fst (do_step__spec st io)) =
        fst (do_step_trans_input__spec st (io.(step_input))).
      Proof.
        consider do_step__spec.
        consider do_step_trans_input__spec.
        consider do_step_trans__spec.
        intros.
        rewrite <-do_step_rel_do_step_input__koika.
        destruct_goal_matches; unfold snd; unfold fst; rewrite_solve.
      Qed.

      Lemma do_steps__spec_app__trace :
        forall ios io,
        snd (fst (do_steps__spec ios)) ++ [fst (do_step_trans_input__spec (fst (fst (do_steps__spec ios))) (io.(step_input)) )] =
        snd (fst (do_steps__spec (ios ++ [io]))).
      Proof.
        intros. consider do_steps__spec.
        repeat rewrite fold_left_app.
        unfold fold_left at 3.
        fast_destruct_goal_matches.
        rewrite<-do_step_rel_do_step_input__spec.
        unfold fst; unfold snd.
        rewrite_solve.
      Qed.

    End Lemmas.

  End Parameterised.

End Core_Common.

Module Type Core_sig (External: External_sig) (Params: EnclaveParameters) (CoreParams: CoreParameters).
  Import Common.
  Import Core_Common.

  Parameter private_params : private_module_sig.

  Parameter rule_name_t : Type.

  (* TODO: make these notations? *)
  Definition reg_t := @Core_Common.reg_t private_params.
  Definition r := @Core_Common.r CoreParams.core_id CoreParams.initial_pc private_params.
  Definition R := @Core_Common.R private_params.

  (* Declare Instance FiniteType_reg_t : FiniteType reg_t. *)
  Definition rule := @Core_Common.rule private_params External.ext.
  Definition sigma := @Core_Common.sigma External.ext.
  Definition Sigma := @Core_Common.Sigma External.ext.

  Parameter rules  : rule_name_t -> rule.

  Parameter schedule : Syntax.scheduler pos_t rule_name_t.

  Instance FiniteType_reg_t : FiniteType reg_t := @Core_Common.FiniteType_reg_t private_params.

  (* TODO: clean up instantiation *)
  Parameter output_correctness : @P_output_correctness CoreParams.core_id CoreParams.initial_pc
                                                       private_params External.ext
                                                       rule_name_t rules schedule.
  Parameter correctness : @P_correctness CoreParams.core_id CoreParams.initial_pc
                                         private_params External.ext
                                         rule_name_t rules schedule.

  Parameter output_compliance : @P_output_compliance CoreParams.core_id CoreParams.initial_pc
                                                     private_params External.ext
                                                     rule_name_t rules schedule.

  Parameter compliance : @P_compliance CoreParams.core_id CoreParams.initial_pc
                                       private_params External.ext
                                       rule_name_t rules schedule.

End Core_sig.

Module EnclaveInterface.
  Import Common.

  Definition enclave_data :=
    {| struct_name := "enclave_data";
       struct_fields := [("eid", bits_t 32);
                         ("shared_regions", bits_t 6);
                         ("valid", bits_t 1)
                        ]
    |}.

  Record struct_enclave_data :=
    { enclave_data_eid : bits_t 32;
      enclave_data_shared_regions : bits_t 6;
      enclave_data_valid : bits_t 1;
    }.

  (* TODO: remove Other? *)
  Inductive mem_region :=
  | MemRegion_Enclave (eid: enclave_id)
  | MemRegion_Shared (id: shared_id)
  | MemRegion_Other
  .

  Scheme Equality for mem_region.

  Definition mk_enclave_data (data: struct_enclave_data) : struct_t enclave_data :=
    (data.(enclave_data_eid), (data.(enclave_data_shared_regions), (data.(enclave_data_valid), tt))).
    (* (data.(enclave_data_eid), *)
    (*  (data.(enclave_data_addr_min), (data.(enclave_data_size),  *)
    (*                                  (data.(enclave_data_shared_regions), (data.(enclave_data_valid), tt))))). *)

  (* TODO: generalize this. *)
  Definition extract_enclave_data (data: struct_t enclave_data) : struct_enclave_data :=
      (* let '(eid, (addr_min, (size, (shared_regions, (valid, _))))) := data in *)
      let '(eid, (shared_regions, (valid, _))) := data in
      {| enclave_data_eid := eid;
         (* enclave_data_addr_min := addr_min; *)
         (* enclave_data_size := size; *)
         enclave_data_shared_regions := shared_regions;
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
      shared_regions : shared_id -> bool;
    }.

  Definition bits_regions_to_function (regions: bits_t 6) : shared_id -> bool :=
      match vect_to_list regions with
      | [s01; s02; s03; s12; s13; s23] =>
          fun id =>
            match id with
            | Shared01 => s01
            | Shared02 => s02
            | Shared03 => s03
            | Shared12 => s12
            | Shared13 => s13
            | Shared23 => s23
            end
      | _ => fun _ => false (* should not occur *)
      end.

  Definition shared_region_config_to_bits (config: shared_id -> bool) : bits_t 6 :=
    vect_of_list [config Shared01; config Shared02; config Shared03;
                  config Shared12; config Shared13; config Shared23].

  Definition enclave_config_to_enclave_data (config: enclave_config) : struct_t enclave_data :=
    mk_enclave_data {| enclave_data_eid := enclave_id_to_bits config.(eid);
                       enclave_data_shared_regions := shared_region_config_to_bits config.(shared_regions);
                       enclave_data_valid := Ob~1
                    |}.

  Definition can_enter_enclave (next_enclave: enclave_config) (other_core_enclave: option enclave_config) : bool :=
    match other_core_enclave with
    | None => true
    | Some config =>
        let next_shared := shared_region_config_to_bits (next_enclave.(shared_regions)) in
        let other_shared := shared_region_config_to_bits (config.(shared_regions)) in
        (* Other core hasn't claimed the requested memory regions *)
        negb (enclave_id_beq next_enclave.(eid) config.(eid)) &&
        (bits_eqb (Bits.and next_shared other_shared) Bits.zero)
    end.


  Definition enclave_req_to_enclave_data (req: struct_t enclave_req) : struct_t enclave_data :=
    let '(eid, (shared, _)) := req in
    mk_enclave_data {| enclave_data_eid := eid;
                       enclave_data_shared_regions := shared;
                       enclave_data_valid := Ob~1
                    |}.

  Definition eid_to_initial_enclave_data (eid: enclave_id) : struct_t enclave_data :=
    mk_enclave_data {| enclave_data_eid := enclave_id_to_bits eid;
                       enclave_data_shared_regions := Ob~0~0~0~0~0~0;
                       enclave_data_valid := Ob~1
                    |}.


End EnclaveInterface.

Module SM_Common.
  Import Common.
  Import EnclaveInterface.

  Definition ENUM_CORESTATE_RUNNING := Ob~0~0.
  Definition ENUM_CORESTATE_PURGING:= Ob~0~1.
  Definition ENUM_CORESTATE_WAITING:= Ob~1~0.

  Definition core_state :=
    {| enum_name := "core_states";
       enum_members := vect_of_list ["Running"; "Purging"; "Waiting"];
       enum_bitpatterns := vect_of_list [ENUM_CORESTATE_RUNNING; ENUM_CORESTATE_PURGING; ENUM_CORESTATE_WAITING]
    |}.

  (* Note: somewhat redundant registers *)
  Inductive private_reg_t' :=
  | state0
  | state1
  | enc_data0
  | enc_data1
  | enc_req0
  | enc_req1
  | clk
  .

  Definition private_reg_t := private_reg_t'.

  Instance FiniteType_private_reg_t : FiniteType private_reg_t := _.

  Definition R_private (idx: private_reg_t) : type :=
    match idx with
    | state0 => enum_t core_state
    | state1 => enum_t core_state
    | enc_data0 => struct_t enclave_data
    | enc_data1 => struct_t enclave_data
    | enc_req0 => struct_t enclave_data
    | enc_req1 => struct_t enclave_data
    | clk => bits_t 1
    end.

  Definition r_private (idx: private_reg_t) : R_private idx :=
    match idx with
    | state0 => Bits.zero
    | state1 => Bits.zero
    | enc_data0 => eid_to_initial_enclave_data Enclave0
    | enc_data1 => eid_to_initial_enclave_data Enclave1
    | enc_req0 => value_of_bits Bits.zero
    | enc_req1 => value_of_bits Bits.zero
    | clk => Bits.zero
    end.

  Inductive public_reg_t :=
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

  Definition R_public (idx: public_reg_t) : type :=
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


  Inductive reg_t : Type :=
  | public (idx: public_reg_t)
  | private (idx: private_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | public st => R_public st
    | private st => R_private st
    end.

  (* SLOW: 10s *)
  (* Slowness mostly comes from autorewrites *)
  Declare Instance FiniteType_public_reg_t : FiniteType public_reg_t.
  (* Instance FiniteType_public_reg_t : FiniteType public_reg_t := _. *)
  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition state := env_t ContextEnv (fun idx : reg_t => R idx).

  Inductive rule_name_t :=
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
  | ExitEnclave0
  | ExitEnclave1
  | EnterEnclave0
  | EnterEnclave1
  | DoClk
  .

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


  Section RuleHelpers.

    Definition lookup_reg_state (core: ind_core_id) : reg_t :=
      match core with
      | CoreId0 => private state0
      | CoreId1 => private state1
      end.

    Definition lookup_reg_enc_data (core: ind_core_id) : reg_t :=
      match core with
      | CoreId0 => private enc_data0
      | CoreId1 => private enc_data1
      end.

    Definition lookup_reg_enc_req (core: ind_core_id) : reg_t :=
      match core with
      | CoreId0 => private enc_req0
      | CoreId1 => private enc_req1
      end.

    Definition lookup_reg_proc_reset (core: ind_core_id) : reg_t :=
      match core with
      | CoreId0 => public purge_core0
      | CoreId1 => public purge_core1
      end.

    Definition lookup_reg_mem_reset (core: ind_core_id) : reg_t :=
      match core with
      | CoreId0 => public purge_mem0
      | CoreId1 => public purge_mem1
      end.

    Definition lookup_reg_pc (core: ind_core_id) : reg_t :=
      match core with
      | CoreId0 => public pc_core0
      | CoreId1 => public pc_core1
      end.

    Definition max_eid : bits_t 32 :=
      Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1.
  End RuleHelpers.


  (* TODO: move things into records? *)
  Section Parameterised.
    Context {initial_pc0 initial_pc1: addr_t}.
    Context {enclave_params: enclave_params_sig}.

    Definition enclave_base := _enclave_base enclave_params.
    Definition enclave_size := _enclave_size enclave_params.
    Definition enclave_bootloader_addr := _enclave_bootloader_addr enclave_params.
    Definition shared_region_base := _shared_region_base enclave_params.
    Definition shared_region_size := _shared_region_size enclave_params.

    Context {ext_sig: external_sig}.

    Definition r_public (idx: public_reg_t) : R_public idx :=
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
      | pc_core0 => initial_pc0
      | pc_core1 => initial_pc1
      | purge_core0 => value_of_bits (Bits.zero)
      | purge_core1 => value_of_bits (Bits.zero)
      | purge_mem0 => value_of_bits (Bits.zero)
      | purge_mem1 => value_of_bits (Bits.zero)
      end.

    Definition r (idx: reg_t) : R idx :=
      match idx with
      | public st => r_public st
      | private st => r_private st
      end.

    Definition ext_fn_t := _ext_fn_t ext_sig.
    Definition Sigma := _Sigma ext_sig.
    Definition rule := rule R Sigma.
    Definition sigma := _sigma ext_sig.

    Definition valid_shared_regions : UInternalFunction reg_t empty_ext_fn_t :=
      {{ fun valid_shared_regions (eid: bits_t 32) (shared_regions: bits_t 6) : bits_t 1 =>
           match eid with
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 =>
               shared_regions[|3`d3| :+ 3] == Ob~0~0~0
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 =>
               (shared_regions[|3`d1|] ++ shared_regions[|3`d2|] ++ shared_regions[|3`d5|]) == Ob~0~0~0
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0 =>
               (shared_regions[|3`d0|] ++ shared_regions[|3`d2|] ++ shared_regions[|3`d4|]) == Ob~0~0~0
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1 =>
               (shared_regions[|3`d0|] ++ shared_regions[|3`d1|] ++ shared_regions[|3`d3|]) == Ob~0~0~0
           return default: Ob~0
           end
      }}.

    Definition valid_enclave_req : UInternalFunction reg_t empty_ext_fn_t :=
      {{ fun valid_enclave_req (req: struct_t enclave_req) : bits_t 1 =>
             (get(req, eid) <= #max_eid) &&
             (valid_shared_regions(get(req,eid), get(req, shared_regions)))
      }}.


    Definition addr_in_eid_range : UInternalFunction reg_t empty_ext_fn_t :=
      {{ fun addr_in_eid_range (eid: bits_t 32) (addr: bits_t 32): bits_t 1 =>
           match eid with
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 =>
               let addr_min := #(enclave_base Enclave0) in
               let addr_max := #(enclave_size Enclave0) + addr_min in
               addr_min <= addr && addr < addr_max
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 =>
               let addr_min := #(enclave_base Enclave1) in
               let addr_max := #(enclave_size Enclave1) + addr_min in
               addr_min <= addr && addr < addr_max
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0 =>
               let addr_min := #(enclave_base Enclave2) in
               let addr_max := #(enclave_size Enclave2) + addr_min in
               addr_min <= addr && addr < addr_max
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1 =>
               let addr_min := #(enclave_base Enclave3) in
               let addr_max := #(enclave_size Enclave3) + addr_min in
               addr_min <= addr && addr < addr_max
           return default : Ob~0
           end
    }}.

    Definition addr_in_shared_range : UInternalFunction reg_t empty_ext_fn_t :=
      {{ fun addr_in_shared_range (shared: bits_t 6) (addr: bits_t 32) : bits_t 1 =>
            let shared01_base := #(shared_region_base Shared01) in
            let shared02_base := #(shared_region_base Shared02) in
            let shared03_base := #(shared_region_base Shared03) in
            let shared12_base := #(shared_region_base Shared12) in
            let shared13_base := #(shared_region_base Shared13) in
            let shared23_base := #(shared_region_base Shared23) in
            let shared_size := #(shared_region_size) in
            (shared[|3`d0|] && (shared01_base <= addr && addr < (shared01_base + shared_size))) ||
            (shared[|3`d1|] && (shared02_base <= addr && addr < (shared02_base + shared_size))) ||
            (shared[|3`d2|] && (shared03_base <= addr && addr < (shared03_base + shared_size))) ||
            (shared[|3`d3|] && (shared12_base <= addr && addr < (shared12_base + shared_size))) ||
            (shared[|3`d4|] && (shared13_base <= addr && addr < (shared13_base + shared_size))) ||
            (shared[|3`d5|] && (shared23_base <= addr && addr < (shared23_base + shared_size)))
      }}.

    Definition valid_addr_req : UInternalFunction reg_t empty_ext_fn_t :=
      {{ fun valid_addr_req (eid: bits_t 32) (shared: bits_t 6) (addr: bits_t 32) : bits_t 1 =>
           addr_in_eid_range (eid,addr) || addr_in_shared_range(shared,addr)
      }}.

    Definition canSwitchToEnc (core: ind_core_id) : UInternalFunction reg_t empty_ext_fn_t :=
      let other_core := match core with CoreId0 => CoreId1 | CoreId1 => CoreId0 end in
      let reg_other_enc := lookup_reg_enc_data other_core in
      {{ fun canSwitchToEnc (eid: bits_t 32) (shared: bits_t 6): bits_t 1 =>
           let other_enc_data := read0(reg_other_enc) in
           (* Enclave is not valid or regions are disjoint *)
           (!get(other_enc_data, valid)) ||
           (get(other_enc_data, eid) != eid &&
            ((get(other_enc_data, shared_regions) && shared) == Ob~0~0~0~0~0~0))
             (* TODO: rewrite properly *)
      }}.

    Notation "'__public__' instance " :=
      (fun reg => public ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
    Notation "'(' instance ').(' method ')' args" :=
      (USugar (UCallModule instance _ method args))
        (in custom koika at level 1, method constr, args custom koika_args at level 99).

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
           let enclaveRequest := (__public__ fromCore).(EnclaveReq.deq)() in
           let eid := get(enclaveRequest, eid) in
           let shared_regions := get(enclaveRequest, shared_regions) in
           if (valid_enclave_req(enclaveRequest)) then
             write0(reg_state, enum core_state { Purging });
               (* TODO *)
             write0(reg_enc_req, struct enclave_data
                                        { eid := eid;
                                          shared_regions := shared_regions;
                                          valid := Ob~1 });
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
           let request := (__public__ fromCore).(MemReq.deq)() in
           let address := get(request, addr) in
           let enc_data := read0(reg_enc) in
           (* let addr_min := get(enc_data, addr_min) in *)
           (* let addr_max := get(enc_data, size) + addr_min in *)
           let TODO_temp_bypass := address >= #(MMIO_UART_ADDRESS) in
           if (valid_addr_req (get(enc_data,eid), get(enc_data, shared_regions), address) ||
               TODO_temp_bypass) then
             (__public__ toMem).(MemReq.enq)(request)
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
           let response:= (__public__ fromMem).(MemResp.deq)() in
           let address := get(response, addr) in
           let enc_data := read0(reg_enc) in
           (* let addr_min := get(enc_data, addr_min) in *)
           (* let addr_max := get(enc_data, size) + addr_min in *)
           let TODO_temp_bypass := address >= #(MMIO_UART_ADDRESS) in
           if (valid_addr_req (get(enc_data,eid), get(enc_data, shared_regions), address) ||
               TODO_temp_bypass) then
             (__public__ toCore).(MemResp.enq)(response)
           else pass
      }}.

    Definition eid_to_bootloader_addr : UInternalFunction reg_t empty_ext_fn_t :=
      {{ fun eid_to_bootloader_addr (eid: bits_t 32) : bits_t 32 =>
           match eid with
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 =>
               #(enclave_bootloader_addr Enclave0)
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 =>
               #(enclave_bootloader_addr Enclave1)
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0 =>
               #(enclave_bootloader_addr Enclave2)
           | #Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1 =>
               #(enclave_bootloader_addr Enclave3)
           return default : |32`d0|
           end
      }}.
    Definition reset_fifos : UInternalFunction reg_t ext_fn_t :=
      {{ fun reset_fifos () : bits_t 0 =>
           (__public__ fromCore0_IMem).(MemReq.reset)();
           (__public__ fromCore0_DMem).(MemReq.reset)();
           (__public__ fromCore0_Enc).(EnclaveReq.reset)();
           (__public__ toCore0_IMem).(MemResp.reset)();
           (__public__ toCore0_DMem).(MemResp.reset)();
           (__public__ fromCore1_IMem).(MemReq.reset)();
           (__public__ fromCore1_DMem).(MemReq.reset)();
           (__public__ fromCore1_Enc).(EnclaveReq.reset)();
           (__public__ toCore1_IMem).(MemResp.reset)();
           (__public__ toCore1_DMem).(MemResp.reset)();
           (__public__ toMem0_IMem).(MemReq.reset)();
           (__public__ toMem0_DMem).(MemReq.reset)();
           (__public__ toMem1_IMem).(MemReq.reset)();
           (__public__ toMem1_DMem).(MemReq.reset)();
           (__public__ fromMem0_IMem).(MemResp.reset)();
           (__public__ fromMem0_DMem).(MemResp.reset)();
           (__public__ fromMem1_IMem).(MemResp.reset)();
           (__public__ fromMem1_DMem).(MemResp.reset)()
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

    (* TODO: implement turns *)
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
              read0(private clk) == #valid_clk) then
           let enc_req := read0(reg_enc_req) in
           let eid := get(enc_req,eid) in
           let shared_req := get(enc_req, shared_regions) in
           (* Check for permission to enter by reading other core's enclave data *)
           if ({canSwitchToEnc core}(eid, shared_req)) then
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

    Definition do_clk : uaction reg_t ext_fn_t :=
      {{ write0 (private clk, !read0(private clk)) }}.

    Definition tc_update_enclave0 := tc_rule R Sigma (sm_update_enclave CoreId0) <: rule.
    Definition tc_update_enclave1 := tc_rule R Sigma (sm_update_enclave CoreId1) <: rule.

    Definition tc_filter_reqs_imem0 := tc_rule R Sigma (sm_filter_reqs CoreId0 CacheType_Imem) <: rule.
    Definition tc_filter_reqs_dmem0 := tc_rule R Sigma (sm_filter_reqs CoreId0 CacheType_Dmem) <: rule.
    Definition tc_filter_reqs_imem1 := tc_rule R Sigma (sm_filter_reqs CoreId1 CacheType_Imem) <: rule.
    Definition tc_filter_reqs_dmem1 := tc_rule R Sigma (sm_filter_reqs CoreId1 CacheType_Dmem) <: rule.

    Definition tc_filter_resps_imem0 := tc_rule R Sigma (sm_filter_resps CoreId0 CacheType_Imem) <: rule.
    Definition tc_filter_resps_dmem0 := tc_rule R Sigma (sm_filter_resps CoreId0 CacheType_Dmem) <: rule.
    Definition tc_filter_resps_imem1 := tc_rule R Sigma (sm_filter_resps CoreId1 CacheType_Imem) <: rule.
    Definition tc_filter_resps_dmem1 := tc_rule R Sigma (sm_filter_resps CoreId1 CacheType_Dmem) <: rule.

    Definition tc_exit_enclave0 := tc_rule R Sigma (sm_exit_enclave CoreId0) <: rule.
    Definition tc_exit_enclave1 := tc_rule R Sigma (sm_exit_enclave CoreId1) <: rule.

    Definition tc_enter_enclave0 := tc_rule R Sigma (sm_enter_enclave CoreId0) <: rule.
    Definition tc_enter_enclave1 := tc_rule R Sigma (sm_enter_enclave CoreId1) <: rule.

   Definition tc_clk := tc_rule R Sigma do_clk <: rule.

   Definition rules (rl : rule_name_t) : rule:=
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
     | ExitEnclave0 => tc_exit_enclave0
     | ExitEnclave1 => tc_exit_enclave1
     | EnterEnclave0 => tc_enter_enclave0
     | EnterEnclave1 => tc_enter_enclave1
     | DoClk => tc_clk
     end.

    Section Interface.
      Definition lift_ext_log (log: Log R_public ContextEnv) : Log R ContextEnv :=
        ContextEnv.(create) (fun reg => match reg return (RLog (R reg)) with
                                     | public s => ContextEnv.(getenv) log s
                                     | _ => []
                                     end).

      Definition proj_log__pub (log: Log R ContextEnv) : Log R_public ContextEnv :=
        ContextEnv.(create) (fun reg => ContextEnv.(getenv) log (SM_Common.public reg)).

      Definition is_public_log (log: Log R ContextEnv) : Prop :=
        forall reg, match reg with
               | public r => True
               | private r => ContextEnv.(getenv) log reg = []
               end.

    End Interface.

    Section CycleSemantics.
      (* Could add ghost state *)

      Definition impl_output_t : Type := Log R ContextEnv (* * ghost_output *).

      Record ghost_output :=
        { ghost_output_config0 : option enclave_config;
          ghost_output_config1 : option enclave_config
        }.

      Record step_io :=
        { step_input : Log R_public ContextEnv;
          step_feedback : Log R_public ContextEnv
        }.

      Definition log_t := Log R ContextEnv.
      Definition input_t := Log R_public ContextEnv.
      Definition output_t : Type := Log R ContextEnv * ghost_output.
      Definition feedback_t := Log R_public ContextEnv.

      (* TODO: need ghost state to interface with the memory module? *)
      Definition update_function : state -> Log R ContextEnv -> impl_output_t :=
        fun st log => interp_scheduler_delta st sigma rules log schedule.

      Definition initial_state (eid0: option enclave_id) (eid1: option enclave_id) (clk: bits_t 1): state :=
        ContextEnv.(create) (fun reg => match reg return R reg with
                                     | private enc_data0 =>
                                         match eid0 with
                                         | Some id => eid_to_initial_enclave_data id
                                         | None => value_of_bits Bits.zero
                                         end
                                     | private enc_data1 =>
                                         match eid1 with
                                         | Some id => eid_to_initial_enclave_data id
                                         | None => value_of_bits Bits.zero
                                         end
                                     | private clk => clk
                                     | private reg' => r_private reg'
                                     | public reg' => r_public reg'
                                     end).


      Definition do_step_input__impl (st: state) (ext_input: input_t) : impl_output_t * log_t :=
         let input := lift_ext_log ext_input in
         let output := update_function st input in
         (output, log_app output input).

      Definition do_step__impl (st: state) (step: step_io) : state * impl_output_t :=
        let '(output, acc) := do_step_input__impl st step.(step_input) in
        let final := log_app (lift_ext_log step.(step_feedback)) acc in
        (commit_update st final, output).

      Definition do_steps__impl (steps: list step_io)
                               : state * list impl_output_t :=
        fold_left (fun '(st, evs) step =>
                     let '(st', ev) := do_step__impl st step in
                     (st', evs ++ [ev]))
                  steps (initial_state (Some Enclave0) (Some Enclave1) Ob~0, []).

    End CycleSemantics.

    Section Taint.

      Inductive taint_t :=
      | TaintCore (core_id: ind_core_id)
      | Bottom.

      Definition private_reg_to_taint (reg: private_reg_t) : taint_t :=
        match reg with
        | state0 => TaintCore CoreId0
        | state1 => TaintCore CoreId1
        | enc_data0 => TaintCore CoreId0
        | enc_data1 => TaintCore CoreId1
        | enc_req0 => TaintCore CoreId0
        | enc_req1 => TaintCore CoreId1
        | clk => Bottom
        end.

      (* Only works for partitioned interfaces right now *)
      Definition public_reg_to_core_id (reg: public_reg_t) : ind_core_id :=
        match reg with
        | fromCore0_IMem st => CoreId0
        | fromCore0_DMem st => CoreId0
        | fromCore0_Enc st => CoreId0
        | toCore0_IMem st => CoreId0
        | toCore0_DMem st => CoreId0
        (* Core1 <-> SM *)
        | fromCore1_IMem st => CoreId1
        | fromCore1_DMem st => CoreId1
        | fromCore1_Enc st => CoreId1
        | toCore1_IMem st => CoreId1
        | toCore1_DMem st => CoreId1
        (* SM <-> Mem *)
        | toMem0_IMem st => CoreId0
        | toMem0_DMem st => CoreId0
        | toMem1_IMem st => CoreId1
        | toMem1_DMem st => CoreId1
        | fromMem0_IMem st => CoreId0
        | fromMem0_DMem st => CoreId0
        | fromMem1_IMem st => CoreId1
        | fromMem1_DMem st => CoreId1
        | pc_core0 => CoreId0
        | pc_core1 => CoreId1
        | purge_core0 => CoreId0
        | purge_core1 => CoreId1
        | purge_mem0 => CoreId0
        | purge_mem1 => CoreId1
        end.


      Definition public_reg_to_taint (reg: public_reg_t) : taint_t :=
        let core_id := public_reg_to_core_id reg in
        TaintCore core_id.

      Definition reg_to_taint (reg: reg_t) : taint_t :=
        match reg with
        | public s => public_reg_to_taint s
        | private s => private_reg_to_taint s
        end.

      Scheme Equality for taint_t.

    End Taint.

    Section Spec.
      Inductive enclave_state_t :=
      | EnclaveState_Running
      | EnclaveState_Switching (next_enclave: enclave_config)
      .

      Inductive sm_state_machine :=
      | SmState_Enclave (machine_state: state) (config: enclave_config)
                        (enclave_state: enclave_state_t)
      | SmState_Waiting (new: enclave_config).

      Inductive sm_magic_state_machine :=
      | SmMagicState_Continue (st: sm_state_machine) (ext: Log R ContextEnv) (config: option enclave_config)
      | SmMagicState_Exit (waiting: enclave_config) (ext: Log R ContextEnv)
      | SmMagicState_TryToEnter (next_enclave: enclave_config).

      Record iso_machine_t :=
        { iso_sm0 : sm_state_machine;
          iso_sm1 : sm_state_machine;
          turn : bool
        }.

      Definition filter_public (log: Log R ContextEnv) (core: ind_core_id) : Log R ContextEnv :=
        ContextEnv.(create) (fun r => match r with
                                   | private s => []
                                   | reg => if (taint_t_beq (reg_to_taint reg) (TaintCore core))
                                              || (taint_t_beq (reg_to_taint reg) Bottom) then
                                              ContextEnv.(getenv) log reg
                                           else []
                                   end).

      (* TODO: normal way of writing this? *)
      Definition observe_enclave_exit (core_id: ind_core_id) (log: Log R ContextEnv) : bool.
        refine(
        let enc_data_reg := match core_id with
                            | CoreId0 => private enc_data0
                            | CoreId1 => private enc_data1
                            end in
        match rew_latest_write log enc_data_reg _ with
        | Some v =>
            let data := EnclaveInterface.extract_enclave_data v in
            bits_eqb (EnclaveInterface.enclave_data_valid data) Ob~0
        | None => false
        end).
        - destruct core_id; reflexivity.
      Defined.

      Definition local_output_t : Type := Log R ContextEnv * option enclave_config.
      Definition spec_output_t : Type := local_output_t * local_output_t.

      Definition spec_state_t := iso_machine_t.
      Definition initial_spec_state : spec_state_t. Admitted.

      Definition check_for_context_switching (core_id: ind_core_id) (input_log: Log R_public ContextEnv)
                                             : option EnclaveInterface.enclave_config.
      Admitted.

      Definition local_core_step (can_switch: bool) (core_id: ind_core_id)
                                 (config: sm_state_machine)
                                 (step: step_io)
                                 : sm_magic_state_machine :=
        match config with
        | SmState_Enclave machine enclave enclave_state =>
            let '(machine', output_log) := do_step__impl machine step in
            match enclave_state with
            | EnclaveState_Running =>
                let enclave_state' :=
                  match check_for_context_switching core_id step.(step_input) with
                  | Some next_enclave => EnclaveState_Switching next_enclave
                  | None => EnclaveState_Running
                  end in
                SmMagicState_Continue (SmState_Enclave machine' enclave enclave_state') output_log (Some enclave)
            | EnclaveState_Switching next_enclave =>
                if observe_enclave_exit core_id output_log
                then SmMagicState_Exit next_enclave output_log
                else SmMagicState_Continue (SmState_Enclave machine' enclave enclave_state) output_log (Some enclave)
            end
        | SmState_Waiting next_enclave =>
            if can_switch
            then SmMagicState_TryToEnter next_enclave
            else SmMagicState_Continue config log_empty None
        end.

      Definition TODO_spin_up_machine (core: ind_core_id) (next: enclave_config) (turn: bool) : state :=
        match core with
        | CoreId0 => initial_state (Some next.(eid)) None (if turn then Ob~1 else Ob~0)
        | CoreId1 => initial_state None (Some next.(eid)) (if turn then Ob~1 else Ob~0)
        end.

      Definition do_magic_step (core: ind_core_id)
                               (turn: bool)
                               (config: sm_magic_state_machine)
                               (other_cores_enclave: option enclave_config)
                               : sm_state_machine * Log R ContextEnv * option enclave_config :=
        match config with
        | SmMagicState_Continue st obs cur_config => (st, obs, cur_config)
        | SmMagicState_Exit next_enclave obs =>
           (SmState_Waiting next_enclave, obs, None)
        | SmMagicState_TryToEnter next_enclave =>
            if can_enter_enclave next_enclave other_cores_enclave then
              let machine := TODO_spin_up_machine core next_enclave turn in
              let sm_state := SmState_Enclave machine next_enclave EnclaveState_Running in
              let obs := log_empty in (* TODO *)
              (sm_state, obs, Some next_enclave)
             else (SmState_Waiting next_enclave, log_empty, None)
        end.

      Definition get_enclave_config (st: sm_state_machine) : option enclave_config :=
        match st with
        | SmState_Enclave _ config _ => Some config
        | _ => None
        end.

      (*
      Definition iso_step (st: iso_machine_t) (input: Log R ContextEnv) (feedback: Log R ContextEnv)
                          : iso_machine_t * output_t :=
        let magic0 := local_core_step (negb st.(turn)) CoreId0 st.(iso_sm0)
                                      (filter_public input CoreId0) (filter_public feedback CoreId0) in
        let magic1 := local_core_step st.(turn) CoreId1 st.(iso_sm1)
                                      (filter_public input CoreId1) (filter_public feedback CoreId1) in
        let '(iso0', log0) := do_magic_step CoreId0 (negb st.(turn)) magic0 (get_enclave_config st.(iso_sm1)) in
        let '(iso1', log1) := do_magic_step CoreId1 (negb st.(turn)) magic1 (get_enclave_config st.(iso_sm0)) in
        let st' := {| iso_sm0 := iso0';
                      iso_sm1 := iso1';
                      turn := negb st.(turn)
                   |} in
        (st', (log0, log1)). (* TODO: process log0 and log1 *)
        *)

      Definition do_step_input__spec (spec_st: spec_state_t) (input: Log R_public ContextEnv)
                                   : spec_output_t.
      Admitted.

      Definition valid_input (spec_st: spec_state_t) (log: Log R_public ContextEnv) : Prop.
      Admitted.

      Definition valid_output (spec_st: spec_state_t) (input: Log R_public ContextEnv) (log: spec_output_t) : Prop.
      Admitted.

      Definition valid_feedback (spec_st: spec_state_t)
                                (input: Log R_public ContextEnv) (feedback: Log R_public ContextEnv)
                                : Prop.
      Admitted.


      Definition do_step__spec (spec_st: spec_state_t) (step: step_io)
                             : spec_state_t * spec_output_t * props_t. Admitted.

      Definition do_steps__spec (steps: list step_io)
                              : spec_state_t * list spec_output_t * list props_t :=
        fold_left (fun '(st, evs0, props) step =>
                     let '(st', ev0, prop) := do_step__spec st step in
                     (st', evs0 ++ [ev0], props ++ [prop]))
                  steps (initial_spec_state , [], []).

    End Spec.

    Section Correctness.
      (* needs to include any observable registers *)
      Definition trace_equivalent (koika_tr: list impl_output_t)
                                  (spec_tr: list spec_output_t) : Prop.
      Admitted.

      Theorem correctness :
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
          (koika_st: state) (koika_tr: list impl_output_t),
        valid_inputs props ->
        valid_feedbacks props ->
        do_steps__spec steps = (spec_st, spec_tr, props) ->
        do_steps__impl steps = (koika_st, koika_tr) ->
        trace_equivalent koika_tr spec_tr.
      Admitted.

      Definition output_log_equivalent : impl_output_t -> spec_output_t -> Prop. Admitted.

      Theorem output_correctness:
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
          (koika_st: state) (koika_tr: list impl_output_t)
          (input: Log R_public ContextEnv) (impl_output: impl_output_t) (spec_output: spec_output_t),
          valid_inputs props ->
          valid_feedbacks props ->
          do_steps__spec steps = (spec_st, spec_tr, props) ->
          do_steps__impl steps = (koika_st, koika_tr) ->
          valid_input spec_st input ->
          fst (do_step_input__impl koika_st input) = impl_output ->
          do_step_input__spec spec_st input = spec_output ->
          output_log_equivalent impl_output spec_output.
      Admitted.

    End Correctness.

    Section Compliance.

      Theorem output_compliance :
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
          (input: input_t) (output: spec_output_t) (prop: props_t),
          valid_inputs props ->
          valid_feedbacks props ->
          do_steps__spec steps = (spec_st, spec_tr, props) ->
          valid_input spec_st input ->
          do_step_input__spec spec_st input = output ->
          valid_output spec_st input output.
      Admitted.

      Theorem compliance:
        forall (steps: list step_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t),
        valid_inputs props ->
        valid_feedbacks props ->
        do_steps__spec steps = (spec_st, spec_tr, props) ->
        valid_outputs props.
      Admitted.
    End Compliance.

    Section Lemmas.

      Lemma do_steps__impl_app__state:
        forall ios io,
        fst (do_steps__impl (ios ++ [io])) =
        fst (do_step__impl (fst (do_steps__impl ios)) io).
      Proof.
        consider do_steps__impl.
        intros. rewrite fold_left_app.
        unfold fold_left at 1.
        unfold fst. fast_destruct_goal_matches; auto.
      Qed.

      Lemma do_step_rel_do_step_input__impl :
        forall st io,
        snd (do_step__impl st io) =
        fst (do_step_input__impl st (io.(step_input))).
      Proof.
        consider do_step__impl.
        intros.
        destruct_goal_matches.
      Qed.

      Lemma do_steps__impl_app__trace:
        forall ios io,
        snd (do_steps__impl ios) ++ [fst (do_step_input__impl (fst (do_steps__impl ios)) (step_input io) )] =
        snd (do_steps__impl (ios ++ [io])).
      Proof.
        consider do_steps__impl.
        intros. rewrite fold_left_app.
        unfold fold_left at 3.
        fast_destruct_goal_matches.
        unfold snd.
        simpl fst at 2.
        rewrite<-do_step_rel_do_step_input__impl.
        rewrite_solve.
      Qed.

      Lemma do_steps__spec_app__state:
        forall ios io,
        fst (fst (do_steps__spec (ios ++ [io]))) =
        fst (fst (do_step__spec (fst (fst (do_steps__spec ios))) io)).
      Proof.
        intros. consider do_steps__spec.
        rewrite fold_left_app.
        unfold fold_left at 1.
        fast_destruct_goal_matches.
        unfold fst. rewrite_solve.
      Qed.

      Lemma do_step_rel_do_step_input__spec :
        forall st io,
        snd (fst (do_step__spec st io)) =
        do_step_input__spec st (io.(step_input)).
      Proof.
      Admitted.


      Lemma do_steps__spec_app__trace :
        forall ios io,
        snd (fst (do_steps__spec ios)) ++ [do_step_input__spec (fst (fst (do_steps__spec ios))) (io.(step_input))] =
        snd (fst (do_steps__spec (ios ++ [io]))).
      Proof.
        intros. consider do_steps__spec.
        repeat rewrite fold_left_app.
        unfold fold_left at 3.
        fast_destruct_goal_matches.
        rewrite<-do_step_rel_do_step_input__spec.
        unfold fst; unfold snd.
        rewrite_solve.
      Qed.

    End Lemmas.

  End Parameterised.

End SM_Common.

(* NOTE: in our model we say this is fixed, so we can talk about the private registers. *)
(* Core Params in the SM is weird. But we need it for the initial state of the PC? *)
Module SecurityMonitor (External: External_sig) (Params: EnclaveParameters)
                       (Params0: CoreParameters) (Params1: CoreParameters).
  Import Common.
  Import EnclaveInterface.

  Definition r := @SM_Common.r Params0.initial_pc Params1.initial_pc.

  Definition ext_fn_t := @SM_Common.ext_fn_t External.ext.
  Definition Sigma := @SM_Common.Sigma External.ext.

  Definition rules := @SM_Common.rules Params.params External.ext.

  Definition do_step_input__impl := @SM_Common.do_step_input__impl Params.params External.ext.
  Definition do_step__impl:=
    @SM_Common.do_step__impl Params.params External.ext.
  Definition do_steps__impl :=
    @SM_Common.do_steps__impl Params0.initial_pc Params1.initial_pc Params.params External.ext.

  Definition do_step_input__spec :=
    @SM_Common.do_step_input__spec Params0.initial_pc Params1.initial_pc Params.params External.ext.
  Definition do_step__spec:=
    @SM_Common.do_step__spec Params0.initial_pc Params1.initial_pc Params.params External.ext.
  Definition do_steps__spec:=
    @SM_Common.do_steps__spec Params0.initial_pc Params1.initial_pc Params.params External.ext.

End SecurityMonitor.

(* Module Type Machine_sig. *)
(*   Parameter reg_t : Type. *)
(*   Parameter ext_fn_t : Type. *)
(*   Parameter R : reg_t -> type. *)
(*   Parameter Sigma : ext_fn_t -> ExternalSignature. *)
(*   Parameter r : forall reg, R reg. *)
(*   Parameter rule_name_t : Type. *)
(*   Parameter rules : rule_name_t -> rule R Sigma. *)
(*   Parameter FiniteType_reg_t : FiniteType reg_t. *)
(*   Parameter schedule : Syntax.scheduler pos_t rule_name_t. *)
(*   Parameter ext_fn_specs : ext_fn_t -> ext_fn_spec. *)

(* End Machine_sig. *)

Module Mem_Common.
  Import Common.

  Inductive public_reg_t :=
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

  Definition R_public (idx: public_reg_t) : type :=
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

  Definition r_public (idx: public_reg_t) : R_public idx :=
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

  Instance FiniteType_public_reg_t : FiniteType public_reg_t := _.

  Section Parameterised.
    Context {private_sig: private_module_sig}.
    Context {ext_sig: external_sig}.
    Context {enclave_params: enclave_params_sig}.

    Definition private_reg_t := _private_reg_t private_sig.
    Definition R_private := _R_private private_sig.
    Definition r_private : forall (idx: private_reg_t), R_private idx := _r_private private_sig.
    Instance FiniteType_private_reg_t : FiniteType private_reg_t := _FiniteType_private_reg_t private_sig.

    Definition enclave_base := _enclave_base enclave_params.
    Definition enclave_size := _enclave_size enclave_params.
    Definition enclave_bootloader_addr := _enclave_bootloader_addr enclave_params.
    Definition shared_region_base := _shared_region_base enclave_params.
    Definition shared_region_size := _shared_region_size enclave_params.

    Inductive reg_t :=
    | public (r: public_reg_t)
    | private (r: private_reg_t)
    .

    Instance FiniteType_reg_t : FiniteType reg_t := _.

    Definition R (idx: reg_t) : type :=
      match idx with
      | public r => R_public r
      | private r => R_private r
      end.

    Definition r idx : R idx :=
      match idx with
      | public s => r_public s
      | private s => r_private s
      end.

    Definition ext_fn_t := _ext_fn_t ext_sig.
    Definition Sigma := _Sigma ext_sig.
    Definition rule := rule R Sigma.
    Definition sigma := _sigma ext_sig.

    Context {rule_name_t : Type}.
    Context {rules: rule_name_t -> rule}.
    Context {schedule: Syntax.scheduler pos_t rule_name_t}.

    Import EnclaveInterface.

    Section Taint.

      Definition public_reg_to_taint (reg: public_reg_t) : ind_core_id:=
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
      Definition proj_log__pub (log: Log R ContextEnv) : Log R_public ContextEnv :=
        ContextEnv.(create) (fun reg => ContextEnv.(getenv) log (public reg)).

      Definition lift_ext_log (log: Log R_public ContextEnv) : Log R ContextEnv :=
        ContextEnv.(create) (fun reg => match reg return (RLog (R reg)) with
                                     | public s => ContextEnv.(getenv) log s
                                     | _ => []
                                     end).

      Definition filter_ext_log (log: Log R_public ContextEnv) (core: ind_core_id) : Log R_public ContextEnv :=
        ContextEnv.(create) (fun reg => if ind_core_id_beq (public_reg_to_taint reg) core
                                     then ContextEnv.(getenv) log reg
                                     else []).

      Definition tau := Log R_public ContextEnv.
      Definition trace := list tau.
    End Interface.

    (* TODO: rename *)
    (* TODO: reorganize *)
    Context {private_external_state_t : Type}.
    Context {initial_private_external_state_t : private_external_state_t}.

    Definition koika_state_t : Type := env_t ContextEnv (fun idx: reg_t => R idx).
    Definition dram_t : Type := nat -> option data_t.
    Definition external_state_t : Type := dram_t * private_external_state_t.
    Definition state : Type := koika_state_t * external_state_t.

    Context {external_state_update_function: state -> Log R ContextEnv -> Log R ContextEnv * external_state_t}.

    Section CycleSemantics.

      Definition initial_external_state (initial_dram: dram_t) : external_state_t :=
        (initial_dram, initial_private_external_state_t).

      Definition initial_state (initial_dram: dram_t) : state :=
        (ContextEnv.(create) r, initial_external_state initial_dram).

      Definition koika_update_function : koika_state_t -> Log R ContextEnv -> Log R ContextEnv :=
        fun st log => interp_scheduler_delta st sigma rules log schedule.

      Definition update_function (st: state) (input_log: Log R ContextEnv) : Log R ContextEnv * external_state_t :=
        let '(koika_st, ext_st) := st in
        let koika_log := koika_update_function koika_st input_log in
        let '(ext_log, ext_st') := external_state_update_function (koika_st, ext_st) (log_app koika_log input_log) in
        (log_app ext_log koika_log, ext_st').

      Definition input_t : Type := Log R_public ContextEnv * option enclave_config * option enclave_config.
      Definition feedback_t := Log R_public ContextEnv.

      Record step_io :=
        { step_input : Log R_public ContextEnv;
          step_feedback : Log R_public ContextEnv
        }.

      Record ghost_io :=
        { ghost_step : step_io;
          ghost_input_config0 : option enclave_config;
          ghost_input_config1 : option enclave_config;
        }.

      Definition get_input_config (step: ghost_io) (core: ind_core_id) : option enclave_config :=
        match core with
        | CoreId0 => step.(ghost_input_config0)
        | CoreId1 => step.(ghost_input_config1)
        end.

      Definition do_step_input__impl (st: state) (ext_input: Log R_public ContextEnv)
                                   : Log R ContextEnv * external_state_t :=
        let input := lift_ext_log ext_input in
        update_function st input.

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
      Definition initial_enclave_config0 : enclave_config :=
        {| eid := Enclave0;
           shared_regions := fun _ => false
        |}.
      Definition initial_enclave_config1 : enclave_config :=
        {| eid := Enclave1;
           shared_regions  := fun _ => false
        |}.

    End TODO_MOVE.

    Section TODO_dram.
      Definition enclave_base_nat enc_id := Bits.to_nat (enclave_base enc_id).
      Definition enclave_max_nat enc_id := Bits.to_nat (Bits.plus (enclave_base enc_id)
                                                                  (enclave_size enc_id)).

      Definition shared_base_nat (id: shared_id) := Bits.to_nat (shared_region_base id).
      Definition shared_max_nat (id: shared_id) :=
        Bits.to_nat (Bits.plus (shared_region_base id)
                               (shared_region_size)).

      Definition memory_map : Type := EnclaveInterface.mem_region -> dram_t.

      Import EnclaveInterface.

      Definition addr_in_region (region: mem_region) (addr: nat): bool :=
        match region with
        | MemRegion_Enclave eid =>
            (enclave_base_nat eid <=? addr) && (addr <? (enclave_max_nat eid))
        | MemRegion_Shared id =>
            (shared_base_nat id <=? addr) && (addr <? shared_max_nat id)
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
          let shared := enclave_config.(shared_regions) in
          if addr_in_region enclave_region addr then
            (mem_map enclave_region) addr
          else if shared Shared01 && addr_in_region (MemRegion_Shared Shared01) addr then
            (mem_map (MemRegion_Shared Shared01)) addr
          else if shared Shared02 && addr_in_region (MemRegion_Shared Shared02) addr then
            (mem_map (MemRegion_Shared Shared02)) addr
          else if shared Shared03 && addr_in_region (MemRegion_Shared Shared01) addr then
            (mem_map (MemRegion_Shared Shared03)) addr
          else if shared Shared12 && addr_in_region (MemRegion_Shared Shared12) addr then
            (mem_map (MemRegion_Shared Shared12)) addr
          else if shared Shared13 && addr_in_region (MemRegion_Shared Shared13) addr then
            (mem_map (MemRegion_Shared Shared13)) addr
          else if shared Shared23 && addr_in_region (MemRegion_Shared Shared23) addr then
            (mem_map (MemRegion_Shared Shared23)) addr
          else None.

      Definition update_regions (config: enclave_config) (dram: dram_t)
                                (regions: memory_map)
                                : memory_map :=
        fun region =>
          match region with
          | MemRegion_Enclave _eid =>
              if enclave_id_beq _eid config.(eid) then
                filter_dram dram region
              else regions region
          | MemRegion_Shared id =>
              if config.(shared_regions) id then
                filter_dram dram region
              else regions region
          | MemRegion_Other => regions region
          end.

    End TODO_dram.

    Section Spec.

      (* Interface properties *)
      Definition valid_input_log__common (input_log: Log R_public ContextEnv) : Prop.
      Admitted.

      Definition valid_output_log__common (output_log: Log R_public ContextEnv) : Prop.
      Admitted.

      Definition valid_feedback_log__common (log: Log R_public ContextEnv) : Prop :=
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

      Definition public_state_is_reset (st: state) (core_id: ind_core_id): Prop :=
        forall reg, public_reg_to_taint reg = core_id ->
               ContextEnv.(getenv) (fst st) (public reg) = r_public reg.

      Definition output_t := Log R ContextEnv.

      Definition get_purge_reg (core: ind_core_id) : public_reg_t :=
        match core with
        | CoreId0 => purge0
        | CoreId1 => purge1
        end.

      Definition get_dram_from_state (st: state) : dram_t :=
        let '(_, (dram, _)) := st in dram.

      (* TODO: infer this *)
      Definition pf_R_ext_purge_reg: forall core,
          (R (public (get_purge_reg core))) = enum_t purge_state.
      Proof.
        destruct core; reflexivity.
      Defined.

      Definition filter_step (step: step_io) (core: ind_core_id) : step_io :=
        {| step_input := filter_ext_log (step_input step) core;
           step_feedback := filter_ext_log (step_feedback step) core
        |}.

      Definition proj_ghost_io (step: ghost_io) (core: ind_core_id) : step_io * option enclave_config :=
        (filter_step step.(ghost_step) core, get_input_config step core).

      (* TODO: currently wrong. need to proj log of step *)
      Definition do_local_step_trans__spec (machine: local_spec_state_t)
                                         (core: ind_core_id)
                                         (step: step_io)
                                         (opt_config: option enclave_config)
                                         (mem_map: memory_map)
                                         : local_spec_state_t * output_t * memory_map :=
        let '(st, phase) := machine in
        let '(st', output) := do_step__impl st step in
        (* let ext_output := proj_log__pub output in *)
        let purge_reg := get_purge_reg core in
        match phase with
        | SpecSt_Running config =>
            let continue := ((st', phase), output, mem_map) in
            let ext_st' := get_dram_from_state st' in
            match rew_latest_write output (public purge_reg) (pf_R_ext_purge_reg core) with
            | Some v => if bits_eqb v ENUM_purge_purged
                       then ((st', SpecSt_Waiting), output, update_regions config ext_st' mem_map)
                       else continue
            | None => continue
            end
        | SpecSt_Waiting =>
            let continue := ((st', SpecSt_Waiting), output, mem_map) in
            let input_log := step.(step_input) in
            match rew_latest_write input_log purge_reg (pf_R_ext_purge_reg core), opt_config with
            | Some v, Some config =>
               if bits_eqb v ENUM_purge_restart then
                 let dram := get_dram mem_map config in
                 ((initial_state dram, SpecSt_Running config), output, mem_map)
               else (* don't care *) continue
            | _, _ => continue
            end
        end.

      Definition do_local_step_trans_input__spec (machine: local_spec_state_t)
                                               (input: Log R_public ContextEnv)
                                               : Log R ContextEnv * external_state_t :=
        let '(st, phase) := machine in
        do_step_input__impl st input.

      Definition ghost_input_t : Type := Log R_public ContextEnv * (option enclave_config * option enclave_config).
      Definition get_ghost_input (io: ghost_io) : ghost_input_t :=
        (io.(ghost_step).(step_input), (io.(ghost_input_config0), io.(ghost_input_config1))).

      Definition spec_output_t : Type := Log R ContextEnv * Log R ContextEnv.

      Definition do_step_trans_input__spec (spec_st: spec_state_t)
                                         (ghost_input: ghost_input_t)
                                   : spec_output_t :=
        let ext_input := fst(ghost_input) in
        let output0 := do_local_step_trans_input__spec (machine0 spec_st) (filter_ext_log ext_input CoreId0) in
        let output1 := do_local_step_trans_input__spec (machine1 spec_st) (filter_ext_log ext_input CoreId1) in
        (fst output0, fst output1).

      Definition do_step_trans__spec (spec_st: spec_state_t) (step: ghost_io)
                                   : spec_state_t * spec_output_t :=
        let '(step0, config0) := proj_ghost_io step CoreId0 in
        let '(step1, config1) := proj_ghost_io step CoreId1 in
        let '(machine0', output0, mem_map') :=
            do_local_step_trans__spec (machine0 spec_st) CoreId0 step0 config0 (regions spec_st) in
        let '(machine1', output1, mem_map'') :=
            do_local_step_trans__spec (machine1 spec_st) CoreId1 step1 config1 mem_map' in
        ({| machine0 := machine0';
            machine1 := machine1';
            regions := mem_map'' |}, (output0, output1)).

      Definition only_write_ext_purge (log: Log R_public ContextEnv) (core: ind_core_id) (v: bits_t 2) : Prop :=
        let purge_reg := get_purge_reg core in
           rew_latest_write log purge_reg (pf_R_ext_purge_reg core) = Some v
        \/ latest_write log purge_reg = None.

      (* addr req are in range *)
      Definition mem_reqs_in_config (log: Log R_public ContextEnv) (config: enclave_config) (core: ind_core_id)
                                    : Prop.
      Admitted.

      Definition disjoint_configs (opt_config0: option enclave_config) (opt_config1: option enclave_config) : Prop :=
        match opt_config0, opt_config1 with
        | Some config0, Some config1 =>
            config0.(eid) <> config1.(eid) /\
            (forall shared_id, config0.(shared_regions) shared_id && config1.(shared_regions) shared_id = false)
        | _, _ => True
        end.

      Definition valid_local_step_input (local_st: local_spec_state_t)
                                        (core: ind_core_id)
                                        (step: step_io)
                                        (opt_config: option enclave_config)
                                        (mem_map: memory_map)
                                        : Prop.
        Admitted.
      (*
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
            (* TODO: incomplete *)
            (rew_latest_write input purge (pf_R_ext_purge_reg core) = Some ENUM_purge_restart ->
             opt_config <> None /\
             public_state_is_reset (fst st') core (* TODO: whose responsibility to clear FIFOs? *)
            )
        end.
        *)

      Definition valid_input (spec_st: spec_state_t)
                             (input: ghost_input_t) : Prop.
      Admitted.

      (*
        let '(step0, config0) := proj_ghost_io step CoreId0 in
        let '(step1, config1) := proj_ghost_io step CoreId1 in
        let '(_, _, mem_map') :=
            do_local_step_trans__spec (machine0 spec_st) CoreId0 step0 config0 (regions spec_st) in
        valid_local_step_input (machine0 spec_st) CoreId0 step0 config0 (regions spec_st) /\
        valid_local_step_input (machine1 spec_st) CoreId1 step1 config1 mem_map' /\
        (* not same config *)
        disjoint_configs config0 config1 /\
        (* only one restart at a time *)
        (not (latest_write step0.(step_input) purge0 = Some ENUM_purge_restart /\
            latest_write step1.(step_input) purge1 = Some ENUM_purge_restart)) /\
        valid_input_log__common step.(ghost_step).(step_input). (* TODO *)
        *)

      (* Not very interesting: machine0 only outputs to public0; behaves like interface *)

      Definition valid_output (spec_st: spec_state_t) (input: ghost_input_t) (output: spec_output_t) : Prop.
      Admitted.

      Definition valid_feedback (spec_st: spec_state_t) (input: ghost_input_t)
                                (feedback: Log R_public ContextEnv) : Prop :=
        feedback = log_empty.


      Definition do_step__spec (spec_st: spec_state_t) (step: ghost_io)
                             : spec_state_t * spec_output_t * props_t :=
        let '(st', (log0, log1)) := do_step_trans__spec spec_st step in
        let props' := {| P_input := valid_input spec_st (get_ghost_input step);
                         P_output := valid_output spec_st (get_ghost_input step) (log0,log1);
                         P_feedback := valid_feedback spec_st (get_ghost_input step) step.(ghost_step).(step_feedback)
                      |} in
        (st', (log0, log1), props').

      Definition do_steps__spec (initial_dram: dram_t) (steps: list ghost_io)
                              : spec_state_t * list spec_output_t * list props_t :=
        fold_left (fun '(st, evs0, props) step =>
                     let '(st', ev0, prop) := do_step__spec st step in
                     (st', evs0 ++ [ev0], props ++ [prop]))
                  steps (initial_spec_state initial_dram, [], []).

    End Spec.

    Section Correctness.

      (* TODO: clean *)
      Definition log_equivalent (koika_log: Log R ContextEnv) (spec_log: Log R_public ContextEnv) : Prop :=
        forall (reg: public_reg_t),
          latest_write koika_log (public reg) = latest_write spec_log reg /\
          (forall port, may_read koika_log port (public reg) = may_read spec_log port reg) /\
          (forall port, may_write koika_log log_empty port (public reg) =
                   may_write spec_log log_empty port reg).

      Definition tau_equivalent (impl_tau: Log R ContextEnv) (spec_tau: spec_output_t) : Prop :=
        let (log0, log1) := spec_tau in
        let spec_ext_log := ContextEnv.(create)
                              (fun reg => match public_reg_to_taint reg with
                                       | CoreId0 => ContextEnv.(getenv) log0 (public reg)
                                       | CoreId1 => ContextEnv.(getenv) log1 (public reg)
                                       end) in
        log_equivalent impl_tau spec_ext_log.

      Definition trace_equivalent (koika_tr: list (Log R ContextEnv))
                                  (spec_tr: list spec_output_t) : Prop :=
        Forall2 tau_equivalent koika_tr spec_tr.

      Definition P_correctness :=
        forall (initial_dram: dram_t)
          (steps: list ghost_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
          (koika_st: state) (koika_tr: list (Log R ContextEnv)),
        valid_inputs props ->
        valid_feedbacks props ->
        do_steps__spec initial_dram steps = (spec_st, spec_tr, props) ->
        do_steps__impl initial_dram (List.map ghost_step steps) = (koika_st, koika_tr) ->
        trace_equivalent koika_tr spec_tr.

      (* TODO: fix types *)
      Definition output_log_equivalent : Log R ContextEnv -> Log R ContextEnv * Log R ContextEnv -> Prop.
      Admitted.

      Definition P_output_correctness :=
        forall (initial_dram: dram_t)
          (steps: list ghost_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
          (koika_st: state) (koika_tr: list (Log R ContextEnv))
          (input: ghost_input_t) (impl_output spec_output0 spec_output1: Log R ContextEnv),
          valid_inputs props ->
          valid_feedbacks props ->
          do_steps__spec initial_dram steps = (spec_st, spec_tr, props) ->
          do_steps__impl initial_dram (List.map ghost_step steps) = (koika_st, koika_tr) ->
          valid_input spec_st input ->
          fst (do_step_input__impl koika_st (fst input)) = impl_output ->
          do_step_trans_input__spec spec_st input = (spec_output0, spec_output1) ->
          output_log_equivalent impl_output (spec_output0, spec_output1).
    End Correctness.

    Section Compliance.
      Definition P_output_compliance :=
        forall (initial_dram: dram_t)
          (steps: list ghost_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t)
          (input: ghost_io) (output: spec_output_t) (prop: props_t),
          valid_inputs props ->
          valid_feedbacks props ->
          do_steps__spec initial_dram steps = (spec_st, spec_tr, props) ->
          valid_input spec_st (get_ghost_input input) ->
          do_step_trans_input__spec spec_st (get_ghost_input input) = output ->
          valid_output spec_st (get_ghost_input input) output.

      Definition P_compliance :=
        forall (initial_dram: dram_t)
          (steps: list ghost_io)
          (spec_st: spec_state_t) (spec_tr: list spec_output_t) (props: list props_t),
        valid_inputs props ->
        valid_feedbacks props ->
        do_steps__spec initial_dram steps = (spec_st, spec_tr, props) ->
        valid_outputs props.

    End Compliance.

    Section Lemmas.

      Lemma do_steps__impl_app__state:
        forall dram ios io,
        fst (do_steps__impl dram (ios ++ [io])) =
        fst (do_step__impl (fst (do_steps__impl dram ios)) io).
      Proof.
        consider do_steps__impl.
        intros. rewrite fold_left_app.
        simpl. fast_destruct_goal_matches.
        unfold fst. rewrite_solve.
      Qed.

      Lemma do_step_rel_do_step_input__impl :
        forall st io,
        snd (do_step__impl st io) =
        fst (do_step_input__impl st (io.(step_input))).
      Proof.
        consider do_step__impl.
        consider do_step_input__impl.
        intros.
        destruct_goal_matches.
      Qed.

      Lemma do_steps__impl_app__trace:
        forall dram ios io,
        snd (do_steps__impl dram ios) ++ [fst (do_step_input__impl (fst (do_steps__impl dram ios)) (step_input io) )] =
        snd (do_steps__impl dram (ios ++ [io])).
      Proof.
        intros. consider do_steps__impl.
        repeat rewrite fold_left_app.
        unfold fold_left at 3.
        fast_destruct_goal_matches.
        unfold snd.
        simpl fst at 2.
        rewrite<-do_step_rel_do_step_input__impl.
        rewrite_solve.
      Qed.

      Lemma do_steps__spec_app__state:
        forall dram ios io,
        fst (fst (do_steps__spec dram (ios ++ [io]))) =
        fst (fst (do_step__spec (fst (fst (do_steps__spec dram ios))) io)).
      Proof.
        intros. consider do_steps__spec.
        rewrite fold_left_app.
        unfold fold_left at 1.
        fast_destruct_goal_matches.
        unfold fst. rewrite_solve.
      Qed.

      Lemma filter_then_do_step_rel_do_step_input__impl:
        forall st io core_id,
        snd (do_step__impl st (filter_step io core_id)) =
        fst (do_step_input__impl st (filter_ext_log io.(step_input) core_id)).
      Proof.
        consider do_step__impl; consider do_step_input__impl; intros.
        destruct_goal_matches.
        unfold snd.
        consider filter_step. simpl step_input in *.
        rewrite_solve.
      Qed.

      Lemma do_step_rel_do_step_input__spec :
        forall st io,
        snd (fst (do_step__spec st io)) =
        do_step_trans_input__spec st (get_ghost_input io).
      Proof.
        consider do_step__spec.
        consider do_step_trans_input__spec.
        consider do_step_trans__spec.
        consider do_local_step_trans_input__spec.
        consider get_ghost_input.
        intros; fast_destruct_goal_matches.
        unfold fst; unfold snd.
        fast_destruct_goal_matches; simplify_tuples; subst.
        consider proj_ghost_io; simplify_tuples; subst.
        subst_tuple_for l1.
        subst_tuple_for l2.
        subst_tuple_for o1.
        subst_tuple_for o2.
        assert (
          forall machine io core_id regions,
          snd (fst (do_local_step_trans__spec machine core_id (filter_step (ghost_step io) core_id)
                                            (get_input_config io core_id) regions)) =
          fst (do_step_input__impl (fst machine) (filter_ext_log (step_input (ghost_step io)) core_id)))
               as Helper.
        { clear.
          intros.
          consider do_local_step_trans__spec.
          destruct_all_matches; simpl fst; simpl snd.
          all: rewrite<-filter_then_do_step_rel_do_step_input__impl; rewrite_solve.
        }
        { repeat rewrite Helper; auto. }
      Qed.


      Lemma do_steps__spec_app__trace :
        forall dram (ios: list ghost_io) (io: ghost_io),
        snd (fst (do_steps__spec dram ios)) ++
            [do_step_trans_input__spec (fst (fst (do_steps__spec dram ios))) (get_ghost_input io)] =
        snd (fst (do_steps__spec dram (ios ++ [io]))).
      Proof.
        intros. consider do_steps__spec.
        repeat rewrite fold_left_app.
        unfold fold_left at 3.
        fast_destruct_goal_matches.
        rewrite<-do_step_rel_do_step_input__spec.
        unfold fst; unfold snd.
        rewrite_solve.
      Qed.

    End Lemmas.

  End Parameterised.

End Mem_Common.

Module Type Memory_sig (External: External_sig) (EnclaveParams: EnclaveParameters).
  Import Common.
  Import Mem_Common.

  Parameter private_params : private_module_sig.
  Parameter rule_name_t : Type.

  Definition reg_t := @Mem_Common.reg_t private_params.
  Definition r := @Mem_Common.r private_params.
  Definition R := @Mem_Common.R private_params.

  Instance FiniteType_reg_t : FiniteType reg_t := @Mem_Common.FiniteType_reg_t private_params.
  Definition rule := @Mem_Common.rule private_params External.ext.
  Definition sigma := @Mem_Common.sigma External.ext.

  Parameter rules : rule_name_t -> rule.

  Parameter schedule : Syntax.scheduler pos_t rule_name_t.

  Parameter private_external_state_t : Type.
  Parameter initial_private_external_state : private_external_state_t.

  Definition koika_state_t := @Mem_Common.koika_state_t private_params.
  Definition external_state_t := @Mem_Common.external_state_t private_external_state_t.
  Definition initial_external_state (dram: dram_t) : external_state_t :=
    (@Mem_Common.initial_external_state _ initial_private_external_state dram).
  Definition state := @Mem_Common.state private_params private_external_state_t.

  Parameter external_update_function: state -> Log R ContextEnv -> Log R ContextEnv * external_state_t.

  Parameter output_correctness : @P_output_correctness private_params External.ext EnclaveParams.params
                                                       rule_name_t rules schedule
                                                       private_external_state_t
                                                       initial_private_external_state
                                                       external_update_function.
  Parameter correctness : @P_correctness private_params External.ext EnclaveParams.params
                                         rule_name_t rules schedule
                                         private_external_state_t
                                         initial_private_external_state
                                         external_update_function.
  Parameter output_compliance: @P_output_compliance private_params External.ext EnclaveParams.params
                                                    rule_name_t rules schedule
                                                    private_external_state_t
                                                    initial_private_external_state
                                                    external_update_function.

  Parameter compliance: @P_compliance private_params External.ext EnclaveParams.params
                                      rule_name_t rules schedule
                                      private_external_state_t
                                      initial_private_external_state
                                      external_update_function.
End Memory_sig.

Module Machine (External: External_sig) (EnclaveParams: EnclaveParameters)
               (Params0: CoreParameters) (Params1: CoreParameters)
               (Core0: Core_sig External EnclaveParams Params0)
               (Core1: Core_sig External EnclaveParams Params1)
               (Memory: Memory_sig External EnclaveParams).
  Module SM := SecurityMonitor External EnclaveParams Params0 Params1.

  Import Common.

  Inductive reg_t : Type :=
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
  | core0_rf (state: Rf.reg_t)
  | core1_rf (state: Rf.reg_t)
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
  (* Private registers *)
  | Core0_private (state: _private_reg_t Core0.private_params)
  | Core1_private (state: _private_reg_t Core1.private_params)
  | SM_private (state: SM_Common.private_reg_t)
  | Mem_private (state: _private_reg_t Memory.private_params)
  .

  (* TODO: fix finite types *)
  Instance FiniteType_core0_private : FiniteType (_private_reg_t Core0.private_params) :=
    _FiniteType_private_reg_t Core0.private_params.
  Instance FiniteType_core1_private : FiniteType (_private_reg_t Core1.private_params) :=
    _FiniteType_private_reg_t Core1.private_params.
  Instance FiniteType_mem_private : FiniteType (_private_reg_t Memory.private_params) :=
    _FiniteType_private_reg_t Memory.private_params.

  (* SLOW: ~30s *)
  (* Instance FiniteType_reg_t : FiniteType reg_t := _. *)
  (* Instance EqDec_reg_t : EqDec reg_t := _. *)
  Declare Instance FiniteType_reg_t : FiniteType reg_t.
  Declare Instance EqDec_reg_t : EqDec reg_t.

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
    | core0_rf st => Rf.R st
    | core1_rf st => Rf.R st
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
    (* Private registers *)
    | Core0_private st => (_R_private Core0.private_params) st
    | Core1_private st => (_R_private Core1.private_params) st
    | SM_private st => SM_Common.R_private st
    | Mem_private st => (_R_private Memory.private_params) st
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
    | core0_rf st => Rf.r st
    | core1_rf st => Rf.r st
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
    (* Private registers *)
    | Core0_private st => (_r_private Core0.private_params) st
    | Core1_private st => (_r_private Core1.private_params) st
    | SM_private st => SM_Common.r_private st
    | Mem_private st => (_r_private Memory.private_params) st
    end.

    Inductive rule_name_t :=
    | Core0Rule (r: Core0.rule_name_t)
    | Core1Rule (r: Core1.rule_name_t)
    | SmRule   (r: SM_Common.rule_name_t)
    | MemRule  (r: Memory.rule_name_t)
    .

    Definition ext_fn_t := _ext_fn_t External.ext.
    Definition Sigma := _Sigma External.ext.
    Definition rule := rule R Sigma.
    Definition sigma := _sigma External.ext.

    Definition FnLift_id : RLift _ ext_fn_t ext_fn_t Sigma Sigma := ltac:(lift_auto).

    Section Core0_Lift.

      Definition core0_public_lift (reg: Core_Common.public_reg_t) : reg_t :=
        match reg with
        | Core_Common.core_id => core_id0
        | Core_Common.toIMem s => Core0ToSM_IMem s
        | Core_Common.toDMem s => Core0ToSM_DMem s
        | Core_Common.toSMEnc s => Core0ToSM_Enc s
        | Core_Common.fromIMem s => SMToCore0_IMem s
        | Core_Common.fromDMem s => SMToCore0_DMem s
        | Core_Common.rf s => core0_rf s
        | Core_Common.pc => pc0
        | Core_Common.purge => purge_core0
        end.

      Definition core0_lift (reg: Core0.reg_t) : reg_t :=
        match reg with
        | Core_Common.public s => core0_public_lift s
        | Core_Common.private s => Core0_private s
        end.

      Definition Lift_core0 : RLift _ Core0.reg_t reg_t Core0.R R := ltac:(mk_rlift core0_lift).
    End Core0_Lift.

    Section Core1_Lift.

      Definition core1_public_lift (reg: Core_Common.public_reg_t) : reg_t :=
        match reg with
        | Core_Common.core_id => core_id1
        | Core_Common.toIMem s => Core1ToSM_IMem s
        | Core_Common.toDMem s => Core1ToSM_DMem s
        | Core_Common.toSMEnc s => Core1ToSM_Enc s
        | Core_Common.fromIMem s => SMToCore1_IMem s
        | Core_Common.fromDMem s => SMToCore1_DMem s
        | Core_Common.rf s => core1_rf s
        | Core_Common.pc => pc1
        | Core_Common.purge => purge_core1
        end.

      Definition core1_lift (reg: Core1.reg_t) : reg_t :=
        match reg with
        | Core_Common.public s => core1_public_lift s
        | Core_Common.private s => Core1_private s
        end.

      Definition Lift_core1 : RLift _ Core1.reg_t reg_t Core1.R R := ltac:(mk_rlift core1_lift).
    End Core1_Lift.

    Section SM_Lift.

      Definition sm_public_lift (reg: SM_Common.public_reg_t) : reg_t :=
        match reg with
        | SM_Common.fromCore0_IMem st => Core0ToSM_IMem st
        | SM_Common.fromCore0_DMem st => Core0ToSM_DMem st
        | SM_Common.fromCore0_Enc st => Core0ToSM_Enc st
        | SM_Common.toCore0_IMem st => SMToCore0_IMem st
        | SM_Common.toCore0_DMem st => SMToCore0_DMem st
        (* Core1 <-> SM_Common *)
        | SM_Common.fromCore1_IMem st => Core1ToSM_IMem st
        | SM_Common.fromCore1_DMem st => Core1ToSM_DMem st
        | SM_Common.fromCore1_Enc st => Core1ToSM_Enc st
        | SM_Common.toCore1_IMem st => SMToCore1_IMem st
        | SM_Common.toCore1_DMem st => SMToCore1_DMem st
        (* SM_Common <-> Mem *)
        | SM_Common.toMem0_IMem st => SMToMem0_IMem st
        | SM_Common.toMem0_DMem st => SMToMem0_DMem st
        | SM_Common.toMem1_IMem st => SMToMem1_IMem st
        | SM_Common.toMem1_DMem st => SMToMem1_DMem st
        | SM_Common.fromMem0_IMem st => MemToSM0_IMem st
        | SM_Common.fromMem0_DMem st => MemToSM0_DMem st
        | SM_Common.fromMem1_IMem st => MemToSM1_IMem st
        | SM_Common.fromMem1_DMem st => MemToSM1_DMem st
        (* pc *)
        | SM_Common.pc_core0 => pc0
        | SM_Common.pc_core1 => pc1
        (* purge *)
        | SM_Common.purge_core0 => purge_core0
        | SM_Common.purge_core1 => purge_core1
        | SM_Common.purge_mem0 => purge_mem0
        | SM_Common.purge_mem1 => purge_mem1
        end.

      Definition sm_lift (reg: SM_Common.reg_t) : reg_t :=
        match reg with
        | SM_Common.public st => sm_public_lift st
        | SM_Common.private st => SM_private st

        end.

      Definition Lift_sm : RLift _ SM_Common.reg_t reg_t SM_Common.R R := ltac:(mk_rlift sm_lift).

    End SM_Lift.

    Section Mem_Lift.

      Definition mem_public_lift (reg: @Mem_Common.public_reg_t) : reg_t :=
        match reg with
        | Mem_Common.toIMem0 st => SMToMem0_IMem st
        | Mem_Common.toIMem1 st => SMToMem1_IMem st
        | Mem_Common.toDMem0 st => SMToMem0_DMem st
        | Mem_Common.toDMem1 st => SMToMem1_DMem st
        | Mem_Common.fromIMem0 st => MemToSM0_IMem st
        | Mem_Common.fromIMem1 st => MemToSM1_IMem st
        | Mem_Common.fromDMem0 st => MemToSM0_DMem st
        | Mem_Common.fromDMem1 st => MemToSM1_DMem st
        | Mem_Common.purge0 => purge_mem0
        | Mem_Common.purge1 => purge_mem1
        end.

      Definition mem_lift (reg: Memory.reg_t) : reg_t :=
        match reg with
        | Mem_Common.public st => mem_public_lift st
        | Mem_Common.private st => Mem_private st
        end.

      Definition Lift_mem : RLift _ Memory.reg_t reg_t Memory.R R := ltac:(mk_rlift mem_lift).

    End Mem_Lift.

    Section Rules.
      Definition core0_rule_name_lift (rl: Core0.rule_name_t) : rule_name_t :=
        Core0Rule rl.
      Definition core1_rule_name_lift (rl: Core1.rule_name_t) : rule_name_t :=
        Core1Rule rl.
      Definition sm_rule_name_lift (rl: SM_Common.rule_name_t) : rule_name_t :=
        SmRule rl.
      Definition mem_rule_name_lift (rl: Memory.rule_name_t) : rule_name_t :=
        MemRule rl.

      Definition lifted_core0_rules (rl: Core0.rule_name_t) : rule :=
        lift_rule Lift_core0 FnLift_id (Core0.rules rl).
      Definition lifted_core1_rules (rl: Core1.rule_name_t) : rule :=
        lift_rule Lift_core1 FnLift_id (Core1.rules rl).
      Definition lifted_sm_rules (rl: SM_Common.rule_name_t) : rule :=
        lift_rule Lift_sm FnLift_id (@SM_Common.rules EnclaveParams.params External.ext rl).
      Definition lifted_mem_rules (rl: Memory.rule_name_t) : rule :=
        lift_rule Lift_mem FnLift_id (Memory.rules rl).

      Definition rules (rl: rule_name_t) : rule :=
        match rl with
        | Core0Rule r => lifted_core0_rules r
        | Core1Rule r => lifted_core1_rules r
        | SmRule r => lifted_sm_rules r
        | MemRule r => lifted_mem_rules r
        end.

    End Rules.

    Section Schedule.

      Definition lifted_core0_schedule := lift_scheduler core0_rule_name_lift Core0.schedule.
      Definition lifted_core1_schedule := lift_scheduler core1_rule_name_lift Core1.schedule.
      Definition lifted_sm_schedule := lift_scheduler sm_rule_name_lift SM_Common.schedule.
      Definition lifted_mem_schedule := lift_scheduler mem_rule_name_lift Memory.schedule.

      Definition schedule :=
        lifted_core0_schedule ||> lifted_core1_schedule ||> lifted_sm_schedule ||> lifted_mem_schedule.

    End Schedule.
End Machine.
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
      | private st => None (* not external *)
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
          else if enclave_config.(shared_region) && (addr_in_region MemRegion_Shared addr) then
            (mem_map MemRegion_Shared) addr
          else None.

      (* Copy back relevant regions of dram *)
      Definition update_regions (config: enclave_config) (dram: dram_t)
                                (regions: memory_map)
                                : memory_map :=
        fun region =>
          if mem_region_beq region MemRegion_Shared && config.(shared_region) then
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
      | private st => None (* not external *)
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
