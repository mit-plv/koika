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

  Inductive reg_t :=
  | core_id
  | toIMem (state: MemReq.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | toSMEnc (state: EnclaveReq.reg_t)
  (* | rf (state: Rf.reg_t) *)
  | pc
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
   | toSMEnc r => EnclaveReq.R r
   (* | rf r => Rf.R r  *)
   | pc => bits_t 32
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
    | toSMEnc s => EnclaveReq.r s
    (* | rf r => Rf.r r  *)
    | pc => CoreParams.initial_pc
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

  (* TODO: code duplication *)
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
      | pc => True (* don't care *)
      | purge => True (* don't care *)
      | internal s => internal_reg_reset st s
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

End EmptyCore.
