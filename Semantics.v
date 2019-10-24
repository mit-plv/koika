Require Import Coq.Lists.List Coq.Bool.Bool.
Require Export SGA.Common SGA.Environments SGA.Vect SGA.Syntax SGA.TypedSyntax.
Import ListNotations.

Section Logs.
  Inductive LogEntryKind :=
    LogRead | LogWrite.

  Record LogEntry {T} :=
    LE { kind: LogEntryKind;
         port: Port;
         val: match kind with
              | LogRead => unit: Type
              | LogWrite => T
              end }.

  Definition RLog T :=
    list (@LogEntry T).

  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.
  Definition Log := REnv.(env_t) (fun idx => RLog (R idx)).

  Definition log_empty : Log :=
    REnv.(create) (fun _ => []).

  Definition log_app (l1 l2: Log) :=
    REnv.(map2) (fun _ ll1 ll2 => ll1 ++ ll2) l1 l2.

  Definition log_find {T} (log: Log) reg (f: @LogEntry (R reg) -> option T) : option T :=
    list_find_opt f (REnv.(getenv) log reg).

  Definition log_cons (reg: reg_t) le (l: Log) :=
    REnv.(putenv) l reg (le :: REnv.(getenv) l reg).

  Definition log_forallb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.forallb (fun '(LE _ kind prt _) => f kind prt) (REnv.(getenv) log reg).

  Definition log_existsb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.existsb (fun '(LE _ kind prt _) => f kind prt) (REnv.(getenv) log reg).
End Logs.

Arguments LE {T} kind port val : assert.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.
Arguments Log {reg_t} R REnv : assert.

Section Interp.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation Log := (Log R REnv).

  Definition is_read0 kind prt :=
    match kind, prt with
    | LogRead, P0 => true
    | _, _ => false
    end.

  Definition is_read1 kind prt :=
    match kind, prt with
    | LogRead, P1 => true
    | _, _ => false
    end.

  Definition is_write0 kind prt :=
    match kind, prt with
    | LogWrite, P0 => true
    | _, _ => false
    end.

  Definition is_write1 kind prt :=
    match kind, prt with
    | LogWrite, P1 => true
    | _, _ => false
    end.

  Open Scope bool_scope.

  Definition may_read0 (sched_log rule_log: Log) idx :=
    negb (log_existsb sched_log idx is_write0) &&
    negb (log_existsb (log_app rule_log sched_log) idx is_write1).

  Definition may_read1 (sched_log: Log) idx :=
    negb (log_existsb sched_log idx is_write1).

  Definition latest_write0 (log: Log) idx :=
    log_find log idx
             (fun le => match le with
                     | (LE LogWrite P0 v) => Some v
                     | _ => None
                     end).

  Definition latest_write1 (log: Log) idx :=
    log_find log idx
             (fun le => match le with
                     | (LE LogWrite P1 v) => Some v
                     | _ => None
                     end).

  Definition may_write (sched_log rule_log: Log) prt idx :=
    match prt with
    | P0 => negb (log_existsb (log_app rule_log sched_log) idx is_read1) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write0) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    | P1 => negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    end.

  Notation rule := (rule pos_t var_t R Sigma).
  Notation action := (action pos_t var_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Definition vcontext (sig: tsig var_t) :=
    context (fun '(k, tau) => type_denote tau) sig.

  Section Action.
    Fixpoint interp_action
             {sig: tsig var_t}
             {tau}
             (Gamma: vcontext sig)
             (sched_log: Log)
             (action_log: Log)
             (a: action sig tau)
    : option (Log * tau * (vcontext sig)) :=
      match a in TypedSyntax.action _ _ _ _ ts tau return (vcontext ts -> option (Log * tau * (vcontext ts)))  with
      | Fail tau => fun _ =>
        None
      | Var m => fun Gamma =>
        Some (action_log, cassoc m Gamma, Gamma)
      | Const cst => fun Gamma =>
        Some (action_log, cst, Gamma)
      | Seq r1 r2 => fun Gamma =>
        let/opt3 action_log, _, Gamma := interp_action Gamma sched_log action_log r1 in
        interp_action Gamma sched_log action_log r2
      | @Assign _ _ _ _ _ _ _ k tau m ex => fun Gamma =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log ex in
        Some (action_log, Ob, creplace m v Gamma)
      | @Bind _ _ _ _ _ _ sig tau tau' var ex body => fun (Gamma : vcontext sig) =>
        let/opt3 action_log1, v, Gamma := interp_action Gamma sched_log action_log ex in
        let/opt3 action_log2, v, Gamma := interp_action (CtxCons (var, tau) v Gamma) sched_log action_log1 body in
        Some (action_log2, v, ctl Gamma)
      | If cond tbranch fbranch => fun Gamma =>
        let/opt3 action_log, cond, Gamma := interp_action Gamma sched_log action_log cond in
        if Bits.single cond then
          interp_action Gamma sched_log action_log tbranch
        else
          interp_action Gamma sched_log action_log fbranch
      | Read P0 idx => fun Gamma =>
        if may_read0 sched_log action_log idx then
          Some (log_cons idx (LE LogRead P0 tt) action_log, REnv.(getenv) r idx, Gamma)
        else None
      | Read P1 idx => fun Gamma =>
        if may_read1 sched_log idx then
          Some (log_cons idx (LE LogRead P1 tt) action_log,
                match latest_write0 (log_app action_log sched_log) idx with
                | Some v => v
                | None => REnv.(getenv) r idx
                end,
               Gamma)
        else None
      | Write prt idx val => fun Gamma =>
        let/opt3 action_log, val, Gamma_new := interp_action Gamma sched_log action_log val in
        if may_write sched_log action_log prt idx then
          Some (log_cons idx (LE LogWrite prt val) action_log, Bits.nil, Gamma_new)
        else None
      | Unop fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, (PrimSpecs.sigma1 fn) arg1, Gamma)
      | Binop fn arg1 arg2 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        let/opt3 action_log, arg2, Gamma := interp_action Gamma sched_log action_log arg2 in
        Some (action_log, (PrimSpecs.sigma2 fn) arg1 arg2, Gamma)
      | ExternalCall fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, sigma fn arg1, Gamma)
      | APos _ a => fun Gamma =>
        interp_action Gamma sched_log action_log a
      end Gamma.
  End Action.

  Section Scheduler.
    Context (rules: rule_name_t -> rule).

    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      let interp_try r s1 s2 :=
          match interp_action CtxEmpty sched_log log_empty (rules r) with
          | Some (l, _, _) => interp_scheduler' (log_app l sched_log) s1
          | None => interp_scheduler' sched_log s2
          end in
      match s with
      | Done => sched_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler' sched_log s
      end.

    Definition interp_scheduler (s: scheduler) :=
      interp_scheduler' log_empty s.
  End Scheduler.
End Interp.

Section EnvUpdates.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Definition rlog_latest_write_fn {k} (le: LogEntry (R k)) :=
    match le with
    | LE LogWrite _ v => Some v
    | _ => None
    end.

  Definition latest_write (log: Log R REnv) idx :=
    log_find log idx rlog_latest_write_fn.

  Definition commit_update (r0: REnv.(env_t) R) (log: Log R REnv) : REnv.(env_t) R :=
    REnv.(create) (fun k => match latest_write log k with
                         | Some v => v
                         | None => REnv.(getenv) r0 k
                         end).
End EnvUpdates.

