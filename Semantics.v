Require Import Coq.Lists.List Coq.Bool.Bool.
Require Export SGA.Common SGA.Environments SGA.Syntax SGA.TypedSyntax.

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

Arguments LE {_}.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.
Arguments Log {reg_t} R REnv.

Section Interp.
  Context {name_t var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).
  Open Scope bool_scope.

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

  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler name_t).

  Definition vcontext (sig: tsig var_t) :=
    context (fun '(k, tau) => Type_of_type tau) sig.

  Section Expr.
    Context {sig: tsig var_t}.
    Context (Gamma: vcontext sig).
    Context (sched_log: Log).

    Fixpoint interp_expr {tau}
             (rule_log: Log)
             (e: expr sig tau)
      : option (Log * tau) :=
      match e with
      | Var m =>
        Some (rule_log, cassoc m Gamma)
      | Const cst => Some (rule_log, cst)
      | Read P0 idx =>
        if may_read0 sched_log rule_log idx then
          Some (log_cons idx (LE LogRead P0 tt) rule_log, REnv.(getenv) r idx)
        else None
      | Read P1 idx =>
        if may_read1 sched_log idx then
          Some (log_cons idx (LE LogRead P1 tt) rule_log,
                match latest_write0 (log_app rule_log sched_log) idx with
                | Some v => v
                | None => REnv.(getenv) r idx
                end)
        else None
      | Call fn arg1 arg2 =>
        let/opt2 rule_log, arg1 := interp_expr rule_log arg1 in
        let/opt2 rule_log, arg2 := interp_expr rule_log arg2 in
        Some (rule_log, (sigma fn) arg1 arg2)
      end.
  End Expr.

  Section Rule.
    Fixpoint interp_rule
             {sig: tsig var_t}
             (Gamma: vcontext sig)
             (sched_log: Log)
             (rule_log: Log)
             (rl: rule sig)
    : option Log :=
      match rl in TypedSyntax.rule _ _ _ t return (vcontext t -> option Log) with
      | Skip => fun _ => Some rule_log
      | Fail => fun _ => None
      | Seq r1 r2 =>
        fun Gamma =>
          let/opt rule_log := interp_rule Gamma sched_log rule_log r1 in
          interp_rule Gamma sched_log rule_log r2
      | @Bind _ _ _ _ _ _ tau var ex body =>
        fun Gamma =>
          let/opt2 rule_log, v := interp_expr Gamma sched_log rule_log ex in
          interp_rule (CtxCons (var, tau) v Gamma) sched_log rule_log body
      | If cond tbranch fbranch =>
        fun Gamma =>
        let/opt2 rule_log, cond := interp_expr Gamma sched_log rule_log cond in
        if Bits.single cond then
          interp_rule Gamma sched_log rule_log tbranch
        else
          interp_rule Gamma sched_log rule_log fbranch
      | Write prt idx val =>
        fun Gamma =>
          let/opt2 rule_log, val := interp_expr Gamma sched_log rule_log val in
          if may_write sched_log rule_log prt idx then
            Some (log_cons idx (LE LogWrite prt val) rule_log)
          else None
      end Gamma.
  End Rule.

  Section Scheduler.
    Context (rules: name_t -> rule nil).

    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      let interp_try r s1 s2 :=
          match interp_rule CtxEmpty sched_log log_empty (rules r) with
          | Some l => interp_scheduler' (log_app l sched_log) s1
          | CannotRun => interp_scheduler' sched_log s2
          end in
      match s with
      | Done => sched_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
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

