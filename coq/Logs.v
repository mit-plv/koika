(*! Language | Logs of reads and writes !*)
Require Export Koika.Common Koika.Environments Koika.Vect Koika.Syntax Koika.TypedSyntax.

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
  Context {RKind: Type}.
  Context {RKind_denote: RKind -> Type}.
  Context {_R: reg_t -> RKind}.
  Context {REnv: Env reg_t}.

  Notation R := (fun idx => RKind_denote (_R idx)).
  Definition _Log := REnv.(env_t) (fun idx => RLog (R idx)).
  Notation Log := _Log.

  Definition log_empty : Log :=
    REnv.(create) (fun _ => []).

  Definition log_app (l1 l2: Log) :=
    map2 REnv (fun _ ll1 ll2 => ll1 ++ ll2) l1 l2.

  Definition log_find {T} (log: Log) reg (f: @LogEntry (R reg) -> option T) : option T :=
    list_find_opt f (REnv.(getenv) log reg).

  Definition log_cons (reg: reg_t) le (l: Log) :=
    REnv.(putenv) l reg (le :: REnv.(getenv) l reg).

  Definition log_forallb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.forallb (fun '(LE _ kind prt _) => f kind prt) (REnv.(getenv) log reg).

  Definition log_existsb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.existsb (fun '(LE _ kind prt _) => f kind prt) (REnv.(getenv) log reg).

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

  Definition may_read0 (sched_log: Log) idx :=
    negb (log_existsb sched_log idx is_write0) &&
    negb (log_existsb sched_log idx is_write1).

  Definition may_read1 (sched_log: Log) idx :=
    negb (log_existsb sched_log idx is_write1).

  Definition latest_write0 (log: Log) idx :=
    log_find log idx
             (fun le => match le with
                     | (LE _ LogWrite P0 v) => Some v
                     | _ => None
                     end).

  Definition latest_write1 (log: Log) idx :=
    log_find log idx
             (fun le => match le with
                     | (LE _ LogWrite P1 v) => Some v
                     | _ => None
                     end).

  Definition may_write (sched_log rule_log: Log) prt idx :=
    match prt with
    | P0 => negb (log_existsb (log_app rule_log sched_log) idx is_read1) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write0) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    | P1 => negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    end.

  Definition log_latest_write_fn {T} (le: @LogEntry T) :=
    match le with
    | LE _ LogWrite _ v => Some v
    | _ => None
    end.

  Definition latest_write (log: Log) idx :=
    log_find log idx log_latest_write_fn.

  Definition commit_update (r0: REnv.(env_t) R) (log: Log) : REnv.(env_t) R :=
    REnv.(create) (fun k => match latest_write log k with
                         | Some v => v
                         | None => REnv.(getenv) r0 k
                         end).
End Logs.

Arguments LE {T} kind port val : assert.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.

Definition Log {reg_t} R REnv := @_Log reg_t type type_denote R REnv.
Definition CLog {reg_t} R REnv := @_Log reg_t nat Bits.bits R REnv.
