(*! Language | Logs of reads and writes !*)
Require Export Koika.Common Koika.Environments Koika.Syntax Koika.TypedSyntax.

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
  Context {R: reg_t -> Type}.
  Context {REnv: Env reg_t}.

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

  Definition may_read (sched_log: Log) prt idx :=
    match prt with
    | P0 => negb (log_existsb sched_log idx is_write0) &&
           negb (log_existsb sched_log idx is_write1)
    | P1 => negb (log_existsb sched_log idx is_write1)
    end.

  Definition log_latest_write0_fn {T} (le: @LogEntry T) :=
    match le with
    | LE _ LogWrite P0 v => Some v
    | _ => None
    end.

  Definition latest_write0 (log: Log) idx :=
    log_find log idx log_latest_write0_fn.

  Definition log_latest_write1_fn {T} (le: @LogEntry T) :=
    match le with
    | LE _ LogWrite P1 v => Some v
    | _ => None
    end.

  Definition latest_write1 (log: Log) idx :=
    log_find log idx log_latest_write1_fn.

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

  Fixpoint no_latest_writes (log: Log) l :=
    match l with
    | [] => True
    | [a] => latest_write log a = None
    | a::b => latest_write log a = None /\ no_latest_writes log b
    end.

End Logs.

Arguments LE {T} kind port val : assert.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.

Section Maps.
  Context {reg_t: Type}.

  Context {REnv: Env reg_t}.
  Context {R1: reg_t -> Type}.
  Context {R2: reg_t -> Type}.

  Notation Log1 := (@_Log reg_t R1 REnv).
  Notation Log2 := (@_Log reg_t R2 REnv).

  Definition LogEntry_map {T T'} (f: T -> T') :=
    fun '(LE kind prt v) =>
      match kind return match kind with
                        | LogRead => unit: Type
                        | LogWrite => T
                        end -> _ with
      | LogRead => fun v => LE LogRead prt v
      | LogWrite => fun v => LE LogWrite prt (f v)
      end v.

  Definition RLog_map {T T'} (f: T -> T') l :=
    List.map (LogEntry_map f) l.

  Definition log_map
             (f: forall idx, RLog (R1 idx) ->
                        RLog (R2 idx))
             (log: Log1) : Log2 :=
    Environments.map REnv (fun k l1 => f k l1) log.

  Definition log_map_values
             (f: forall idx, R1 idx ->
                        R2 idx)
             (log: Log1) : Log2 :=
    log_map (fun k => RLog_map (f k)) log.
End Maps.

Definition Log {reg_t} R REnv := @_Log reg_t (fun idx => type_denote (R idx)) REnv.
Definition CLog {reg_t} R REnv := @_Log reg_t (fun idx => Bits.bits (R idx)) REnv.

Arguments may_read : simpl never.
Arguments may_write : simpl never.
