(*! Language | Alternative implementation of logs !*)
Require Export Koika.Common Koika.Environments Koika.Syntax Koika.TypedSyntax.

Section Logs.
  (* Using primitive projections makes rewriting in may_{read,write}[01] much easier. *)
  Set Primitive Projections.
  Record LogEntry {T} :=
    LE { lread0: bool;
         lread1: bool;
         lwrite0: option T;
         lwrite1: option T }.
  Unset Primitive Projections.

  Arguments LogEntry : clear implicits.

  Context {reg_t: Type}.
  Context {R: reg_t -> Type}.
  Context {REnv: Env reg_t}.

  Definition _Log := REnv.(env_t) (fun idx => LogEntry (R idx)).
  Notation Log := _Log.

  Definition logentry_empty {T} : LogEntry T :=
    {| lread0 := false;
       lread1 := false;
       lwrite0 := None;
       lwrite1 := None |}.

  Definition log_empty : Log :=
    REnv.(create) (fun _ => logentry_empty).

  Definition opt_default {A} (a: A) (o: option A) :=
    match o with
    | Some a => a
    | None => a
    end.

  Definition opt_or {A} (o1 o2: option A) :=
    match o1 with
    | Some _ => o1
    | None => o2
    end.

  Definition logentry_app {T} (l1 l2: LogEntry T) :=
    {| lread0 := l1.(lread0) || l2.(lread0);
       lread1 := l1.(lread1) || l2.(lread1);
       lwrite0 := opt_or l1.(lwrite0) l2.(lwrite0);
       lwrite1 := opt_or l1.(lwrite1) l2.(lwrite1) |}.

  Definition log_app (l1 l2: Log) :=
    map2 REnv (fun _ => logentry_app) l1 l2.

  Open Scope bool_scope.

  Definition nonep {A} (o: option A) :=
    match o with
    | Some _ => false
    | None => true
    end.

  Definition may_read0 (sched_log: Log) idx :=
    match REnv.(getenv) sched_log idx with
    | {| lread0 := _; lread1 := _; lwrite0 := None; lwrite1 := None |} => true
    | _ => false
    end.

  Definition may_read1 (sched_log: Log) idx :=
    match REnv.(getenv) sched_log idx with
    | {| lread0 := _; lread1 := _; lwrite0 := _; lwrite1 := None |} => true
    | _ => false
    end.

  Definition may_write0 (sched_log rule_log: Log) idx :=
    match REnv.(getenv) sched_log idx, REnv.(getenv) rule_log idx with
    | {| lread0 := _; lread1 := false; lwrite0 := None; lwrite1 := None |},
      {| lread0 := _; lread1 := false; lwrite0 := None; lwrite1 := None |} => true
    | _, _ => false
    end.

  Definition may_write1 (sched_log rule_log: Log) idx :=
    match REnv.(getenv) sched_log idx, REnv.(getenv) rule_log idx with
    | {| lread0 := _; lread1 := _; lwrite0 := _; lwrite1 := None |},
      {| lread0 := _; lread1 := _; lwrite0 := _; lwrite1 := None |} => true
    | _, _ => false
    end.

  Definition commit_update (r0: REnv.(env_t) R) (log: Log) : REnv.(env_t) R :=
    REnv.(create) (fun k => let rl := REnv.(getenv) log k in
                         match rl.(lwrite1), rl.(lwrite0) with
                         | Some v, _ => v
                         | _, Some v => v
                         | None, None => REnv.(getenv) r0 k
                         end).
End Logs.

Arguments LE {T} lread0 lread1 lwrite0 lwrite1 : assert.
Arguments LogEntry: clear implicits.
Arguments logentry_app {T} !l1 !l2 /: assert.

Definition Log {reg_t} R REnv := @_Log reg_t (fun idx => type_denote (R idx)) REnv.
Definition CLog {reg_t} R REnv := @_Log reg_t (fun idx => Bits.bits (R idx)) REnv.

Arguments may_read0 {reg_t R REnv} !sched_log !idx /.
Arguments may_read1 {reg_t R REnv} !sched_log !idx /.
Arguments may_write0 {reg_t R REnv} !sched_log !rule_log !idx / : simpl nomatch.
Arguments may_write1 {reg_t R REnv} !sched_log !rule_log !idx / : simpl nomatch.
