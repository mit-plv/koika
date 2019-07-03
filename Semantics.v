Require Import Coq.Lists.List.
Require Import SGA.Common SGA.Syntax.

Import ListNotations.

Inductive value :=
| vtt
| vbits (bits: list bool).

Inductive result {A} :=
| Success (a: A)
| CannotRun
| Stuck.
Arguments result : clear implicits.

Definition result_bind {A B} (r: result A) (f: A -> result B) :=
  match r with
  | Success a => f a
  | CannotRun => CannotRun
  | Stuck => Stuck
  end.

Definition result_map {A B} (r: result A) (f: A -> B) :=
  result_bind r (fun a => Success (f a)).

Definition opt_result {A} (default: result A) (o: option A) :=
  match o with
  | Some a => Success a
  | None => default
  end.

(* Definition bool_result (default: result unit) (b: bool) := *)
(*   if b then Success tt else default. *)

(* Inductive ReadLogEntry := *)
(* | LogRead (level: Level) (vec: nat) (idx: nat). *)

(* Inductive WriteLogEntry := *)
(* | LogWrite (level: Level) (vec: nat) (idx: nat) (val: value). *)

(* Definition ReadLog := list ReadLogEntry. *)
(* Definition WriteLog := list ReadLogEntry. *)
(* Definition Log := (ReadLog * WriteLog)%type. *)

(* Scheme Equality for Level. *)

Inductive LogEntryKind := LogRead | LogWrite.
Record LogEntry := LE
  { kind: LogEntryKind;
    level: Level;
    reg: nat;
    val: value (* vtt for reads *) }.

Definition Log := list LogEntry.

Section Interp.
  Context {TVar: Type}.
  Context {TFn: Type}.

  Context {GammaEnv: Env TVar value}.
  Context {SigmaEnv: Env TFn (list (list bool) -> value) }.
  Open Scope bool_scope.

  Definition log_find log reg (f: LogEntryKind -> Level -> value -> bool) :=
    List.find (fun '(LE kind lvl r v) => (Nat.eqb reg r) && f kind lvl v) log.

  Definition log_existsb log reg (f: LogEntryKind -> Level -> value -> bool) :=
    List.existsb (fun '(LE kind lvl r v) => (Nat.eqb reg r) && f kind lvl v) log.

  Definition may_read0 sched_log rule_log idx :=
    if (log_existsb sched_log idx
                    (fun kind lvl _ => match kind, lvl with
                                    | LogWrite, P0 => true
                                    | _, _ => false
                                    end)) ||
       (log_existsb (sched_log ++ rule_log) idx
                    (fun kind lvl _ => match kind, lvl with
                                    | _, P1 => true
                                    | _, _ => false
                                    end))
    then CannotRun
    else Success tt.

  Definition may_read1 sched_log rule_log idx :=
    if (log_existsb sched_log idx
                    (fun kind lvl _ => match kind, lvl with
                                    | LogWrite, P1 => true
                                    | _, _ => false
                                    end))
    then CannotRun
    else match log_find (rule_log ++ sched_log) idx
                        (fun kind lvl _ => match kind, lvl with
                                        | LogWrite, P0 => true
                                        | _, _ => false
                                        end) with
         | Some (LE kind lvl reg v) => Success (Some v)
         | None => Success None
         end.

  Definition may_write sched_log rule_log lvl idx :=
    if match lvl with
       | P0 => (log_existsb (sched_log ++ rule_log) idx
                           (fun kind lvl _ => match kind, lvl with
                                           | LogRead, P1 | LogWrite, _ => true
                                           | _, _ => false
                                           end))
       | P1 => (log_existsb (sched_log ++ rule_log) idx
                           (fun kind lvl _ => match kind, lvl with
                                           | LogWrite, P1 => true
                                           | _, _ => false
                                           end)) end
    then CannotRun
    else Success tt.

  Fixpoint interp
           (Sigma: SigmaEnv.(env_t))
           (Gamma: GammaEnv.(env_t))
           (V: list value)
           (sched_log: Log)
           (rule_log: Log)
           (s: syntax TVar TFn) :=
    match s with
    | Bind var expr body =>
      result_bind (interp Sigma Gamma V sched_log rule_log expr) (fun '(rule_log', v) =>
      interp Sigma (putenv Gamma var v) V sched_log rule_log body)
    | Var var =>
      result_map (opt_result Stuck (getenv Gamma var)) (fun val => (rule_log, val))
    | Skip =>
      Success (rule_log, vtt)
    | Const bs =>
      Success (rule_log, vbits bs)
    | If cond tbranch fbranch =>
      result_bind (interp Sigma Gamma V sched_log rule_log cond) (fun '(rule_log', condv) =>
      if condv
      then interp Sigma Gamma V sched_log rule_log' tbranch
      else interp Sigma Gamma V sched_log rule_log' fbranch)
    | Fail =>
      CannotRun
    | Read P0 idx =>
      result_bind (may_read0 sched_log rule_log idx) (fun _ =>
      result_map (opt_result Stuck (nth_error V idx)) (fun v =>
      ((LE LogRead P0 idx vtt) :: rule_log, v)))
    | Read P1 idx =>
      result_bind (may_read1 sched_log rule_log idx) (fun latest_w0 =>
      result_map (opt_result Stuck (nth_error V idx)) (fun v =>
      ((LE LogRead P1 idx vtt) :: rule_log, match latest_w0 with
                                           | Some v => v
                                           | None => v
                                           end)))
    | Write lvl idx val =>
      result_bind (interp Sigma Gamma V sched_log rule_log val) (fun '(rule_log, v) =>
      result_map (may_write sched_log rule_log lvl idx) (fun _ =>
      ((LE LogWrite lvl idx v) :: rule_log, vtt)))
    | Call fn args =>
      result_bind
        (List.fold_left
           (fun (acc: result (Log * list (list bool))) arg =>
              result_bind acc (fun '(rule_log, argvs) =>
              result_bind (interp Sigma Gamma V sched_log rule_log arg) (fun '(rule_log, argv) =>
              match argv with
              | vbits bits => Success (rule_log, bits :: argvs)
              | _ => Stuck
              end)))
           args (Success (rule_log, [])))
        (fun '(rule_log, argvs) =>
           result_bind (opt_result Stuck (getenv Sigma fn)) (fun fn =>
           Success (rule_log, (fn argvs))))
    end.
End Interp.
