Require Import Coq.Lists.List.
Require Import SGA.Syntax.

Import ListNotations.

Inductive value :=
| vtt
| vbits (bits: list bool).

Definition opt_bind {A B} (o: option A) (f: A -> option B) :=
  match o with
  | Some a => f a
  | None => None
  end.

Definition opt_map {A B} (o: option A) (f: A -> B) :=
  opt_bind o (fun a => Some (f a)).

Axiom magic : forall {A B} (_: B), A.

(* Inductive ReadLogEntry := *)
(* | LogRead (level: Level) (vec: nat) (idx: nat). *)

(* Inductive WriteLogEntry := *)
(* | LogWrite (level: Level) (vec: nat) (idx: nat) (val: value). *)

(* Definition ReadLog := list ReadLogEntry. *)
(* Definition WriteLog := list ReadLogEntry. *)
(* Definition Log := (ReadLog * WriteLog)%type. *)

(* Scheme Equality for Level. *)

Inductive LogEntry :=
| LogRead (level: Level) (vec: nat) (idx: nat)
| LogWrite (level: Level) (vec: nat) (idx: nat) (val: value).

Definition Log := list LogEntry.

Class Env {K V: Type}: Type :=
  { tenv: Type;
    getenv: tenv -> K -> option V;
    putenv: tenv -> K -> V -> tenv }.
Arguments Env : clear implicits.
Arguments tenv {_ _}.

Section Interp.
  Context {TVar: Type}.
  Context {TFn: Type}.

  Context (GammaEnv: Env TVar value).
  Context (SigmaEnv: Env TFn (list value -> option value)).

  Context (Sigma: SigmaEnv.(tenv)).
  Context (V: SigmaEnv.(tenv)).
  Context (sched_log: Log).

  Fixpoint interp
           (Gamma: GammaEnv.(tenv))
           (rule_log: Log)
           (s: syntax TVar TFn) :=
    match s with
    | Bind var expr body =>
      opt_bind (interp Gamma rule_log expr) (fun '(rule_log', v) =>
      interp (putenv Gamma var v) rule_log body)
    | Var var =>
      opt_map (getenv Gamma var) (fun val => (rule_log, val))
    | Skip =>
      Some (rule_log, vtt)
    | Const bs =>
      Some (rule_log, vbits bs)
    | If cond tbranch fbranch =>
      opt_bind (interp Gamma rule_log cond) (fun '(rule_log', condv) =>
      if condv
      then interp Gamma rule_log' tbranch
      else interp Gamma rule_log' fbranch)
    | Fail =>
      None
    | Read P0 idx =>
      let invalid :=
          orb
            (List.existsb
               (fun entry =>
                  match entry with
                  | LogRead P1 _ _ | LogWrite _ _ _ _ => true
                  | _ => false
                  end) sched_log)
            (List.existsb
               (fun entry =>
                  match entry with
                  | LogRead P1 _ _ | LogWrite P1 _ _ _ => true
                  | _ => false
               end) rule_log) in magic tt
    | Read P1 idx =>
      magic tt
    | Write P0 idx value =>
      magic tt
    | Write P1 idx value =>
      magic tt
    | Call fn args =>
      opt_bind
        (List.fold_left
           (fun (acc: option (Log * list value)) arg =>
              opt_bind acc (fun '(rule_log, argvs) =>
              opt_map (interp Gamma rule_log arg) (fun '(rule_log, argv) =>
              (rule_log, argv :: argvs))))
           args (Some (rule_log, [])))
        (fun '(rule_log, argvs) =>
           opt_bind (getenv Sigma fn) (fun fn =>
           opt_bind (fn argvs) (fun resv =>
           Some (rule_log, resv))))
    end.