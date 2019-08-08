Require Import SGA.Common.

Inductive Port :=
  P0 | P1.

Section Syntax.
  Context {pos_t name_t var_t reg_t fn_t: Type}.

  Inductive uaction :=
  | UFail (n: nat)
  | UVar (var: var_t)
  | UConst {n} (cst: bits n)
  | USeq (r1 r2: uaction)
  | UBind (v: var_t) (ex: uaction) (body: uaction)
  | UIf (cond: uaction) (tbranch: uaction) (fbranch: uaction)
  | URead (port: Port) (idx: reg_t)
  | UWrite (port: Port) (idx: reg_t) (value: uaction)
  | UCall (fn: fn_t) (arg1: uaction) (arg2: uaction)
  | UAPos (p: pos_t) (e: uaction).

  Inductive uscheduler :=
  | UDone
  | UTry (r: name_t) (s1 s2: uscheduler)
  | UCons (r: name_t) (s: uscheduler)
  | USPos (p: pos_t) (s: uscheduler).
End Syntax.

Arguments uaction : clear implicits.
Arguments uscheduler : clear implicits.
