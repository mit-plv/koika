Require Import SGA.Common.

Inductive Port :=
  P0 | P1.

Section Syntax.
  Context {pos_t var_t reg_t fn_t: Type}.

  Inductive uexpr :=
  | UVar (var: var_t)
  | UConst {n} (cst: bits n)
  | URead (port: Port) (idx: reg_t)
  | UCall (fn: fn_t) (arg1: uexpr) (arg2: uexpr)
  | UEPos (p: pos_t) (e: uexpr).

  Inductive urule  :=
  | USkip
  | UFail
  | USeq (r1 r2: urule)
  | UBind (v: var_t) (ex: uexpr) (body: urule)
  | UIf (cond: uexpr) (tbranch: urule) (fbranch: urule)
  | UWrite (port: Port) (idx: reg_t) (value: uexpr)
  | URPos (p: pos_t) (r: urule).

  Inductive uscheduler :=
  | UDone
  | UTry (r: urule) (s1 s2: uscheduler)
  | USPos (p: pos_t) (s: uscheduler).
End Syntax.

Arguments uexpr : clear implicits.
Arguments urule : clear implicits.
Arguments uscheduler : clear implicits.
