Require Import SGA.Common SGA.TypedSyntax.

Section Syntax.
  Context {pos_t name_t var_t reg_t fn_t: Type}.

  Inductive uaction :=
  | UFail (tau: type)
  | UVar (var: var_t)
  | UConst {tau: type} (cst: type_denote tau)
  | UConstEnum (sig: enum_sig) (cst: string)
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

  Definition UConstBits {sz} (bs: bits sz) := @UConst (bits_t sz) bs.
End Syntax.

Arguments uaction : clear implicits.
Arguments uscheduler : clear implicits.
