Require Import SGA.Common SGA.TypedSyntax.

Section Syntax.
  Context {pos_t rule_name_t method_name_t var_t reg_t fn_t: Type}.

  Inductive uaction :=
  | UError
  | UFail (tau: type)
  | UVar (var: var_t)
  | UConst {tau: type} (cst: type_denote tau)
  | UConstString (s: string)
  | UConstEnum (sig: enum_sig) (cst: string)
  | UAssign (v: var_t) (ex: uaction)
  | USeq (r1 r2: uaction)
  | UBind (v: var_t) (ex: uaction) (body: uaction)
  | UIf (cond: uaction) (tbranch: uaction) (fbranch: uaction)
  | URead (port: Port) (idx: reg_t)
  | UWrite (port: Port) (idx: reg_t) (value: uaction)
  | UCall (fn: fn_t) (arg1: uaction) (arg2: uaction)
  | UInternalCall (sig: @InternalSignature method_name_t var_t) (body: uaction) (args: list uaction)
  | UAPos (p: pos_t) (e: uaction).

  Inductive uscheduler :=
  | UDone
  | UTry (r: rule_name_t) (s1 s2: uscheduler)
  | UCons (r: rule_name_t) (s: uscheduler)
  | USPos (p: pos_t) (s: uscheduler).
End Syntax.

Arguments uaction : clear implicits.
Arguments uscheduler : clear implicits.
