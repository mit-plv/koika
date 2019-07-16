Require Import Coq.Lists.List.
Require Export SGA.Common SGA.Environments SGA.Types SGA.Syntax.

Section TypedSyntax.
  Context {var_t reg_t fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: fn_t -> ExternalSignature}.

  Definition tsig := list (var_t * type).

  Inductive expr {sig: tsig} : type -> Type :=
  | Var {k: var_t} {tau: type} (m: member (k, tau) sig): expr tau
  | Const {n: nat} (cst: bits n): expr (bits_t n)
  | Read (port: Port) (idx: reg_t): expr (R idx)
  | Call (fn: fn_t)
         (arg1: expr (Sigma fn).(arg1Type))
         (arg2: expr (Sigma fn).(arg2Type))
    : expr (Sigma fn).(retType).

  Inductive rule : tsig -> Type :=
  | Skip {sig} : rule sig
  | Fail {sig} : rule sig
  | Seq {sig} (r1 r2: rule sig) : rule sig
  | Bind {sig} {tau}
         (var: var_t)
         (ex: @expr sig tau)
         (body: rule (cons (var, tau) sig)) : rule sig
  | If {sig}
       (cond: @expr sig (bits_t 1))
       (tbranch: rule sig) (fbranch: rule sig) : rule sig
  | Write {sig}
          (port: Port) (idx: reg_t)
          (value: @expr sig (R idx)) : rule sig.

  Inductive scheduler :=
  | Done
  | Try (r: @rule nil) (s1 s2: scheduler).
End TypedSyntax.

Arguments tsig : clear implicits.
Arguments expr var_t {reg_t fn_t} R Sigma.
Arguments rule var_t {reg_t fn_t} R Sigma.
Arguments scheduler var_t {reg_t fn_t} R Sigma.

Hint Extern 10 => eapply @ExternalSignature_injRet : types.
