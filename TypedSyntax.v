Require Import Coq.Lists.List.
Require Export SGA.Common SGA.Environments SGA.Types SGA.Syntax.

Section TypedSyntax.
  Context {name_t var_t reg_t fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: fn_t -> ExternalSignature}.

  Definition tsig := list (var_t * type).

  Inductive action : tsig -> type -> Type :=
  | Fail {sig} tau : action sig tau
  | Var {sig} {k: var_t} {tau: type}
        (m: member (k, tau) sig) : action sig tau
  | Const {sig} {n: nat}
          (cst: bits n) : action sig (bits_t n)
  | Seq {sig tau}
        (r1: action sig (bits_t 0))
        (r2: action sig tau) : action sig tau
  | Bind {sig} {tau tau'}
         (var: var_t)
         (ex: action sig tau)
         (body: action (List.cons (var, tau) sig) tau') : action sig tau'
  | If {sig tau}
       (cond: action sig (bits_t 1))
       (tbranch fbranch: action sig tau) : action sig tau
  | Read {sig}
         (port: Port)
         (idx: reg_t): action sig (R idx)
  | Write {sig}
          (port: Port) (idx: reg_t)
          (value: action sig (R idx)) : action sig (bits_t 0)
  | Call {sig}
         (fn: fn_t)
         (arg1: action sig (Sigma fn).(arg1Type))
         (arg2: action sig (Sigma fn).(arg2Type)) : action sig (Sigma fn).(retType).

  Inductive scheduler :=
  | Done
  | Cons (r: name_t) (s: scheduler)
  | Try (r: name_t) (s1 s2: scheduler).

  Definition rule := action nil (bits_t 0).

  Record schedule :=
    { s_sched : scheduler;
      s_actions : name_t -> rule }.
End TypedSyntax.

Arguments tsig : clear implicits.
Arguments rule var_t {reg_t fn_t} R Sigma.
Arguments action var_t {reg_t fn_t} R Sigma.
Arguments scheduler : clear implicits.
Arguments schedule name_t var_t {reg_t fn_t} R Sigma.

Hint Extern 10 => eapply @ExternalSignature_injRet : types.
