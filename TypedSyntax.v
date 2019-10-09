Require Import Coq.Lists.List.
Require Export SGA.Common SGA.Environments SGA.Types.

Section TypedSyntax.
  Context {name_t var_t reg_t fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: fn_t -> ExternalSignature}.

  Inductive action : tsig var_t -> type -> Type :=
  | Fail {sig} tau : action sig tau
  | Var {sig} {k: var_t} {tau: type}
        (m: member (k, tau) sig) : action sig tau
  | Const {sig} {tau: type}
          (cst: type_denote tau) : action sig tau
  | Assign {sig} {k:var_t} {tau:type}
           (m: member (k,tau) sig) (ex: action sig tau) : action sig unit_t
  | Seq {sig tau}
        (r1: action sig unit_t)
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
          (value: action sig (R idx)) : action sig unit_t
  | Call {sig}
         (fn: fn_t)
         (arg1: action sig (Sigma fn).(arg1Type))
         (arg2: action sig (Sigma fn).(arg2Type)) : action sig (Sigma fn).(retType).

  Inductive scheduler :=
  | Done
  | Cons (r: name_t) (s: scheduler)
  | Try (r: name_t) (s1 s2: scheduler).

  Definition rule := action nil unit_t.

  Record schedule :=
    { s_sched : scheduler;
      s_actions : name_t -> rule }.
End TypedSyntax.

Arguments rule var_t {reg_t fn_t} R Sigma : assert.
Arguments action var_t {reg_t fn_t} R Sigma sig tau : assert.
Arguments scheduler : clear implicits.
Arguments schedule name_t var_t {reg_t fn_t} R Sigma : assert.

Hint Extern 10 => eapply @ExternalSignature_injRet : types.
