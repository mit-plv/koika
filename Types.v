Require Import List.
Require Import SGA.Common SGA.Environments SGA.Syntax.

Inductive type :=
| bits_t (n: nat).

Coercion Nat_of_type '(bits_t n) :=
  n.

Coercion Type_of_type (tau: type) :=
  bits tau.

Instance EqDec_type : EqDec type := _.

Record ExternalSignature :=
  FunSig { arg1Type: type;
           arg2Type: type;
           retType: type }.

Coercion Type_of_signature fn :=
  fn.(arg1Type) -> fn.(arg2Type) -> fn.(retType).

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

Lemma ExternalSignature_injRet :
  forall (s1 s2 s1' s2': type) (retType retType': type),
    FunSig s1 s2 retType =
    FunSig s1' s2' retType' ->
    retType = retType'.
Proof. now inversion 1. Qed.

Hint Extern 10 => eapply @ExternalSignature_injRet : types.
