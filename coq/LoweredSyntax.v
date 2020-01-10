(*! Language | Lowered ASTs (weakly-typed) !*)
Require Export Koika.Common Koika.Environments Koika.Types Koika.Primitives.

Import PrimTyped CircuitSignatures.

Section Syntax.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> nat}.
  Context {Sigma: ext_fn_t -> CExternalSignature}.

  Inductive action : csig var_t -> nat -> Type :=
  | Fail {sig} sz : action sig sz
  | Var {sig} {k: var_t} {sz: nat}
        (m: member (k, sz) sig) : action sig sz
  | Const {sig} {sz: nat}
          (cst: bits sz) : action sig sz
  | Assign {sig} {k: var_t} {sz: nat}
           (m: member (k, sz) sig) (ex: action sig sz) : action sig 0
  | Seq {sig sz}
        (r1: action sig 0)
        (r2: action sig sz) : action sig sz
  | Bind {sig} {sz sz'}
         (var: var_t)
         (ex: action sig sz)
         (body: action (List.cons (var, sz) sig) sz') : action sig sz'
  | If {sig sz}
       (cond: action sig 1)
       (tbranch fbranch: action sig sz) : action sig sz
  | Read {sig}
         (port: Port)
         (idx: reg_t): action sig (R idx)
  | Write {sig}
          (port: Port) (idx: reg_t)
          (value: action sig (R idx)) : action sig 0
  | Unop {sig}
          (fn: fbits1)
          (arg1: action sig (CSigma1 fn).(arg1Sig))
    : action sig (CSigma1 fn).(retSig)
  | Binop {sig}
          (fn: fbits2)
          (arg1: action sig (CSigma2 fn).(arg1Sig))
          (arg2: action sig (CSigma2 fn).(arg2Sig))
    : action sig (CSigma2 fn).(retSig)
  | ExternalCall {sig}
                 (fn: ext_fn_t)
                 (arg: action sig (Sigma fn).(arg1Sig))
    : action sig (Sigma fn).(retSig)
  | APos {sig sz} (pos: pos_t) (a: action sig sz)
    : action sig sz.

  Inductive scheduler :=
  | Done
  | Cons (r: rule_name_t) (s: scheduler)
  | Try (r: rule_name_t) (s1 s2: scheduler)
  | SPos (pos: pos_t) (s: scheduler).

  Definition rule := action nil 0.
End Syntax.

Arguments rule pos_t var_t {reg_t ext_fn_t} R Sigma : assert.
Arguments action pos_t var_t {reg_t ext_fn_t} R Sigma sig sz : assert.
Arguments scheduler : clear implicits.
