(*! Language | Compilation from typed ASTs to lowered ASTs !*)
Require Export Koika.Common Koika.Environments.
Require Import Koika.Syntax Koika.TypedSyntaxFunctions.
Require Koika.TypedSyntax Koika.LoweredSyntax.

Import PrimTyped CircuitSignatures.

Module Typed := TypedSyntax.
Module Low := LoweredSyntax.

Section Lowering.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Definition lsig_of_tsig (sig: tsig var_t) : lsig var_t :=
    List.map (fun '(k, tau) => (k, type_sz tau)) sig.

  Definition CR_of_R idx :=
    type_sz (R idx).
  Notation CR := CR_of_R.

  Definition CSigma_of_Sigma fn :=
    CSig_of_Sig (Sigma fn).
  Notation CSigma := CSigma_of_Sigma.

  Definition cr_of_r (r: REnv.(env_t) R)
    : REnv.(env_t) (fun idx => bits (CR idx)) :=
    map REnv (fun idx v => bits_of_value v) r.

  Definition csigma_of_sigma (sigma: forall f, Sig_denote (Sigma f))
    : forall f, CSig_denote (CSigma f) :=
    fun f => fun bs => bits_of_value (sigma f (value_of_bits bs)).

  Notation typed_action := (Typed.action pos_t var_t R Sigma).
  Notation low_action := (Low.action pos_t var_t CR CSigma).

  Section Action.
    Definition lower_unop {sig} (fn: fn1)
               (a: low_action sig (type_sz (PrimSignatures.Sigma1 fn).(arg1Sig))):
      low_action sig (type_sz (PrimSignatures.Sigma1 fn).(retSig)) :=
      let lArg1 fn := low_action sig (type_sz (PrimSignatures.Sigma1 fn).(arg1Sig)) in
      let lRet fn := low_action sig (type_sz (PrimSignatures.Sigma1 fn).(retSig)) in
      match fn return lArg1 fn -> lRet fn with
      | Display fn => fun a => LoweredSyntax.Unop (Lowered (DisplayBits fn)) a
      | Conv tau fn => fun a =>
        match fn return lArg1 (Conv tau fn) -> lRet (Conv tau fn) with
        | Pack => fun a => a
        | Unpack => fun a => a
        | Ignore => fun a => LoweredSyntax.Unop (Lowered (IgnoreBits _)) a
        end a
      | Bits1 fn => fun a => LoweredSyntax.Unop fn a
      | Struct1 fn sig f => fun a =>
        match fn return lArg1 (Struct1 fn sig f) -> lRet (Struct1 fn sig f) with
        | GetField => fun a =>
          Low.Unop (GetFieldBits sig f) a
        end a
      | Array1 fn sig idx => fun a =>
        match fn return lArg1 (Array1 fn sig idx) -> lRet (Array1 fn sig idx) with
        | GetElement => fun a =>
          Low.Unop (GetElementBits sig idx) a
        end a
      end a.

    Definition lower_binop {sig} (fn: fn2)
               (a1: low_action sig (type_sz (PrimSignatures.Sigma2 fn).(arg1Sig)))
               (a2: low_action sig (type_sz (PrimSignatures.Sigma2 fn).(arg2Sig))):
      low_action sig (type_sz (PrimSignatures.Sigma2 fn).(retSig)) :=
      let lArg1 fn := low_action sig (type_sz (PrimSignatures.Sigma2 fn).(arg1Sig)) in
      let lArg2 fn := low_action sig (type_sz (PrimSignatures.Sigma2 fn).(arg2Sig)) in
      let lRet fn := low_action sig (type_sz (PrimSignatures.Sigma2 fn).(retSig)) in
      match fn return lArg1 fn -> lArg2 fn -> lRet fn with
      | Eq tau negate => fun a1 a2 => Low.Binop (EqBits (type_sz tau) negate) a1 a2
      | Bits2 fn => fun a1 a2 => Low.Binop fn a1 a2
      | Struct2 fn sig f => fun a1 a2 =>
        match fn return lArg1 (Struct2 fn sig f) -> lArg2 (Struct2 fn sig f) -> lRet (Struct2 fn sig f) with
        | SubstField => fun a1 a2 =>
          Low.Binop (SubstFieldBits sig f) a1 a2
        end a1 a2
      | Array2 fn sig idx => fun a1 a2 =>
        match fn return lArg1 (Array2 fn sig idx) -> lArg2 (Array2 fn sig idx) -> lRet (Array2 fn sig idx) with
        | SubstElement => fun a1 a2 =>
          Low.Binop (SubstElementBits sig idx) a1 a2
        end a1 a2
      end a1 a2.

    Fixpoint lower_action
             {sig: tsig var_t} {tau}
             (a: typed_action sig tau):
      low_action (lsig_of_tsig sig) (type_sz tau) :=
      let l {sig tau} a := @lower_action sig tau a in
      match a with
      | Typed.Fail tau =>
        Low.Fail (type_sz tau)
      | Typed.Var m =>
        Low.Var (member_map _ _ _ m)
      | Typed.Const cst =>
        Low.Const (bits_of_value cst)
      | Typed.Seq r1 r2 =>
        Low.Seq (l r1) (l r2)
      | Typed.Assign m ex =>
        Low.Assign (member_map _ _ _ m) (l ex)
      | Typed.Bind var ex body =>
        Low.Bind var (l ex) (l body)
      | Typed.If cond tbranch fbranch =>
        Low.If (l cond) (l tbranch) (l fbranch)
      | Typed.Read p idx =>
        Low.Read p idx
      | Typed.Write p idx val =>
        Low.Write p idx (l val)
      | Typed.Unop fn a =>
        lower_unop fn (l a)
      | Typed.Binop fn a1 a2 =>
        lower_binop fn (l a1) (l a2)
      | Typed.ExternalCall fn a =>
        Low.ExternalCall fn (l a)
      | Typed.APos p a =>
        Low.APos p (l a)
      end.
  End Action.
End Lowering.

Arguments CR_of_R {reg_t} R idx : assert.
Arguments CSigma_of_Sigma {ext_fn_t} Sigma fn : assert.
Arguments cr_of_r {reg_t} {R} {REnv} r : assert.
Arguments csigma_of_sigma {ext_fn_t} {Sigma} sigma f a : assert.
