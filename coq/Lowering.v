(*! Language | Compilation from typed ASTs to lowered ASTs !*)
Require Export Koika.Common Koika.Environments.
Require Import Koika.Syntax Koika.TypedSyntaxFunctions.
Require Koika.TypedSyntax Koika.LoweredSyntax.

Import PrimTyped CircuitSignatures.

Section Lowering.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Definition lsig_of_tsig (sig: tsig var_t) : lsig :=
    List.map (fun k_tau => type_sz (snd k_tau)) sig.

  Definition lower_R idx :=
    type_sz (R idx).
  Notation lR := lower_R.

  Definition lower_Sigma fn :=
    CSig_of_Sig (Sigma fn).
  Notation lSigma := lower_Sigma.

  Definition lower_r (r: REnv.(env_t) R)
    : REnv.(env_t) (fun idx => bits (lR idx)) :=
    map REnv (fun idx v => bits_of_value v) r.

  Definition lower_sigma (sigma: forall f, Sig_denote (Sigma f))
    : forall f, CSig_denote (lSigma f) :=
    fun f => fun bs => bits_of_value (sigma f (value_of_bits bs)).

  Notation typed_action := (TypedSyntax.action pos_t var_t R Sigma).
  Notation low_action := (LoweredSyntax.action pos_t var_t lR lSigma).

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
          LoweredSyntax.Unop (GetFieldBits sig f) a
        end a
      | Array1 fn sig idx => fun a =>
        match fn return lArg1 (Array1 fn sig idx) -> lRet (Array1 fn sig idx) with
        | GetElement => fun a =>
          LoweredSyntax.Unop (GetElementBits sig idx) a
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
      | Eq tau negate => fun a1 a2 => LoweredSyntax.Binop (EqBits (type_sz tau) negate) a1 a2
      | Bits2 fn => fun a1 a2 => LoweredSyntax.Binop fn a1 a2
      | Struct2 fn sig f => fun a1 a2 =>
        match fn return lArg1 (Struct2 fn sig f) -> lArg2 (Struct2 fn sig f) -> lRet (Struct2 fn sig f) with
        | SubstField => fun a1 a2 =>
          LoweredSyntax.Binop (SubstFieldBits sig f) a1 a2
        end a1 a2
      | Array2 fn sig idx => fun a1 a2 =>
        match fn return lArg1 (Array2 fn sig idx) -> lArg2 (Array2 fn sig idx) -> lRet (Array2 fn sig idx) with
        | SubstElement => fun a1 a2 =>
          LoweredSyntax.Binop (SubstElementBits sig idx) a1 a2
        end a1 a2
      end a1 a2.

    Definition lower_member
               {k: var_t} {tau: type} {sig}
               (m: member (k, tau) sig) :
      member (type_sz tau) (lsig_of_tsig sig) :=
      member_map _ m.

    Fixpoint lower_action
             {sig: tsig var_t} {tau}
             (a: typed_action sig tau):
      low_action (lsig_of_tsig sig) (type_sz tau) :=
      let l {sig tau} a := @lower_action sig tau a in
      match a with
      | TypedSyntax.Fail tau =>
        LoweredSyntax.Fail (type_sz tau)
      | @TypedSyntax.Var _ _ _ _ _ _ _ k _ m =>
        LoweredSyntax.Var k (lower_member m)
      | TypedSyntax.Const cst =>
        LoweredSyntax.Const (bits_of_value cst)
      | TypedSyntax.Seq r1 r2 =>
        LoweredSyntax.Seq (l r1) (l r2)
      | @TypedSyntax.Assign _ _ _ _ _ _ _ k _ m ex =>
        LoweredSyntax.Assign k (lower_member m) (l ex)
      | TypedSyntax.Bind var ex body =>
        LoweredSyntax.Bind var (l ex) (l body)
      | TypedSyntax.If cond tbranch fbranch =>
        LoweredSyntax.If (l cond) (l tbranch) (l fbranch)
      | TypedSyntax.Read p idx =>
        LoweredSyntax.Read p idx
      | TypedSyntax.Write p idx val =>
        LoweredSyntax.Write p idx (l val)
      | TypedSyntax.Unop fn a =>
        lower_unop fn (l a)
      | TypedSyntax.Binop fn a1 a2 =>
        lower_binop fn (l a1) (l a2)
      | TypedSyntax.ExternalCall fn a =>
        LoweredSyntax.ExternalCall fn (l a)
      | TypedSyntax.APos p a =>
        LoweredSyntax.APos p (l a)
      end.
  End Action.
End Lowering.

Arguments lower_R {reg_t} R idx : assert.
Arguments lower_Sigma {ext_fn_t} Sigma fn : assert.
Arguments lower_r {reg_t} {R} {REnv} r : assert.
Arguments lower_sigma {ext_fn_t} {Sigma} sigma f a : assert.
