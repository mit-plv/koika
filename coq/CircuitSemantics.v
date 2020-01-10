(*! Circuits | Interpretation of circuits !*)
Require Export Koika.Common Koika.Environments Koika.CircuitSyntax.

Import PrimTyped CircuitSignatures.

Section Interpretation.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.
  Context {REnv: Env reg_t}.

  Context (cr: REnv.(env_t) (fun idx => bits (CR (idx)))).
  Context (csigma: forall f, CSig_denote (CSigma f)).

  Context {rwdata: nat -> Type}.
  Notation circuit := (@circuit rule_name_t reg_t ext_fn_t rwdata CR CSigma).

  Fixpoint interp_circuit {n} (c: circuit n) : bits n :=
    match c with
    | CNot c =>
      Ob~(negb (Bits.single (interp_circuit c)))
    | CAnd c1 c2 =>
      Ob~(andb (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)))
    | COr c1 c2 =>
      Ob~(orb (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)))
    | CMux select c1 c2 =>
      if Bits.single (interp_circuit select) then interp_circuit c1
      else interp_circuit c2
    | CConst cst =>
      cst
    | CReadRegister idx =>
      REnv.(getenv) cr idx
    | CExternal fn arg =>
      csigma fn (interp_circuit arg)
    | CUnop fn arg1 =>
      PrimSpecs.sigma1 (Bits1 fn) (interp_circuit arg1)
    | CBinop fn arg1 arg2 =>
      PrimSpecs.sigma2 (Bits2 fn) (interp_circuit arg1) (interp_circuit arg2)
    | CBundleRef _ _ _ _ c =>
      interp_circuit c
    | CAnnot _ c =>
      interp_circuit c
    end.
End Interpretation.
