Require Import Koika.Frontend.

Section CircuitTools.
  Context {rule_name_t reg_t ext_fn_t: Type}.
  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.
  Context {rwdata: nat -> Type}.

  Fixpoint circuit_size {sz: nat}
           (c: circuit (rwdata := rwdata) (rule_name_t := rule_name_t) CR CSigma sz): N :=
    1 + match c with
        | CNot c => circuit_size c
        | CAnd c1 c2 => circuit_size c1 + circuit_size c2
        | COr c1 c2 => circuit_size c1 + circuit_size c2
        | CMux select c1 c2 => circuit_size select + circuit_size c1 + circuit_size c2
        | CConst _ => 0
        | CReadRegister _ => 0
        | CUnop _ a1 => circuit_size a1
        | CBinop _ a1 a2 => circuit_size a1 + circuit_size a2
        | CExternal _ a => circuit_size a
        | CBundleRef _ _ _ _ c => circuit_size c
        | CAnnot _ c => circuit_size c
        end.
End CircuitTools.

Definition demo_packages : list interop_package_t :=
  [].
