(*! Circuits | Syntax of circuits (RTL) !*)
Require Export Koika.Common Koika.Environments Koika.Primitives.

Import PrimTyped CircuitSignatures.

Section Circuit.
  Context {rule_name_t reg_t ext_fn_t: Type}.
  Context {rwdata: nat -> Type}. (* Forward declaration *)

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Inductive rwdata_field :=
  | rwdata_r0
  | rwdata_r1
  | rwdata_w0
  | rwdata_w1
  | rwdata_data0
  | rwdata_data1.

  Inductive rwcircuit_field :=
  | rwcircuit_rwdata (r: reg_t) (field: rwdata_field)
  | rwcircuit_canfire.

  Inductive circuit: nat -> Type :=
  | CNot (c: circuit 1): circuit 1
  | CAnd (c1 c2: circuit 1): circuit 1
  | COr (c1 c2: circuit 1): circuit 1
  | CMux {sz} (select: circuit 1) (c1 c2: circuit sz): circuit sz
  | CConst {sz} (cst: bits sz): circuit sz
  | CReadRegister (reg: reg_t): circuit (CR reg)
  | CUnop (fn: fbits1) (a1: circuit (CSigma1 fn).(arg1Sig))
    : circuit (CSigma1 fn).(retSig)
  | CBinop (fn: fbits2) (a1: circuit (CSigma2 fn).(arg1Sig)) (a2: circuit (CSigma2 fn).(arg2Sig))
    : circuit (CSigma2 fn).(retSig)
  | CExternal (idx: ext_fn_t)
              (a: circuit (CSigma idx).(arg1Sig))
    : circuit (CSigma idx).(retSig)
  | CBundleRef {sz} (name: rule_name_t) (regs: list reg_t)
               (bundle: context (fun r => rwdata (CR r)) regs)
               (field: rwcircuit_field) (c: circuit sz): circuit sz
  | CAnnot {sz} (annot: string) (c: circuit sz): circuit sz.
End Circuit.

Arguments circuit {rule_name_t reg_t ext_fn_t rwdata} CR CSigma sz : assert.
