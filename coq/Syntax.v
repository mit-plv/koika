Require Export Koika.Common Koika.Primitives Koika.Types Koika.ErrorReporting.

Section Syntax.
  Context {pos_t var_t rule_name_t fn_name_t: Type}.

  Inductive uaction {reg_t ext_fn_t} :=
  | UError (err: error pos_t var_t fn_name_t)
  | UFail (tau: type)
  | UVar (var: var_t)
  | UConst {tau: type} (cst: type_denote tau)
  | UAssign (v: var_t) (ex: uaction)
  | USeq (a1 a2: uaction)
  | UBind (v: var_t) (ex: uaction) (body: uaction)
  | UIf (cond: uaction) (tbranch: uaction) (fbranch: uaction)
  | URead (port: Port) (idx: reg_t)
  | UWrite (port: Port) (idx: reg_t) (value: uaction)
  | UUnop (ufn1: PrimUntyped.ufn1) (arg1: uaction)
  | UBinop (ufn2: PrimUntyped.ufn2) (arg1: uaction) (arg2: uaction)
  | UExternalCall (ufn: ext_fn_t) (arg: uaction)
  | UInternalCall (ufn: InternalFunction fn_name_t var_t uaction) (args: list uaction)
  | UAPos (p: pos_t) (e: uaction)
  | USugar (s: usugar)
  with usugar {reg_t ext_fn_t} :=
  | UErrorInAst
  | USkip
  | UConstBits {sz} (bs: bits sz)
  | UConstString (s: string)
  | UConstEnum (sig: enum_sig) (cst: string)
  | UProgn (aa: list uaction)
  | ULet (bindings: list (var_t * uaction)) (body: uaction)
  | UWhen (cond: uaction) (body: uaction)
  | USwitch (var: uaction)
            (default: uaction)
            (branches: list (uaction * uaction))
  | UStructInit (sig: struct_sig) (fields: list (string * uaction))
  | UCallModule {module_reg_t module_ext_fn_t: Type}
                (fR: module_reg_t -> reg_t)
                (fSigma: module_ext_fn_t -> ext_fn_t)
                (fn: InternalFunction fn_name_t var_t (@uaction module_reg_t module_ext_fn_t))
                (args: list uaction).

  Coercion USugar: usugar >-> uaction.

  Inductive uscheduler :=
  | UDone
  | UTry (r: rule_name_t) (s1 s2: uscheduler)
  | UCons (r: rule_name_t) (s: uscheduler)
  | USPos (p: pos_t) (s: uscheduler).
End Syntax.

Arguments usugar : clear implicits.
Arguments uaction : clear implicits.
Arguments uscheduler : clear implicits.