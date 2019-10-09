Require Export SGA.Common SGA.Types SGA.ErrorReporting.

Section Syntax.
  Context {pos_t rule_name_t fn_name_t var_t: Type}.

  Inductive uaction {reg_t ufn_t} :=
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
  | UCall (fn: ufn_t) (arg1: uaction) (arg2: uaction)
  | UInternalCall (sig: @InternalSignature fn_name_t var_t)
                  (body: uaction) (args: list uaction)
  | UAPos (p: pos_t) (e: uaction)
  | USugar (s: usugar)
  with usugar {reg_t ufn_t} :=
  | USkip
  | UProgn (aa: list uaction)
  | UConstBits {sz} (bs: bits sz)
  | UConstString (s: string)
  | UConstEnum (sig: enum_sig) (cst: string)
  | UStructInit (sig: struct_sig) (fields: list (string * uaction))
  | USwitch (var: uaction)
            (default: uaction)
            (branches: list (uaction * uaction))
  | UCallModule {module_reg_t: Type} {module_ufn_t: Type}
                (fR: module_reg_t -> reg_t)
                (fSigma: module_ufn_t -> ufn_t)
                (sig: @InternalSignature fn_name_t var_t)
                (body: @uaction module_reg_t module_ufn_t)
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
