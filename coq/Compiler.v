(*! Interop | Top-level compilation function and helpers !*)
Require Import
        Koika.Common Koika.Environments Koika.Types
        Koika.Syntax Koika.TypedSyntax Koika.Lowering Koika.CircuitGeneration.
Require Export Koika.Primitives.

Section EndToEnd.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {FiniteType_reg_t: FiniteType reg_t}.

  Context {Show_var_t: Show var_t}.
  Context {Show_rule_name_t: Show rule_name_t}.

  Notation CR := (lower_R R).
  Notation CSigma := (lower_Sigma Sigma).

  Notation circuit :=
    (circuit (rule_name_t := rule_name_t)
             (rwdata := rwdata (rule_name_t := rule_name_t) CR CSigma)
             CR CSigma).

  Context (opt: forall {sz}, circuit sz -> circuit sz).

  Definition compile_scheduler
             (rules: rule_name_t -> rule pos_t var_t fn_name_t R Sigma)
             (external: rule_name_t -> bool)
             (s: scheduler pos_t rule_name_t)
    : register_update_circuitry rule_name_t CR CSigma _ :=
    let cr := ContextEnv.(create) (readRegisters CR CSigma) in
    compile_scheduler' opt cr (fun rl => lower_action (rules rl)) external s.

  Context {REnv: Env reg_t}.
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Definition interp_circuits
             (circuits: register_update_circuitry rule_name_t CR CSigma REnv)
             (cr: REnv.(env_t) (fun r => bits (CR r))) :=
    let csigma := lower_sigma sigma in
    Environments.map REnv (fun _ c => interp_circuit cr csigma c) circuits.
End EndToEnd.
