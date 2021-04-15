(*! Tools | Functions defined on lowered ASTs !*)
Require Import Koika.Member Koika.Primitives Koika.LoweredSemantics.

Section LoweredSyntaxFunctions.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> nat}
          {Sigma: ext_fn_t -> CExternalSignature}.
  Context {REnv : Env reg_t}.

  Notation rule := (rule pos_t var_t R Sigma).
  Notation action := (action pos_t var_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Inductive LRW := LRWRead | LRWWrite.
  Notation event_t := (LRW * Port)%type.

  Section Footprint.
    Notation footprint_t := (list (reg_t * event_t)).

    Fixpoint action_footprint' {sig tau} (acc: footprint_t) (a: action sig tau) :=
      match a with
      | Fail _ | Var _ _ | Const _ => acc
      | Assign _ m ex => action_footprint' acc ex
      | Seq r1 r2 => action_footprint' (action_footprint' acc r1) r2
      | Bind _ ex body => action_footprint' (action_footprint' acc ex) body
      | If cond tbranch fbranch => action_footprint' (action_footprint' (action_footprint' acc cond) tbranch) fbranch
      | Read port idx => (idx, (LRWRead, port)) :: acc
      | Write port idx value => action_footprint' ((idx, (LRWWrite, port)) :: acc) value
      | Unop fn arg1 => action_footprint' acc arg1
      | Binop fn arg1 arg2 => action_footprint' (action_footprint' acc arg1) arg2
      | ExternalCall fn arg => action_footprint' acc arg
      | APos _ a => action_footprint' acc a
      end.

    Definition action_footprint {sig tau} (a: action sig tau) :=
      action_footprint' [] a.

    Definition action_registers {sig tau} {EQ: EqDec reg_t} (a: action sig tau) : list reg_t :=
      dedup [] (List.map (fun '(rs, _) => rs) (action_footprint a)).

    Context (rules: rule_name_t -> rule).

    Section Dependencies.
      Fixpoint all_scheduler_paths (s: scheduler) : list (list rule_name_t) :=
        let cons r s := List.map (fun rs => r :: rs) (all_scheduler_paths s) in
        match s with
        | Done => [[]]
        | Cons r s => cons r s
        | Try r s1 s2 => List.app (cons r s1) (cons r s2)
        | SPos _ s => all_scheduler_paths s
        end.

      Record reg_rules :=
        { rr_read1 : list rule_name_t;
          rr_write0 : list rule_name_t }.

      Definition rr_add_read1 rr rl :=
        {| rr_read1 := rl :: rr.(rr_read1); rr_write0 := rr.(rr_write0) |}.

      Definition rr_add_write0 rr rl :=
        {| rr_read1 := rr.(rr_read1); rr_write0 := rl :: rr.(rr_write0) |}.

      Notation reg_rules_map := (REnv.(env_t) (fun _ : reg_t => reg_rules)).

      Definition compute_rules_by_registers (footprints: list (rule_name_t * footprint_t)) : reg_rules_map :=
        let rules_by_register := REnv.(create) (fun _ => {| rr_read1 := []; rr_write0 := [] |}) in
        List.fold_left
          (fun (rbr: reg_rules_map) '(rl, action_footprint) =>
             List.fold_left
               (fun (rbr: reg_rules_map) '(reg, evt_port) =>
                  match evt_port with
                  | (LRWRead, P1) => update REnv rbr reg (fun rr => rr_add_read1 rr rl)
                  | (LRWWrite, P0) => update REnv rbr reg (fun rr => rr_add_write0 rr rl)
                  | _ => rbr
                  end)
               action_footprint rbr)
          footprints rules_by_register.

      Definition add_footprints (path: list rule_name_t) :=
        List.map (fun rl => (rl, action_footprint (rules rl))) path.

      Definition find_dependencies reg_rules :=
        List.fold_left
          (fun deps rl_r1 =>
             List.fold_left
               (fun deps rl_w0 =>
                  (rl_w0, rl_r1) :: deps)
               reg_rules.(rr_write0) deps)
          reg_rules.(rr_read1) [].

      Notation edge := (rule_name_t * rule_name_t)%type.

      Definition path_dependency_graph (path: list rule_name_t) : list (reg_t * list edge) :=
        let path_with_footprints := add_footprints path in
        let rules_by_register := compute_rules_by_registers path_with_footprints in
        let deps_by_register := Environments.map REnv (fun reg rr => find_dependencies rr) rules_by_register in
        to_alist REnv deps_by_register.

      Definition dependency_graph (s: scheduler) : list (list (reg_t * list edge)) :=
        let paths := all_scheduler_paths s in
        List.map path_dependency_graph paths.
    End Dependencies.
  End Footprint.
End LoweredSyntaxFunctions.
