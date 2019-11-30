(*! Tools | Functions defined on typed ASTs !*)
Require Import Koika.Member Koika.TypedSyntax Koika.Primitives Koika.Semantics.

Section TypedSyntaxTools.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.

  Notation rule := (rule pos_t var_t R Sigma).
  Notation action := (action pos_t var_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Fixpoint scheduler_rules (s: scheduler) :=
    match s with
    | Done => []
    | Cons r s => r :: scheduler_rules s
    | Try r s1 s2 => r :: scheduler_rules s1 ++ scheduler_rules s2
    | SPos _ s => scheduler_rules s
    end.

  Section Footprint.
    Context {REnv : Env reg_t}.

    Inductive RW := RWRead | RWWrite.
    Notation event_t := (RW * Port)%type.
    Notation footprint_t := (list (reg_t * event_t)).

    Fixpoint action_footprint' {sig tau} (acc: footprint_t) (a: action sig tau) :=
      match a with
      | Fail _ | Var _ | Const _ => acc
      | Assign m ex => action_footprint' acc ex
      | Seq r1 r2 => action_footprint' (action_footprint' acc r1) r2
      | Bind var ex body => action_footprint' (action_footprint' acc ex) body
      | If cond tbranch fbranch => action_footprint' (action_footprint' (action_footprint' acc cond) tbranch) fbranch
      | Read port idx => (idx, (RWRead, port)) :: acc
      | Write port idx value => action_footprint' ((idx, (RWWrite, port)) :: acc) value
      | Unop fn arg1 => action_footprint' acc arg1
      | Binop fn arg1 arg2 => action_footprint' (action_footprint' acc arg1) arg2
      | ExternalCall fn arg => action_footprint' acc arg
      | APos _ a => action_footprint' acc a
      end.

    Definition action_footprint {sig tau} (a: action sig tau) :=
      action_footprint' [] a.

    Fixpoint dedup {A} {EQ: EqDec A} (acc: list A) (l: list A) :=
      match l with
      | [] => acc
      | a :: l =>
        let already_seen := List.in_dec eq_dec a acc in
        let acc := if already_seen then acc else a :: acc in
        dedup acc l
      end.

    Fixpoint action_registers {sig tau} {EQ: EqDec reg_t} (a: action sig tau) : list reg_t :=
      dedup [] (List.map (fun '(rs, _) => rs) (action_footprint a)).

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
                  | (RWRead, P1) => REnv.(putenv) rbr reg (rr_add_read1 (REnv.(getenv) rbr reg) rl)
                  | (RWWrite, P0) => REnv.(putenv) rbr reg (rr_add_write0 (REnv.(getenv) rbr reg) rl)
                  | _ => rbr
                  end)
               action_footprint rbr)
          footprints rules_by_register.

      Context (rules: rule_name_t -> rule).

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

  Inductive any_action :=
  | AnyAction {sig: tsig var_t} {tau: type} (aa_action: action sig tau).

  Fixpoint existsb_subterm (f: any_action -> bool) {sig tau} (a: action sig tau) :=
    f (AnyAction a) ||
      match a with
      | Fail tau => false
      | Var m => false
      | Const cst => false
      | Assign m ex => existsb_subterm f ex
      | Seq r1 r2 => existsb_subterm f r1 || existsb_subterm f r2
      | Bind var ex body => existsb_subterm f ex || existsb_subterm f body
      | If cond tbranch fbranch => existsb_subterm f cond || existsb_subterm f tbranch || existsb_subterm f fbranch
      | Read port idx => false
      | Write port idx value => existsb_subterm f value
      | Unop fn a => existsb_subterm f a
      | Binop fn a1 a2 => existsb_subterm f a1 || existsb_subterm f a2
      | ExternalCall fn arg => existsb_subterm f arg
      | APos _ a => existsb_subterm f a
      end.

  Fixpoint member_mentions_shadowed_binding
           {K V} {EQ: EqDec K} {sig: list (K * V)} {k v} (m: member (k, v) sig) : bool :=
    match m return bool with
    | MemberHd k _ => false
    | MemberTl (k, _) (k', _) sig' m' => beq_dec k k' || member_mentions_shadowed_binding m'
    end.

  Fixpoint action_mentions_shadowed_var {EQ: EqDec var_t} {sig tau} (a: action sig tau) :=
    existsb_subterm (fun a => match a with
                           | AnyAction (Var m) => member_mentions_shadowed_binding m
                           | _ => false
                           end) a.

  Fixpoint action_mentions_var {EQ: EqDec var_t} {sig tau} (k: var_t) (a: action sig tau) :=
    existsb_subterm (fun a => match a with
                           | AnyAction (@Var _ _ _ _ _ _ _ k' _ m) => beq_dec k k'
                           | _ => false
                           end) a.

  Fixpoint is_const_zero {sig tau} (a: action sig tau) :=
    match a with
    | Fail tau => false
    | Var m => false
    | Const cst => N.eqb (Bits.to_N (bits_of_value cst)) N.zero
    | Assign m ex => false
    | Seq r1 r2 => is_const_zero r2
    | Bind var ex body => is_const_zero body
    | If cond tbranch fbranch => is_const_zero tbranch && is_const_zero fbranch
    | Read port idx => false
    | Write port idx value => false
    | Unop fn arg1 => false
    | Binop fn arg1 arg2 => false
    | ExternalCall fn arg => false
    | APos pos a => is_const_zero a
    end.

  Definition action_type {sig tau} (a: action sig tau) : option type :=
    match a with
    | @Fail _ _ _ _ _ _ _ tau => Some tau
    | @Var _ _ _ _ _ _ _ _ tau _ => Some tau
    | @Const _ _ _ _ _ _ _ tau cst => Some tau
    | @Assign _ _ _ _ _ _ _ _ _ _ _ => Some unit_t
    | @Seq _ _ _ _ _ _ _ tau _ _ => Some tau
    | @Bind _ _ _ _ _ _ _ _ tau' _ _ _ => Some tau'
    | @If _ _ _ _ _ _ _ tau _ _ _ => Some tau
    | @Read _ _ _ _ _ _ _ _ _ => None
    | @Write _ _ _ _ _ _ _ _ _ _ => Some unit_t
    | @Unop _ _ _ _ _ _ _ fn _ => Some (PrimSignatures.Sigma1 fn).(retType)
    | @Binop _ _ _ _ _ _ _ fn _ _ => Some (PrimSignatures.Sigma2 fn).(retType)
    | @ExternalCall _ _ _ _ _ _ _ _ _ => None
    | @APos _ _ _ _ _ _ _ tau _ _ => Some tau
    end.

  Fixpoint interp_arithmetic {sig tau} (a: action sig tau) : option (type_denote tau) :=
    match a with
    | Fail tau => None
    | Var m => None
    | Const cst => Some cst
    | Assign m ex => None
    | Seq r1 r2 => None
    | Bind var ex body => None
    | If cond tbranch fbranch => None
    | Read port idx => None
    | Write port idx value => None
    | Unop fn arg1 =>
      let/opt r1 := interp_arithmetic arg1 in
      Some (PrimSpecs.sigma1 fn r1)
    | Binop fn arg1 arg2 =>
      let/opt r1 := interp_arithmetic arg1 in
      let/opt r2 := interp_arithmetic arg2 in
      Some (PrimSpecs.sigma2 fn r1 r2)
    | ExternalCall fn arg => None
    | APos pos a => interp_arithmetic a
    end.
End TypedSyntaxTools.
