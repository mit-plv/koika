Require Import Coq.Bool.Bool Coq.Lists.List.
Require Import Koika.Member Koika.TypedSyntax.
Import ListNotations.

Section TypedSyntaxTools.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.

  Notation rule := (rule pos_t var_t R Sigma).
  Notation action := (action pos_t var_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Section Footprint.
    Context {REnv : Env reg_t}.

    Inductive Event := ERead | EWrite.
    Notation footprint_t := (list (reg_t * (Event * Port))).

    Fixpoint action_footprint {sig tau} (acc: footprint_t) (a: action sig tau) :=
      match a with
      | Fail _ | Var _ | Const _ => acc
      | Assign m ex => action_footprint acc ex
      | Seq r1 r2 => action_footprint (action_footprint acc r1) r2
      | Bind var ex body => action_footprint (action_footprint acc ex) body
      | If cond tbranch fbranch => action_footprint (action_footprint (action_footprint acc cond) tbranch) fbranch
      | Read port idx => (idx, (ERead, port)) :: acc
      | Write port idx value => action_footprint ((idx, (EWrite, port)) :: acc) value
      | Unop fn arg1 => action_footprint acc arg1
      | Binop fn arg1 arg2 => action_footprint (action_footprint acc arg1) arg2
      | ExternalCall fn arg => action_footprint acc arg
      | APos _ a => action_footprint acc a
      end.

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
                | (ERead, P1) => REnv.(putenv) rbr reg (rr_add_read1 (REnv.(getenv) rbr reg) rl)
                | (EWrite, P0) => REnv.(putenv) rbr reg (rr_add_write0 (REnv.(getenv) rbr reg) rl)
                | _ => rbr
                end)
             action_footprint rbr)
        footprints rules_by_register.

    Context (rules: rule_name_t -> rule).

    Definition add_footprints (path: list rule_name_t) :=
      List.map (fun rl => (rl, action_footprint [] (rules rl))) path.

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
      let deps_by_register := map REnv (fun reg rr => find_dependencies rr) rules_by_register in
      to_alist REnv deps_by_register.

    Definition dependency_graph (s: scheduler) : list (list (reg_t * list edge)) :=
      let paths := all_scheduler_paths s in
      List.map path_dependency_graph paths.
  End Footprint.

  Fixpoint existsb_subterm (f: forall sig tau, action sig tau -> bool) {sig tau} (a: action sig tau) :=
    f _ _ a ||
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
    existsb_subterm (fun _ _ a => match a with
                               | Var m => member_mentions_shadowed_binding m
                               | _ => false
                               end) a.

  Fixpoint action_mentions_var {EQ: EqDec var_t} {sig tau} (k: var_t) (a: action sig tau) :=
    existsb_subterm (fun _ _ a => match a with
                               | @Var _ _ _ _ _ _ _ k' _ m => beq_dec k k'
                               | _ => false
                               end) a.
End TypedSyntaxTools.
