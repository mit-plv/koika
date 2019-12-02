(*! Tools | Functions defined on typed ASTs !*)
Require Import Koika.Member Koika.TypedSyntax Koika.Primitives Koika.Semantics.

Section TypedSyntaxTools.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv : Env reg_t}.

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

  Inductive RW := RWRead | RWWrite.
  Notation event_t := (RW * Port)%type.

  Section Footprint.
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

    Context (rules: rule_name_t -> rule).

    Section Classification.
      Inductive register_kind := Wire | Register | EHR.

      Notation reg_events_map := (REnv.(env_t) (fun _ : reg_t => list event_t)).

      Definition footprint_by_register (footprint: footprint_t) : reg_events_map :=
        List.fold_right
          (fun '(reg, evt) map =>
             Environments.update REnv map reg (fun _ evts => evt :: evts))
          (REnv.(create) (fun k => [])) footprint.

      Notation reg_kind_map := (REnv.(env_t) (fun _ : reg_t => register_kind)).

      Definition wire_ok (e: event_t) :=
        match e with
        | (RWWrite, P0) | (RWRead, P1) => true
        | _ => false
        end.

      Definition register_ok (e: event_t) :=
        match e with
        | (_, P0) => true
        | _ => false
        end.

      Definition compute_register_kind (events: list event_t) :=
        if List.forallb wire_ok events then Wire
        else if List.forallb register_ok events then Register
             else EHR.

      Definition classify_registers (s: scheduler) : reg_kind_map :=
        let rule_names := scheduler_rules s in
        let footprints := List.map (fun rn => action_footprint (rules rn)) rule_names in
        let by_register := footprint_by_register (List.concat footprints) in
        Environments.map REnv (fun _ events => compute_register_kind events) by_register.
    End Classification.

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
                  | (RWRead, P1) => update REnv rbr reg (fun _ rr => rr_add_read1 rr rl)
                  | (RWWrite, P0) => update REnv rbr reg (fun _ rr => rr_add_write0 rr rl)
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

  Section StaticAnalysis.
    Inductive tribool := tTrue | tFalse | tUnknown.

    Record register_history :=
      { hr0: tribool; hr1: tribool;
        hw0: tribool; hw1: tribool }.

    Definition empty_history :=
      {| hr0 := tFalse; hr1 := tFalse;
         hw0 := tFalse; hw1 := tFalse |}.

    Definition unknown_history :=
      {| hr0 := tUnknown; hr1 := tUnknown;
         hw0 := tUnknown; hw1 := tUnknown |}.

    Notation reg_history_map := (REnv.(env_t) (fun _ : reg_t => register_history)).

    Inductive register_annotation :=
    | aPos (pos: pos_t)
    | aHistory (rh: reg_history_map).

    Definition merge_tribools t1 t2 :=
      match t1, t2 with
      | tTrue, tTrue => tTrue
      | tFalse, tFalse => tFalse
      | _, _ => tUnknown
      end.

    Definition merge_histories h1 h2 :=
      let '{| hr0 := hr0; hr1 := hr1; hw0 := hw0; hw1 := hw1 |} := h1 in
      let '{| hr0 := hr0'; hr1 := hr1'; hw0 := hw0'; hw1 := hw1' |} := h2 in
      {| hr0 := merge_tribools hr0 hr0';
         hr1 := merge_tribools hr1 hr1';
         hw0 := merge_tribools hw0 hw0';
         hw1 := merge_tribools hw1 hw1' |}.

    Definition merge_history_maps m1 m2 :=
      Environments.map2 REnv (fun _ h1 h2 => merge_histories h1 h2) m1 m2.

    Definition update_history h (evt: event_t) :=
      match evt with
      | (RWRead, P0)  => {| hr0 := tTrue; hr1 := h.(hr1); hw0 := h.(hw0); hw1 := h.(hw1) |}
      | (RWRead, P1)  => {| hr0 := h.(hr0); hr1 := tTrue; hw0 := h.(hw0); hw1 := h.(hw1) |}
      | (RWWrite, P0) => {| hr0 := h.(hr0); hr1 := h.(hr1); hw0 := tTrue; hw1 := h.(hw1) |}
      | (RWWrite, P1) => {| hr0 := h.(hr0); hr1 := h.(hr1); hw0 := h.(hw0); hw1 := tTrue |}
      end.

    Definition update_map env reg (evt: event_t) :=
      Environments.update REnv env reg (fun _ h => update_history h evt).

    Fixpoint annotate_action_register_history
             {sig tau} (env: reg_history_map)
             (a: action sig tau)
      : reg_history_map * TypedSyntax.action register_annotation var_t R Sigma sig tau :=
      match a with
      | Fail tau =>
        (env, APos (aHistory env) (Fail tau))
      | Var m => (env, Var m)
      | Const cst => (env, Const cst)
      | Assign m ex =>
        let '(env, ex) := annotate_action_register_history env ex in
        (env, Assign m ex)
      | Seq r1 r2 =>
        let '(env, r1) := annotate_action_register_history env r1 in
        let '(env, r2) := annotate_action_register_history env r2 in
        (env, Seq r1 r2)
      | Bind var ex body =>
        let '(env, ex) := annotate_action_register_history env ex in
        let '(env, body) := annotate_action_register_history env body in
        (env, Bind var ex body)
      | If cond tbranch fbranch =>
        let '(env, cond) := annotate_action_register_history env cond in
        let '(tenv, tbranch) := annotate_action_register_history env tbranch in
        let '(fenv, fbranch) := annotate_action_register_history env fbranch in
        (merge_history_maps tenv fenv, If cond tbranch fbranch)
      | Read port idx =>
        (update_map env idx (RWRead, port),
         APos (aHistory env) (Read port idx))
      | Write port idx value =>
        let (env, value) := annotate_action_register_history env value in
        (update_map env idx (RWWrite, port),
         APos (aHistory env) (Write port idx value))
      | Unop fn arg1 =>
        let '(env, arg1) := annotate_action_register_history env arg1 in
        (env, Unop fn arg1)
      | Binop fn arg1 arg2 =>
        let '(env, arg1) := annotate_action_register_history env arg1 in
        let '(env, arg2) := annotate_action_register_history env arg2 in
        (env, Binop fn arg1 arg2)
      | ExternalCall fn arg =>
        let '(env, arg) := annotate_action_register_history env arg in
        (env, ExternalCall fn arg)
      | APos pos a =>
        let '(env, a) := annotate_action_register_history env a in
        (env, APos (aPos pos) a)
      end.

    (* LATER: this should properly handle switches *)
    Fixpoint rule_max_log_size {sig tau} (a: action sig tau) : nat :=
      match a with
      | Fail tau => 0
      | Var m => 0
      | Const cst => 0
      | Assign m ex => rule_max_log_size ex
      | Seq r1 r2 => rule_max_log_size r1 + rule_max_log_size r2
      | Bind var ex body => rule_max_log_size ex + rule_max_log_size body
      | If cond tbranch fbranch =>
        rule_max_log_size cond + max (rule_max_log_size tbranch) (rule_max_log_size fbranch)
      | Read port idx => 1
      | Write port idx value => 1
      | Unop fn arg1 => rule_max_log_size arg1
      | Binop fn arg1 arg2 => rule_max_log_size arg1 + rule_max_log_size arg2
      | ExternalCall fn arg => rule_max_log_size arg
      | APos pos a => rule_max_log_size a
      end.
  End StaticAnalysis.

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

  Fixpoint is_pure {sig tau} (a: action sig tau) :=
    match a with
    | Fail tau => false
    | Var m => true
    | Const cst => true
    | Assign m ex => false
    | Seq r1 r2 => is_pure r1 && is_pure r2
    | Bind var ex body => is_pure ex && is_pure body
    | If cond tbranch fbranch => is_pure cond && is_pure tbranch && is_pure fbranch
    | Read port idx => false
    | Write port idx value => false
    | Unop fn arg1 => is_pure arg1
    | Binop fn arg1 arg2 => is_pure arg1 && is_pure arg2
    | ExternalCall fn arg => false
    | APos pos a => is_pure a
    end.

  Fixpoint returns_zero {sig tau} (a: action sig tau) :=
    match a with
    | Fail tau => false
    | Var m => false
    | Const cst => N.eqb (Bits.to_N (bits_of_value cst)) N.zero
    | Assign m ex => false
    | Seq r1 r2 => returns_zero r2
    | Bind var ex body => returns_zero body
    | If cond tbranch fbranch => returns_zero tbranch && returns_zero fbranch
    | Read port idx => false
    | Write port idx value => false
    | Unop fn arg1 => false
    | Binop fn arg1 arg2 => false
    | ExternalCall fn arg => false
    | APos pos a => returns_zero a
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
