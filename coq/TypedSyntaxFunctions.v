(*! Tools | Functions defined on typed ASTs !*)
Require Import Koika.Member Koika.TypedSyntax Koika.Primitives Koika.TypedSemantics.

Section TypedSyntaxFunctions.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}
          {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv : Env reg_t}.

  Notation rule := (rule pos_t var_t fn_name_t R Sigma).
  Notation action := (action pos_t var_t fn_name_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Fixpoint scheduler_rules (s: scheduler) :=
    match s with
    | Done => []
    | Cons r s => r :: scheduler_rules s
    | Try r s1 s2 => r :: scheduler_rules s1 ++ scheduler_rules s2
    | SPos _ s => scheduler_rules s
    end.

  Fixpoint unannot {sig tau} (a: action sig tau) :=
    match a in TypedSyntax.action _ _ _ _ _ sig tau return action sig tau with
    | APos _ a => unannot a
    | a => a
    end.

  Inductive TRW := TRWRead | TRWWrite.
  Notation event_t := (TRW * Port)%type.


  Section Footprint.
    Notation footprint_t := (list (reg_t * event_t)).

    Fixpoint action_footprint' {sig tau} (acc: footprint_t) (a: action sig tau) {struct a} :=
      match a with
      | Fail _ | Var _ | Const _ => acc
      | Assign m ex => action_footprint' acc ex
      | Seq r1 r2 => action_footprint' (action_footprint' acc r1) r2
      | Bind var ex body => action_footprint' (action_footprint' acc ex) body
      | If cond tbranch fbranch => action_footprint' (action_footprint' (action_footprint' acc cond) tbranch) fbranch
      | Read port idx => (idx, (TRWRead, port)) :: acc
      | Write port idx value => (idx, (TRWWrite, port)) :: action_footprint' acc value
      | Unop fn arg1 => action_footprint' acc arg1
      | Binop fn arg1 arg2 => action_footprint' (action_footprint' acc arg1) arg2
      | ExternalCall fn arg => action_footprint' acc arg
      | InternalCall fn args body =>
        let acc := cfoldr (fun _ _ arg acc => action_footprint' acc arg) args acc in
        action_footprint' acc body
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
                  | (TRWRead, P1) => update REnv rbr reg (fun rr => rr_add_read1 rr rl)
                  | (TRWWrite, P0) => update REnv rbr reg (fun rr => rr_add_write0 rr rl)
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
        hw0: tribool; hw1: tribool;
        hcf: tribool (* true if there are never conflicts on this register *) }.

    Definition empty_history :=
      {| hr0 := tFalse; hr1 := tFalse;
         hw0 := tFalse; hw1 := tFalse;
         hcf := tTrue |}.

    Definition unknown_history :=
      {| hr0 := tUnknown; hr1 := tUnknown;
         hw0 := tUnknown; hw1 := tUnknown;
         hcf := tFalse |}.

    Notation reg_history_map := (REnv.(env_t) (fun _ : reg_t => register_history)).
    Definition empty_history_map := REnv.(create) (fun _ => empty_history).

    Inductive register_annotation :=
    | PosAnnot (pos: pos_t)
    | HistoryAnnot (rh: reg_history_map).

    Notation annotated_action sig tau :=
      (TypedSyntax.action register_annotation var_t fn_name_t R Sigma sig tau).

    Definition join_tribools t1 t2 :=
      match t1, t2 with
      | tTrue, tTrue => tTrue
      | tFalse, tFalse => tFalse
      | _, _ => tUnknown
      end.

    Definition join_histories h1 h2 :=
      let '{| hr0 := hr0; hr1 := hr1; hw0 := hw0; hw1 := hw1; hcf := hcf |} := h1 in
      let '{| hr0 := hr0'; hr1 := hr1'; hw0 := hw0'; hw1 := hw1'; hcf := hcf' |} := h2 in
      {| hr0 := join_tribools hr0 hr0';
         hr1 := join_tribools hr1 hr1';
         hw0 := join_tribools hw0 hw0';
         hw1 := join_tribools hw1 hw1';
         hcf := join_tribools hcf hcf' |}.

    Definition join_history_maps m1 m2 :=
      Environments.map2 REnv (fun _ h1 h2 => join_histories h1 h2) m1 m2.

    Definition tandb t1 t2 :=
      match t1, t2 with
      | tFalse, _ | _, tFalse => tFalse
      | tTrue, tTrue => tTrue
      | _, _ => tUnknown
      end.

    Definition tnegb t :=
      match t with
      | tFalse => tTrue
      | tTrue => tFalse
      | tUnknown => tUnknown
      end.

    Infix "&&" := tandb.
    Notation "! a" := (tnegb a) (at level 35).

    Definition update_cf l evt :=
      match evt with
      | (TRWRead, P0)
      | (TRWRead, P1) => tTrue
      | (TRWWrite, P0) => !l.(hr1) && !l.(hw0) && !l.(hw1)
      | (TRWWrite, P1) => !l.(hw1)
      end.

    Definition update_history l (evt: event_t) :=
      let hcf := l.(hcf) && update_cf l evt in
      match evt with
      | (TRWRead, P0)  => {| hr0 := tTrue; hr1 := l.(hr1); hw0 := l.(hw0); hw1 := l.(hw1); hcf := hcf |}
      | (TRWRead, P1)  => {| hr0 := l.(hr0); hr1 := tTrue; hw0 := l.(hw0); hw1 := l.(hw1); hcf := hcf |}
      | (TRWWrite, P0) => {| hr0 := l.(hr0); hr1 := l.(hr1); hw0 := tTrue; hw1 := l.(hw1); hcf := hcf |}
      | (TRWWrite, P1) => {| hr0 := l.(hr0); hr1 := l.(hr1); hw0 := l.(hw0); hw1 := tTrue; hcf := hcf |}
      end.

    Definition update_map lenv reg (evt: event_t) :=
      Environments.update REnv lenv reg (fun l => update_history l evt).

    Fixpoint annotate_action_register_histories
             {sig tau} (env: reg_history_map)
             (a: action sig tau)
      : reg_history_map * annotated_action sig tau :=
      match a with
      | Fail tau =>
        (env, APos (HistoryAnnot env) (Fail tau))
      | Var m => (env, Var m)
      | Const cst => (env, Const cst)
      | Assign m ex =>
        let '(env, ex) := annotate_action_register_histories env ex in
        (env, Assign m ex)
      | Seq r1 r2 =>
        let '(env, r1) := annotate_action_register_histories env r1 in
        let '(env, r2) := annotate_action_register_histories env r2 in
        (env, Seq r1 r2)
      | Bind var ex body =>
        let '(env, ex) := annotate_action_register_histories env ex in
        let '(env, body) := annotate_action_register_histories env body in
        (env, Bind var ex body)
      | If cond tbranch fbranch =>
        let '(env, cond) := annotate_action_register_histories env cond in
        let '(tenv, tbranch) := annotate_action_register_histories env tbranch in
        let '(fenv, fbranch) := annotate_action_register_histories env fbranch in
        (join_history_maps tenv fenv, If cond tbranch fbranch)
      | Read port idx =>
        (update_map env idx (TRWRead, port),
         APos (HistoryAnnot env) (Read port idx))
      | Write port idx value =>
        let (env, value) := annotate_action_register_histories env value in
        (update_map env idx (TRWWrite, port),
         APos (HistoryAnnot env) (Write port idx value))
      | Unop fn arg1 =>
        let '(env, arg1) := annotate_action_register_histories env arg1 in
        (env, Unop fn arg1)
      | Binop fn arg1 arg2 =>
        let '(env, arg1) := annotate_action_register_histories env arg1 in
        let '(env, arg2) := annotate_action_register_histories env arg2 in
        (env, Binop fn arg1 arg2)
      | ExternalCall fn arg =>
        let '(env, arg) := annotate_action_register_histories env arg in
        (env, ExternalCall fn arg)
      | InternalCall fn args body =>
        let '(env, args) :=
            cfoldr (fun sg k arg cont =>
                      fun env =>
                        let '(env, arg) := annotate_action_register_histories env arg in
                        let '(env, args) := cont env in
                        (env, CtxCons k arg args)) args
                   (fun env => (env, CtxEmpty)) env in
        let '(env, body) := annotate_action_register_histories env body in
        (env, InternalCall fn args body)
      | APos pos a =>
        let '(env, a) := annotate_action_register_histories env a in
        (env, APos (PosAnnot pos) a)
      end.

    Definition annotate_rule_register_histories (a: action [] unit_t) :=
      annotate_action_register_histories empty_history_map a.

    Definition torb t1 t2 :=
      match t1, t2 with
      | tTrue, _ | _, tTrue => tTrue
      | tFalse, tFalse => tFalse
      | _, _ => tUnknown
      end.

    Definition timplb t1 t2 :=
      torb (tnegb t1) t2.

    Infix "||" := torb.
    Infix "=>>" := timplb (at level 99).

    Definition append_tribools t1 t2 :=
      join_tribools t1 (t1 || t2).

    (* L is the accumulated log, l is the rule-only log; this is like willFire_of_canFire *)
    Definition append_cf L l :=
      tTrue
        && (l.(hr0) =>> !L.(hw0) && !L.(hw1))
        && (l.(hw0) =>> !L.(hr1) && !L.(hw0) && !L.(hw1))
        && (l.(hr1) =>> !L.(hw1))
        && (l.(hw1) =>> !L.(hw1)).

    Definition append_histories h1 h2 :=
      let '{| hr0 := hr0; hr1 := hr1; hw0 := hw0; hw1 := hw1; hcf := hcf |} := h1 in
      let '{| hr0 := hr0'; hr1 := hr1'; hw0 := hw0'; hw1 := hw1'; hcf := hcf' |} := h2 in
      {| hr0 := append_tribools hr0 hr0';
         hr1 := append_tribools hr1 hr1';
         hw0 := append_tribools hw0 hw0';
         hw1 := append_tribools hw1 hw1';
         hcf := hcf && hcf' && append_cf h1 h2 |}.

    Definition append_history_maps m1 m2 :=
      Environments.map2 REnv (fun _ h1 h2 => append_histories h1 h2) m1 m2.

    Fixpoint compute_scheduler_register_histories'
             (hists: rule_name_t -> reg_history_map)
             (sched_env: reg_history_map)
             (s: scheduler) : reg_history_map :=
      match s with
      | Done => sched_env
      | Cons r s =>
        let sched_env := append_history_maps sched_env (hists r) in
        compute_scheduler_register_histories' hists sched_env s
      | Try r s1 s2 =>
        let sched_env := append_history_maps sched_env (hists r) in
        join_history_maps (compute_scheduler_register_histories' hists sched_env s1)
                          (compute_scheduler_register_histories' hists sched_env s2)
      | SPos pos s => compute_scheduler_register_histories' hists sched_env s
      end.

    Definition compute_scheduler_register_histories
             (hists: rule_name_t -> reg_history_map)
             (s: scheduler) : reg_history_map :=
      compute_scheduler_register_histories' hists empty_history_map s.

    Section Classification.
      Inductive register_kind := Value | Wire | Register | EHR.

      Notation reg_kind_map := (REnv.(env_t) (fun _ : reg_t => register_kind)).

      Definition compute_register_kind (history: register_history) :=
        match history with
        | {| hcf := tTrue |} => Value
        | {| hr1 := tFalse; hw1 := tFalse |} => Register
        | {| hr0 := tFalse; hw1 := tFalse |} => Wire
        | _ => EHR
        end.

      Definition classify_registers (histories: reg_history_map) : reg_kind_map :=
        Environments.map REnv (fun _ history => compute_register_kind history) histories.
    End Classification.

    Section Interface.
      Context (RLEnv: Env rule_name_t).
      Context (rules: rule_name_t -> rule).
      Context (s: scheduler).

      Definition annotated_rule :=
        TypedSyntax.action register_annotation var_t fn_name_t R Sigma [] unit_t.

      Definition compute_register_histories
        : RLEnv.(env_t) (fun _ => reg_history_map) *
          RLEnv.(env_t) (fun _ => annotated_rule) *
          REnv.(env_t) (fun _ => register_kind) :=
        let rule_env := RLEnv.(create) (fun rl => annotate_rule_register_histories (rules rl)) in
        let (reg_histories_per_rule, annotated_rules) :=
            unzip RLEnv rule_env in
        let reg_histories :=
            compute_scheduler_register_histories (RLEnv.(getenv) reg_histories_per_rule) s in
        let classified_registers := classify_registers reg_histories in
        ((reg_histories_per_rule, annotated_rules), classified_registers).

      Definition may_fail_without_revert (histories: reg_history_map) :=
        let ok h :=
            match h with
            | {| hr1 := tFalse; hw0 := tFalse; hw1 := tFalse |}
            | {| hw0 := tFalse; hw1 := tFalse; hcf := tTrue |} => true
            | _ => false
            end in
        Environments.fold_right REnv (fun _ rh acc => andb (ok rh) acc) histories true.
    End Interface.

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
      | InternalCall fn args body =>
        cfoldl (fun k arg acc => acc + rule_max_log_size arg) args 0
        + rule_max_log_size body
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
      | InternalCall fn args body =>
        cfoldl (fun k arg acc => acc || existsb_subterm f arg) args false
        || existsb_subterm f body
      | APos _ a => existsb_subterm f a
      end.

  Fixpoint member_mentions_shadowed_binding
           {K V} {EQ: EqDec K} {sig: list (K * V)} {k v} (m: member (k, v) sig) : bool :=
    match m return bool with
    | MemberHd k _ => false
    | MemberTl (k, _) (k', _) sig' m' => beq_dec k k' || member_mentions_shadowed_binding m'
    end.

  Definition action_mentions_shadowed_var {EQ: EqDec var_t} {sig tau} (a: action sig tau) :=
    existsb_subterm (fun a => match a with
                           | AnyAction (Var m) => member_mentions_shadowed_binding m
                           | _ => false
                           end) a.

  Definition action_mentions_var {EQ: EqDec var_t} {sig tau} (k: var_t) (a: action sig tau) :=
    existsb_subterm (fun a => match a with
                           | AnyAction (@Var _ _ _ _ _ _ _ _ k' _ m) => beq_dec k k'
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
    | InternalCall fn args body =>
      cfoldr (fun _ k arg acc => acc && is_pure arg) args true
      && is_pure body
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
    | InternalCall fn args body => returns_zero body
    | APos pos a => returns_zero a
    end.

  Definition action_type {sig tau} (a: action sig tau) : option type :=
    match a with
    | @Fail _ _ _ _ _ _ _ _ tau => Some tau
    | @Var _ _ _ _ _ _ _ _ _ tau _ => Some tau
    | @Const _ _ _ _ _ _ _ _ tau cst => Some tau
    | @Assign _ _ _ _ _ _ _ _ _ _ _ _ => Some unit_t
    | @Seq _ _ _ _ _ _ _ _ tau _ _ => Some tau
    | @Bind _ _ _ _ _ _ _ _ _ tau' _ _ _ => Some tau'
    | @If _ _ _ _ _ _ _ _ tau _ _ _ => Some tau
    | @Read _ _ _ _ _ _ _ _ _ _ => None
    | @Write _ _ _ _ _ _ _ _ _ _ _ => Some unit_t
    | @Unop _ _ _ _ _ _ _ _ fn _ => Some (PrimSignatures.Sigma1 fn).(retSig)
    | @Binop _ _ _ _ _ _ _ _ fn _ _ => Some (PrimSignatures.Sigma2 fn).(retSig)
    | @ExternalCall _ _ _ _ _ _ _ _ _ _ => None
    | @InternalCall _ _ _ _ _ _ _ _ tau _ _ _ _ => Some tau
    | @APos _ _ _ _ _ _ _ _ tau _ _ => Some tau
    end.

  Definition is_tt {sig tau} (a: action sig tau) :=
    beq_dec (action_type a) (Some unit_t) && is_pure a.

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
    | InternalCall fn args body => None
    | APos pos a => interp_arithmetic a
    end.

  Fixpoint action_size {sig tau}
           (a: TypedSyntax.action pos_t var_t fn_name_t R Sigma sig tau) :=
    (1 + match a with
         | Assign v ex =>
           action_size ex
         | Seq a1 a2 =>
           action_size a1 + action_size a2
         | Bind v ex body =>
           action_size ex + action_size body
         | If cond tbranch fbranch =>
           action_size cond + action_size tbranch + action_size fbranch
         | Write port idx value =>
           action_size value
         | Unop ufn1 arg1 =>
           action_size arg1
         | Binop ufn2 arg1 arg2 =>
           action_size arg1 + action_size arg2
         | ExternalCall ufn arg =>
           action_size arg
         | InternalCall fn argspec body =>
           cfoldl (fun _ arg acc => acc + action_size arg) argspec (action_size body)
         | APos p e => action_size e
         | _ => 0
         end)%N.

  Record rd1_wr1_acc_t :=
    { acc_wr1: REnv.(env_t) (fun _ => bool);
      acc_conflicts: REnv.(env_t) (fun _ => bool) }.

  Definition join_rd1_wr1_env_t (e1 e2: REnv.(env_t) (fun _ => bool)) :=
    Environments.map2 REnv (fun r b1 b2 => b1 || b2) e1 e2.

  Fixpoint find_read1s_after_write1s' {sig tau} (acc: rd1_wr1_acc_t) (a: action sig tau) {struct a} :=
      match a with
      | Fail _ | Var _ | Const _ | Read P0 _ | Write P0 _ _ => acc
      | Assign m ex => find_read1s_after_write1s' acc ex
      | Seq r1 r2 => find_read1s_after_write1s' (find_read1s_after_write1s' acc r1) r2
      | Bind var ex body => find_read1s_after_write1s' (find_read1s_after_write1s' acc ex) body
      | If cond tbranch fbranch =>
        let acc := find_read1s_after_write1s' acc cond in
        let tacc := find_read1s_after_write1s' acc tbranch in
        let facc := find_read1s_after_write1s' acc fbranch in
        {| acc_wr1 := join_rd1_wr1_env_t tacc.(acc_wr1) facc.(acc_wr1);
           acc_conflicts := join_rd1_wr1_env_t tacc.(acc_conflicts) facc.(acc_conflicts) |}
      | Read P1 idx =>
        {| acc_wr1 := acc.(acc_wr1);
           acc_conflicts :=
             REnv.(putenv) acc.(acc_conflicts) idx
                           (REnv.(getenv) acc.(acc_conflicts) idx ||
                            REnv.(getenv) acc.(acc_wr1) idx) |}
      | Write P1 idx value =>
        {| acc_wr1 := REnv.(putenv) acc.(acc_wr1) idx true;
           acc_conflicts := acc.(acc_conflicts) |}
      | Unop fn arg1 =>
        find_read1s_after_write1s' acc arg1
      | Binop fn arg1 arg2 =>
        let acc := find_read1s_after_write1s' acc arg1 in
        find_read1s_after_write1s' acc arg2
      | ExternalCall fn arg =>
        find_read1s_after_write1s' acc arg
      | InternalCall fn args body =>
        let acc := cfoldr (fun _ _ arg acc => find_read1s_after_write1s' acc arg) args acc in
        find_read1s_after_write1s' acc body
      | APos _ a => find_read1s_after_write1s' acc a
      end.

  Definition find_read1s_after_write1s {sig tau} (a: action sig tau) :=
    let acc := find_read1s_after_write1s'
                {| acc_wr1 := REnv.(create) (fun _ => false);
                   acc_conflicts := REnv.(create) (fun _ => false) |} a in
    Environments.fold_right REnv
      (fun r (conflicted: bool) acc => if conflicted then r :: acc else acc)
      acc.(acc_conflicts) [].
End TypedSyntaxFunctions.
