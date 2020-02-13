(*! Language | Semantics of typed Kôika programs !*)
Require Export Koika.Common Koika.Environments Koika.Logs Koika.Syntax Koika.TypedSyntax.

Section Interp.
  Context {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Notation Log := (Log R REnv).

  Notation rule := (rule pos_t var_t fn_name_t R Sigma).
  Notation action := (action pos_t var_t fn_name_t R Sigma).
  Notation scheduler := (scheduler pos_t rule_name_t).

  Definition tcontext (sig: tsig var_t) :=
    context (fun k_tau => type_denote (snd k_tau)) sig.

  Definition acontext (sig argspec: tsig var_t) :=
    context (fun k_tau => action sig (snd k_tau)) argspec.

  Section Action.
    Section Args.
      Context (interp_action:
                 forall {sig: tsig var_t} {tau}
                   (Gamma: tcontext sig)
                   (sched_log: Log) (action_log: Log)
                   (a: action sig tau),
                   option (Log * type_denote tau * (tcontext sig))).

      Fixpoint interp_args'
               {sig: tsig var_t}
               (Gamma: tcontext sig)
               (sched_log: Log)
               (action_log: Log)
               {argspec: tsig var_t}
               (args: acontext sig argspec)
        : option (Log * tcontext argspec * (tcontext sig)) :=
        match args with
        | CtxEmpty => Some (action_log, CtxEmpty, Gamma)
        | @CtxCons _ _ argspec k_tau arg args =>
          let/opt3 action_log, ctx, Gamma := interp_args' Gamma sched_log action_log args in
          let/opt3 action_log, v, Gamma := interp_action _ _ Gamma sched_log action_log arg in
          Some (action_log, CtxCons k_tau v ctx, Gamma)
        end.
    End Args.

    Fixpoint interp_action
             {sig: tsig var_t}
             {tau}
             (Gamma: tcontext sig)
             (sched_log: Log)
             (action_log: Log)
             (a: action sig tau)
             {struct a}
    : option (Log * tau * (tcontext sig)) :=
      match a in TypedSyntax.action _ _ _ _ _ ts tau return (tcontext ts -> option (Log * tau * (tcontext ts)))  with
      | Fail tau => fun _ =>
        None
      | Var m => fun Gamma =>
        Some (action_log, cassoc m Gamma, Gamma)
      | Const cst => fun Gamma =>
        Some (action_log, cst, Gamma)
      | Seq r1 r2 => fun Gamma =>
        let/opt3 action_log, _, Gamma := interp_action Gamma sched_log action_log r1 in
        interp_action Gamma sched_log action_log r2
      | @Assign _ _ _ _ _ _ _ _ k tau m ex => fun Gamma =>
        let/opt3 action_log, v, Gamma := interp_action Gamma sched_log action_log ex in
        Some (action_log, Ob, creplace m v Gamma)
      | @Bind _ _ _ _ _ _ _ sig tau tau' var ex body => fun (Gamma : tcontext sig) =>
        let/opt3 action_log1, v, Gamma := interp_action Gamma sched_log action_log ex in
        let/opt3 action_log2, v, Gamma := interp_action (CtxCons (var, tau) v Gamma) sched_log action_log1 body in
        Some (action_log2, v, ctl Gamma)
      | If cond tbranch fbranch => fun Gamma =>
        let/opt3 action_log, cond, Gamma := interp_action Gamma sched_log action_log cond in
        if Bits.single cond then
          interp_action Gamma sched_log action_log tbranch
        else
          interp_action Gamma sched_log action_log fbranch
      | Read prt idx => fun Gamma =>
        if may_read sched_log prt idx then
          Some (log_cons idx (LE LogRead prt tt) action_log,
                match prt with
                | P0 => REnv.(getenv) r idx
                | P1 => match latest_write0 (log_app action_log sched_log) idx with
                       | Some v => v
                       | None => REnv.(getenv) r idx
                       end
                end,
                Gamma)
        else None
      | Write prt idx val => fun Gamma =>
        let/opt3 action_log, val, Gamma_new := interp_action Gamma sched_log action_log val in
        if may_write sched_log action_log prt idx then
          Some (log_cons idx (LE LogWrite prt val) action_log, Bits.nil, Gamma_new)
        else None
      | Unop fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, (PrimSpecs.sigma1 fn) arg1, Gamma)
      | Binop fn arg1 arg2 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        let/opt3 action_log, arg2, Gamma := interp_action Gamma sched_log action_log arg2 in
        Some (action_log, (PrimSpecs.sigma2 fn) arg1 arg2, Gamma)
      | ExternalCall fn arg1 => fun Gamma =>
        let/opt3 action_log, arg1, Gamma := interp_action Gamma sched_log action_log arg1 in
        Some (action_log, sigma fn arg1, Gamma)
      | InternalCall name args body => fun Gamma =>
        let/opt3 action_log, results, Gamma := interp_args' (@interp_action) Gamma sched_log action_log args in
        let/opt3 action_log, v, _ := interp_action results sched_log action_log body in
        Some (action_log, v, Gamma)
      | APos _ a => fun Gamma =>
        interp_action Gamma sched_log action_log a
      end Gamma.

    Definition interp_rule (sched_log: Log) (rl: rule) : option Log :=
      match interp_action CtxEmpty sched_log log_empty rl with
      | Some (l, _, _) => Some l
      | None => None
      end.
  End Action.

  Section Scheduler.
    Context (rules: rule_name_t -> rule).

    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      let interp_try r s1 s2 :=
          match interp_rule sched_log (rules r) with
          | Some l => interp_scheduler' (log_app l sched_log) s1
          | None => interp_scheduler' sched_log s2
          end in
      match s with
      | Done => sched_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler' sched_log s
      end.

    Definition interp_scheduler (s: scheduler) :=
      interp_scheduler' log_empty s.
  End Scheduler.
End Interp.

Notation interp_args r sigma Gamma sched_log action_log args :=
  (interp_args' (@interp_action _ _ _ _ _ _ _ _ r sigma) Gamma sched_log action_log args).
