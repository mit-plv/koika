Require Import Koika.Common.
Require Import Koika.Environments.
Require Import Koika.Logs.
Require Import Koika.Syntax.
Require Import Koika.TypedSemantics.
Require Import Koika.TypedSyntax.

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
  Notation interp_rule := (interp_rule r sigma).

  Section Scheduler.
    Context (rules: rule_name_t -> rule).

    Fixpoint interp_scheduler_delta'
             (sched_log: Log)
             (acc_log: Log)
             (s: scheduler)
             {struct s} :=
      let interp_try r s1 s2 :=
          match interp_rule sched_log (rules r) with
          | Some l => interp_scheduler_delta' (log_app l sched_log) (log_app l acc_log) s1
          | None => interp_scheduler_delta' sched_log acc_log s2
          end in
      match s with
      | Done => acc_log
      | Cons r s => interp_try r s s
      | Try r s1 s2 => interp_try r s1 s2
      | SPos _ s => interp_scheduler_delta' sched_log acc_log s
      end.

    Definition interp_scheduler_delta (sched_log: Log) (s: scheduler) :=
      interp_scheduler_delta' sched_log log_empty s.

  End Scheduler.
End Interp.
