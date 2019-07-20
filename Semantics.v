Require Import Coq.Lists.List Coq.Bool.Bool.
Require Export SGA.Common SGA.Environments SGA.Syntax SGA.TypedSyntax.

Import ListNotations.

Section Logs.
  Inductive LogEntryKind :=
    LogRead | LogWrite.

  Record LogEntry {T} :=
    LE { kind: LogEntryKind;
         port: Port;
         val: match kind with
              | LogRead => unit: Type
              | LogWrite => T
              end }.

  Definition RLog T :=
    list (@LogEntry T).

  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.
  Definition Log := REnv.(env_t) (fun idx => RLog (R idx)).

  Definition log_empty : Log :=
    REnv.(create) (fun _ => []).

  Definition log_app (l1 l2: Log) :=
    REnv.(map2) (fun _ ll1 ll2 => ll1 ++ ll2) l1 l2.

  Fixpoint list_find_opt {A B} (f: A -> option B) (l: list A) : option B :=
    match l with
    | [] => None
    | x :: l =>
      let fx := f x in
      match fx with
      | Some y => Some y
      | None => list_find_opt f l
      end
    end.

  Lemma list_find_opt_app {A B} (f: A -> option B) (l l': list A) :
    list_find_opt f (l ++ l') =
    match list_find_opt f l with
    | Some x => Some x
    | None => list_find_opt f l'
    end.
  Proof.
    induction l; cbn; intros.
    - reflexivity.
    - rewrite IHl. destruct (f a); reflexivity.
  Qed.

  Definition log_find {T} (log: Log) reg (f: @LogEntry (R reg) -> option T) : option T :=
    list_find_opt f (REnv.(getenv) log reg).

  Lemma log_find_empty {T} idx (f: @LogEntry (R idx) -> option T):
    log_find (log_empty: Log) idx f = None.
  Proof.
    unfold log_find, log_empty; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_find_app {T} (l l': Log) reg (f: @LogEntry (R reg) -> option T) :
    log_find (log_app l l') reg f =
    match log_find l reg f with
    | Some x => Some x
    | None => log_find l' reg f
    end.
  Proof.
    unfold log_find, log_app, map2.
    rewrite getenv_create.
    rewrite list_find_opt_app.
    reflexivity.
  Qed.

  Definition log_cons (reg: reg_t) le (l: Log) :=
    REnv.(putenv) l reg (le :: REnv.(getenv) l reg).

  Lemma log_cons_eq :
    forall (log: Log) idx le,
      REnv.(getenv) (log_cons idx le log) idx = le :: REnv.(getenv) log idx.
  Proof.
    unfold log_cons; intros; rewrite get_put_eq; reflexivity.
  Qed.

  Lemma log_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      REnv.(getenv) (log_cons idx' le log) idx = REnv.(getenv) log idx.
  Proof.
    unfold log_cons; intros; rewrite get_put_neq; eauto.
  Qed.

  Lemma log_find_cons_eq {T}:
    forall (log: Log) idx le (f: _ -> option T),
      log_find (log_cons idx le log) idx f =
      match f le with
      | Some v => Some v
      | _ => log_find log idx f
      end.
  Proof.
    unfold log_find; intros;
      rewrite log_cons_eq; reflexivity.
  Qed.

  Lemma log_find_cons_neq {T}:
    forall (log: Log) idx idx' le (f: _ -> option T),
      idx <> idx' ->
      log_find (log_cons idx' le log) idx f =
      log_find log idx f.
  Proof.
    unfold log_find; intros;
      rewrite log_cons_neq by eassumption; reflexivity.
  Qed.

  Definition log_forallb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.forallb (fun '(LE _ kind prt _) => f kind prt) (REnv.(getenv) log reg).

  Definition log_existsb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.existsb (fun '(LE _ kind prt _) => f kind prt) (REnv.(getenv) log reg).

  (* FIXME move these lemmas out of the semantics *)
  Lemma log_forallb_not_existb (log: Log) reg (f: LogEntryKind -> Port -> bool) :
    negb (log_existsb log reg f) = log_forallb log reg (fun k p => negb (f k p)).
  Proof.
    unfold log_existsb, log_forallb.
    induction (getenv _ _ _); cbn.
    - reflexivity.
    - destruct a; cbn.
      rewrite negb_orb, IHy.
      reflexivity.
  Qed.

  Lemma log_existsb_log_cons_eq :
    forall (log: Log) idx k p v f,
      log_existsb (log_cons idx (LE _ k p v) log) idx f =
      f k p || log_existsb log idx f.
  Proof.
    unfold log_existsb; intros; rewrite log_cons_eq; reflexivity.
  Qed.

  Lemma log_existsb_log_cons_neq :
    forall (log: Log) idx idx' k p v f,
      idx <> idx' ->
      log_existsb (log_cons idx' (LE _ k p v) log) idx f =
      log_existsb log idx f.
  Proof.
    unfold log_existsb; intros; rewrite log_cons_neq; eauto.
  Qed.

  Lemma log_existsb_empty :
    forall idx f,
      log_existsb (log_empty: Log) idx f = false.
  Proof.
    unfold log_existsb, log_empty; intros;
      rewrite getenv_create; reflexivity.
  Qed.

  Lemma getenv_logapp:
    forall (l l': Log) idx,
      REnv.(getenv) (log_app l l') idx =
      REnv.(getenv) l idx ++ REnv.(getenv) l' idx.
  Proof.
    unfold log_app, map2; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_forallb_app:
    forall (l l': Log) reg (f: LogEntryKind -> Port -> bool),
      log_forallb (log_app l l') reg f =
      log_forallb l reg f && log_forallb l' reg f.
  Proof.
    unfold log_forallb.
    intros; rewrite getenv_logapp.
    rewrite !forallb_app; reflexivity.
  Qed.

  Lemma log_existsb_app:
    forall (l l': Log) reg (f: LogEntryKind -> Port -> bool),
      log_existsb (log_app l l') reg f =
      log_existsb l reg f || log_existsb l' reg f.
  Proof.
    unfold log_existsb, log_app; intros.
    unfold map2; rewrite getenv_create.
    rewrite existsb_app; reflexivity.
  Qed.

  Lemma log_app_assoc:
    forall (l l' l'': Log),
      log_app l (log_app l' l'') =
      log_app (log_app l l') l''.
  Proof.
    unfold log_app, map2; intros.
    apply create_funext; intros.
    rewrite !getenv_create.
    apply app_assoc.
  Qed.

  Lemma log_app_empty_l : forall (l: Log),
      log_app l log_empty = l.
  Proof.
    intros.
    apply equiv_eq.
    unfold equiv, log_app, map2, log_empty; intros.
    rewrite !getenv_create, app_nil_r.
    reflexivity.
  Qed.

  Lemma log_app_empty_r : forall (l: Log),
      log_app log_empty l = l.
  Proof.
    intros.
    apply equiv_eq.
    unfold equiv, log_app, map2, log_empty; intros.
    rewrite !getenv_create.
    reflexivity.
  Qed.
End Logs.

Arguments LE {_}.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.
Arguments Log {reg_t} R REnv.

Section Interp.
  Context {var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).
  Open Scope bool_scope.

  Notation Log := (Log R REnv).

  Definition is_read0 kind prt :=
    match kind, prt with
    | LogRead, P0 => true
    | _, _ => false
    end.

  Definition is_read1 kind prt :=
    match kind, prt with
    | LogRead, P1 => true
    | _, _ => false
    end.

  Definition is_write0 kind prt :=
    match kind, prt with
    | LogWrite, P0 => true
    | _, _ => false
    end.

  Definition is_write1 kind prt :=
    match kind, prt with
    | LogWrite, P1 => true
    | _, _ => false
    end.

  Notation negf f := (fun kind prt => negb (f kind prt)).

  Definition may_read0 (sched_log rule_log: Log) idx :=
    negb (log_existsb sched_log idx is_write0) &&
    negb (log_existsb (log_app rule_log sched_log) idx is_write1).

  Definition may_read1 (sched_log: Log) idx :=
    negb (log_existsb sched_log idx is_write1).

  Definition latest_write0 (log: Log) idx :=
    log_find log idx
             (fun le => match le with
                     | (LE LogWrite P0 v) => Some v
                     | _ => None
                     end).

  Lemma latest_write0_empty idx:
    latest_write0 (log_empty: Log) idx = None.
  Proof.
    apply log_find_empty.
  Qed.

  Lemma latest_write0_app :
    forall (sl sl': Log) idx,
      latest_write0 (log_app sl sl') idx =
      match latest_write0 sl idx with
      | Some e => Some e
      | None => latest_write0 sl' idx
      end.
  Proof.
    unfold latest_write0; eauto using log_find_app.
  Qed.

  Lemma latest_write0_cons_eq :
    forall (log: Log) idx le,
      latest_write0 (log_cons idx le log) idx =
      match le with
      | LE LogWrite P0 v => Some v
      | _ => latest_write0 log idx
      end.
  Proof.
    unfold latest_write0; intros.
    rewrite log_find_cons_eq; destruct le, kind0, port0; reflexivity.
  Qed.

  Lemma latest_write0_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      latest_write0 (log_cons idx' le log) idx =
      latest_write0 log idx.
  Proof.
    unfold latest_write0; intros.
    rewrite log_find_cons_neq by assumption; reflexivity.
  Qed.

  Definition latest_write1 (log: Log) idx :=
    log_find log idx
             (fun le => match le with
                     | (LE LogWrite P1 v) => Some v
                     | _ => None
                     end).

  Lemma latest_write1_app :
    forall (sl sl': Log) idx,
      latest_write1 (log_app sl sl') idx =
      match latest_write1 sl idx with
      | Some e => Some e
      | None => latest_write1 sl' idx
      end.
  Proof.
    unfold latest_write1; eauto using log_find_app.
  Qed.

  Lemma latest_write1_cons_eq :
    forall (log: Log) idx le,
      latest_write1 (log_cons idx le log) idx =
      match le with
      | LE LogWrite P1 v => Some v
      | _ => latest_write1 log idx
      end.
  Proof.
    unfold latest_write1; intros.
    rewrite log_find_cons_eq; destruct le, kind0, port0; reflexivity.
  Qed.

  Lemma latest_write1_cons_neq :
    forall (log: Log) idx idx' le,
      idx <> idx' ->
      latest_write1 (log_cons idx' le log) idx =
      latest_write1 log idx.
  Proof.
    unfold latest_write1; intros.
    rewrite log_find_cons_neq by assumption; reflexivity.
  Qed.

  Definition may_write (sched_log rule_log: Log) prt idx :=
    match prt with
    | P0 => negb (log_existsb (log_app rule_log sched_log) idx is_read1) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write0) &&
           negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    | P1 => negb (log_existsb (log_app rule_log sched_log) idx is_write1)
    end.

  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler var_t R Sigma).

  Definition vcontext (sig: tsig var_t) :=
    context (fun '(k, tau) => Type_of_type tau) sig.

  Section Expr.
    Context {sig: tsig var_t}.
    Context (Gamma: vcontext sig).
    Context (sched_log: Log).

    Fixpoint interp_expr {tau}
             (rule_log: Log)
             (e: expr sig tau)
      : option (Log * tau) :=
      match e with
      | Var m =>
        Some (rule_log, cassoc m Gamma)
      | Const cst => Some (rule_log, cst)
      | Read P0 idx =>
        if may_read0 sched_log rule_log idx then
          Some (log_cons idx (LE LogRead P0 tt) rule_log, REnv.(getenv) r idx)
        else None
      | Read P1 idx =>
        if may_read1 sched_log idx then
          Some (log_cons idx (LE LogRead P1 tt) rule_log,
                match latest_write0 (log_app rule_log sched_log) idx with
                | Some v => v
                | None => REnv.(getenv) r idx
                end)
        else None
      | Call fn arg1 arg2 =>
        let/opt2 rule_log, arg1 := interp_expr rule_log arg1 in
        let/opt2 rule_log, arg2 := interp_expr rule_log arg2 in
        Some (rule_log, (sigma fn) arg1 arg2)
      end.
  End Expr.

  Section Rule.
    Fixpoint interp_rule
             {sig: tsig var_t}
             (Gamma: vcontext sig)
             (sched_log: Log)
             (rule_log: Log)
             (rl: rule sig)
    : option Log :=
      match rl in TypedSyntax.rule _ _ _ t return (vcontext t -> option Log) with
      | Skip => fun _ => Some rule_log
      | Fail => fun _ => None
      | Seq r1 r2 =>
        fun Gamma =>
          let/opt rule_log := interp_rule Gamma sched_log rule_log r1 in
          interp_rule Gamma sched_log rule_log r2
      | @Bind _ _ _ _ _ _ tau var ex body =>
        fun Gamma =>
          let/opt2 rule_log, v := interp_expr Gamma sched_log rule_log ex in
          interp_rule (CtxCons (var, tau) v Gamma) sched_log rule_log body
      | If cond tbranch fbranch =>
        fun Gamma =>
        let/opt2 rule_log, cond := interp_expr Gamma sched_log rule_log cond in
        if Bits.single cond then
          interp_rule Gamma sched_log rule_log tbranch
        else
          interp_rule Gamma sched_log rule_log fbranch
      | Write prt idx val =>
        fun Gamma =>
          let/opt2 rule_log, val := interp_expr Gamma sched_log rule_log val in
          if may_write sched_log rule_log prt idx then
            Some (log_cons idx (LE LogWrite prt val) rule_log)
          else None
      end Gamma.
  End Rule.

  Section Scheduler.
    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      match s with
      | Done => sched_log
      | Try r s1 s2 =>
        match interp_rule CtxEmpty sched_log log_empty r with
        | Some l => interp_scheduler' (log_app l sched_log) s1
        | CannotRun => interp_scheduler' sched_log s2
        end
      end.

    Definition interp_scheduler (s: scheduler) :=
      interp_scheduler' log_empty s.
  End Scheduler.
End Interp.


Section EnvUpdates.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Definition rlog_latest_write_fn {k} (le: LogEntry (R k)) :=
    match le with
    | LE LogWrite _ v => Some v
    | _ => None
    end.

  Definition latest_write (log: Log R REnv) idx :=
    log_find log idx rlog_latest_write_fn.

  Definition commit_update (r0: REnv.(env_t) R) (log: Log R REnv) : REnv.(env_t) R :=
    REnv.(create) (fun k => match latest_write log k with
                         | Some v => v
                         | None => REnv.(getenv) r0 k
                         end).

  Lemma log_find_create {T}:
    forall fn idx (f: LogEntry (R idx) -> option T),
      log_find (REnv.(create) fn) idx f =
      list_find_opt f (fn idx).
  Proof.
    unfold log_find; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma commit_update_assoc:
    forall (r : REnv.(env_t) R) (l l' : Log R REnv),
      commit_update (commit_update r l) l' = commit_update r (log_app l' l).
  Proof.
    unfold commit_update, log_app, map2, latest_write, log_find; intros.
    apply create_funext; intros.
    rewrite !getenv_create.
    rewrite list_find_opt_app.
    destruct list_find_opt; reflexivity.
  Qed.

  Lemma commit_update_empty:
    forall (r : REnv.(env_t) R),
      commit_update r log_empty = r.
  Proof.
    intros; apply equiv_eq; intro.
    unfold commit_update, log_empty, latest_write, log_find; rewrite !getenv_create.
    reflexivity.
  Qed.
End EnvUpdates.

