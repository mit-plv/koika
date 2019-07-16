Require Import Coq.Lists.List.
Require Export SGA.Common SGA.Environments SGA.Syntax SGA.Types.

Import ListNotations.

Section Logs.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.

  Inductive LogEntryKind :=
    LogRead | LogWrite.

  Record LogEntry :=
    LE { kind: LogEntryKind;
         port: Port;
         reg: reg_t;
         val: match kind with
              | LogRead => unit: Type
              | LogWrite => Type_of_type (R reg)
              end }.

  Definition Log := list LogEntry.
End Logs.

Arguments LogEntry: clear implicits.
Arguments Log: clear implicits.

Require Import SGA.Types.

Section Interp.
  Context {var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).
  Open Scope bool_scope.

  Notation Log := (Log reg_t R).

  Definition log_find (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.find (fun '(LE kind lvl r _) => if eq_dec reg r then f kind lvl else false) log.

  Definition log_forallb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.forallb (fun '(LE kind lvl r _) => if eq_dec reg r then f kind lvl else true) log.

  Definition may_read0 sched_log rule_log idx :=
    (log_forallb sched_log idx
                 (fun kind lvl => match kind, lvl with
                               | LogWrite, P0 => false
                               | _, _ => true
                               end)) &&
    (log_forallb (rule_log ++ sched_log) idx
                 (fun kind lvl => match kind, lvl with
                               | LogWrite, P1 => false
                               | _, _ => true
                               end)).

  Definition may_read1 sched_log idx :=
    log_forallb sched_log idx
                (fun kind lvl => match kind, lvl with
                              | LogWrite, P1 => false
                              | _, _ => true
                              end).

  Definition latest_write0' log idx :=
    log_find log idx
             (fun kind lvl => match kind, lvl with
                           | LogWrite, P0 => true
                           | _, _ => false
                           end).

  Definition log_find_value:
    forall log port reg val,
      log_find log idx f = Some {| kind := LogWrite;
                                   port := port;
                                   reg := reg;
                                   val := val |} ->
      
   
    
  
  Lemma find_some_transparent A (f: A -> bool) l x : List.find f l = Some x -> List.In x l /\ f x = true.
  Proof.
   induction l as [|a l IH]; simpl; [easy| ].
   case_eq (f a); intros Ha Eq.
   * injection Eq as ->; auto.
   * destruct (IH Eq); auto.
  Defined.

  Definition latest_write0 (log: Log) idx : option (R idx).
  Proof.
    destruct (latest_write0' log idx) as [ [ kd pt reg val ] | ] eqn:Heq.
    - unfold latest_write0', log_find in Heq.
      apply find_some_transparent in Heq.
      destruct Heq.
      destruct (eq_dec idx reg) in *; try discriminate; subst.
      destruct kd in *; try discriminate; subst.
      exact (Some val).
    - exact None.
  Defined.

  Definition may_write sched_log rule_log lvl idx :=
    match lvl with
       | P0 => log_forallb (rule_log ++ sched_log) idx
                          (fun kind lvl => match kind, lvl with
                                        | LogRead, P1 | LogWrite, _ => false
                                        | _, _ => true
                                        end)
       | P1 => log_forallb (rule_log ++ sched_log) idx
                          (fun kind lvl => match kind, lvl with
                                        | LogWrite, P1 => false
                                        | _, _ => true
                                        end)
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

    (* FXME use a context for the log instead of a plain list with a complex cast? *)
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
          Some ((LE LogRead P0 idx tt) :: rule_log, REnv.(getenv) r idx)
        else None
      | Read P1 idx =>
        if may_read1 sched_log idx then
          Some ((LE LogRead P1 idx tt) :: rule_log,
                match latest_write0 (rule_log ++ sched_log) idx with
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
    Axiom magic : forall {A}, A.

    Fixpoint interp_rule
             {sig: tsig var_t}
             (Gamma: vcontext sig)
             (sched_log: Log)
             (rule_log: Log)
             (rl: rule sig)
    : option Log :=
      match rl in Types.rule _ _ _ t return (vcontext t -> option Log) with
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
        if bits_single cond then
          interp_rule Gamma sched_log rule_log tbranch
        else
          interp_rule Gamma sched_log rule_log fbranch
      | Write lvl idx val =>
        fun Gamma =>
          let/opt2 rule_log, val := interp_expr Gamma sched_log rule_log val in
          if may_write sched_log rule_log lvl idx then
            Some ((LE LogWrite lvl idx (REnv.(getenv) r idx)) :: rule_log)
          else None
      end Gamma.
  End Rule.

  Section Scheduler.
    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      match s with
      | Done => Some sched_log
      | Try r s1 s2 =>
        match interp_rule CtxEmpty sched_log [] r with
        | Some l => interp_scheduler' (l ++ sched_log) s1
        | CannotRun => interp_scheduler' sched_log s2
        end
      end.

    Definition interp_scheduler (s: scheduler) :=
      interp_scheduler' [] s.
  End Scheduler.
End Interp.
