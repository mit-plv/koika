Require Import Koika.Frontend.

Section SemanticProperties.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Lemma getenv_empty :
    forall (r: reg_t), REnv.(getenv) (log_empty (R := R)) r = [].
  Proof.
    unfold log_empty. intros; rewrite getenv_create. auto.
  Qed.

End SemanticProperties.

Hint Rewrite @getenv_empty : log_helpers.

Section LatestWrite.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Definition rew_latest_write0 {T} (log: Log R REnv) (reg: reg_t) (pf_R_equal: R reg = T) : option T :=
    rew [fun t : type => option t] pf_R_equal in latest_write0 log reg.

  Definition rew_latest_write1 {T} (log: Log R REnv) (reg: reg_t) (pf_R_equal: R reg = T) : option T :=
    rew [fun t : type => option t] pf_R_equal in latest_write1 log reg.

  Definition rew_latest_write {T} (log: Log R REnv) (reg: reg_t) (pf_R_equal: R reg = T) : option T :=
    rew [fun t : type => option t] pf_R_equal in latest_write log reg.

End LatestWrite.


Section LogEvents.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Definition observe_enq0 {T} (valid_reg: reg_t) (pf_R_valid_reg: R valid_reg = bits_t 1)
                              (data_reg: reg_t) (pf_R_data_reg: R data_reg = T)
                              (log: Log R REnv) : option T :=
      match latest_write0 log valid_reg with
      | Some b => if Bits.single (rew [fun t : type => t] pf_R_valid_reg in b)
                 then rew_latest_write0 log data_reg pf_R_data_reg
                 else None
      | None => None
      end.

  Definition observe_enq1 {T} (valid_reg: reg_t) (pf_R_valid_reg: R valid_reg = bits_t 1)
                              (data_reg: reg_t) (pf_R_data_reg: R data_reg = T)
                              (log: Log R REnv) : option T :=
      match latest_write1 log valid_reg with
      | Some b => if Bits.single (rew [fun t : type => t] pf_R_valid_reg in b)
                 then rew_latest_write1 log data_reg pf_R_data_reg
                 else None
      | None => None
      end.

End LogEvents.

Ltac unfold_fifo_obs :=
  unfold observe_enq0, observe_enq1 in *.

Hint Unfold rew_latest_write : log_helpers.
Hint Unfold rew_latest_write0 : log_helpers.
Hint Unfold rew_latest_write1 : log_helpers.


Ltac auto_with_log_helpers :=
  autounfold with log_helpers; intros; autorewrite with log_helpers; auto with log_helpers.
Ltac apply_equiv_eq := apply equiv_eq; unfold equiv.
