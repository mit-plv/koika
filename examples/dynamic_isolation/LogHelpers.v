Require Import Koika.Frontend.

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
