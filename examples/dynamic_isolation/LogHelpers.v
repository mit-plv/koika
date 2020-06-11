Require Import Koika.Frontend.

Section LogEvents.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Definition observe_enq0 {T} (valid_reg: reg_t) (pf_R_valid_reg: R valid_reg = bits_t 1)
                              (data_reg: reg_t) (pf_R_data_reg: R data_reg = T)
                              (log: Log R REnv) : option T :=
      match latest_write0 log valid_reg with
      | Some b => if Bits.single (rew [fun t : type => t] pf_R_valid_reg in b)
                 then rew [fun t : type => option t] pf_R_data_reg in (latest_write0 log data_reg)
                 else None
      | None => None
      end.

  Definition observe_enq1 {T} (valid_reg: reg_t) (pf_R_valid_reg: R valid_reg = bits_t 1)
                              (data_reg: reg_t) (pf_R_data_reg: R data_reg = T)
                              (log: Log R REnv) : option T :=
      match latest_write1 log valid_reg with
      | Some b => if Bits.single (rew [fun t : type => t] pf_R_valid_reg in b)
                 then rew [fun t : type => option t] pf_R_data_reg in (latest_write1 log data_reg)
                 else None
      | None => None
      end.

End LogEvents.
