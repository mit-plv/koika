(*! Make sure that the large writeset heuristics in the scheduler don't break things !*)
Require Import Koika.Frontend.

Definition N := 10.
Inductive reg_t := data (idx: Vect.index N).
Inductive rule_name_t := wr_butlast | wr_last.

Definition reg_of_nat n :=
  data (match index_of_nat N n with
        | Some n => n
        | None => thisone
        end).

Definition R (reg: reg_t) : type :=
  bits_t 2.

Definition r (reg: reg_t) : R reg :=
  Ob~0~0.

Fixpoint _wr_butlast n : uaction reg_t empty_ext_fn_t :=
  match n with
  | 0 => {{ pass }}
  | S n => {{ write0(reg_of_nat n, |2`d1| + read0(reg_of_nat n)); `_wr_butlast n` }}
  end.

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | wr_butlast => _wr_butlast (pred N)
  | wr_last => {{ write1(data (largest_index (pred N)), read1(reg_of_nat 0)) }}
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  wr_butlast |> wr_last |> done.

Definition r0 :=
  tc_compute (ContextEnv.(create) r).

Definition first_cycle :=
  tc_compute (interp_scheduler r0 empty_sigma rules sched).

Definition r1 :=
  tc_compute (commit_update r0 first_cycle).

Definition second_cycle :=
  tc_compute (interp_scheduler r1 empty_sigma rules sched).

(* The value of the last register should be 1 *)

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external _ := false;
                   koika_scheduler := sched;
                   koika_module_name := "large_writeset" |};

     ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                 sp_prelude := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.

Definition prog := Interop.Backends.register package.
Extraction "large_writeset.ml" prog.
