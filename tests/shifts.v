(*! Regression test for signed shifts !*)
Require Import Koika.Frontend.

Inductive idx := r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | r16.
Inductive reg_t := cond | r_l (_: idx) | r_r (_: idx) | r_out (_: idx).

Inductive rule_name_t := rl.

Definition R (reg: reg_t) : type :=
  match reg with
  | cond => bits_t 1
  | _ => bits_t 32
  end.

Definition r (reg: reg_t) : R reg :=
  match reg with
  | cond => Ob~1
  | r_l r3 => Ob~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  | r_r r3 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
  | r_l r4 => Ob~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  | r_r r4 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1
  | r_l r5 => Ob~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  | r_r r5 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0
  | r_l r6 => Ob~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
  | r_r r6 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1
  | r_l r7 => Ob~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
  | r_r r7 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  | r_l r8 => Ob~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
  | r_r r8 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
  | r_l r9 => Ob~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
  | r_r r9 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1
  | r_l r10 => Ob~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
  | r_r r10 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0
  | r_l r11 => Ob~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
  | r_r r11 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1
  | r_l r12 => Ob~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1
  | r_r r12 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
  | r_l r13 => Ob~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1
  | r_r r13 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
  | r_l r14 => Ob~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1
  | r_r r14 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1
  | r_l r15 => Ob~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1
  | r_r r15 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0
  | r_l r16 => Ob~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1
  | r_r r16 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1
  | r_out _ => Bits.zero
  end.

Definition urules (rl: rule_name_t) : uaction reg_t empty_ext_fn_t :=
  {{
      write0(r_out r3, if read0(cond)
                       then (read0(r_l r3) >>> read0(r_r r3)) >>> read0(r_r r3)
                       else (read0(r_l r3) >> read0(r_r r3)) >> read0(r_r r3));
      (* Ob~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 *)

      write0(r_out r4, if read0(cond)
                       then (read0(r_l r4) >>> read0(r_r r4)) >>> read0(r_r r4)
                       else (read0(r_l r4) >> read0(r_r r4)) >> read0(r_r r4));
      (* Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 *)

      write0(r_out r5, if read0(cond)
                       then (read0(r_l r5) >>> read0(r_r r5)) >>> read0(r_r r5)
                       else (read0(r_l r5) >> read0(r_r r5)) >> read0(r_r r5));
      (* Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0 *)

      write0(r_out r6, if read0(cond)
                       then (read0(r_l r6) >>> read0(r_r r6)) >>> read0(r_r r6)
                       else (read0(r_l r6) >> read0(r_r r6)) >> read0(r_r r6));
      (* Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1 *)

      write0(r_out r7, if read0(cond)
                       then (read0(r_l r7) >>> read0(r_r r7)) >>> read0(r_r r7)
                       else (read0(r_l r7) >> read0(r_r r7)) >> read0(r_r r7));
      (* Ob~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1 *)

      write0(r_out r8, if read0(cond)
                       then (read0(r_l r8) >>> read0(r_r r8)) >>> read0(r_r r8)
                       else (read0(r_l r8) >> read0(r_r r8)) >> read0(r_r r8));
      (* Ob~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1 *)

      write0(r_out r9, if read0(cond)
                       then (read0(r_l r9) >>> read0(r_r r9)) >>> read0(r_r r9)
                       else (read0(r_l r9) >> read0(r_r r9)) >> read0(r_r r9));
      (* Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1 *)

      write0(r_out r10, if read0(cond)
                        then (read0(r_l r10) >>> read0(r_r r10)) >>> read0(r_r r10)
                        else (read0(r_l r10) >> read0(r_r r10)) >> read0(r_r r10));
      (* Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1 *)

      write0(r_out r11, if read0(cond)
                        then (read0(r_l r11) >>> read0(r_r r11)) >>> read0(r_r r11)
                        else (read0(r_l r11) >> read0(r_r r11)) >> read0(r_r r11));
      (* Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 *)

      write0(r_out r12, if read0(cond)
                        then (read0(r_l r12) >>> read0(r_r r12)) >>> read0(r_r r12)
                        else (read0(r_l r12) >> read0(r_r r12)) >> read0(r_r r12));
      (* Ob~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1 *)

      write0(r_out r13, if read0(cond)
                        then (read0(r_l r13) >>> read0(r_r r13)) >>> read0(r_r r13)
                        else (read0(r_l r13) >> read0(r_r r13)) >> read0(r_r r13));
      (* Ob~1~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0 *)

      write0(r_out r14, if read0(cond)
                        then (read0(r_l r14) >>> read0(r_r r14)) >>> read0(r_r r14)
                        else (read0(r_l r14) >> read0(r_r r14)) >> read0(r_r r14));
      (* Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0~0~0~0~1~1~0~0~0~0~0~0~1~1~0 *)

      write0(r_out r15, if read0(cond)
                        then (read0(r_l r15) >>> read0(r_r r15)) >>> read0(r_r r15)
                        else (read0(r_l r15) >> read0(r_r r15)) >> read0(r_r r15));
      (* Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~0~0 *)

      write0(r_out r16, if read0(cond)
                        then (read0(r_l r16) >>> read0(r_r r16)) >>> read0(r_r r16)
                        else (read0(r_l r16) >> read0(r_r r16)) >> read0(r_r r16));
      (* Ob~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1 *)

      write0(cond, !read0(cond))
  }}.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  rl |> done.

Definition sched_result :=
  tc_compute (interp_scheduler (ContextEnv.(create) r) empty_sigma rules sched).

Definition external (r: rule_name_t) := false.

Definition sched_circuits :=
  compile_scheduler rules external sched.

Definition sched_circuits_result :=
  tc_compute (interp_circuits (ContextEnv.(create) r) empty_sigma sched_circuits).

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := sched;
                   koika_module_name := "shifts" |};

     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_specs |} |}.

Definition prog := Interop.Backends.register package.
Extraction "shifts.ml" prog.
