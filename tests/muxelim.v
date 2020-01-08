(*! Sanity check for mux-elimination optimization !*)
Require Import Koika.Frontend.

Inductive nested_cnt :=
  NC0 | NC1 | NC2 | NC3 | NC4 | NC5 | NC6.
Inductive redundant_cnt :=
  RC0 | RC1.
Inductive reg_t :=
| rc_nested (v: nested_cnt)
| rc_redundant (c: redundant_cnt)
| rc_bitwise
| rdata_nested
| rdata_redundant
| rdata_bitwise.
Inductive rule_name_t := rl_nested | rl_redundant | rl_bitwise.

Definition R reg : type :=
  match reg with
  | rc_nested _ => bits_t 1
  | rc_redundant _ => bits_t 1
  | rc_bitwise => bits_t 3
  | rdata_nested => bits_t 8
  | rdata_redundant => bits_t 8
  | rdata_bitwise => bits_t 8
  end.

Definition r reg : R reg :=
  match reg with
  | rc_nested _ => Bits.zero
  | rc_redundant _ => Bits.zero
  | rc_bitwise => Bits.zero
  | rdata_nested => Bits.zero
  | rdata_redundant => Bits.zero
  | rdata_bitwise => Bits.zero
  end.

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | rl_nested =>
    {{ if read0(rc_nested NC0) then
         if read0(rc_nested NC1) then
           if read0(rc_nested NC2) then pass
           else if read0(rc_nested NC3) then
                  if read0(rc_nested NC4) then pass
                  else if read0(rc_nested NC5) then
                         if read0(rc_nested NC6) then
                           write0(rdata_nested, |8`d24|)
                         else pass
                       else pass
                else pass
         else pass
       else pass }}
  | rl_redundant =>
    {{ if read0(rc_redundant RC0) then
         if read0(rc_redundant RC1) then
           write1(rdata_redundant, |8`d42|)
         else pass
       else pass }}
  | rl_bitwise =>
    {{ match read0(rc_bitwise) with
       | Ob~0~1~0 => write0(rdata_bitwise, |8`d0|)
       | Ob~1~0~0 => write0(rdata_bitwise, |8`d1|)
       | Ob~1~1~0 => write0(rdata_bitwise, |8`d2|)
       | Ob~1~1~1 => write0(rdata_bitwise, |8`d3|)
       | Ob~0~0~0 => write0(rdata_bitwise, |8`d4|)
       return default: fail
       end }}
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  tc_scheduler (rl_nested |> rl_redundant |> rl_bitwise |> done).

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
                   koika_module_name := "muxelim" |};

     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_names := empty_ext_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "muxelim.ml" prog.
