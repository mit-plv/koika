(*! Sanity check for mux-elimination optimization !*)
Require Import Koika.Frontend.

Inductive cnt := C0 | C1 | C2 | C3 | C4 | C5 | C6.
Inductive reg_t := rc1 (v: cnt) | rc3 | rdata1 | rdata3.
Inductive rule_name_t := rl1 | rl3.

Definition R reg : type :=
  match reg with
  | rc1 _ => bits_t 1
  | rc3 => bits_t 3
  | rdata1 => bits_t 8
  | rdata3 => bits_t 8
  end.

Definition r reg : R reg :=
  match reg with
  | rc1 _ => Bits.zero
  | rc3 => Bits.zero
  | rdata1 => Bits.zero
  | rdata3 => Bits.zero
  end.

Definition urules rl : uaction reg_t empty_ext_fn_t :=
  match rl with
  | rl1 => {{ if read0(rc1 C0) then
               if read0(rc1 C1) then
                 if read0(rc1 C2) then pass
                 else if read0(rc1 C3) then
                        if read0(rc1 C4) then pass
                        else if read0(rc1 C5) then
                               if read0(rc1 C6) then
                                 write0(rdata1, |8`d42|)
                               else pass
                             else pass
                      else pass
               else pass
             else pass }}
  | rl3 => {{ match read0(rc3) with
             | Ob~0~1~0 => write0(rdata3, |8`d0|)
             | Ob~1~0~0 => write0(rdata3, |8`d1|)
             | Ob~1~1~0 => write0(rdata3, |8`d2|)
             | Ob~1~1~1 => write0(rdata3, |8`d3|)
             | Ob~0~0~0 => write0(rdata3, |8`d4|)
             return default: fail
             end }}
  end.

Definition rules :=
  tc_rules R empty_Sigma urules.

Definition sched : scheduler :=
  tc_scheduler (rl1 |> rl3 |> done).

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
