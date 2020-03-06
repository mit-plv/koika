(*! Computing GCDs !*)
Require Import Koika.Frontend.
Require Import Koika.Std.

Module GCDMachine.
  Definition ext_fn_t := empty_ext_fn_t.

  Inductive reg_t :=
  | input_data
  | input_valid
  | gcd_busy
  | gcd_a
  | gcd_b
  | output_data.

  Definition pair_t :=
    struct_t {| struct_name := "pair";
                struct_fields := [("a", bits_t 16); ("b", bits_t 16)] |}.

  Definition R r :=
    match r with
    | input_data => pair_t
    | input_valid => bits_t 1
    | gcd_busy => bits_t 1
    | gcd_a => bits_t 16
    | gcd_b => bits_t 16
    | output_data => bits_t 16
    end.

  Definition init_r idx : R idx :=
    match idx with
    | input_data => (Bits.zero, (Bits.zero, tt))
    | input_valid => Bits.zero
    | gcd_busy => Bits.zero
    | gcd_a => Bits.zero
    | gcd_b => Bits.zero
    | output_data => Bits.zero
    end.

  Definition gcd_start : uaction reg_t ext_fn_t :=
    {{
        if read0(input_valid) == Ob~1 && !read0(gcd_busy) then
          let data := read0(input_data) in
          write0(gcd_a, get(data, a));
          write0(gcd_b, get(data, b));
          write0(gcd_busy, Ob~1);
          write0(input_valid, Ob~0)
        else
          fail
    }}.

  Definition gcd_compute : uaction reg_t ext_fn_t :=
    {{
        let a := read0(gcd_a) in
        let b := read0(gcd_b) in
        if a != |16`d0| then
          if a < b then
            write0(gcd_b, a);
            write0(gcd_a, b)
          else
            write0(gcd_a, a - b)
        else
          fail
    }}.

  Definition gcd_get_result : uaction reg_t ext_fn_t :=
    {{
        if (read1(gcd_a) == |16`d0|) && read0(gcd_busy) then
          write0(gcd_busy, Ob~0);
          write0(output_data, read1(gcd_b))
        else
          fail
    }}.

  Inductive rule_name_t :=
    start | step_compute | get_result.

  Definition rules :=
    tc_rules R empty_Sigma
             (fun rl => match rl with
                     | start => gcd_start
                     | step_compute => gcd_compute
                     | get_result => gcd_get_result end).

  Definition bring : scheduler :=
    start |> step_compute |> get_result |> done.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := init_r;
                     koika_ext_fn_types := empty_Sigma;
                     koika_rules := rules;
                     koika_rule_external _ := false;
                     koika_scheduler := bring;
                     koika_module_name := "gcd_machine" |};

       ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                   sp_extfuns := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_specs; |} |}.
End GCDMachine.

Definition prog := Interop.Backends.register GCDMachine.package.
Extraction "gcd_machine.ml" prog.
