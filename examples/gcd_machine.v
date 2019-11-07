Require Import Koika.Frontend.
Require Import Koika.Std.

Module GcdMachine.
  Definition ext_fn_t := empty_ext_fn_t.

  Inductive reg_t := input_data |  input_valid | gcd_busy | gcd_a | gcd_b | output_data.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition pair_sig :=
  {| struct_name := "pair";
     struct_fields := ("a", bits_t 16)
                        :: ("b", bits_t 16)
                        :: nil |}.

  Definition R r :=
    match r with
    | input_data => struct_t pair_sig
    | input_valid => bits_t 1
    | gcd_busy => bits_t 1
    | gcd_a => bits_t 16
    | gcd_b => bits_t 16
    | output_data => bits_t 16
    end.

  Definition init_r idx : R idx :=
    match idx with
    | input_data => (Bits.zeroes _, (Bits.zeroes _, tt))
    | input_valid => Bits.zeroes _
    | gcd_busy => Bits.zeroes _
    | gcd_a => Bits.zeroes _
    | gcd_b => Bits.zeroes _
    | output_data => Bits.zeroes _
    end.

Definition gcd_start : uaction reg_t ext_fn_t  :=
    {{
       if (read0(input_valid) == #(Ob~1)
            && !read0(gcd_busy)) then
         let data := read0(input_data) in
         write0(gcd_a, get(data, a));
         write0(gcd_b, get(data, b));
         write0(gcd_busy, Ob~1);
         write0(input_valid, Ob~0)
       else
         fail
           }}.

  Definition sub  : UInternalFunction reg_t ext_fn_t :=
    {{
        fun (arg1 : bits_t 16) (arg2 : bits_t 16) : bits_t 16 =>
          (arg1 + !arg2 + |16`d1|)
    }} .

  Definition lt16 : UInternalFunction reg_t ext_fn_t :=
    {{
        fun (arg1 : bits_t 16) (arg2 : bits_t 16) : bits_t 1 =>
          sub(arg1, arg2)[|4`d15|]
    }}.

  Definition gcd_compute  : uaction reg_t ext_fn_t :=
    {{
       let a := read0(gcd_a) in
       let b := read0(gcd_b) in
       if !(a == |16`d0|) then
         if lt16(a, b) then
           write0(gcd_b, a);
           write0(gcd_a, b)
         else
           write0(gcd_a, sub(a,b))
       else
         fail
    }}.

    Definition gcd_getresult : uaction reg_t ext_fn_t :=
      {{
       if (read1(gcd_a) == |16`d0|)
          && read1(gcd_busy) then
         write0(gcd_busy, Ob~0);
         write0(output_data, read1(gcd_b))
       else
         fail
      }}.

  Inductive name_t := start | step_compute | get_result.

  Definition cr := ContextEnv.(create) init_r.

  Definition rules :=
    tc_rules R empty_Sigma
             (fun rl => match rl with
                     | start => gcd_start
                     | step_compute => gcd_compute
                     | get_result => gcd_getresult end).

  Definition bring : scheduler :=
    tc_scheduler (start |> step_compute |> get_result |> done).

  Definition koika_package :=
        {| koika_reg_types := R;
           koika_reg_init := init_r;
           koika_reg_finite := _;

           koika_ext_fn_types := empty_Sigma;

           koika_reg_names := show;

           koika_rules := rules;
           koika_rule_names := show;

           koika_scheduler := bring;
           koika_module_name := "externalMemory" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_var_names x := x;
                   sp_ext_fn_names := empty_fn_names;
                   sp_extfuns := None |};
       ip_verilog := {| vp_external_rules := nil;
                       vp_ext_fn_names := empty_fn_names |} |}.
End GcdMachine.
Definition prog := Interop.Backends.register GcdMachine.package.
Extraction "gcd_machine.ml" prog.
