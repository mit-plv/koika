(*! Structure initialization !*)
Require Import Koika.Frontend.

Inductive reg_t := input (_: Vect.index 8) | output.
Definition ext_fn_t := empty_ext_fn_t.
Inductive rule_name_t := rl1 | rl2.

Definition a :=
  {| struct_name := "a";
     struct_fields := [("a0", bits_t 1);
                      ("a1", bits_t 2);
                      ("a2", bits_t 3);
                      ("a3", bits_t 4);
                      ("a4", bits_t 5);
                      ("a5", bits_t 6);
                      ("a6", bits_t 7);
                      ("a7", bits_t 8)] |}.

Definition R r :=
  match r with
  | input idx => bits_t (S (index_to_nat idx))
  | output => struct_t a
  end.

Definition r idx : R idx :=
  match idx with
  | input _ => Bits.zero
  | output => value_of_bits Bits.zero
  end.

Definition idx_of_nat (sz: nat) (n: nat) :=
  match lt_dec n sz as n return if n then Vect.index sz else unit with
  | left pr => index_of_nat_lt _ _ pr
  | _ => tt
  end.

Extraction Inline idx_of_nat.

Definition _rl1 : uaction reg_t ext_fn_t :=
  {{
      write0(output, struct a { a0 := read0(input (idx_of_nat 8 0));
                                  a1 := read0(input (idx_of_nat 8 1));
                                  a2 := read0(input (idx_of_nat 8 2));
                                  a3 := read0(input (idx_of_nat 8 3));
                                  a4 := read0(input (idx_of_nat 8 4));
                                  a5 := read0(input (idx_of_nat 8 5));
                                  a6 := read0(input (idx_of_nat 8 6));
                                  a7 := read0(input (idx_of_nat 8 7)) })
  }}.

Definition _rl2 : uaction reg_t ext_fn_t :=
  {{ write0(output, `UConst (tau := struct_t a) (value_of_bits Bits.zero)`) }}.

Definition rules :=
  tc_rules R empty_Sigma
           (fun r => match r with
                   | rl1 => _rl1
                   | rl2 => _rl2
                  end).

Definition sched : scheduler :=
  rl1 |> rl2 |> done.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external _ := false;
                   koika_scheduler := sched;
                   koika_module_name := "struct_init" |};

     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_specs |} |}.

Definition prog := Interop.Backends.register package.
Extraction "struct_init.ml" prog.
