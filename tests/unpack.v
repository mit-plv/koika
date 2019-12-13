(*! Structure unpacking !*)
Require Import Koika.Frontend.

Inductive reg_t := Rpacked | Runpacked.
Definition ext_fn_t := empty_ext_fn_t.
Inductive rule_name_t := unpack_manual | unpack_unpack.

Definition logsz := 5.
Notation sz := (pow2 logsz).

Definition instr :=
  {| struct_name := "instr";
     struct_fields := [("src", bits_t 8);
                      ("dst", bits_t 8);
                      ("imm", bits_t 16)] |}.


Definition R r :=
  match r with
  | Rpacked => bits_t sz
  | Runpacked => struct_t instr
  end.

Definition r idx : R idx :=
  match idx with
  | Rpacked => Bits.zero
  | Runpacked => (Bits.zero, (Bits.zero, (Bits.zero, tt)))
  end.

Definition _unpack_manual : uaction reg_t ext_fn_t :=
  {{
      let packed := read0(Rpacked) in
      let unpacked := struct instr {| imm := getbits(instr, packed, imm);
                                     src := getbits(instr, packed, src);
                                     dst := getbits(instr, packed, dst) |} in
      write0(Runpacked, unpacked)
  }}.

Definition _unpack_unpack : uaction reg_t ext_fn_t :=
  {{
      let packed := read1(Rpacked) in
      let unpacked := unpack(struct_t instr, packed) in
      write1(Runpacked, unpacked)
  }}.

Definition rules :=
  tc_rules R empty_Sigma
           (fun rl => match rl with
            | unpack_manual => _unpack_manual
            | unpack_unpack => _unpack_unpack
            end).

Definition sched : scheduler :=
  tc_scheduler (unpack_manual |> unpack_unpack |> done).

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external _ := false;
                   koika_scheduler := sched;
                   koika_module_name := "unpack" |};

     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_names := empty_ext_fn_names |} |}.

Definition prog := Interop.Backends.register package.
Extraction "unpack.ml" prog.
