(*! Using structures, enums, and arrays !*)
Require Import Koika.Frontend.

Inductive reg_t := input | output.
Inductive rule_name_t := decr_icmp_ttl | clear_checksum.

Definition proto :=
  {| enum_name := "protocol";
     enum_members :=
       vect_of_list ["ICMP"; "IGMP"; "TCP"; "UDP"];
     enum_bitpatterns :=
       vect_of_list [Ob~0~0~0~0~0~0~0~1; Ob~0~0~0~0~0~0~1~0; Ob~0~0~0~0~0~1~1~0; Ob~0~0~0~1~0~0~0~1] |}.

Definition flag :=
  {| enum_name := "flag";
     enum_members := vect_of_list ["set"; "unset"];
     enum_bitpatterns := vect_of_list [Ob~1; Ob~0] |}.

Definition ipv4_address :=
  {| array_len := 4;
     array_type := bits_t 8 |}.

Definition ipv4_header :=
  {| struct_name := "ipv4_header";
     struct_fields :=
       [("version", bits_t 4);
        ("ihl", bits_t 4);
        ("dscp", bits_t 6);
        ("ecn", bits_t 2);
        ("len", bits_t 16);
        ("id", bits_t 16);
        ("reserved", enum_t flag);
        ("df", enum_t flag);
        ("mf", enum_t flag);
        ("fragment_offset", bits_t 13);
        ("ttl", bits_t 8);
        ("protocol", enum_t proto);
        ("checksum", bits_t 16);
        ("src", array_t ipv4_address);
        ("dst", array_t ipv4_address)] |}.

Definition result (a: type) :=
  {| struct_name := "result";
     struct_fields := [("valid", bits_t 1); ("value", a)] |}.

Definition response := result (struct_t ipv4_header).

Definition R r :=
  match r with
  | input => bits_t (struct_sz ipv4_header)
  | output => bits_t (struct_sz response)
  end.

Infix "+b+" := Bits.app (at level 60).

Definition r reg : R reg :=
  match reg with
  | input =>
    Ob~0~1~0~0~0~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0~1~0~0 +b+
    Ob~0~1~1~1~0~1~1~0~1~0~0~0~0~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0 +b+
    Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~0~0~0~0~0~0~1~0~0~0~0~1 +b+
    Ob~0~0~0~0~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1 +b+
    Ob~0~0~0~0~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0
  | output =>
    Bits.zero
  end.

Definition _decr_icmp_ttl : uaction _ empty_ext_fn_t :=
  {{
      let hdr := unpack(struct_t ipv4_header, read0(input)) in
      let valid := Ob~1 in
      match get(hdr, protocol) with
      | enum proto {| ICMP |} =>
        let t := get(hdr, ttl) in
        if t == |8`d0| then
          set valid := Ob~0
        else
          set hdr := subst(hdr, ttl, t - |8`d1|) (* ← same as [put(hdr, ttl, t - 1)] *)
      return default: pass
      end;
      set hdr := subst(hdr, reserved, enum flag {| unset |}); (* reset the [reserved] field, just in case *)
      write0(output, pack(struct response {| valid := valid; value := hdr |}))
  }}.

Definition _clear_checksum : uaction reg_t empty_ext_fn_t :=
  {{
      let presp := read1(output) in
      let phdr := getbits(response, presp, value) in
      set phdr := substbits(ipv4_header, phdr, checksum, |16`d0|);
      write1(output, substbits(response, presp, value, phdr))
  }}.

Definition rules :=
  tc_rules R empty_Sigma
           (fun rl => match rl with
                   | decr_icmp_ttl => _decr_icmp_ttl
                   | clear_checksum => _clear_checksum
                   end).

Definition scheduler : scheduler :=
  decr_icmp_ttl |> clear_checksum |> done.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init := r;
                   koika_ext_fn_types := empty_Sigma;
                   koika_rules := rules;
                   koika_rule_external _ := false;
                   koika_scheduler := scheduler;
                   koika_module_name := "datatypes" |};

     ip_sim := {| sp_ext_fn_names := empty_ext_fn_names;
                 sp_extfuns := None |};

     ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_specs |} |}.

Definition prog := Interop.Backends.register package.
Extraction "datatypes.ml" prog.
