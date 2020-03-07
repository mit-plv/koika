(*! UART transmitter !*)
Require Import Koika.Frontend.
Require Import Koika.Std.

Module UART.
  Inductive reg_t :=
  | state
  | data
  | data_offset
  | last_write_ack.

  Inductive ext_fn_t := ext_read_byte | ext_write_bit.
  Inductive rule_name_t := read_input | transmit.

  Definition tx_state :=
    {| enum_name := "tx_state";
       enum_members := ["idle"; "start"; "tx"; "finish"];
       enum_bitpatterns := [Ob~0~0; Ob~0~1; Ob~1~0; Ob~1~1] |}%vect.

  Definition R r :=
    match r with
    | state => enum_t tx_state
    | data => bits_t 8
    | data_offset => bits_t 3
    | last_write_ack => bits_t 1
    end.

  Definition r idx : R idx :=
    match idx with
    | state => Ob~0~0
    | data => Bits.zero
    | data_offset => Bits.zero
    | last_write_ack => Bits.zero
    end.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_read_byte => {$ bits_t 1 ~> maybe (bits_t 8) $}
    | ext_write_bit => {$ bits_t 1 ~> bits_t 1 $}
    end.

  Definition _read_input : uaction reg_t ext_fn_t :=
    {{
        let ready := read1(state) == enum tx_state {| idle |} in
        let opt_data := extcall ext_read_byte(ready) in
        (when ready && get(opt_data, valid) do
           write1(data, get(opt_data, data));
           write1(state, enum tx_state {| start |}))
    }}.

  Definition _transmit : uaction reg_t ext_fn_t :=
    {{
        let data := read0(data) in
        let bit := Ob~1 in
        match read0(state) with
        | enum tx_state {| start |} =>
          (set bit := Ob~0;
           write0(state, enum tx_state {| tx |}))
        | enum tx_state {| tx |} =>
          let bits := read0(data) in
          let offset := read0(data_offset) in
          let last_char := offset == Ob~1~1~1 in
          set bit := bits[Ob~0~0~0];
          write0(data, bits >> Ob~1);
          write0(data_offset, offset + Ob~0~0~1);
          when last_char do write0(state, enum tx_state {| finish |})
        | enum tx_state {| finish |} =>
          (set bit := Ob~1;
           write0(state, enum tx_state {| idle |}))
        return default: pass
        end;
        write0(last_write_ack, extcall ext_write_bit(bit)) (* write0 ensures that the call isn't optimized away *)
    }}.

  Definition uart : scheduler :=
    transmit |> read_input |> done.

  Definition cr := ContextEnv.(create) r.

  (* Typechecking  *)
  Definition rules :=
    tc_rules R Sigma
             (fun r => match r with
                    | read_input => _read_input
                    | transmit => _transmit
                    end).

  Definition ext_fn_specs (fn : ext_fn_t) :=
    match fn with
    | ext_read_byte => {| ef_name := "read_byte"; ef_internal := false |}
    | ext_write_bit => {| ef_name := "write_bit"; ef_internal := false |}
    end.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := (fun _ => false);
                     koika_scheduler := uart;
                     koika_module_name := "uart" |};

       ip_sim := {| sp_ext_fn_names := show;
                   sp_extfuns := None |};

       ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
End UART.

Definition prog := Interop.Backends.register UART.package.
Extraction "uart.ml" prog.
