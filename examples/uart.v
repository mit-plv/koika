(*! UART transmitter !*)
Require Import Koika.Frontend.
Require Import Koika.Std.

Module UART.
  Definition CLOCK_SPEED := 25_000_000%N.
  Definition BAUD_RATE := 115200%N.
  Definition _CLOCK_SCALE := (CLOCK_SPEED / BAUD_RATE)%N.
  Definition CLOCK_DELAY_BITS := N.to_nat (N.log2_up _CLOCK_SCALE).
  Definition CLOCK_DELAY := Bits.of_N CLOCK_DELAY_BITS (_CLOCK_SCALE - 1).

  Inductive reg_t :=
  | state
  | in_byte
  | in_byte_offset
  | out_bit
  | delay
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
    | in_byte => bits_t 8
    | in_byte_offset => bits_t 3
    | out_bit => bits_t 1
    | delay => bits_t CLOCK_DELAY_BITS
    | last_write_ack => bits_t 1
    end.

  Definition r idx : R idx :=
    match idx with
    | state => Ob~0~0
    | in_byte => Bits.zero
    | in_byte_offset => Bits.zero
    | out_bit => Ob~1
    | delay => Bits.zero
    | last_write_ack => Bits.zero
    end.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_read_byte => {$ bits_t 1 ~> maybe (bits_t 8) $}
    | ext_write_bit => {$ bits_t 1 ~> bits_t 1 $}
    end.

  Definition _read_input : uaction reg_t ext_fn_t :=
    {{
        let ready := read1(state) == enum tx_state { idle } in
        let opt_byte := extcall ext_read_byte(ready) in
        (when ready && get(opt_byte, valid) do
           write1(in_byte, get(opt_byte, data));
           write1(state, enum tx_state { start }))
    }}.

  Definition _transmit : uaction reg_t ext_fn_t :=
    {{
        let bit := read0(out_bit) in
        let state := read0(state) in
        (if read0(delay) == |CLOCK_DELAY_BITS`d0| then
          match state with
          | enum tx_state { start } =>
            (set bit := Ob~0;
             set state := enum tx_state { tx })
          | enum tx_state { tx } =>
            let bits := read0(in_byte) in
            let offset := read0(in_byte_offset) in
            let last_char := offset == Ob~1~1~1 in
            set bit := bits[Ob~0~0~0];
            write0(in_byte, bits >> Ob~1);
            write0(in_byte_offset, offset + Ob~0~0~1);
            (when last_char do
               set state := enum tx_state { finish })
          | enum tx_state { finish } =>
            (set bit := Ob~1;
             set state := enum tx_state { idle })
          return default: pass
          end;
          write0(delay, #CLOCK_DELAY)
        else
          write0(delay, read0(delay) - |CLOCK_DELAY_BITS`d1|));
        write0(out_bit, bit);
        write0(state, state);
        (* last_write_ack prevents the write from being optimized out *)
        write0(last_write_ack, extcall ext_write_bit(bit))
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
    | ext_read_byte => {| efr_name := "read_byte"; efr_internal := false |}
    | ext_write_bit => {| efr_name := "write_bit"; efr_internal := false |}
    end.

  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := Sigma;
                     koika_rules := rules;
                     koika_rule_external := (fun _ => false);
                     koika_scheduler := uart;
                     koika_module_name := "uart" |};

       ip_sim := {| sp_ext_fn_specs fn := {| efs_name := show fn; efs_method := false |};
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := ext_fn_specs |} |}.
End UART.

Definition prog := Interop.Backends.register UART.package.
Extraction "uart.ml" prog.
