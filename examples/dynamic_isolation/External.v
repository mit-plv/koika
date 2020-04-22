Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import DynamicIsolation.Interfaces.

Module External <: External_sig.
  Import Common.
  Inductive memory := imem | dmem | mainmem.

  Inductive ext_fn_t' :=
  | ext_mem (m: memory)
  | ext_uart_read
  | ext_uart_write
  | ext_led.

  Definition ext_fn_t := ext_fn_t'.
  Definition led_input := maybe (bits_t 1).
  Definition uart_input := maybe (bits_t 8).
  Definition uart_output := maybe (bits_t 8).

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_mem _ => {$ struct_t mem_input ~> struct_t mem_output $}
    | ext_uart_read => {$ bits_t 1 ~> uart_output $}
    | ext_uart_write => {$ uart_input ~> bits_t 1 $}
    | ext_led => {$ led_input ~> bits_t 1 $}
    end.

  Definition ext_fn_specs (fn: ext_fn_t) :=
    match fn with
    | ext_mem imem => {| ef_name := "ext_mem_imem"; ef_internal := false |}
    | ext_mem dmem => {| ef_name := "ext_mem_dmem"; ef_internal := false |}
    | ext_mem main_mem => {| ef_name := "ext_mem_mainmem"; ef_internal := false |}
    | ext_uart_write => {| ef_name := "ext_uart_write"; ef_internal := false |}
    | ext_uart_read => {| ef_name := "ext_uart_read"; ef_internal := false |}
    | ext_led => {| ef_name := "ext_led"; ef_internal := false |}
    end.

  Instance Show_ext_fn_t : Show ext_fn_t := _.

End External.

Module EnclaveParams <: EnclaveParameters.

End EnclaveParams.
