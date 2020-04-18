Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.
Require Import DynamicIsolation.RVEncoding.
Require Import DynamicIsolation.Scoreboard.
Require Import DynamicIsolation.Multiplier.

Require Import DynamicIsolation.External.
Require Import DynamicIsolation.Tactics.
Require Import DynamicIsolation.Interfaces.

Module Memory <: Memory_sig External.
  Import Common.

  Inductive internal_reg_t' : Type := .
  Definition internal_reg_t := internal_reg_t'.
  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with end.

  Inductive reg_t :=
  | toIMem0 (state: MemReq.reg_t)
  | toIMem1 (state: MemReq.reg_t)
  | toDMem0 (state: MemReq.reg_t)
  | toDMem1 (state: MemReq.reg_t)
  | fromIMem0 (state: MemResp.reg_t)
  | fromIMem1 (state: MemResp.reg_t)
  | fromDMem0 (state: MemResp.reg_t)
  | fromDMem1 (state: MemResp.reg_t)
  | internal (r: internal_reg_t)
  .

  Definition R (idx: reg_t) :=
    match idx with
    | toIMem0 st => MemReq.R st
    | toIMem1 st => MemReq.R st
    | toDMem0 st => MemReq.R st
    | toDMem1 st => MemReq.R st
    | fromIMem0 st => MemResp.R st
    | fromIMem1 st => MemResp.R st
    | fromDMem0 st => MemResp.R st
    | fromDMem1 st => MemResp.R st
    | internal st => R_internal st
    end.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  Definition sigma := External.sigma.


  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_LED_ADDRESS  := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.

  Import External.

  Definition memoryBus (m: memory) : UInternalFunction reg_t ext_fn_t :=
    {{ fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1) (put_request: struct_t mem_req) : struct_t mem_output =>
         `match m with
          | imem => {{ extcall (ext_mem m) (struct mem_input {|
                        get_ready := get_ready;
                        put_valid := put_valid;
                        put_request := put_request |}) }}
          | dmem => {{ let addr := get(put_request, addr) in
                      let byte_en := get(put_request, byte_en) in
                      let is_write := byte_en == Ob~1~1~1~1 in

                      let is_uart := addr == #MMIO_UART_ADDRESS in
                      let is_uart_read := is_uart && !is_write in
                      let is_uart_write := is_uart && is_write in

                      let is_led := addr == #MMIO_LED_ADDRESS in
                      let is_led_write := is_led && is_write in

                      let is_mem := !is_uart && !is_led in

                      if is_uart_write then
                        let char := get(put_request, data)[|5`d0| :+ 8] in
                        let may_run := get_ready && put_valid && is_uart_write in
                        let ready := extcall ext_uart_write (struct (Maybe (bits_t 8)) {|
                          valid := may_run; data := char |}) in
                        struct mem_output {| get_valid := may_run && ready;
                                             put_ready := may_run && ready;
                                             get_response := struct mem_resp {|
                                               byte_en := byte_en; addr := addr;
                                               data := |32`d0| |} |}

                      else if is_uart_read then
                        let may_run := get_ready && put_valid && is_uart_read in
                        let opt_char := extcall ext_uart_read (may_run) in
                        let ready := get(opt_char, valid) in
                        struct mem_output {| get_valid := may_run && ready;
                                             put_ready := may_run && ready;
                                             get_response := struct mem_resp {|
                                               byte_en := byte_en; addr := addr;
                                               data := zeroExtend(get(opt_char, data), 32) |} |}

                      else if is_led then
                        let on := get(put_request, data)[|5`d0|] in
                        let may_run := get_ready && put_valid && is_led_write in
                        let current := extcall ext_led (struct (Maybe (bits_t 1)) {|
                          valid := may_run; data := on |}) in
                        let ready := Ob~1 in
                        struct mem_output {| get_valid := may_run && ready;
                                             put_ready := may_run && ready;
                                             get_response := struct mem_resp {|
                                               byte_en := byte_en; addr := addr;
                                               data := zeroExtend(current, 32) |} |}

                      else
                        extcall (ext_mem m) (struct mem_input {|
                          get_ready := get_ready && is_mem;
                          put_valid := put_valid && is_mem;
                          put_request := put_request |})
                   }}
          end` }}.

  Definition mem (m: memory) : uaction reg_t ext_fn_t :=
    let fromMem := match m with imem => fromIMem0 | dmem => fromDMem0 end in
    let toMem := match m with imem => toIMem0 | dmem => toDMem0 end in
    {{
        let get_ready := fromMem.(MemResp.can_enq)() in
        let put_request_opt := toMem.(MemReq.peek)() in
        let put_request := get(put_request_opt, data) in
        let put_valid := get(put_request_opt, valid) in
        let mem_out := {memoryBus m}(get_ready, put_valid, put_request) in
        (when (get_ready && get(mem_out, get_valid)) do fromMem.(MemResp.enq)(get(mem_out, get_response)));
        (when (put_valid && get(mem_out, put_ready)) do ignore(toMem.(MemReq.deq)()))
    }}.

  Definition tc_imem := tc_rule R Sigma (mem imem) <: rule.
  Definition tc_dmem := tc_rule R Sigma (mem dmem) <: rule.

  Inductive rule_name_t' :=
  | Imem
  | Dmem
  .

  Definition rule_name_t := rule_name_t'.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | Imem           => tc_imem
    | Dmem           => tc_dmem
    end.

  Definition schedule : scheduler :=
    Imem |> Dmem |> done.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.
End Memory.
