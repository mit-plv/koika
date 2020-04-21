Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.
Require Import DynamicIsolation.RVEncoding.
Require Import DynamicIsolation.Scoreboard.
Require Import DynamicIsolation.Multiplier.

Require Import DynamicIsolation.External.
Require Import DynamicIsolation.Tactics.
Require Import DynamicIsolation.Interfaces.

(* Heavily inspired by http://csg.csail.mit.edu/6.175/labs/project-part1.html *)

Module CacheTypes.
  Import Common.

  Definition MSI :=
    {| enum_name := "MSI";
       enum_members := vect_of_list ["M"; "S"; "I"];
       enum_bitpatterns := vect_of_list [Ob~0~0; Ob~0~1; Ob~1~0] |}.

  Definition cache_type :=
    {| enum_name := "cache_type";
       enum_members := vect_of_list ["imem"; "dmem"];
       enum_bitpatterns := vect_of_list [Ob~0; Ob~1] |}.


  Definition cache_mem_req :=
    {| struct_name := "cache_mem_req";
       struct_fields := [("core_id" , bits_t 1);
                         ("cache_type", enum_t cache_type);
                         ("addr"    , addr_t);
                         ("MSI_state"   , enum_t MSI)] |}.

  Definition cache_mem_resp :=
    {| struct_name := "cache_mem_resp";
       struct_fields := [("core_id"   , bits_t 1);
                         ("cache_type", enum_t cache_type);
                         ("addr"      , addr_t);
                         ("MSI_state" , enum_t MSI);
                         ("data"      , maybe (data_t))
                        ] |}.

  Module FifoCacheMemReq <: Fifo.
    Definition T:= struct_t cache_mem_req.
  End FifoCacheMemReq.
  Module CacheMemReq := Fifo1 FifoMemReq.

  Module FifoCacheMemResp <: Fifo.
    Definition T:= struct_t cache_mem_resp.
  End FifoCacheMemResp.
  Module CacheMemResp := Fifo1 FifoMemResp.

  Definition cache_mem_msg_tag :=
    {| enum_name := "cache_mem_msg_tag";
       enum_members := vect_of_list ["Req"; "Resp"];
       enum_bitpatterns := vect_of_list [Ob~0; Ob~1] |}.

  (* NOTE: This should be a union type if one existed. What is the best way to encode this? *)
  Definition cache_mem_msg :=
    {| struct_name := "cache_mem_msg";
       struct_fields := [("type", enum_t cache_mem_msg_tag );
                         ("req" , struct_t cache_mem_req);
                         ("resp" , struct_t cache_mem_resp)
                        ] |}.

End CacheTypes.

Module MessageFifo1.
  Import CacheTypes.

  (* A message FIFO has two enqueue methods (enq_resp and enq_req), and behaves such that a request
   * never blocks a response.
   *)
  Inductive reg_t :=
  | reqQueue (state: CacheMemReq.reg_t)
  | respQueue (state: CacheMemResp.reg_t).

  Definition R r :=
    match r with
    | reqQueue s => CacheMemReq.R s
    | respQueue s => CacheMemResp.R s
    end.

  Definition r idx : R idx :=
    match idx with
    | reqQueue s => CacheMemReq.r s
    | respQueue s => CacheMemResp.r s
    end.

  Definition enq_resp : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq_resp (resp: struct_t cache_mem_resp) : bits_t 0 =>
         respQueue.(CacheMemResp.enq)()
    }}.

  Definition enq_req : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq_req (resp: struct_t cache_mem_req) : bits_t 0 =>
         reqQueue.(CacheMemReq.enq)()
    }}.

  Definition has_resp : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun has_resp () : bits_t 1 =>
         respQueue.(CacheMemResp.can_deq)()
    }}.

  Definition has_req : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun has_req () : bits_t 1 =>
         reqQueue.(CacheMemReq.can_deq)()
    }}.

  Definition not_empty : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun not_empty () : bits_t 1 =>
         has_resp() || has_req()
    }}.

  (* TODO: ugly; peek returns a maybe type *)
  Definition peek : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun peek () : maybe (struct_t cache_mem_msg) =>
         if has_resp() then
           let resp_opt := respQueue.(CacheMemResp.peek)() in
           let msg := struct cache_mem_msg {| type := enum cache_mem_msg_tag {| Resp |};
                                              resp := get(resp_opt, data)
                                           |} in
           {valid (struct_t cache_mem_msg)}(msg)
         else if has_req() then
           let req_opt := reqQueue.(CacheMemReq.peek)() in
           let msg := struct cache_mem_msg {| type := enum cache_mem_msg_tag {| Req |};
                                              resp := get(req_opt, data)
                                           |} in
           {valid (struct_t cache_mem_msg)}(msg)
         else
           {invalid (struct_t cache_mem_msg)}()
    }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : struct_t cache_mem_msg =>
       guard (not_empty());
       if has_resp() then
           let resp_opt := respQueue.(CacheMemResp.peek)() in
           struct cache_mem_msg {| type := enum cache_mem_msg_tag {| Resp |};
                                   resp := get(resp_opt, data)
                                |}
       else
           let req_opt := reqQueue.(CacheMemReq.peek)() in
           struct cache_mem_msg {| type := enum cache_mem_msg_tag {| Req |};
                                   resp := get(req_opt, data)
                                |}
   }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  (* TODO: Test this. *)
End MessageFifo1.

Module WIPMemory <: Memory_sig External.
  Import Common.

  (* This memory has two L1 I&D caches, a message router, and protocol processor, and the main memory.
   * TODO: next we will add a L2 cache.
   *)

  (* TODO: In theory we would do this in a more modular way, but we simplify for now.
   *)
  Inductive internal_reg_t' : Type :=
  | core0IToRouter (state: MessageFifo1.reg_t)
  | core0DToRouter (state: MessageFifo1.reg_t)
  | core1IToRouter (state: MessageFifo1.reg_t)
  | core1DToRouter (state: MessageFifo1.reg_t)
  | RouterToCore0I (state: MessageFifo1.reg_t)
  | RouterToCore0D (state: MessageFifo1.reg_t)
  | RouterToCore1I (state: MessageFifo1.reg_t)
  | RouterToCore1D (state: MessageFifo1.reg_t)
  | RouterToProto (state: MessageFifo1.reg_t)
  | ProtoToRouter (state: MessageFifo1.reg_t)
  | routerTiebreaker (* To implement round-robin fairness *)
  .

  Definition internal_reg_t := internal_reg_t'.

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | core0IToRouter st => MessageFifo1.R st
    | core0DToRouter st => MessageFifo1.R st
    | core1IToRouter st => MessageFifo1.R st
    | core1DToRouter st => MessageFifo1.R st
    | RouterToCore0I st => MessageFifo1.R st
    | RouterToCore0D st => MessageFifo1.R st
    | RouterToCore1I st => MessageFifo1.R st
    | RouterToCore1D st => MessageFifo1.R st
    | RouterToProto st => MessageFifo1.R st
    | ProtoToRouter st => MessageFifo1.R st
    | routerTiebreaker => bits_t 2
    end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with
    | core0IToRouter st => MessageFifo1.r st
    | core0DToRouter st => MessageFifo1.r st
    | core1IToRouter st => MessageFifo1.r st
    | core1DToRouter st => MessageFifo1.r st
    | RouterToCore0I st => MessageFifo1.r st
    | RouterToCore0D st => MessageFifo1.r st
    | RouterToCore1I st => MessageFifo1.r st
    | RouterToCore1D st => MessageFifo1.r st
    | RouterToProto st => MessageFifo1.r st
    | ProtoToRouter st => MessageFifo1.r st
    | routerTiebreaker => Bits.zero
    end.

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.

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

  Definition r idx : R idx :=
    match idx with
    | toIMem0 st => MemReq.r st
    | toIMem1 st => MemReq.r st
    | toDMem0 st => MemReq.r st
    | toDMem1 st => MemReq.r st
    | fromIMem0 st => MemResp.r st
    | fromIMem1 st => MemResp.r st
    | fromDMem0 st => MemResp.r st
    | fromDMem1 st => MemResp.r st
    | internal st => r_internal st
    end.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)

  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_LED_ADDRESS  := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.


  Notation "'__internal__' instance " :=
    (fun reg => internal ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Import External.
  Import CacheTypes.

  (* ===================== Message routing rules ============================== *)
  Definition router_memToCore : uaction reg_t ext_fn_t :=
    {{ let msg := (__internal__ ProtoToRouter).(MessageFifo1.deq)() in
       if (get(msg, type) == enum cache_mem_msg_tag {| Req |}) then
         let req := get(msg, req) in
         if (get(req, core_id) == Ob~0) then
           if (get(req, cache_type) == enum cache_type {| imem |}) then
             (__internal__ RouterToCore0I).(MessageFifo1.enq_req)(req)
           else
             (__internal__ RouterToCore0D).(MessageFifo1.enq_req)(req)
         else
           if (get(req, cache_type) == enum cache_type {| imem |}) then
             (__internal__ RouterToCore1I).(MessageFifo1.enq_req)(req)
           else
             (__internal__ RouterToCore1D).(MessageFifo1.enq_req)(req)
       else (* Resp *)
         let resp := get(msg, resp) in
         if (get(resp, core_id) == Ob~0) then
           if (get(req, cache_type) == enum cache_type {| imem |}) then
             (__internal__ RouterToCore0I).(MessageFifo1.enq_resp)(resp)
           else
             (__internal__ RouterToCore0D).(MessageFifo1.enq_resp)(resp)
         else
           if (get(resp, cache_type) == enum cache_type {| imem |}) then
             (__internal__ RouterToCore1I).(MessageFifo1.enq_resp)(resp)
           else
             (__internal__ RouterToCore1D).(MessageFifo1.enq_resp)(resp)
    }}.

  Definition router_getResp : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun router_getResp (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
           match tiebreaker with
           | Ob~0~0 =>
               if ((__internal__ core0IToRouter).(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core0IToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | Ob~0~1 =>
               if ((__internal__ core0DToRouter).(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core0DToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | Ob~1~0 =>
               if ((__internal__ core1IToRouter).(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core1IToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | Ob~1~1 =>
               if ((__internal__ core1DToRouter).(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core1DToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           return default : {invalid (struct_t cache_mem_msg)}()
           end
    }}.

  Definition router_getReq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun router_getReq (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
           match tiebreaker with
           | Ob~0~0 =>
               if (!(__internal__ core0IToRouter).(MessageFifo1.has_resp)() &&
                    (__internal__ core0IToRouter).(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core0IToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | Ob~0~1 =>
               if (!(__internal__ core0DToRouter).(MessageFifo1.has_resp)() &&
                    (__internal__ core0DToRouter).(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core0DToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | Ob~1~0 =>
               if (!(__internal__ core1IToRouter).(MessageFifo1.has_resp)() &&
                    (__internal__ core1IToRouter).(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core1IToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | Ob~1~1 =>
               if (!(__internal__ core1DToRouter).(MessageFifo1.has_resp)() &&
                    (__internal__ core1DToRouter).(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}((__internal__ core1DToRouter).(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           return default : {invalid (struct_t cache_mem_msg)}()
           end
    }}.

  (* TODO: very ugly... *)
  (* ======= Search for responses, starting with tiebreaker ====== *)
  Definition router_searchResponses : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun router_searchResponses (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
         let foundMsg := Ob~0 in
         let msg := {invalid (struct_t cache_mem_msg)}() in
         when (!foundMsg) do (
           let curResp := router_getResp (tiebreaker) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := get(curResp, data);
              write0(internal routerTiebreaker, tiebreaker + |2`d1|)
            )
          );
         when (!foundMsg) do (
           let curResp := router_getResp (tiebreaker+|2`d1|) in
           when (get(curResp, valid)) do (
             set foundMsg := Ob~1;
             set msg := get(curResp, data);
             write0(internal routerTiebreaker, tiebreaker + |2`d2|)
           )
         );
         when (!foundMsg) do (
           let curResp := router_getResp (tiebreaker+|2`d2|) in
           when (get(curResp, valid)) do (
             set foundMsg := Ob~1;
             set msg := get(curResp, data);
             write0(internal routerTiebreaker, tiebreaker + |2`d3|)
           )
         );
         when (!foundMsg) do (
           let curResp := router_getResp (tiebreaker+|2`d3|) in
           when (get(curResp, valid)) do (
             set foundMsg := Ob~1;
             set msg := get(curResp, data);
             write0(internal routerTiebreaker, tiebreaker + |2`d4|)
           )
         )
     }}.

  (* ======= Search for responses, starting with tiebreaker ====== *)
  Definition router_searchRequests : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun router_searchRequests (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
         let foundMsg := Ob~0 in
         let msg := {invalid (struct_t cache_mem_msg)}() in
         when (!foundMsg) do (
           let curReq := router_getReq (tiebreaker) in
            when (get(curReq, valid)) do (
              set foundMsg := Ob~1;
              set msg := get(curReq, data);
              write0(internal routerTiebreaker, tiebreaker + |2`d1|)
            )
          );
         when (!foundMsg) do (
           let curReq := router_getReq (tiebreaker+|2`d1|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := get(curReq, data);
             write0(internal routerTiebreaker, tiebreaker + |2`d2|)
           )
         );
         when (!foundMsg) do (
           let curReq := router_getReq (tiebreaker+|2`d2|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := get(curReq, data);
             write0(internal routerTiebreaker, tiebreaker + |2`d3|)
           )
         );
         when (!foundMsg) do (
           let curReq := router_getReq (tiebreaker+|2`d3|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := get(curReq, data);
             write0(internal routerTiebreaker, tiebreaker + |2`d4|)
           )
         )
     }}.

  Definition router_coreToMem : uaction reg_t ext_fn_t :=
    {{ let tiebreaker := read0(internal routerTiebreaker) in
       (* Search for requests, starting with tiebreaker *)
       let msg := router_searchResponses (tiebreaker) in
       if (get(msg, valid)) then
         (* enqueue *)
         (__internal__ RouterToProto).(MessageFifo1.enq_resp)(get(msg,resp))
       else
       (* Search for responses, starting with tiebreaker *)
         let msg := router_searchRequests (tiebreaker) in
         if (get(msg,valid)) then
           (__internal__ RouterToProto).(MessageFifo1.enq_req)(get(msg,req))
         else
           write0(internal routerTiebreaker, tiebreaker + |2`d1|)
    }}.

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

  Instance FiniteType_reg_t : FiniteType reg_t := _.
End WIPMemory.


Module SimpleMemory <: Memory_sig External.
  Import Common.

  (* TOOD: Silly workaround due to extraction issues: https://github.com/coq/coq/issues/12124 *)
  Inductive internal_reg_t' : Type :=
  | Foo | Bar .

  Definition internal_reg_t := internal_reg_t'.

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | Foo => bits_t 1
    | Bar => bits_t 1
    end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with
    | Foo => Bits.zero
    | Bar => Bits.zero
    end.

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

  Definition r idx : R idx :=
    match idx with
    | toIMem0 st => MemReq.r st
    | toIMem1 st => MemReq.r st
    | toDMem0 st => MemReq.r st
    | toDMem1 st => MemReq.r st
    | fromIMem0 st => MemResp.r st
    | fromIMem1 st => MemResp.r st
    | fromDMem0 st => MemResp.r st
    | fromDMem1 st => MemResp.r st
    | internal st => r_internal st
    end.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)


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
End SimpleMemory.
