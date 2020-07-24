Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.
Require Import dynamic_isolation.RVEncoding.
Require Import dynamic_isolation.Scoreboard.
Require Import dynamic_isolation.Multiplier.

Require Import dynamic_isolation.External.
Require Import dynamic_isolation.Interfaces.
Require Import dynamic_isolation.Interp.
Require Import dynamic_isolation.Lift.
Require Import dynamic_isolation.LogHelpers.
Require Import dynamic_isolation.Tactics.

(* Heavily inspired by http://csg.csail.mit.edu/6.175/labs/project-part1.html *)

Definition post_t := unit.
Definition var_t := string.
Definition fn_name_t := string.


Module CacheTypes.
  Import Common.
  Import External.

  Definition cache_mem_req :=
    {| struct_name := "cache_mem_req";
       struct_fields := [("core_id" , bits_t 1);
                         ("cache_type", enum_t cache_type);
                         ("addr"    , addr_t);
                         ("MSI_state"   , enum_t MSI)
                        ]
    |}.

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
  Module CacheMemReq := Fifo1 FifoCacheMemReq.

  Module FifoCacheMemResp <: Fifo.
    Definition T:= struct_t cache_mem_resp.
  End FifoCacheMemResp.
  Module CacheMemResp := Fifo1 FifoCacheMemResp.

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

  (* TODO: figure out syntax to write as a function of log size *)
  Definition getTag {reg_t}: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun getTag (addr: bits_t 32) : cache_tag_t =>
         addr[|5`d14|:+18]
    }}.

  Definition getIndex {reg_t}: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun getIndex (addr: bits_t 32) : cache_index_t =>
         addr[|5`d2|:+12]
    }}.

  Definition dummy_mem_req : struct_t mem_req := value_of_bits (Bits.zero).
  Definition dummy_mem_resp : struct_t mem_resp := value_of_bits (Bits.zero).

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
         respQueue.(CacheMemResp.enq)(resp)
    }}.

  Definition enq_req : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq_req (req: struct_t cache_mem_req) : bits_t 0 =>
         reqQueue.(CacheMemReq.enq)(req)
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
           let msg := struct cache_mem_msg { type := enum cache_mem_msg_tag { Resp };
                                             resp := get(resp_opt, data)
                                           } in
           {valid (struct_t cache_mem_msg)}(msg)
         else if has_req() then
           let req_opt := reqQueue.(CacheMemReq.peek)() in
           let msg := struct cache_mem_msg { type := enum cache_mem_msg_tag { Req };
                                             resp := get(req_opt, data)
                                           } in
           {valid (struct_t cache_mem_msg)}(msg)
         else
           {invalid (struct_t cache_mem_msg)}()
    }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : struct_t cache_mem_msg =>
       guard (not_empty());
       if has_resp() then
           let resp_opt := respQueue.(CacheMemResp.deq)() in
           struct cache_mem_msg { type := enum cache_mem_msg_tag { Resp };
                                   resp := resp_opt
                                }
       else
           let req_opt := reqQueue.(CacheMemReq.deq)() in
           struct cache_mem_msg { type := enum cache_mem_msg_tag { Req };
                                   req := req_opt
                                }
   }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  (* TODO: Test this. *)
End MessageFifo1.

Module MessageRouter.
  Inductive private_reg_t :=
  | routerTieBreaker (* To implement round robin fairness *)
  .

  Definition R_private (idx: private_reg_t) : type :=
    match idx with
    | routerTieBreaker => bits_t 2
    end.

  Definition r_private (idx: private_reg_t) : R_private idx :=
    match idx with
    | routerTieBreaker => Bits.zero
    end.

  Inductive reg_t : Type :=
  | FromCore0I (state: MessageFifo1.reg_t)
  | FromCore0D (state: MessageFifo1.reg_t)
  | FromCore1I (state: MessageFifo1.reg_t)
  | FromCore1D (state: MessageFifo1.reg_t)
  | ToCore0I (state: MessageFifo1.reg_t)
  | ToCore0D (state: MessageFifo1.reg_t)
  | ToCore1I (state: MessageFifo1.reg_t)
  | ToCore1D (state: MessageFifo1.reg_t)
  | ToProto (state: MessageFifo1.reg_t)
  | FromProto (state: MessageFifo1.reg_t)
  | private (state: private_reg_t)
  .

  Definition R (idx: reg_t) : type :=
    match idx with
    | FromCore0I st => MessageFifo1.R st
    | FromCore0D st => MessageFifo1.R st
    | FromCore1I st => MessageFifo1.R st
    | FromCore1D st => MessageFifo1.R st
    | ToCore0I st => MessageFifo1.R st
    | ToCore0D st => MessageFifo1.R st
    | ToCore1I st => MessageFifo1.R st
    | ToCore1D st => MessageFifo1.R st
    | ToProto st => MessageFifo1.R st
    | FromProto st => MessageFifo1.R st
    | private st => R_private st
    end.

  Notation "'__private__' instance " :=
    (fun reg => private ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Import CacheTypes.
  Import External.

  Definition Sigma := empty_Sigma.
  Definition ext_fn_t := empty_ext_fn_t.
  Definition rule := rule R Sigma.

  (* ===================== Message routing rules ============================== *)
  Definition memToCore : uaction reg_t empty_ext_fn_t :=
    {{ let msg := FromProto.(MessageFifo1.deq)() in
       if (get(msg, type) == enum cache_mem_msg_tag { Req }) then
         let req := get(msg, req) in
         if (get(req, core_id) == Ob~0) then
           if (get(req, cache_type) == enum cache_type { imem }) then
             ToCore0I.(MessageFifo1.enq_req)(req)
           else
             ToCore0D.(MessageFifo1.enq_req)(req)
         else
           if (get(req, cache_type) == enum cache_type { imem }) then
             ToCore1I.(MessageFifo1.enq_req)(req)
           else
             ToCore1D.(MessageFifo1.enq_req)(req)
       else (* Resp *)
         let resp := get(msg, resp) in
         if (get(resp, core_id) == Ob~0) then
           if (get(resp, cache_type) == enum cache_type { imem }) then
             ToCore0I.(MessageFifo1.enq_resp)(resp)
           else
             ToCore0D.(MessageFifo1.enq_resp)(resp)
         else
           if (get(resp, cache_type) == enum cache_type { imem }) then
             ToCore1I.(MessageFifo1.enq_resp)(resp)
           else
             ToCore1D.(MessageFifo1.enq_resp)(resp)
    }}.

  Definition getResp : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun getResp (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
           match tiebreaker with
           | #Ob~0~0 =>
               if (FromCore0I.(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore0I.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | #Ob~0~1 =>
               if (FromCore0D.(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore0D.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | #Ob~1~0 =>
               if (FromCore1I.(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore1I.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | #Ob~1~1 =>
               if (FromCore1D.(MessageFifo1.has_resp)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore1D.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           return default : {invalid (struct_t cache_mem_msg)}()
           end
    }}.

  Definition getReq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun getReq (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
           match tiebreaker with
           | #Ob~0~0 =>
               if (!FromCore0I.(MessageFifo1.has_resp)() &&
                    FromCore0I.(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore0I.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | #Ob~0~1 =>
               if (!FromCore0D.(MessageFifo1.has_resp)() &&
                    FromCore0D.(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore0D.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | #Ob~1~0 =>
               if (!FromCore1I.(MessageFifo1.has_resp)() &&
                    FromCore1I.(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore1I.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           | #Ob~1~1 =>
               if (!FromCore1D.(MessageFifo1.has_resp)() &&
                    FromCore1D.(MessageFifo1.has_req)()) then
                 {valid (struct_t cache_mem_msg)}(FromCore1D.(MessageFifo1.deq)())
               else
                 {invalid (struct_t cache_mem_msg)}()
           return default : {invalid (struct_t cache_mem_msg)}()
           end
    }}.

  (* TODO: very ugly... *)
  (* ======= Search for responses, starting with tiebreaker ====== *)
  Definition searchResponses : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun searchResponses (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
         let foundMsg := Ob~0 in
         let msg := {invalid (struct_t cache_mem_msg)}() in
         (when (!foundMsg) do (
           let curResp := getResp (tiebreaker) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := {valid (struct_t cache_mem_msg)} (get(curResp, data));
              write0(private routerTieBreaker, tiebreaker + |2`d1|)
            )
         ));
         (when (!foundMsg) do (
            let curResp := getResp (tiebreaker+|2`d1|) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := {valid (struct_t cache_mem_msg)} (get(curResp, data));
              write0(private routerTieBreaker, tiebreaker + |2`d2|)
            )
          ));
         (when (!foundMsg) do (
            let curResp := getResp (tiebreaker+|2`d2|) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := {valid (struct_t cache_mem_msg)} (get(curResp, data));
              write0(private routerTieBreaker, tiebreaker + |2`d3|)
            )
          ));
         (when (!foundMsg) do (
            let curResp := getResp (tiebreaker+|2`d3|) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := {valid (struct_t cache_mem_msg)} (get(curResp, data));
              write0(private routerTieBreaker, tiebreaker + |2`d4|)
            )
          ));
         msg
     }}.

  (* ======= Search for responses, starting with tiebreaker ====== *)

  (* TODO: This is not isolation friendly right now; should do it round robin style *)
  Definition searchRequests : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun searchRequests (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
         let foundMsg := Ob~0 in
         let msg := {invalid (struct_t cache_mem_msg)}() in
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker) in
            when (get(curReq, valid)) do (
              set foundMsg := Ob~1;
              set msg := curReq;
              write0(private routerTieBreaker, tiebreaker + |2`d1|)
            )
          ));
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker+|2`d1|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := curReq;
             write0(private routerTieBreaker, tiebreaker + |2`d2|)
           )
         ));
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker+|2`d2|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := curReq;
             write0(private routerTieBreaker, tiebreaker + |2`d3|)
           )
         ));
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker+|2`d3|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := curReq;
             write0(private routerTieBreaker, tiebreaker + |2`d4|)
           )
         ));
         msg
     }}.

  Definition coreToMem : uaction reg_t empty_ext_fn_t :=
    {{ let tiebreaker := read0(private routerTieBreaker) in
       (* Search for requests, starting with tieBreaker *)
       let msg_opt := searchResponses (tiebreaker) in
       if (get(msg_opt, valid)) then
         (* enqueue *)
         let msg := get(msg_opt,data) in
         ToProto.(MessageFifo1.enq_resp)(get(msg,resp))
       else
       (* Search for responses, starting with tiebreaker *)
         let msg_opt := searchRequests (tiebreaker) in
         if (get(msg_opt,valid)) then
           let msg := get(msg_opt, data) in
           ToProto.(MessageFifo1.enq_req)(get(msg,req))
         else
           write0(private routerTieBreaker, tiebreaker + |2`d1|)
    }}.

  Inductive rule_name_t :=
  | Rl_MemToCore
  | Rl_CoreToMem
  .

  Definition tc_memToCore := tc_rule R Sigma memToCore <: rule.
  Definition tc_coreToMem := tc_rule R Sigma coreToMem <: rule.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | Rl_MemToCore => tc_memToCore
    | Rl_CoreToMem => tc_coreToMem
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Rl_MemToCore |> Rl_CoreToMem |> done.

End MessageRouter.

Module Type CacheParams.
  Parameter _core_id : Common.ind_core_id.
  Parameter _cache_type : Common.ind_cache_type.
End CacheParams.

Module Cache (Params: CacheParams).
  Import CacheTypes.
  Import Common.
  Import External.

  Definition core_id : core_id_t :=
    match Params._core_id with
    | CoreId0 => Ob~0
    | CoreId1 => Ob~1
    end.

  Definition cache_type : enum_t cache_type :=
    match Params._cache_type with
    | CacheType_Imem => Ob~0
    | CacheType_Dmem => Ob~1
    end.

  Definition external_memory : External.cache :=
    match Params._cache_type, Params._core_id with
    | CacheType_Imem, CoreId0 => External.imem0
    | CacheType_Imem, CoreId1 => External.imem1
    | CacheType_Dmem, CoreId0 => External.dmem0
    | CacheType_Dmem, CoreId1 => External.dmem1
    end.

  (* Hard-coded for now: direct-mapped cache: #sets = #blocks; word-addressable *)

  Definition mshr_tag :=
    {| enum_name := "mshr_tag";
       enum_members := vect_of_list ["Ready"; "SendFillReq"; "WaitFillResp"];
       enum_bitpatterns := vect_of_list [Ob~0~0; Ob~0~1; Ob~1~0]
    |}.

  (* TODO *)
  Definition MSHR_t :=
    {| struct_name := "MSHR";
       struct_fields := [("mshr_tag", enum_t mshr_tag);
                         ("req", struct_t mem_req)
                        ] |}.

  Definition flush_status :=
    {| enum_name := "flush_status";
       enum_members := vect_of_list ["Ready"; "Flushing"; "Flushed"];
       enum_bitpatterns := vect_of_list [Ob~0~0; Ob~0~1; Ob~1~0] |}.

  Definition flush_state_t :=
    {| struct_name := "flush_state";
       struct_fields := [("status", enum_t flush_status);
                         ("curIndex", cache_index_t)]
    |}.

  Inductive private_reg_t :=
  | downgradeState
  | requestsQ (state: MemReq.reg_t)
  | responsesQ (state: MemResp.reg_t)
  | MSHR
  | flushState
  .

  Instance FiniteType_private_reg_t : FiniteType private_reg_t := _.

  Definition R_private (idx: private_reg_t) : type :=
    match idx with
    | downgradeState => bits_t 1
    | requestsQ st => MemReq.R st
    | responsesQ st => MemResp.R st
    | MSHR => struct_t MSHR_t
    | flushState => struct_t flush_state_t
    end.

  Definition r_private (idx: private_reg_t) : R_private idx :=
    match idx with
    | downgradeState => Ob~0
    | requestsQ st => MemReq.r st
    | responsesQ st => MemResp.r st
    | MSHR => value_of_bits (Bits.zero)
    | flushState => value_of_bits (Bits.zero)
    end.

  Inductive reg_t :=
  | fromMem (state: MessageFifo1.reg_t)
  | toMem (state: MessageFifo1.reg_t)
  | private (state: private_reg_t)
  .

  Definition R (idx: reg_t) : type :=
    match idx with
    | fromMem st => MessageFifo1.R st
    | toMem st => MessageFifo1.R st
    | private st => R_private st
    end.

  Notation "'__private__' instance " :=
    (fun reg => private ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Definition Sigma := External.Sigma.
  Definition ext_fn_t := External.ext_fn_t.

  (* Ready -> SendFillReq;
     SendFillReq -> WaitFillResp;
     WaitFillResp -> Ready
  *)

  (* Definition downgrade : uaction reg_t empty_ext_fn_t. Admitted. *)

  (* TODO: move to Std *)
  Section Maybe.
    Context (tau: type).

    Definition fromMaybe {reg_t fn}: UInternalFunction reg_t fn :=
      {{ fun fromMaybe (default: tau) (val: maybe tau) : tau =>
           if get(val, valid) then get(val, data)
           else default
      }}.
  End Maybe.

  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_LED_ADDRESS  := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.

  Definition memoryBus (m: External.cache) : UInternalFunction reg_t ext_fn_t :=
    {{ fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1) (put_request: struct_t ext_cache_mem_req)
         : struct_t cache_mem_output =>
         `match m with
          | imem0 => {{ extcall (ext_cache imem0) (struct cache_mem_input {
                        get_ready := get_ready;
                        put_valid := put_valid;
                        put_request := put_request }) }}
          | imem1 => {{ extcall (ext_cache imem1) (struct cache_mem_input {
                        get_ready := get_ready;
                        put_valid := put_valid;
                        put_request := put_request }) }}
          | dmem0    =>
                   {{ extcall (ext_cache dmem0) (struct cache_mem_input {
                        get_ready := get_ready;
                        put_valid := put_valid;
                        put_request := put_request }) }}
          | dmem1    =>
                   {{ extcall (ext_cache dmem1) (struct cache_mem_input {
                        get_ready := get_ready;
                        put_valid := put_valid;
                        put_request := put_request }) }}
          end
         `
   }}.

  (* If Store: do nothing in response *)
  (* If Load: send response *)
  Definition hit (mem: External.cache): UInternalFunction reg_t ext_fn_t :=
    {{ fun hit (req: struct_t mem_req) (row: struct_t cache_row) (write_on_load: bits_t 1): enum_t mshr_tag =>
         let new_state := enum mshr_tag { Ready } in
         (
         if (get(req, byte_en) == Ob~0~0~0~0) then
           (__private__ responsesQ).(MemResp.enq)(
             struct mem_resp { addr := get(req, addr);
                                data := get(row,data);
                                byte_en := get(req, byte_en)
                             });
             if (write_on_load) then
               let cache_req := struct ext_cache_mem_req
                                      { byte_en := Ob~1~1~1~1;
                                         tag := getTag(get(req,addr));
                                         index := getIndex(get(req,addr));
                                         data := get(row,data);
                                         MSI := {valid (enum_t MSI)}(get(row,flag))
                                      } in
               ignore({memoryBus mem}(Ob~1, Ob~1, cache_req))
             else pass
         else (* TODO: commit data *)
           if (get(row,flag) == enum MSI { M }) then
             let cache_req := struct ext_cache_mem_req
                                    { byte_en := get(req,byte_en);
                                       tag := getTag(get(req,addr));
                                       index := getIndex(get(req,addr));
                                       data := get(req,data);
                                       MSI := {valid (enum_t MSI)}(enum MSI { M })
                                    } in
             ignore({memoryBus mem}(Ob~1, Ob~1, cache_req));
             (__private__ responsesQ).(MemResp.enq)(
               struct mem_resp { addr := get(req, addr);
                                  data := |32`d0|;
                                  byte_en := get(req, byte_en)
                               })
           else
             set new_state := enum mshr_tag { SendFillReq }
         );
         new_state
    }}.

  Definition dummy_ext_cache_mem_req : struct_t ext_cache_mem_req := value_of_bits (Bits.zero).

  Definition downgrade (mem: External.cache): uaction reg_t ext_fn_t :=
    {{
        if (fromMem.(MessageFifo1.not_empty)() &&
            !fromMem.(MessageFifo1.has_resp)()) then
          write0(private downgradeState, Ob~1);
          let req := get(fromMem.(MessageFifo1.deq)(), req) in
          let index := getIndex(get(req,addr)) in
          let tag := getTag(get(req,addr)) in
          let cache_req := struct ext_cache_mem_req { byte_en := Ob~0~0~0~0;
                                                       tag := tag;
                                                       index := index;
                                                       data := |32`d0|;
                                                       MSI := {invalid (enum_t MSI)}() } in
          guard (!toMem.(MessageFifo1.has_resp)());
          let cache_output := {memoryBus mem}(Ob~1, Ob~1, cache_req) in
          guard ((get(cache_output, get_valid)));
          let row := get(get(cache_output, get_response),row) in
          if (get(row,tag) == tag &&
              ((get(req, MSI_state) == enum MSI { I } && get(row, flag) != enum MSI { I }) ||
               (get(req, MSI_state) == enum MSI { S } && get(row, flag) == enum MSI { M }))) then
            let data_opt := (if get(row,flag) == enum MSI { M }
                             then {valid data_t}(get(row,data))
                             else {invalid data_t}()) in
            toMem.(MessageFifo1.enq_resp)(struct cache_mem_resp { core_id := (#core_id);
                                                                   cache_type := (`UConst (cache_type)`);
                                                                   addr := tag ++ index ++ (Ob~0~0);
                                                                   MSI_state := get(req, MSI_state);
                                                                   data := data_opt
                                                                });
            let cache_req := struct ext_cache_mem_req { byte_en := |4`d0|;
                                                         tag := tag;
                                                         index := index;
                                                         data := |32`d0|;
                                                         MSI := {valid (enum_t MSI)}(get(req, MSI_state))
                                                      } in
           ignore({memoryBus mem}(Ob~1, Ob~1, cache_req))
          else pass
        else
          write0(private downgradeState, Ob~0)
    }}.


  (* TOOD: for now, just assume miss and skip cache and forward to memory *)
  Definition process_request (mem: External.cache): uaction reg_t ext_fn_t :=
    {{
        let mshr := read0(private MSHR) in
        let downgrade_state := read1(private downgradeState) in
        guard((get(mshr,mshr_tag) == enum mshr_tag { Ready }) && !downgrade_state);
        let req := (__private__ requestsQ).(MemReq.deq)() in
        let addr := get(req,addr) in
        let tag := getTag(addr) in
        let index := getIndex(addr) in
        (* No offset because single element cache oops *)
        let cache_req := struct ext_cache_mem_req { byte_en := Ob~0~0~0~0;
                                                     tag := tag;
                                                     index := index;
                                                     data := get(req,data);
                                                     MSI := {invalid (enum_t MSI)}()
                                                  } in
        guard((__private__ responsesQ).(MemResp.can_enq)());
        guard(!toMem.(MessageFifo1.has_resp)());
        let cache_output := {memoryBus mem}(Ob~1, Ob~1, cache_req) in
        guard ((get(cache_output, get_valid)));
        let row := get(get(cache_output, get_response), row) in
        let inCache := ((get(row,tag) == tag) && (get(row,flag) != enum MSI { I } )) in
        if (inCache) then
          let newMSHR := {hit mem}(req, row, Ob~0) in
          write0(private MSHR, struct MSHR_t { mshr_tag := newMSHR;
                                                 req := req
                                              })
          (* miss *)
        else (
          (when (get(row,flag) != enum MSI { I }) do ((* tags unequal; need to downgrade *)
            let data_opt := (if get(row,flag) == enum MSI { M }
                             then {valid data_t}(get(row,data))
                             else {invalid data_t}()) in
            toMem.(MessageFifo1.enq_resp)(struct cache_mem_resp { core_id := (#core_id);
                                                                   cache_type := (`UConst (cache_type)`);
                                                                   addr := get(row,tag) ++ index ++ Ob~0~0;
                                                                   MSI_state := enum MSI { I };
                                                                   data := data_opt });
              (* TODO: should this be a write *)
            let cache_req := struct ext_cache_mem_req { byte_en := |4`d0|;
                                                         tag := |18`d0|;
                                                         index := index;
                                                         data := |32`d0|;
                                                         MSI := {valid (enum_t MSI)}(enum MSI { I }) } in
            ignore({memoryBus mem}(Ob~1, Ob~1, cache_req))
          ));
          write0(private MSHR, struct MSHR_t { mshr_tag := enum mshr_tag { SendFillReq };
                                                 req := req
                                              })
        )
    }}.


  Definition byte_en_to_msi_state : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun byte_en_to_msi_state (byte_en: bits_t 4) : enum_t MSI =>
         match byte_en with
         | #Ob~0~0~0~0 => enum MSI { S }
         return default : enum MSI { M }
         end
    }}.

  Definition SendFillReq : uaction reg_t ext_fn_t :=
    {{
        let mshr := read0(private MSHR) in
        let downgrade_state := read1(private downgradeState) in
        guard(get(mshr,mshr_tag) == enum mshr_tag { SendFillReq } && !downgrade_state);
        let mshr_req := get(mshr,req) in
        toMem.(MessageFifo1.enq_req)(
                  struct cache_mem_req { core_id := (#core_id);
                                          cache_type := (`UConst (cache_type)`);
                                          addr := get(mshr_req, addr);
                                          MSI_state := (match get(mshr_req,byte_en) with
                                                        | #Ob~0~0~0~0 => enum MSI { S }
                                                        return default : enum MSI { M }
                                                        end)
                                       });
        write0(private MSHR, struct MSHR_t { mshr_tag := enum mshr_tag { WaitFillResp };
                                               req := mshr_req
                                            })
    }}.

  Definition WaitFillResp (mem: External.cache): uaction reg_t ext_fn_t :=
    {{
        let mshr := read0(private MSHR) in
        let downgrade_state := read1(private downgradeState) in
        guard(get(mshr,mshr_tag) == enum mshr_tag { WaitFillResp }
              && !downgrade_state
              && fromMem.(MessageFifo1.has_resp)());
        let resp := get(fromMem.(MessageFifo1.deq)(),resp) in

        let req := get(mshr, req) in
        let row := struct cache_row { tag := getTag(get(req, addr));
                                       data := {fromMaybe data_t}(|32`d0|, get(resp,data));
                                       flag := get(resp, MSI_state)
                                    } in
        ignore({hit mem}(req, row, Ob~1));
        (* write to Mem *)
        write0(private MSHR, struct MSHR_t { mshr_tag := enum mshr_tag { Ready };
                                               req := (`UConst dummy_mem_req`)
                                            })
    }}.

  (*
  Definition Flush (mem: External.cache): uaction reg_t ext_fn_t :=
    {{
        let mshr := read0(private MSHR) in
        let flush_st := read0(private flushState) in
        guard(get(mshr,mshr_tag) == enum mshr_tag { Ready } &&
              get(flush_st, flush_status) == enum flush_status { Flushing });
        let index := get(flush_st, curIndex) in
        let cache_req := struct ext_cache_mem_req { byte_en := Ob~1~1~1~1;
                                                     tag := |18`d0|;
                                                     index := index;
                                                     data := |32`d0|;
                                                     MSI := {valid(enum_t MSI)}(enum MSI { I })
                                                  } in
        let cache_output := {memoryBus mem}(Ob~1, Ob~1, cache_req) in
        let row := get(get(cache_output, get_response), row) in
        let tag := get(row,tag) in
        let index := get(row,index) in
        let addr := tag ++ index ++ Ob~0~0 in

        (if (get(row,flag) != enum MSI { I }) then
          (* Invalidate in MSI *)
          toMem.(MessageFifo1.enq_resp)(struct cache_mem_resp { core_id := (#core_id);
                                                                 cache_type := (`UConst (cache_type)`);
                                                                 addr := addr;
                                                                 MSI_state := enum MSI { I };
                                                                 data := {valid data_t}(get(row,data)) })
        else pass);
        let cache_req := struct ext_cache_mem_req { byte_en := Ob~1~1~1~1;
                                                     tag := |18`d0|;
                                                     index := index;
                                                     data := |32`d0|;
                                                     MSI := {valid (enum_t MSI)}(enum MSI { I }) } in
        ignore({memoryBus mem}(Ob~1, Ob~1, cache_req));
        if (index == |12`d4095|) then
          write0(private flushState, struct flush_state_t { status := enum flush_status { Flushed };
                                                              curIndex := |12`d0| })
        else
          write0(private flushState, struct flush_state_t { status := enum flush_status { Flushing };
                                                              curIndex := index + |12`d1| })
    }}.
    *)
  Definition can_send_req : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun can_send_req () : bits_t 1 =>
         let mshr := read0(private MSHR) in
         get(mshr,mshr_tag) == enum mshr_tag { Ready } &&
         (__private__ requestsQ).(MemReq.can_enq)()
    }}.

  Definition req: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun req (r: struct_t mem_req) : bits_t 0 =>
         let mshr := read0(private MSHR) in
         guard(get(mshr,mshr_tag) == enum mshr_tag { Ready });
         (__private__ requestsQ).(MemReq.enq)(r)
    }}.

  Definition can_recv_resp: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun can_recv_resp () : bits_t 1 =>
         (__private__ responsesQ).(MemResp.can_deq)()
    }}.

  Definition resp: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun resp () : struct_t mem_resp =>
         (__private__ responsesQ).(MemResp.deq)()
    }}.

  Definition is_ready: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun is_ready () : bits_t 1 =>
         let mshr := read0(private MSHR) in
         get(mshr, mshr_tag) == enum mshr_tag { Ready }
    }}.

  (*
  Definition do_flush: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun do_flush () : bits_t 1 =>
         let st := read0(private flushState) in
         if (get(st,status) == enum flush_status { Flushed }) then
           Ob~1
         else if (get(st,status) == enum flush_status { Ready }) then
           write0(private flushState, struct flush_state_t { status := enum flush_status { Flushing };
                                                               curIndex := |12`d0| });
           Ob~0
         else Ob~0
    }}.
    *)

  Inductive rule_name_t :=
  | Rl_Downgrade
  | Rl_ProcessRequest
  | Rl_SendFillReq
  | Rl_WaitFillResp
  .

  Definition rule := rule R Sigma.

  (* NOTE: type-checking with unbound memory doesn't fail fast *)
  Definition tc_downgrade_imem0 := tc_rule R Sigma (downgrade External.imem0) <: rule.
  Definition tc_downgrade_dmem0 := tc_rule R Sigma (downgrade External.dmem0) <: rule.
  Definition tc_downgrade_imem1 := tc_rule R Sigma (downgrade External.imem1) <: rule.
  Definition tc_downgrade_dmem1 := tc_rule R Sigma (downgrade External.dmem1) <: rule.

  Definition tc_processRequest_imem0 := tc_rule R Sigma (process_request External.imem0) <: rule.
  Definition tc_processRequest_dmem0 := tc_rule R Sigma (process_request External.dmem0) <: rule.
  Definition tc_processRequest_imem1 := tc_rule R Sigma (process_request External.imem1) <: rule.
  Definition tc_processRequest_dmem1 := tc_rule R Sigma (process_request External.dmem1) <: rule.

  Definition tc_sendFillReq := tc_rule R Sigma (SendFillReq) <: rule.
  Definition tc_waitFillResp_imem0 := tc_rule R Sigma (WaitFillResp External.imem0) <: rule.
  Definition tc_waitFillResp_dmem0 := tc_rule R Sigma (WaitFillResp External.dmem0) <: rule.
  Definition tc_waitFillResp_imem1 := tc_rule R Sigma (WaitFillResp External.imem1) <: rule.
  Definition tc_waitFillResp_dmem1 := tc_rule R Sigma (WaitFillResp External.dmem1) <: rule.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | Rl_Downgrade =>
        match Params._cache_type, Params._core_id with
        | CacheType_Imem,CoreId0 => tc_downgrade_imem0
        | CacheType_Imem,CoreId1 => tc_downgrade_imem1
        | CacheType_Dmem,CoreId0 => tc_downgrade_dmem0
        | CacheType_Dmem,CoreId1 => tc_downgrade_dmem1
        end
    | Rl_ProcessRequest =>
        match Params._cache_type, Params._core_id with
        | CacheType_Imem,CoreId0 => tc_processRequest_imem0
        | CacheType_Imem,CoreId1 => tc_processRequest_imem1
        | CacheType_Dmem,CoreId0 => tc_processRequest_dmem0
        | CacheType_Dmem,CoreId1 => tc_processRequest_dmem1
        end
    | Rl_SendFillReq => tc_sendFillReq
    | Rl_WaitFillResp =>
        match Params._cache_type, Params._core_id with
        | CacheType_Imem,CoreId0 => tc_waitFillResp_imem0
        | CacheType_Imem,CoreId1 => tc_waitFillResp_imem1
        | CacheType_Dmem,CoreId0 => tc_waitFillResp_dmem0
        | CacheType_Dmem,CoreId1 => tc_waitFillResp_dmem1
        end
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Rl_Downgrade |> Rl_ProcessRequest |> Rl_SendFillReq |> Rl_WaitFillResp |> done.

End Cache.

Module ProtocolProcessor.
  Import Common.
  Import CacheTypes.
  Import External.

  Definition USHR_state :=
    {| enum_name := "USHR_state";
       enum_members := vect_of_list ["Ready"; "Downgrading"; "Confirming"];
       enum_bitpatterns := vect_of_list [Ob~0~0; Ob~0~1; Ob~1~0]
    |}.

  Definition USHR :=
    {| struct_name := "USHR";
       struct_fields := [("state", enum_t USHR_state);
                         ("req", struct_t cache_mem_req)]
    |}.

  Definition num_sets : nat := Nat.shiftl 1 External.log_num_sets.

  Inductive private_reg_t :=
  | ushr
  | downgrade_tracker
  | bypass
  .

  Instance FiniteType_private_reg_t : FiniteType private_reg_t := _.

  Definition R_private (reg: private_reg_t) : type :=
    match reg with
    | ushr => struct_t USHR
    | downgrade_tracker => bits_t 4
    | bypass => maybe (data_t)
    end.

  Definition r_private (reg: private_reg_t) : R_private reg :=
    match reg with
    | ushr => value_of_bits (Bits.zero)
    | downgrade_tracker => Bits.zero
    | bypass => value_of_bits (Bits.zero)
    end.

  (* TODO: Should be a DDR3_Req or similar, and should parameterise based on DDR3AddrSize/DataSize *)
  Inductive reg_t :=
  | FromRouter (state: MessageFifo1.reg_t)
  | ToRouter (state: MessageFifo1.reg_t)
  | ToMem (state: MemReq.reg_t)
  | FromMem (state: MemResp.reg_t)
  | private (state: private_reg_t)
  .

  Definition R (idx: reg_t) : type :=
    match idx with
    | FromRouter st => MessageFifo1.R st
    | ToRouter st => MessageFifo1.R st
    | ToMem st => MemReq.R st
    | FromMem st => MemResp.R st
    | private st => R_private st
    end.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Definition Sigma := Sigma.
  Definition ext_fn_t := ext_fn_t.

  Definition receive_responses : uaction reg_t ext_fn_t :=
    {{
        guard(FromRouter.(MessageFifo1.has_resp)());
        let respFromCore := get(FromRouter.(MessageFifo1.deq)(), resp) in
        let data_opt := get(respFromCore, data) in
        let resp_addr := get(respFromCore,addr) in
        (
        if (get(data_opt,valid)) then
          ToMem.(MemReq.enq)(struct mem_req { byte_en := Ob~1~1~1~1;
                                               addr := resp_addr;
                                               data := get(data_opt, data)
                                            });
          let ushr := read0(private ushr) in
          if (get(ushr,state) == enum USHR_state { Confirming } ||
              get(ushr,state) == enum USHR_state { Downgrading}) then
            let req := get(ushr,req) in
            let req_addr := get(req,addr) in
            if (getTag(req_addr) == getTag(resp_addr) &&
                getIndex(req_addr) == getIndex(resp_addr)) then
              write0(private bypass, {valid (data_t)}(get(data_opt,data)))
            else pass
          else pass
        else pass
        );
        let input := struct bookkeeping_input
                            { idx := getIndex(resp_addr);
                               book := {valid (struct_t Bookkeeping_row)}(
                                           struct Bookkeeping_row { state := get(respFromCore, MSI_state);
                                                                     tag := getTag(resp_addr)
                                                                  });
                               core_id := get(respFromCore,core_id);
                               cache_type := get(respFromCore, cache_type)
                           } in
        ignore(extcall ext_ppp_bookkeeping (input))
        (* TODO: update bookkeeping row/directory *)
    }}.

  Definition get_state : UInternalFunction reg_t ext_fn_t :=
    {{ fun get_state (core_id: bits_t 1) (cache_type: enum_t cache_type) (index: cache_index_t) (tag: cache_tag_t)
         : enum_t MSI =>
         let input := struct bookkeeping_input { idx := index;
                                                  book := {invalid (struct_t Bookkeeping_row)}();
                                                  core_id := core_id;
                                                  cache_type := cache_type
                                               } in
         let row_opt := extcall ext_ppp_bookkeeping (input) in
         if (get(row_opt,valid)) then
           let row := get(row_opt,data) in
           if (get(row,tag) == tag) then
             get(row,state)
           else
             enum MSI { I }
         else
           fail@(enum_t MSI)
     }}.

  (* Check dmem *)
  Definition has_line : UInternalFunction reg_t ext_fn_t :=
    {{ fun has_line (index: cache_index_t) (tag: cache_tag_t) (core_id: bits_t 1): bits_t 1 =>
         get_state(core_id, enum cache_type { dmem}, index, tag) == enum MSI { M }
    }}.

  Definition cache_encoding : UInternalFunction reg_t ext_fn_t :=
    {{ fun cache_encoding (core_id: bits_t 1) (cache_ty: enum_t cache_type) : bits_t 2 =>
           core_id ++ (cache_ty == enum cache_type { dmem })
    }}.

  Definition compute_downgrade_tracker : UInternalFunction reg_t ext_fn_t :=
    {{ fun compute_downgrade_tracker (index: cache_index_t) (tag: cache_tag_t) : bits_t 4 =>
         let core0_imem := get_state(Ob~0, enum cache_type { imem }, index, tag) in
         let core0_dmem := get_state(Ob~0, enum cache_type { dmem }, index, tag) in
         let core1_imem := get_state(Ob~1, enum cache_type { imem }, index, tag) in
         let core1_dmem := get_state(Ob~1, enum cache_type { dmem }, index, tag) in
         (core1_dmem != enum MSI { I }) ++
         (core1_imem != enum MSI { I }) ++
         (core0_dmem != enum MSI { I }) ++
         (core0_imem != enum MSI { I })
    }}.

  Definition set_invalid_at_cache : UInternalFunction reg_t ext_fn_t :=
    {{ fun set_invalid_at_cache (tracker: bits_t 4) (core_id: bits_t 1) (cache_ty: enum_t cache_type) : bits_t 4 =>
       (!(Ob~0~0~0~1 << cache_encoding (core_id, cache_ty))) && tracker
    }}.


  Definition do_downgrade_from_tracker : UInternalFunction reg_t ext_fn_t :=
    {{ fun do_downgrade_from_tracker (addr: addr_t) (tracker: bits_t 4) : bits_t 4 =>
         if (tracker[|2`d0|]) then
            ToRouter.(MessageFifo1.enq_req)(struct cache_mem_req { core_id := Ob~0;
                                                                    cache_type := enum cache_type { imem };
                                                                    addr := addr;
                                                                    MSI_state := enum MSI { I }
                                                                 });
            tracker[|2`d1|:+3] ++ Ob~0
          else if (tracker[|2`d1|]) then
            ToRouter.(MessageFifo1.enq_req)(struct cache_mem_req { core_id := Ob~0;
                                                                    cache_type := enum cache_type { dmem };
                                                                    addr := addr;
                                                                    MSI_state := enum MSI { I }
                                                                 });
            tracker[|2`d2|:+2] ++ Ob~0~0
          else if (tracker[|2`d2|]) then
            ToRouter.(MessageFifo1.enq_req)(struct cache_mem_req { core_id := Ob~1;
                                                                    cache_type := enum cache_type { imem };
                                                                    addr := addr;
                                                                    MSI_state := enum MSI { I }
                                                                 });

            tracker[|2`d3|] ++ Ob~0~0~0
          else if (tracker[|2`d3|]) then
            ToRouter.(MessageFifo1.enq_req)(struct cache_mem_req { core_id := Ob~1;
                                                                    cache_type := enum cache_type { dmem };
                                                                    addr := addr;
                                                                    MSI_state := enum MSI { I }
                                                                 });
            Ob~0~0~0~0
          else Ob~0~0~0~0
    }}.

  (* If Core is trying to load,
   * - if other has state M, issue downgrade request to S and grab line from them
   * - if no one has state M, issue memory request
   *   (then give core state S)
   *
   * If Core is trying to store,
   * - for al with state M or S, issue downgrade request to I
   * - if other has state M, grab line from them
   *     else issue memory request
   *   (core is then given state M)
   *)
  Definition receive_upgrade_requests: uaction reg_t ext_fn_t :=
    {{
        let ushr := read0(private ushr) in
        guard (!FromRouter.(MessageFifo1.has_resp)() &&
                FromRouter.(MessageFifo1.has_req)() &&
                (get(ushr, state) == enum USHR_state { Ready })
              );
        let req := get(FromRouter.(MessageFifo1.deq)(),req) in
        let addr := get(req,addr) in

        let tag := getTag(addr) in
        let index := getIndex(addr) in
        let core_id := get(req,core_id) in
        let other_core_has_line := has_line(index, tag, !core_id) in
        write0(private bypass, {invalid (data_t)}());
        (* Load *)
        if (get(req,MSI_state) == enum MSI { S }) then
          write0(private ushr, struct USHR { state := enum USHR_state { Confirming };
                                               req := req });
          if (other_core_has_line) then
            (* Parent !get(req,core_id) has the line, issue downgrade to S *)
            ToRouter.(MessageFifo1.enq_req)(struct cache_mem_req { core_id := !core_id;
                                                                    cache_type := enum cache_type { dmem };
                                                                    addr := addr;
                                                                    MSI_state := enum MSI { S }
                                                                 })
          else
            (* No one has the line, request from memory *)
            ToMem.(MemReq.enq)(struct mem_req { byte_en := Ob~0~0~0~0;
                                                 addr := addr;
                                                 data := |32`d0| })
        (* Store *)
        else if (get(req,MSI_state) == enum MSI { M }) then
          (when (!other_core_has_line &&
                  (get_state(core_id, get(req,cache_type), index, tag) == enum MSI { I })
                ) do
            (* Request line from main memory *)
            ToMem.(MemReq.enq)(struct mem_req { byte_en := Ob~0~0~0~0;
                                                 addr := addr;
                                                 data := |32`d0| }));
          (* For all lines that are M/S, downgrade to I: it's either the case that
           * there is one M core (others I), or mix of S/I cores *)
          let downgrade_tracker :=
              set_invalid_at_cache(compute_downgrade_tracker(index, tag),
                                   core_id, get(req, cache_type)) in
          let tracker2 := do_downgrade_from_tracker(addr, downgrade_tracker) in
          write0(private downgrade_tracker, tracker2);
          if (tracker2 == |4`d0|) then
            (* done issuing downgrade requests *)
            write0(private ushr, struct USHR { state := enum USHR_state { Downgrading };
                                                 req := req })
          else
            write0(private ushr, struct USHR { state := enum USHR_state { Confirming };
                                                 req := req })
        else pass (* Should not happen? Could do fail for ease of debugging *)
    }}.

  Definition issue_downgrades: uaction reg_t ext_fn_t :=
    {{
        let ushr := read0(private ushr) in
        guard(get(ushr, state) == enum USHR_state { Downgrading });
        let req := get(ushr,req) in
        let tracker := read0(private downgrade_tracker) in
        let tracker2 := do_downgrade_from_tracker(get(req,addr), tracker) in
        write0(private downgrade_tracker, tracker2);
        (when (tracker2 == |4`d0|) do
            (write0(private ushr, struct USHR { state := enum USHR_state { Confirming };
                                                 req := req })))
    }}.

  Definition dummy_cache_mem_req : struct_t cache_mem_req := value_of_bits (Bits.zero).

  Definition confirm_downgrades: uaction reg_t ext_fn_t :=
    {{ let ushr := read0(private ushr) in
       guard(get(ushr, state) == enum USHR_state { Confirming });
       let req := get(ushr,req) in
       let addr := get(req,addr) in
       (* Either load req, or store req and all states are invalid other than core's *)
       let states := compute_downgrade_tracker (getIndex(addr), getTag(addr)) in
       let states2 := set_invalid_at_cache(states, get(req,core_id),get(req,cache_type)) in
       if ((get(req, MSI_state) == enum MSI { S }) ||
           states2 == Ob~0~0~0~0) then
         let data := {invalid (data_t)}() in
         let bypass_opt := read1(private bypass) in
         (
           (* if (getState(addr,child) != I) then *)
         if (states[cache_encoding(get(req,core_id), get(req,cache_type))]) then
            pass (* (data = invalid) *)
         else if (get(bypass_opt,valid)) then
              set data := bypass_opt
         else
           let resp := FromMem.(MemResp.deq)() in
           set data := {valid data_t} (get(resp, data))
         );
         (* Parent sending response to child *)
         ToRouter.(MessageFifo1.enq_resp)(
                      struct cache_mem_resp { core_id := get(req, core_id);
                                               cache_type := get(req, cache_type);
                                               addr := addr;
                                               MSI_state := get(req, MSI_state);
                                               data := data
                                            });
         let input := struct bookkeeping_input
                            { idx := getIndex(addr);
                               book := {valid (struct_t Bookkeeping_row)}(
                                           struct Bookkeeping_row { state := get(req, MSI_state);
                                                                     tag := getTag(addr)
                                                                  });
                               core_id := get(req,core_id);
                               cache_type := get(req, cache_type)
                           } in
         ignore(extcall ext_ppp_bookkeeping (input));
         write0(private ushr, struct USHR { state := enum USHR_state { Ready };
                                              req := `UConst dummy_cache_mem_req` })
       else pass
    }}.

  (*
  Definition forward_req: uaction reg_t empty_ext_fn_t :=
    {{
        let ushr := read0(private ushr) in
        guard (!FromRouter.(MessageFifo1.has_resp)() &&
                FromRouter.(MessageFifo1.has_req)() &&
                (get(ushr, state) == enum USHR_state { Ready })
              );
        let req := get(FromRouter.(MessageFifo1.deq)(),req) in
        (* For now, just forward *)
        ToMem.(MemReq.enq)(struct mem_req { byte_en := Ob~0~0~0~0;
                                             addr := get(req,addr);
                                             data := |32`d0| });
        write0(private ushr, struct USHR { state := enum USHR_state { Confirming };
                                             req := req })
    }}.
    *)

    (*
  Definition dummy_cache_mem_req : struct_t cache_mem_req := value_of_bits (Bits.zero).

  Definition forward_resp_from_mem : uaction reg_t empty_ext_fn_t :=
    {{ let ushr := read0(private ushr) in
       guard(get(ushr, state) == enum USHR_state { Confirming });
       let resp := FromMem.(MemResp.deq)() in
       let req_info := get(ushr, req) in
       ToRouter.(MessageFifo1.enq_resp)(
                    struct cache_mem_resp { core_id := get(req_info, core_id);
                                             cache_type := get(req_info, cache_type);
                                             addr := get(resp, addr);
                                             MSI_state := get(req_info, MSI_state);
                                             data := {valid data_t} (get(resp, data))
                                          });
       write0(private ushr, struct USHR { state := enum USHR_state { Ready };
                                            req := `UConst dummy_cache_mem_req` })
    }}.
    *)

  Inductive rule_name_t :=
  | Rl_ReceiveResp
  | Rl_ReceiveUpgradeReqs
  | Rl_IssueDowngrades
  | Rl_ConfirmDowngrades.

  Definition rule := rule R Sigma.

  Definition tc_receiveResp := tc_rule R Sigma receive_responses <: rule.
  Definition tc_receiveUpgradeReqs := tc_rule R Sigma receive_upgrade_requests <: rule.
  Definition tc_issueDowngrades := tc_rule R Sigma issue_downgrades <: rule.
  Definition tc_confirmDowngrades := tc_rule R Sigma confirm_downgrades <: rule.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | Rl_ReceiveResp => tc_receiveResp
    | Rl_ReceiveUpgradeReqs => tc_receiveUpgradeReqs
    | Rl_IssueDowngrades => tc_issueDowngrades
    | Rl_ConfirmDowngrades => tc_confirmDowngrades
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Rl_ReceiveResp |> Rl_ReceiveUpgradeReqs |> Rl_IssueDowngrades |> Rl_ConfirmDowngrades |> done.

End ProtocolProcessor.

Module MainMem.
  Import Common.
  Inductive reg_t :=
  | FromProto (state: MemReq.reg_t)
  | ToProto   (state: MemResp.reg_t)
  .

  Definition R idx : type :=
    match idx with
    | FromProto st => MemReq.R st
    | ToProto st => MemResp.R st
    end.

  Import External.

  Definition ext_fn_t := External.ext_fn_t.
  Definition Sigma := External.Sigma.
  Definition rule := rule R Sigma.

  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_LED_ADDRESS  := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.

  Definition mainMemoryBus : UInternalFunction reg_t ext_fn_t :=
    {{ fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1) (put_request: struct_t mem_req) : struct_t mem_output=>
       extcall (ext_mainmem)
               (struct mem_input {
                          get_ready := get_ready;
                          put_valid := put_valid;
                          put_request := put_request })
    }}.

  Definition mem : uaction reg_t ext_fn_t :=
    let fromMem := ToProto in
    let toMem := FromProto in
    {{
        let get_ready := fromMem.(MemResp.can_enq)() in
        let put_request_opt := toMem.(MemReq.peek)() in
        let put_request := get(put_request_opt, data) in
        let put_valid := get(put_request_opt, valid) in
        let mem_out := mainMemoryBus(get_ready, put_valid, put_request) in
        (when (get_ready && get(mem_out, get_valid)) do fromMem.(MemResp.enq)(get(mem_out, get_response)));
        (when (put_valid && get(mem_out, put_ready)) do ignore(toMem.(MemReq.deq)()))
    }}.

  Definition tc_mem := tc_rule R Sigma mem <: rule.

  Inductive rule_name_t :=
  | Rl_mem
  .

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | Rl_mem => tc_mem
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Rl_mem |> done.

End MainMem.

Module WIPMemory <: Memory_sig External EnclaveParams.
  Import Common.

  (* This memory has two L1 I&D caches, a message router, and protocol processor, and the main memory.
   * TODO: next we will add a L2 cache.
   *)

  Import CacheTypes.

  Import Mem_Common.

  Module Params_Core0IMem <: CacheParams.
    Definition _core_id := CoreId0.
    Definition _cache_type := CacheType_Imem.
  End Params_Core0IMem.

  Module Params_Core0DMem <: CacheParams.
    Definition _core_id := CoreId0.
    Definition _cache_type := CacheType_Dmem.
  End Params_Core0DMem.

  Module Params_Core1IMem <: CacheParams.
    Definition _core_id := CoreId1.
    Definition _cache_type := CacheType_Imem.
  End Params_Core1IMem.

  Module Params_Core1DMem <: CacheParams.
    Definition _core_id := CoreId1.
    Definition _cache_type := CacheType_Dmem.
  End Params_Core1DMem.

  Module Core0IMem := Cache Params_Core0IMem.
  Module Core0DMem := Cache Params_Core0DMem.
  Module Core1IMem := Cache Params_Core1IMem.
  Module Core1DMem := Cache Params_Core1DMem.

  (* TODO: In theory we would do this in a more modular way, but we simplify for now.
   *)
  Inductive private_reg_t :=
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
  | ProtoToMem (state: MemReq.reg_t)
  | MemToProto (state: MemResp.reg_t)
  | Router_private (state: MessageRouter.private_reg_t)
  | Proto_private (state: ProtocolProcessor.private_reg_t)
  | Core0I_private (state: Core0IMem.private_reg_t)
  | Core0D_private (state: Core0DMem.private_reg_t)
  | Core1I_private (state: Core1IMem.private_reg_t)
  | Core1D_private (state: Core1DMem.private_reg_t)
  .

  Definition R_private (idx: private_reg_t) : type :=
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
    | ProtoToMem st => MemReq.R st
    | MemToProto st => MemResp.R st
    | Router_private st => MessageRouter.R_private st
    | Proto_private st => ProtocolProcessor.R_private st
    | Core0I_private st => Core0IMem.R_private st
    | Core0D_private st => Core0DMem.R_private st
    | Core1I_private st => Core1IMem.R_private st
    | Core1D_private st => Core1DMem.R_private st
    end.

  Definition r_private (idx: private_reg_t) : R_private idx :=
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
    | ProtoToMem st => MemReq.r st
    | MemToProto st => MemResp.r st
    | Router_private st => MessageRouter.r_private st
    | Proto_private st => ProtocolProcessor.r_private st
    | Core0I_private st => Core0IMem.r_private st
    | Core0D_private st => Core0DMem.r_private st
    | Core1I_private st => Core1IMem.r_private st
    | Core1D_private st => Core1DMem.r_private st
    end.

  (* Declare Instance FiniteType_private_reg_t : FiniteType private_reg_t. *)
  Instance FiniteType_private_reg_t : FiniteType private_reg_t := _.

  Definition private_params : private_module_sig :=
    {| _private_reg_t := private_reg_t;
       _R_private := R_private;
       _r_private := r_private;
       _FiniteType_private_reg_t := FiniteType_private_reg_t
    |}.

  Definition reg_t := @Mem_Common.reg_t private_params.
  Definition r := @Mem_Common.r private_params.
  Definition R := @Mem_Common.R private_params.

  Instance FiniteType_reg_t : FiniteType reg_t := @Mem_Common.FiniteType_reg_t private_params.
  Definition rule := @Mem_Common.rule private_params External.ext.
  Definition sigma := @Mem_Common.sigma External.ext.

  Notation "'__private__' instance " :=
    (fun reg => private ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'__public__' instance " :=
    (fun reg => public ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Import External.

  (* =============== Lifts ================ *)
  Notation private := (@private private_params).

  Section Core0_IMemLift.

    Definition core0_imem_lift (reg: Core0IMem.reg_t) : reg_t :=
      match reg with
      | Core0IMem.fromMem st => (private (RouterToCore0I st))
      | Core0IMem.toMem st => (private (core0IToRouter st))
      | Core0IMem.private st => (private (Core0I_private st))
      end.

    Definition Lift_core0_imem : RLift _ Core0IMem.reg_t reg_t Core0IMem.R R := ltac:(mk_rlift core0_imem_lift).
    Definition FnLift_core0_imem : RLift _ Core0IMem.ext_fn_t ext_fn_t Core0IMem.Sigma Sigma := ltac:(lift_auto).

  End Core0_IMemLift.

  Section Core0_DMemLift.
    Definition core0_dmem_lift (reg: Core0DMem.reg_t) : reg_t :=
      match reg with
      | Core0DMem.fromMem st => (private (RouterToCore0D st))
      | Core0DMem.toMem st => (private (core0DToRouter st))
      | Core0DMem.private st => (private (Core0D_private st))
      end.

    Definition Lift_core0_dmem : RLift _ Core0DMem.reg_t reg_t Core0DMem.R R := ltac:(mk_rlift core0_dmem_lift).
    Definition FnLift_core0_dmem : RLift _ Core0DMem.ext_fn_t ext_fn_t Core0DMem.Sigma Sigma := ltac:(lift_auto).

  End Core0_DMemLift.

  Section Core1_IMemLift.
    Definition core1_imem_lift (reg: Core1IMem.reg_t) : reg_t :=
      match reg with
      | Core1IMem.fromMem st => (private (RouterToCore1I st))
      | Core1IMem.toMem st => (private (core1IToRouter st))
      | Core1IMem.private st => (private (Core1I_private st))
      end.

    Definition Lift_core1_imem : RLift _ Core1IMem.reg_t reg_t Core1IMem.R R := ltac:(mk_rlift core1_imem_lift).
    Definition FnLift_core1_imem : RLift _ Core1IMem.ext_fn_t ext_fn_t Core1IMem.Sigma Sigma := ltac:(lift_auto).

  End Core1_IMemLift.

  Section Core1_DMemLift.
    Definition core1_dmem_lift (reg: Core1DMem.reg_t) : reg_t :=
      match reg with
      | Core1DMem.fromMem st => (private (RouterToCore1D st))
      | Core1DMem.toMem st => (private (core1DToRouter st))
      | Core1DMem.private st => (private (Core1D_private st))
      end.

    Definition Lift_core1_dmem : RLift _ Core1DMem.reg_t reg_t Core1DMem.R R := ltac:(mk_rlift core1_dmem_lift).
    Definition FnLift_core1_dmem : RLift _ Core1DMem.ext_fn_t ext_fn_t Core1DMem.Sigma Sigma := ltac:(lift_auto).

  End Core1_DMemLift.

  (* TODO: Core1 *)
  Section MessageRouterLift.
    Definition router_lift (reg: MessageRouter.reg_t) : reg_t :=
    match reg with
    | MessageRouter.FromCore0I st => (private (core0IToRouter st))
    | MessageRouter.FromCore0D st => (private (core0DToRouter st))
    | MessageRouter.FromCore1I st => (private (core1IToRouter st))
    | MessageRouter.FromCore1D st => (private (core1DToRouter st))
    | MessageRouter.ToCore0I st => (private (RouterToCore0I st))
    | MessageRouter.ToCore0D st => (private (RouterToCore0D st))
    | MessageRouter.ToCore1I st => (private (RouterToCore1I st))
    | MessageRouter.ToCore1D st => (private (RouterToCore1D st))
    | MessageRouter.ToProto st => (private (RouterToProto st))
    | MessageRouter.FromProto st => (private (ProtoToRouter st))
    | MessageRouter.private st => (private (Router_private st))
    end.

    Definition Lift_router : RLift _ MessageRouter.reg_t reg_t MessageRouter.R R := ltac:(mk_rlift router_lift).
    Definition FnLift_router : RLift _ MessageRouter.ext_fn_t ext_fn_t MessageRouter.Sigma Sigma := ltac:(lift_auto).

  End MessageRouterLift.

  Section ProtocolProcessorLift.

    Definition proto_lift (reg: ProtocolProcessor.reg_t) : reg_t :=
    match reg with
    | ProtocolProcessor.FromRouter st => (private (RouterToProto st))
    | ProtocolProcessor.ToRouter st => (private (ProtoToRouter st ))
    | ProtocolProcessor.ToMem st => (private (ProtoToMem st))
    | ProtocolProcessor.FromMem st => (private (MemToProto st))
    | ProtocolProcessor.private st => (private (Proto_private st))
    end.

    Definition Lift_proto : RLift _ ProtocolProcessor.reg_t reg_t ProtocolProcessor.R R := ltac:(mk_rlift proto_lift).
    Definition FnLift_proto : RLift _ ProtocolProcessor.ext_fn_t ext_fn_t ProtocolProcessor.Sigma Sigma := ltac:(lift_auto).

  End ProtocolProcessorLift.

  Section MainMemLift.
    Definition main_mem_lift (reg: MainMem.reg_t) : reg_t :=
      match reg with
      | MainMem.FromProto st => private (ProtoToMem st)
      | MainMem.ToProto st => private (MemToProto st)
      end.

    Definition Lift_main_mem: RLift _ MainMem.reg_t reg_t MainMem.R R := ltac:(mk_rlift main_mem_lift).
    Definition FnLift_main_mem: RLift _ MainMem.ext_fn_t ext_fn_t MainMem.Sigma Sigma := ltac:(lift_auto).
  End MainMemLift.

  (* TODO: slow *)

  Instance FiniteType_ext_reg_t : FiniteType public_reg_t := _.
  (* Instance FiniteType_reg_t : FiniteType reg_t := _. *)
  (* Declare Instance FiniteType_reg_t : FiniteType reg_t.   *)
  Instance EqDec_reg_t : EqDec reg_t := _.

  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_LED_ADDRESS  := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.

  Definition memoryBus (m: External.cache) : UInternalFunction reg_t ext_fn_t :=
    {{ fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1) (put_request: struct_t mem_req)
         : maybe (struct_t mem_output) =>
         `match m with
          | (imem0 | imem1) => {{ {invalid (struct_t mem_output) }() }}
          | (dmem0 | dmem1) => {{
                      let addr := get(put_request, addr) in
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
                        let ready := extcall ext_uart_write (struct (Maybe (bits_t 8)) {
                          valid := may_run; data := char }) in
                        {valid (struct_t mem_output)}(
                          struct mem_output { get_valid := may_run && ready;
                                               put_ready := may_run && ready;
                                               get_response := struct mem_resp {
                                                 byte_en := byte_en; addr := addr;
                                                 data := |32`d0| } })

                      else if is_uart_read then
                        let may_run := get_ready && put_valid && is_uart_read in
                        let opt_char := extcall ext_uart_read (may_run) in
                        let ready := get(opt_char, valid) in
                        {valid (struct_t mem_output)}(
                          struct mem_output { get_valid := may_run && ready;
                                               put_ready := may_run && ready;
                                               get_response := struct mem_resp {
                                                 byte_en := byte_en; addr := addr;
                                                 data := zeroExtend(get(opt_char, data), 32) } })

                      else if is_led then
                        let on := get(put_request, data)[|5`d0|] in
                        let may_run := get_ready && put_valid && is_led_write in
                        let current := extcall ext_led (struct (Maybe (bits_t 1)) {
                          valid := may_run; data := on }) in
                        let ready := Ob~1 in
                        {valid (struct_t mem_output)}(
                          struct mem_output { get_valid := may_run && ready;
                                               put_ready := may_run && ready;
                                               get_response := struct mem_resp {
                                                 byte_en := byte_en; addr := addr;
                                                 data := zeroExtend(current, 32) } })

                      else
                        {invalid (struct_t mem_output)}()
                   }}
          end` }} .

  Section SystemRules.
    (* TODO: stop duplicating, need to do lifts properly *)
    Definition memCore0I : uaction reg_t ext_fn_t :=
      {{
          guard(read0(public purge0) == enum purge_state { Ready });
          let get_ready := (__public__ fromIMem0).(MemResp.can_enq)() in
          let put_request_opt := (__public__ toIMem0).(MemReq.peek)() in
          let put_request := get(put_request_opt, data) in
          let put_valid := get(put_request_opt, valid) in

          let mem_out_opt := {memoryBus imem0}(get_ready, put_valid, put_request) in
          if (get(mem_out_opt,valid)) then
            (* valid output *)
            let mem_out := get(mem_out_opt,data) in
            (when (get_ready && get(mem_out, get_valid)) do (__public__ fromIMem0).(MemResp.enq)(get(mem_out, get_response)));
            (when (put_valid && get(mem_out, put_ready)) do ignore((__public__ toIMem0).(MemReq.deq)()))
          else
            (* TODO: these rules can fail *)
            (when (put_valid && (`core0_imem_lift`).(Core0IMem.can_send_req)()) do (
              ignore((__public__ toIMem0).(MemReq.deq)());
              (`core0_imem_lift`).(Core0IMem.req)(put_request)
            ));
            (when (get_ready && (`core0_imem_lift`).(Core0IMem.can_recv_resp)()) do (
              let resp := (`core0_imem_lift`).(Core0IMem.resp)() in
              (__public__ fromIMem0).(MemResp.enq)(resp))
            )
      }}.

    Definition tc_memCore0I := tc_rule R Sigma memCore0I <: rule.

    Definition memCore0D : uaction reg_t ext_fn_t :=
      {{
          guard(read0(public purge0) == enum purge_state { Ready });
          let get_ready := (__public__ fromDMem0).(MemResp.can_enq)() in
          let put_request_opt := (__public__ toDMem0).(MemReq.peek)() in
          let put_request := get(put_request_opt, data) in
          let put_valid := get(put_request_opt, valid) in

          let mem_out_opt := {memoryBus dmem0}(get_ready, put_valid, put_request) in
          if (get(mem_out_opt,valid)) then
            (* valid output *)
            let mem_out := get(mem_out_opt,data) in
            (when (get_ready && get(mem_out, get_valid)) do (__public__ fromDMem0).(MemResp.enq)(get(mem_out, get_response)));
            (when (put_valid && get(mem_out, put_ready)) do ignore((__public__ toDMem0).(MemReq.deq)()))
          else
            (* TODO: these rules can fail *)
            (when (put_valid && (`core0_dmem_lift`).(Core0DMem.can_send_req)()) do (
              ignore((__public__ toDMem0).(MemReq.deq)());
              (`core0_dmem_lift`).(Core0DMem.req)(put_request)
            ));
            (when (get_ready && (`core0_dmem_lift`).(Core0DMem.can_recv_resp)()) do (
              let resp := (`core0_dmem_lift`).(Core0DMem.resp)() in
              (__public__ fromDMem0).(MemResp.enq)(resp))
            )
      }}.

    Definition tc_memCore0D := tc_rule R Sigma memCore0D <: rule.

    Definition memCore1I : uaction reg_t ext_fn_t :=
      {{
          guard(read0(public purge1) == enum purge_state { Ready });
          let get_ready := (__public__ fromIMem1).(MemResp.can_enq)() in
          let put_request_opt := (__public__ toIMem1).(MemReq.peek)() in
          let put_request := get(put_request_opt, data) in
          let put_valid := get(put_request_opt, valid) in

          let mem_out_opt := {memoryBus imem1}(get_ready, put_valid, put_request) in
          if (get(mem_out_opt,valid)) then
            (* valid output *)
            let mem_out := get(mem_out_opt,data) in
            (when (get_ready && get(mem_out, get_valid)) do (__public__ fromIMem1).(MemResp.enq)(get(mem_out, get_response)));
            (when (put_valid && get(mem_out, put_ready)) do ignore((__public__ toIMem1).(MemReq.deq)()))
          else
            (* TODO: these rules can fail *)
            (when (put_valid && (`core1_imem_lift`).(Core1IMem.can_send_req)()) do (
              ignore((__public__ toIMem1).(MemReq.deq)());
              (`core1_imem_lift`).(Core1IMem.req)(put_request)
            ));
            (when (get_ready && (`core1_imem_lift`).(Core1IMem.can_recv_resp)()) do (
              let resp := (`core1_imem_lift`).(Core1IMem.resp)() in
              (__public__ fromIMem1).(MemResp.enq)(resp))
            )
      }}.

    Definition tc_memCore1I := tc_rule R Sigma memCore1I <: rule.

    Definition memCore1D : uaction reg_t ext_fn_t :=
      {{
          guard(read0(public purge1) == enum purge_state { Ready });
          let get_ready := (__public__ fromDMem1).(MemResp.can_enq)() in
          let put_request_opt := (__public__ toDMem1).(MemReq.peek)() in
          let put_request := get(put_request_opt, data) in
          let put_valid := get(put_request_opt, valid) in

          let mem_out_opt := {memoryBus dmem1}(get_ready, put_valid, put_request) in
          if (get(mem_out_opt,valid)) then
            (* valid output *)
            let mem_out := get(mem_out_opt,data) in
            (when (get_ready && get(mem_out, get_valid)) do (__public__ fromDMem1).(MemResp.enq)(get(mem_out, get_response)));
            (when (put_valid && get(mem_out, put_ready)) do ignore((__public__ toDMem1).(MemReq.deq)()))
          else
            (* TODO: these rules can fail *)
            (when (put_valid && (`core1_dmem_lift`).(Core1DMem.can_send_req)()) do (
              ignore((__public__ toDMem1).(MemReq.deq)());
              (`core1_dmem_lift`).(Core1DMem.req)(put_request)
            ));
            (when (get_ready && (`core1_dmem_lift`).(Core1DMem.can_recv_resp)()) do (
              let resp := (`core1_dmem_lift`).(Core1DMem.resp)() in
              (__public__ fromDMem1).(MemResp.enq)(resp))
            )
      }}.

    Definition tc_memCore1D := tc_rule R Sigma memCore1D <: rule.

    (* TODO *)
    Definition purge_placeholder0 : uaction reg_t ext_fn_t :=
      let purge_reg := public purge0 in
      {{
          let purge := read0(purge_reg) in
          if (purge == enum purge_state { Purging }) then
            (if (`core0_imem_lift`).(Core0IMem.can_recv_resp)() then
              ignore((`core0_imem_lift`).(Core0IMem.resp)())
             else pass);
            (if (`core0_dmem_lift`).(Core0DMem.can_recv_resp)() then
              ignore((`core0_dmem_lift`).(Core0DMem.resp)())
             else pass);
            (* TODO: placeholder until purge is actually implemented *)
            if (`core0_imem_lift`).(Core0IMem.is_ready)() &&
               (`core0_dmem_lift`).(Core0DMem.is_ready)() then
              write0(purge_reg, enum purge_state { Purged })
            else pass
          else if (purge == enum purge_state { Restart }) then
            write0(purge_reg, enum purge_state { Ready })
          else fail
      }}.

    Definition tc_purge0 := tc_rule R Sigma (purge_placeholder0) <: rule.

    Definition purge_placeholder1 : uaction reg_t ext_fn_t :=
      let purge_reg := public purge1 in
      {{
          let purge := read0(purge_reg) in
          if (purge == enum purge_state { Purging }) then
            (if (`core1_imem_lift`).(Core1IMem.can_recv_resp)() then
              ignore((`core1_imem_lift`).(Core1IMem.resp)())
             else pass);
            (if (`core1_dmem_lift`).(Core1DMem.can_recv_resp)() then
              ignore((`core1_dmem_lift`).(Core1DMem.resp)())
             else pass);
            (* TODO: placeholder until purge is actually implemented *)
            if (`core1_imem_lift`).(Core1IMem.is_ready)() &&
               (`core1_dmem_lift`).(Core1DMem.is_ready)() then
              write0(purge_reg, enum purge_state { Purged })
            else pass
          else if (purge == enum purge_state { Restart }) then
            write0(purge_reg, enum purge_state { Ready })
          else fail
      }}.

    Definition tc_purge1 := tc_rule R Sigma (purge_placeholder1) <: rule.

    (*
    Definition do_purge0 : uaction reg_t ext_fn_t :=
      {{
          guard(read0(purge0) == enum purge_state { Purging });
          let imem_done_flush := (`core0_imem_lift`).(Core0IMem.do_flush)() in
          let dmem_done_flush := (`core0_dmem_lift`).(Core0DMem.do_flush)() in
          if (imem_done_flush && dmem_done_flush) then
            write0(purge0, enum purge_state { Purged })
          else
            pass
      }}.
      *)

    Inductive SystemRule :=
    | SysRl_MemCore0I
    | SysRl_MemCore0D
    | SysRl_MemCore1I
    | SysRl_MemCore1D
    | SysRl_Purge0
    | SysRl_Purge1
    .

    Definition system_rules (rl: SystemRule) : rule :=
      match rl with
      | SysRl_MemCore0I => tc_memCore0I
      | SysRl_MemCore0D => tc_memCore0D
      | SysRl_MemCore1I => tc_memCore1I
      | SysRl_MemCore1D => tc_memCore1D
      | SysRl_Purge0 => tc_purge0
      | SysRl_Purge1 => tc_purge1
      end.

    Definition private_system_schedule : Syntax.scheduler pos_t SystemRule :=
      SysRl_MemCore0I |> SysRl_MemCore0D |> SysRl_MemCore1I |> SysRl_MemCore1D |>
                         SysRl_Purge0 |> SysRl_Purge1 |> done.

  End SystemRules.

  Section Rules.
    Inductive rule_name_t' :=
    | Rl_System (r: SystemRule)
    | Rl_Core0IMem (r: Core0IMem.rule_name_t)
    | Rl_Core0DMem (r: Core0DMem.rule_name_t)
    | Rl_Core1IMem (r: Core1IMem.rule_name_t)
    | Rl_Core1DMem (r: Core1DMem.rule_name_t)
    | Rl_Proto (r: ProtocolProcessor.rule_name_t)
    | Rl_Router (r: MessageRouter.rule_name_t)
    | Rl_MainMem (r: MainMem.rule_name_t)
    .

    Definition rule_name_t := rule_name_t'.

    Definition core0I_rule_name_lift (rl: Core0IMem.rule_name_t) : rule_name_t :=
      Rl_Core0IMem rl.

    Definition core0D_rule_name_lift (rl: Core0DMem.rule_name_t) : rule_name_t :=
      Rl_Core0DMem rl.

    Definition core1I_rule_name_lift (rl: Core1IMem.rule_name_t) : rule_name_t :=
      Rl_Core1IMem rl.

    Definition core1D_rule_name_lift (rl: Core1DMem.rule_name_t) : rule_name_t :=
      Rl_Core1DMem rl.

    Definition proto_rule_name_lift (rl: ProtocolProcessor.rule_name_t) : rule_name_t :=
      Rl_Proto rl.

    Definition router_rule_name_lift (rl: MessageRouter.rule_name_t) : rule_name_t :=
      Rl_Router rl.

    Definition main_mem_name_lift (rl: MainMem.rule_name_t) : rule_name_t :=
      Rl_MainMem rl.

    Definition core0I_rules (rl: Core0IMem.rule_name_t) : rule :=
      lift_rule Lift_core0_imem FnLift_core0_imem (Core0IMem.rules rl).
    Definition core0D_rules (rl: Core0DMem.rule_name_t) : rule :=
      lift_rule Lift_core0_dmem FnLift_core0_dmem (Core0DMem.rules rl).
    Definition core1I_rules (rl: Core1IMem.rule_name_t) : rule :=
      lift_rule Lift_core1_imem FnLift_core1_imem (Core1IMem.rules rl).
    Definition core1D_rules (rl: Core1DMem.rule_name_t) : rule :=
      lift_rule Lift_core1_dmem FnLift_core1_dmem (Core1DMem.rules rl).
    Definition proto_rules (rl: ProtocolProcessor.rule_name_t) : rule :=
      lift_rule Lift_proto FnLift_proto (ProtocolProcessor.rules rl).
    Definition router_rules (rl: MessageRouter.rule_name_t) : rule :=
      lift_rule Lift_router FnLift_router (MessageRouter.rules rl).
    Definition main_mem_rules (rl: MainMem.rule_name_t) : rule :=
      lift_rule Lift_main_mem FnLift_main_mem (MainMem.rules rl).

    Definition rules (rl: rule_name_t) : rule :=
      match rl with
      | Rl_System r => system_rules r
      | Rl_Core0IMem r => core0I_rules r
      | Rl_Core0DMem r => core0D_rules r
      | Rl_Core1IMem r => core1I_rules r
      | Rl_Core1DMem r => core1D_rules r
      | Rl_Proto r => proto_rules r
      | Rl_Router r => router_rules r
      | Rl_MainMem r => main_mem_rules r
     end.

  End Rules.

  Section Schedule.
    Definition system_schedule := lift_scheduler Rl_System private_system_schedule.
    Definition core0I_schedule := lift_scheduler Rl_Core0IMem Core0IMem.schedule.
    Definition core0D_schedule := lift_scheduler Rl_Core0DMem  Core0DMem.schedule.
    Definition core1I_schedule := lift_scheduler Rl_Core1IMem Core1IMem.schedule.
    Definition core1D_schedule := lift_scheduler Rl_Core1DMem  Core1DMem.schedule.
    Definition proto_schedule := lift_scheduler Rl_Proto ProtocolProcessor.schedule.
    Definition router_schedule := lift_scheduler Rl_Router MessageRouter.schedule.
    Definition main_mem_schedule := lift_scheduler Rl_MainMem MainMem.schedule.

    Definition schedule :=
      system_schedule ||> core0I_schedule ||> core0D_schedule
                      ||> core1I_schedule ||> core1D_schedule
                      ||> router_schedule
                      ||> proto_schedule ||> main_mem_schedule.

  End Schedule.

  Parameter private_external_state_t : Type.
  Parameter initial_private_external_state : private_external_state_t.

  Definition koika_state_t := @Mem_Common.koika_state_t private_params.
  Definition external_state_t := @Mem_Common.external_state_t private_external_state_t.
  Definition initial_external_state (dram: dram_t) : external_state_t :=
    (@Mem_Common.initial_external_state _ initial_private_external_state dram).
  Definition state := @Mem_Common.state private_params private_external_state_t.

  Parameter external_update_function: state -> Log R ContextEnv -> Log R ContextEnv * external_state_t.

  Parameter output_correctness : @P_output_correctness private_params External.ext EnclaveParams.params
                                                       rule_name_t rules schedule
                                                       private_external_state_t
                                                       initial_private_external_state
                                                       external_update_function.
  Parameter correctness : @P_correctness private_params External.ext EnclaveParams.params
                                         rule_name_t rules schedule
                                         private_external_state_t
                                         initial_private_external_state
                                         external_update_function.
  Parameter compliance: @P_compliance private_params External.ext EnclaveParams.params
                                      rule_name_t rules schedule
                                      private_external_state_t
                                      initial_private_external_state
                                      external_update_function.


End WIPMemory.

(*
Module SimpleMemory <: Memory_sig OriginalExternal.
  Import Common.

  (* TOOD: Silly workaround due to extraction issues: https://github.com/coq/coq/issues/12124 *)
  Inductive private_reg_t' : Type :=
  | Foo | Bar .

  Definition private_reg_t := private_reg_t'.

  Definition R_private (idx: private_reg_t) : type :=
    match idx with
    | Foo => bits_t 1
    | Bar => bits_t 1
    end.

  Definition r_private (idx: private_reg_t) : R_private idx :=
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
  | private (r: private_reg_t)
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
    | private st => R_private st
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
    | private st => r_private st
    end.

  Definition ext_fn_t := OriginalExternal.ext_fn_t.
  Definition Sigma := OriginalExternal.Sigma.
  Definition rule := rule R Sigma.
  (* Definition sigma := External.sigma. *)


  Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
  Definition MMIO_LED_ADDRESS  := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.

  Import OriginalExternal.

  Definition memoryBus (m: memory) : UInternalFunction reg_t ext_fn_t :=
    {{ fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1) (put_request: struct_t mem_req) : struct_t mem_output =>
         `match m with
          | imem =>  {{ extcall (ext_mem imem) (struct mem_input {
                         get_ready := get_ready;
                         put_valid := put_valid;
                         put_request := put_request }) }}
          | dmem =>  {{ let addr := get(put_request, addr) in
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
                         let ready := extcall ext_uart_write (struct (Maybe (bits_t 8)) {
                           valid := may_run; data := char }) in
                         struct mem_output { get_valid := may_run && ready;
                                              put_ready := may_run && ready;
                                              get_response := struct mem_resp {
                                                byte_en := byte_en; addr := addr;
                                                data := |32`d0| } }

                       else if is_uart_read then
                         let may_run := get_ready && put_valid && is_uart_read in
                         let opt_char := extcall ext_uart_read (may_run) in
                         let ready := get(opt_char, valid) in
                         struct mem_output { get_valid := may_run && ready;
                                              put_ready := may_run && ready;
                                              get_response := struct mem_resp {
                                                byte_en := byte_en; addr := addr;
                                                data := zeroExtend(get(opt_char, data), 32) } }

                       else if is_led then
                         let on := get(put_request, data)[|5`d0|] in
                         let may_run := get_ready && put_valid && is_led_write in
                         let current := extcall ext_led (struct (Maybe (bits_t 1)) {
                           valid := may_run; data := on }) in
                         let ready := Ob~1 in
                         struct mem_output { get_valid := may_run && ready;
                                              put_ready := may_run && ready;
                                              get_response := struct mem_resp {
                                                byte_en := byte_en; addr := addr;
                                                data := zeroExtend(current, 32) } }

                       else
                         extcall (ext_mem dmem) (struct mem_input {
                           get_ready := get_ready && is_mem;
                           put_valid := put_valid && is_mem;
                           put_request := put_request })
                   }}
          end` }}.

  (* TODO: not defined for main_mem *)
  Definition mem (m: memory) : uaction reg_t ext_fn_t :=
    let fromMem := match m with imem0 => fromIMem0 | dmem0 => fromDMem0 end in
    let toMem := match m with imem0 => toIMem0 | dmem0 => toDMem0 end in
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

  Instance FiniteType_private_reg_t : FiniteType private_reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.
End SimpleMemory.
*)
