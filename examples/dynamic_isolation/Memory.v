Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.
Require Import DynamicIsolation.RVEncoding.
Require Import DynamicIsolation.Scoreboard.
Require Import DynamicIsolation.Multiplier.

Require Import DynamicIsolation.External.
Require Import DynamicIsolation.Lift.
Require Import DynamicIsolation.Tactics.
Require Import DynamicIsolation.Interfaces.

(* Heavily inspired by http://csg.csail.mit.edu/6.175/labs/project-part1.html *)

Definition post_t := unit.
Definition var_t := string.
Definition fn_name_t := string.


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
                         ("MSI_state"   , enum_t MSI);
                         ("tmp_req", struct_t mem_req)
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

  (* TODO: We simplify:  *)


  Definition log_num_sets := 12.
  Definition log_tag_size := 18. (* 32 - 2 - 12 *)

  Definition cache_tag_t := bits_t log_tag_size. (* TODO  *)
  Definition cache_index_t := bits_t log_num_sets.
  (* TODO: avoiding Koika arrays for now. This should be an array based on the block size *)
  Definition cache_line_t := bits_t 32. 


  (* TODO: figure out syntax to write as a function of log size *)
  Definition getTag {reg_t}: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun getTag (addr: bits_t 32) : cache_tag_t =>
         addr[|5`d14|:+18]
    }}.

  Definition getIndex {reg_t}: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun getIndex (addr: bits_t 32) : cache_tag_t =>
         addr[|5`d2|:+12]
    }}.

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
                                   req := get(req_opt, data)
                                |}
   }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  (* TODO: Test this. *)
End MessageFifo1.

Module MessageRouter.
  Inductive internal_reg_t :=
  | routerTieBreaker (* To implement round robin fairness *)
  .

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | routerTieBreaker => bits_t 2
    end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
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
  | internal (state: internal_reg_t)
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
    | internal st => R_internal st
    end.

  Notation "'__internal__' instance " :=
    (fun reg => internal ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Import CacheTypes.

  Definition Sigma := empty_Sigma.
  Definition ext_fn_t := empty_ext_fn_t.
  Definition rule := rule R Sigma.

  (* ===================== Message routing rules ============================== *)
  Definition memToCore : uaction reg_t empty_ext_fn_t :=
    {{ let msg := FromProto.(MessageFifo1.deq)() in
       if (get(msg, type) == enum cache_mem_msg_tag {| Req |}) then
         let req := get(msg, req) in
         if (get(req, core_id) == Ob~0) then
           if (get(req, cache_type) == enum cache_type {| imem |}) then
             ToCore0I.(MessageFifo1.enq_req)(req)
           else
             ToCore0D.(MessageFifo1.enq_req)(req)
         else
           if (get(req, cache_type) == enum cache_type {| imem |}) then
             ToCore1I.(MessageFifo1.enq_req)(req)
           else
             ToCore1D.(MessageFifo1.enq_req)(req)
       else (* Resp *)
         let resp := get(msg, resp) in
         if (get(resp, core_id) == Ob~0) then
           if (get(resp, cache_type) == enum cache_type {| imem |}) then
             ToCore0I.(MessageFifo1.enq_resp)(resp)
           else
             ToCore0D.(MessageFifo1.enq_resp)(resp)
         else
           if (get(resp, cache_type) == enum cache_type {| imem |}) then
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
              write0(internal routerTieBreaker, tiebreaker + |2`d1|)
            )
         ));
         (when (!foundMsg) do (
            let curResp := getResp (tiebreaker+|2`d1|) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := {valid (struct_t cache_mem_msg)} (get(curResp, data));
              write0(internal routerTieBreaker, tiebreaker + |2`d2|)
            )
          ));
         (when (!foundMsg) do (
            let curResp := getResp (tiebreaker+|2`d2|) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := {valid (struct_t cache_mem_msg)} (get(curResp, data));
              write0(internal routerTieBreaker, tiebreaker + |2`d3|)
            )
          ));
         (when (!foundMsg) do (
            let curResp := getResp (tiebreaker+|2`d3|) in
            when (get(curResp, valid)) do (
              set foundMsg := Ob~1;
              set msg := {valid (struct_t cache_mem_msg)} (get(curResp, data));
              write0(internal routerTieBreaker, tiebreaker + |2`d4|)
            )
          ));
         msg
     }}.

  (* ======= Search for responses, starting with tiebreaker ====== *)
  Definition searchRequests : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun searchRequests (tiebreaker : bits_t 2) : maybe (struct_t cache_mem_msg) =>
         let foundMsg := Ob~0 in
         let msg := {invalid (struct_t cache_mem_msg)}() in
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker) in
            when (get(curReq, valid)) do (
              set foundMsg := Ob~1;
              set msg := curReq;
              write0(internal routerTieBreaker, tiebreaker + |2`d1|)
            )
          ));
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker+|2`d1|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := curReq;
             write0(internal routerTieBreaker, tiebreaker + |2`d2|)
           )
         ));
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker+|2`d2|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := curReq;
             write0(internal routerTieBreaker, tiebreaker + |2`d3|)
           )
         ));
         (when (!foundMsg) do (
           let curReq := getReq (tiebreaker+|2`d3|) in
           when (get(curReq, valid)) do (
             set foundMsg := Ob~1;
             set msg := curReq;
             write0(internal routerTieBreaker, tiebreaker + |2`d4|)
           )
         ));
         msg
     }}.

  Definition coreToMem : uaction reg_t empty_ext_fn_t :=
    {{ let tiebreaker := read0(internal routerTieBreaker) in
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
           write0(internal routerTieBreaker, tiebreaker + |2`d1|)
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
  Parameter core_id : Common.core_id_t.
  Parameter cache_type : enum_t CacheTypes.cache_type.
End CacheParams.

Module Cache (Params: CacheParams).
  Import CacheTypes.
  Import Common.

  (* Hard-coded for now: direct-mapped cache: #sets = #blocks; word-addressable *)
  
  Definition cache_row := 
    {| struct_name := "cache_row";
       struct_fields := [("tag", cache_tag_t);
                         ("data", cache_line_t);
                         ("flag", enum_t MSI)] |}.

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
  
  Inductive internal_reg_t :=
  | requestsQ (state: MemReq.reg_t)
  | responsesQ (state: MemResp.reg_t)
  | MSHR
  .

  Instance FiniteType_internal_reg_t : FiniteType internal_reg_t := _.

  Definition R_internal (idx: internal_reg_t) : type :=
    match idx with
    | requestsQ st => MemReq.R st
    | responsesQ st => MemResp.R st
    | mshr => struct_t MSHR_t
    end.

  Definition r_internal (idx: internal_reg_t) : R_internal idx :=
    match idx with
    | requestsQ st => MemReq.r st
    | responsesQ st => MemResp.r st
    | mshr => value_of_bits (Bits.zero)
    end.


  Inductive reg_t :=
  | fromMem (state: MessageFifo1.reg_t)
  | toMem (state: MessageFifo1.reg_t)
  | internal (state: internal_reg_t)
  .
  
  Definition R (idx: reg_t) : type :=
    match idx with
    | fromMem st => MessageFifo1.R st
    | toMem st => MessageFifo1.R st
    | internal st => R_internal st
    end.

  Notation "'__internal__' instance " :=
    (fun reg => internal ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Definition Sigma := empty_Sigma.
  Definition ext_fn_t := empty_ext_fn_t.

  (* Ready -> SendFillReq;
     SendFillReq -> WaitFillResp;
     WaitFillResp -> Ready
  *)

  (* Definition downgrade : uaction reg_t empty_ext_fn_t. Admitted. *)

  Definition dummy_mem_req : struct_t mem_req := value_of_bits (Bits.zero).
  Definition dummy_mem_resp : struct_t mem_resp := value_of_bits (Bits.zero).

  (* TOOD: for now, just assume miss and skip cache and forward to memory *)
  Definition dummy_process_request : uaction reg_t empty_ext_fn_t :=
    {{ 
        let mshr := read0(internal MSHR) in
        guard(get(mshr,mshr_tag) == enum mshr_tag {| Ready |});
        let req := (__internal__ requestsQ).(MemReq.deq)() in
        write0(internal MSHR, struct MSHR_t {| mshr_tag := enum mshr_tag {| SendFillReq |};
                                               req := req
                                            |})
                                               
    }}.

  Definition byte_en_to_msi_state : UInternalFunction reg_t empty_ext_fn_t := 
    {{ fun byte_en_to_msi_state (byte_en: bits_t 4) : enum_t MSI => 
         match byte_en with
         | Ob~0~0~0~0 => enum MSI {| S |}
         return default : enum MSI {| M |}
         end
    }}.

  Definition core_id := Params.core_id.
  Definition cache_type := Params.cache_type.

  Definition dummy_SendFillReq : uaction reg_t empty_ext_fn_t :=
    {{  
        let mshr := read0(internal MSHR) in
        guard(get(mshr,mshr_tag) == enum mshr_tag {| SendFillReq |});
        let mshr_req := get(mshr,req) in
        toMem.(MessageFifo1.enq_req)(
                  struct cache_mem_req {| core_id := (#core_id);
                                          cache_type := (`UConst (cache_type)`);
                                          addr := get(mshr_req, addr);
                                          MSI_state := (match get(mshr_req,byte_en) with
                                                        | Ob~0~0~0~0 => enum MSI {| S |}
                                                        return default : enum MSI {| M |}
                                                        end);
                                          tmp_req := mshr_req
                                       |});
        write0(internal MSHR, struct MSHR_t {| mshr_tag := enum mshr_tag {| WaitFillResp |};
                                               req := mshr_req
                                            |})
    }}.
 
  (* TODO: move to Std *)
  Section Maybe.
    Context (tau: type).

    Definition fromMaybe {reg_t fn}: UInternalFunction reg_t fn := 
      {{ fun fromMaybe (default: tau) (val: maybe tau) : tau =>
           if get(val, valid) then get(val, data)
           else default 
      }}. 
  End Maybe.
             

  (* If Store: do nothing in response *)
  (* If Load: send response *)
  Definition hit : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun hit (req: struct_t mem_req) (row: struct_t cache_row) : enum_t mshr_tag =>
         let new_state := enum mshr_tag {| Ready |} in
         if (get(req, byte_en) == Ob~0~0~0~0) then
           (__internal__ responsesQ).(MemResp.enq)(
             struct mem_resp {| addr := get(req, addr);
                                data := get(row,data);
                                byte_en := get(req, byte_en)
                             |})
         else (* TODO: commit data *)
           pass
         ;
         new_state
    }}.

  Definition dummy_WaitFillResp : uaction reg_t empty_ext_fn_t :=
    {{  
        let mshr := read0(internal MSHR) in
        guard(get(mshr,mshr_tag) == enum mshr_tag {| WaitFillResp |} &&
              fromMem.(MessageFifo1.has_resp)());
        let resp := get(fromMem.(MessageFifo1.deq)(),resp) in

        let req := get(mshr, req) in
        let row := struct cache_row {| tag := getTag(get(req, addr));
                                       data := {fromMaybe data_t}(|32`d0|, get(resp,data))
                                    |} in
        ignore(hit(req, row)); 
        write0(internal MSHR, struct MSHR_t {| mshr_tag := enum mshr_tag {| Ready |};
                                               req := (`UConst dummy_mem_req`)
                                            |})
    }}.
        
  Definition req: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun req (r: struct_t mem_req) : bits_t 0 =>
         let mshr := read0(internal MSHR) in
         guard(get(mshr,mshr_tag) == enum mshr_tag {| Ready |});
         (__internal__ requestsQ).(MemReq.enq)(r)
    }}.

  Definition resp: UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun resp () : struct_t mem_resp =>
         (__internal__ responsesQ).(MemResp.deq)()
    }}.

  Inductive rule_name_t :=
  | Rl_ProcessRequest
  | Rl_SendFillReq
  | Rl_WaitFillResp
  .

  Definition rule := rule R Sigma.

  Definition tc_processRequest := tc_rule R Sigma (dummy_process_request) <: rule.
  Definition tc_sendFillReq := tc_rule R Sigma (dummy_SendFillReq) <: rule.
  Definition tc_waitFillResp := tc_rule R Sigma (dummy_WaitFillResp) <: rule.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | Rl_ProcessRequest => tc_processRequest
    | Rl_SendFillReq => tc_sendFillReq
    | Rl_WaitFillResp => tc_waitFillResp
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Rl_ProcessRequest |> Rl_SendFillReq |> Rl_WaitFillResp |> done.
                   
End Cache.

Module ProtocolProcessor.
  Import Common.
  Import CacheTypes.

  (* TODO: Should be a DDR3_Req or similar, and should parameterise based on DDR3AddrSize/DataSize *)
  Inductive reg_t :=
  | FromRouter (state: MessageFifo1.reg_t)
  | ToRouter (state: MessageFifo1.reg_t)
  | ToMem (state: MemReq.reg_t)
  | FromMem (state: MemResp.reg_t)
  . 

  Definition R (idx: reg_t) : type := 
    match idx with
    | FromRouter st => MessageFifo1.R st
    | ToRouter st => MessageFifo1.R st
    | ToMem st => MemReq.R st
    | FromMem st => MemResp.R st
    end.

  Definition Sigma := empty_Sigma.
  Definition ext_fn_t := empty_ext_fn_t.

  (* For now: we assume everything is always invalid because the caches don't actually exist.  *)

  Definition forward_req : uaction reg_t empty_ext_fn_t :=
    {{ 
        guard (!FromRouter.(MessageFifo1.has_resp)() &&
                FromRouter.(MessageFifo1.has_req)()
              );
        let req := get(FromRouter.(MessageFifo1.deq)(),req) in
        (* Tmp: just forward *)
        ToMem.(MemReq.enq)(get(req, tmp_req))
    }}.

  Definition forward_resp_from_mem : uaction reg_t empty_ext_fn_t :=
    {{ let resp := FromMem.(MemResp.deq)() in
       FromMem.(MemResp.enq)(resp)
    }}.

  Inductive rule_name_t :=
  | Rl_ForwardReq
  | Rl_ForwardResp
  .

  Definition rule := rule R Sigma.

  Definition tc_forwardReq := tc_rule R Sigma (forward_req) <: rule.
  Definition tc_forwardResp := tc_rule R Sigma (forward_resp_from_mem) <: rule.

  Definition rules (rl: rule_name_t) : rule :=
    match rl with
    | Rl_ForwardReq => tc_forwardReq
    | Rl_ForwardResp => tc_forwardResp
    end.

  Definition schedule : Syntax.scheduler pos_t rule_name_t :=
    Rl_ForwardReq |> Rl_ForwardResp |> done.
                   
     (*
  Definition forward_resp : uaction reg_t empty_ext_fn_t :=
    {{ 
        guard (FromRouter.(MessageFifo1.has_resp)());
        let resp := FromRouter.(MessageFifo1.deq)() in
        let cid := get(resp, core_id) in
        let idx := getIndex (get(resp, addr)) in
        let resp_data := get(resp,data) in
        if (get(resp_data, valid)) then
          let req := struct mem_req {| addr := get(resp, addr);
                                       data := get(resp_data, data);
                                       byte_en := get(resp, byte_en)
                                    |} in
          ToMem.(MemReq.enq)(req)
        else pass
    }}.
    *)


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

  Definition memoryBus (m: memory) : UInternalFunction reg_t ext_fn_t :=
    {{ fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1) (put_request: struct_t mem_req) : struct_t mem_output =>
         `match m with
          | imem => {{ extcall (ext_mem m) (struct mem_input {|
                        get_ready := get_ready;
                        put_valid := put_valid;
                        put_request := put_request |}) }}
          | _    => {{
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
          end` }} .

  Definition mem : uaction reg_t ext_fn_t :=
    let fromMem := ToProto in
    let toMem := FromProto in
    {{
        let get_ready := fromMem.(MemResp.can_enq)() in
        let put_request_opt := toMem.(MemReq.peek)() in
        let put_request := get(put_request_opt, data) in
        let put_valid := get(put_request_opt, valid) in
        let mem_out := {memoryBus mainmem}(get_ready, put_valid, put_request) in
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

Module WIPMemory <: Memory_sig External.
  Import Common.

  (* This memory has two L1 I&D caches, a message router, and protocol processor, and the main memory.
   * TODO: next we will add a L2 cache.
   *)

  Import CacheTypes.

  Module Params_Core0IMem <: CacheParams.
    Definition core_id := Ob~0.
    Definition cache_type : enum_t cache_type := Ob~0. (* imem *)
  End Params_Core0IMem.

  Module Params_Core0DMem <: CacheParams.
    Definition core_id := Ob~0.
    Definition cache_type : enum_t cache_type := Ob~1. (* dmem *)
  End Params_Core0DMem.

  Module Params_Core1IMem <: CacheParams.
    Definition core_id := Ob~1.
    Definition cache_type : enum_t cache_type := Ob~0. (* imem *)
  End Params_Core1IMem.


  Module Params_Core1DMem <: CacheParams.
    Definition core_id := Ob~1.
    Definition cache_type : enum_t cache_type := Ob~1. (* dmem *)
  End Params_Core1DMem.

  Module Core0IMem := Cache Params_Core0IMem.
  Module Core0DMem := Cache Params_Core0DMem.
  Module Core1IMem := Cache Params_Core1IMem.
  Module Core1DMem := Cache Params_Core0DMem.

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
  | ProtoToMem (state: MemReq.reg_t)
  | MemToProto (state: MemResp.reg_t)
  | Router_internal (state: MessageRouter.internal_reg_t)
  | Core0I_internal (state: Core0IMem.internal_reg_t)
  | Core0D_internal (state: Core0DMem.internal_reg_t)
  | Core1I_internal (state: Core1IMem.internal_reg_t)
  | Core1D_internal (state: Core1DMem.internal_reg_t)
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
    | ProtoToMem st => MemReq.R st
    | MemToProto st => MemResp.R st
    | Router_internal st => MessageRouter.R_internal st
    | Core0I_internal st => Core0IMem.R_internal st
    | Core0D_internal st => Core0DMem.R_internal st
    | Core1I_internal st => Core1IMem.R_internal st
    | Core1D_internal st => Core1DMem.R_internal st
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
    | ProtoToMem st => MemReq.r st
    | MemToProto st => MemResp.r st
    | Router_internal st => MessageRouter.r_internal st
    | Core0I_internal st => Core0IMem.r_internal st
    | Core0D_internal st => Core0DMem.r_internal st
    | Core1I_internal st => Core1IMem.r_internal st
    | Core1D_internal st => Core1DMem.r_internal st
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

  Notation "'__internal__' instance " :=
    (fun reg => internal ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Notation "'(' instance ').(' method ')' args" :=
    (USugar (UCallModule instance _ method args))
      (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Import External.

  (* =============== Lifts ================ *)

  Section Core0_IMemLift.
    Definition core0_imem_lift (reg: Core0IMem.reg_t) : reg_t :=
      match reg with
      | Core0IMem.fromMem st => (internal (RouterToCore0I st))
      | Core0IMem.toMem st => (internal (core0IToRouter st))
      | Core0IMem.internal st => (internal (Core0I_internal st))
      end.

    Definition Lift_core0_imem : RLift _ Core0IMem.reg_t reg_t Core0IMem.R R := ltac:(mk_rlift core0_imem_lift).
    Definition FnLift_core0_imem : RLift _ Core0IMem.ext_fn_t ext_fn_t Core0IMem.Sigma Sigma := ltac:(lift_auto).

  End Core0_IMemLift.

  Section Core0_DMemLift.
    Definition core0_dmem_lift (reg: Core0DMem.reg_t) : reg_t :=
      match reg with
      | Core0DMem.fromMem st => (internal (RouterToCore0D st))
      | Core0DMem.toMem st => (internal (core0DToRouter st))
      | Core0DMem.internal st => (internal (Core0D_internal st))
      end.

    Definition Lift_core0_dmem : RLift _ Core0DMem.reg_t reg_t Core0DMem.R R := ltac:(mk_rlift core0_dmem_lift).
    Definition FnLift_core0_dmem : RLift _ Core0DMem.ext_fn_t ext_fn_t Core0DMem.Sigma Sigma := ltac:(lift_auto).

  End Core0_DMemLift.

  (* TODO: Core1 *)
  Section MessageRouterLift.
    Definition router_lift (reg: MessageRouter.reg_t) : reg_t := 
    match reg with
    | MessageRouter.FromCore0I st => (internal (core0IToRouter st))
    | MessageRouter.FromCore0D st => (internal (core0DToRouter st))
    | MessageRouter.FromCore1I st => (internal (core1IToRouter st))
    | MessageRouter.FromCore1D st => (internal (core1DToRouter st))
    | MessageRouter.ToCore0I st => (internal (RouterToCore0I st))
    | MessageRouter.ToCore0D st => (internal (RouterToCore0D st))
    | MessageRouter.ToCore1I st => (internal (RouterToCore1I st))
    | MessageRouter.ToCore1D st => (internal (RouterToCore1D st))
    | MessageRouter.ToProto st => (internal (RouterToProto st))
    | MessageRouter.FromProto st => (internal (ProtoToRouter st))
    | MessageRouter.internal st => (internal (Router_internal st))
    end.

    Definition Lift_router : RLift _ MessageRouter.reg_t reg_t MessageRouter.R R := ltac:(mk_rlift router_lift).
    Definition FnLift_router : RLift _ MessageRouter.ext_fn_t ext_fn_t MessageRouter.Sigma Sigma := ltac:(lift_auto).
    
  End MessageRouterLift.

  Section ProtocolProcessorLift.

    Definition proto_lift (reg: ProtocolProcessor.reg_t) : reg_t :=
    match reg with 
    | ProtocolProcessor.FromRouter st => (internal (RouterToProto st))
    | ProtocolProcessor.ToRouter st => (internal (ProtoToRouter st ))
    | ProtocolProcessor.ToMem st => (internal (ProtoToMem st))
    | ProtocolProcessor.FromMem st => (internal (MemToProto st))
    end.

    Definition Lift_proto : RLift _ ProtocolProcessor.reg_t reg_t ProtocolProcessor.R R := ltac:(mk_rlift proto_lift).
    Definition FnLift_proto : RLift _ ProtocolProcessor.ext_fn_t ext_fn_t ProtocolProcessor.Sigma Sigma := ltac:(lift_auto).

  End ProtocolProcessorLift.

  Section MainMemLift.
    Definition main_mem_lift (reg: MainMem.reg_t) : reg_t := 
      match reg with
      | MainMem.FromProto st => internal (ProtoToMem st)
      | MainMem.ToProto st => internal (MemToProto st)
      end.

    Definition Lift_main_mem: RLift _ MainMem.reg_t reg_t MainMem.R R := ltac:(mk_rlift main_mem_lift).
    Definition FnLift_main_mem: RLift _ MainMem.ext_fn_t ext_fn_t MainMem.Sigma Sigma := ltac:(lift_auto).
  End MainMemLift.

  (* TODO: slow *)
  Instance FiniteType_reg_t : FiniteType reg_t := _. 
  (* Declare Instance FiniteType_reg_t : FiniteType reg_t.   *)
  Instance EqDec_reg_t : EqDec reg_t := _.

  Section SystemRules.
    Definition forwardToCore0I : uaction reg_t ext_fn_t :=
      {{ let req := toIMem0.(MemReq.deq)() in
         (`core0_imem_lift`).(Core0IMem.req)(req) 
      }}.

    Definition tc_forwardToCore0I := tc_rule R Sigma forwardToCore0I <: rule.

    Definition forwardToCore0D : uaction reg_t ext_fn_t :=
      {{ let req := toDMem0.(MemReq.deq)() in
         (`core0_dmem_lift`).(Core0DMem.req)(req)
      }}.

    Definition tc_forwardToCore0D := tc_rule R Sigma forwardToCore0D <: rule.

    Definition forwardFromCore0I : uaction reg_t ext_fn_t :=
      {{ let resp := (`core0_imem_lift`).(Core0IMem.resp)() in
         fromIMem0.(MemResp.enq)(resp)
      }}.

    Definition tc_forwardFromCore0I := tc_rule R Sigma forwardFromCore0I <: rule.

    Definition forwardFromCore0D : uaction reg_t ext_fn_t :=
      {{ let resp := (`core0_dmem_lift`).(Core0DMem.resp)() in
         fromDMem0.(MemResp.enq)(resp)
      }}.

    Definition tc_forwardFromCore0D := tc_rule R Sigma forwardFromCore0D <: rule.

    Inductive SystemRule :=
    | SysRl_ForwardToCore0I
    | SysRl_ForwardToCore0D
    | SysRl_ForwardFromCore0I
    | SysRl_ForwardFromCore0D
    .

    Definition system_rules (rl: SystemRule) : rule :=
      match rl with
      | SysRl_ForwardToCore0I => tc_forwardToCore0I
      | SysRl_ForwardToCore0D => tc_forwardToCore0D
      | SysRl_ForwardFromCore0I => tc_forwardFromCore0I
      | SysRl_ForwardFromCore0D => tc_forwardFromCore0D
      end.

    Definition internal_system_schedule : Syntax.scheduler pos_t SystemRule :=
      SysRl_ForwardToCore0I |> SysRl_ForwardToCore0D |> SysRl_ForwardFromCore0I |> SysRl_ForwardFromCore0D |> done.

  End SystemRules.

  Section Rules.
    Inductive rule_name_t' :=
    | Rl_System (r: SystemRule)
    | Rl_Core0IMem (r: Core0IMem.rule_name_t)
    | Rl_Core0DMem (r: Core0DMem.rule_name_t)
    | Rl_Proto (r: ProtocolProcessor.rule_name_t)
    | Rl_Router (r: MessageRouter.rule_name_t)
    | Rl_MainMem (r: MainMem.rule_name_t)
    .

    Definition rule_name_t := rule_name_t'.

    Definition core0I_rule_name_lift (rl: Core0IMem.rule_name_t) : rule_name_t :=
      Rl_Core0IMem rl.

    Definition core0D_rule_name_lift (rl: Core0DMem.rule_name_t) : rule_name_t :=
      Rl_Core0DMem rl.

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
      | Rl_Proto r => proto_rules r
      | Rl_Router r => router_rules r
      | Rl_MainMem r => main_mem_rules r
     end.

  End Rules.

  Section Schedule.
    Definition system_schedule := lift_scheduler Rl_System internal_system_schedule.
    Definition core0I_schedule := lift_scheduler Rl_Core0IMem Core0IMem.schedule.
    Definition core0D_schedule := lift_scheduler Rl_Core0DMem  Core0DMem.schedule.
    Definition proto_schedule := lift_scheduler Rl_Proto ProtocolProcessor.schedule.
    Definition router_schedule := lift_scheduler Rl_Router MessageRouter.schedule.
    Definition main_mem_schedule := lift_scheduler Rl_MainMem MainMem.schedule.

    Definition schedule :=
      system_schedule ||> core0I_schedule ||> core0D_schedule ||> router_schedule 
                      ||> proto_schedule ||> main_mem_schedule.

  End Schedule.

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

  Inductive simple_memory :=
  | imem0
  | dmem0
  .

  Definition memoryBus (m: simple_memory) : UInternalFunction reg_t ext_fn_t :=
    {{ fun memoryBus (get_ready: bits_t 1) (put_valid: bits_t 1) (put_request: struct_t mem_req) : struct_t mem_output =>
         `match m with
          | imem0 => {{ extcall (ext_mem imem) (struct mem_input {|
                         get_ready := get_ready;
                         put_valid := put_valid;
                         put_request := put_request |}) }}
          | dmem0 => {{ let addr := get(put_request, addr) in
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
                         extcall (ext_mem dmem) (struct mem_input {|
                           get_ready := get_ready && is_mem;
                           put_valid := put_valid && is_mem;
                           put_request := put_request |})
                   }}
          end` }}.

  (* TODO: not defined for main_mem *)
  Definition mem (m: simple_memory) : uaction reg_t ext_fn_t :=
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

  Definition tc_imem := tc_rule R Sigma (mem imem0) <: rule.
  Definition tc_dmem := tc_rule R Sigma (mem dmem0) <: rule.

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
