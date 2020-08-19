Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import dynamic_isolation.Interfaces.


Module External <: External_sig.
  Import Common.

  Inductive cache := imem0 | dmem0 | imem1 | dmem1.

  Inductive ext_fn_t' :=
  | ext_cache (c: cache)
  | ext_mainmem
  | ext_uart_read0
  | ext_uart_write0
  | ext_led0
  | ext_uart_read1
  | ext_uart_write1
  | ext_led1
  | ext_ppp_bookkeeping
  .

  Definition ext_fn_t := ext_fn_t'.
  Definition led_input := maybe (bits_t 1).
  Definition uart_input := maybe (bits_t 8).
  Definition uart_output := maybe (bits_t 8).

  Definition log_num_sets := 12.
  Definition log_tag_size := 18. (* 32 - 2 - 12 *)

  Definition cache_tag_t := bits_t log_tag_size. (* TODO  *)
  Definition cache_index_t := bits_t log_num_sets.
  (* TODO: avoiding Koika arrays for now. This should be an array based on the block size *)
  Definition cache_line_t := bits_t 32.

  Definition MSI :=
    {| enum_name := "MSI";
       enum_members := vect_of_list ["I"; "S"; "M"];
       enum_bitpatterns := vect_of_list [Ob~0~0; Ob~0~1; Ob~1~0] |}.

  Definition ext_cache_mem_req :=
    {| struct_name := "ext_cache_mem_req";
       struct_fields := [("byte_en", bits_t 4);
                         ("tag", cache_tag_t);
                         ("index", cache_index_t);
                         ("data", bits_t 32);
                         ("MSI", maybe (enum_t MSI));
                         ("ignore_response", bits_t 1)
                        ]
    |}.

  Definition cache_mem_input :=
    {| struct_name := "cache_mem_input";
       struct_fields := [("get_ready", bits_t 1);
                         ("put_valid", bits_t 1);
                         ("put_request", struct_t ext_cache_mem_req)] |}.

  Definition cache_row :=
    {| struct_name := "cache_row";
       struct_fields := [("tag", cache_tag_t);
                         ("data", cache_line_t);
                         ("flag", enum_t MSI)] |}.

  Definition ext_cache_mem_resp :=
    {| struct_name := "ext_cache_mem_resp";
       struct_fields := [("row", struct_t cache_row)] |}.

  Definition cache_mem_output :=
    {| struct_name := "cache_mem_output";
       struct_fields := [("get_valid", bits_t 1);
                        ("put_ready", bits_t 1);
                        ("get_response", struct_t ext_cache_mem_resp)] |}.

  Definition bookkeeping_row :=
    {| struct_name := "bookkeeping_row";
       struct_fields := [("state", enum_t MSI);
                         ("tag", cache_tag_t)]
    |}.

  (* Should be an array but avoiding arrays; fetch all entries at once *)
  Definition bookkeeping_entry :=
    {| struct_name := "bookkeeping_entry";
       struct_fields := [("imem0", struct_t bookkeeping_row);
                         ("dmem0", struct_t bookkeeping_row);
                         ("imem1", struct_t bookkeeping_row);
                         ("dmem1", struct_t bookkeeping_row)
                        ]
    |}.

   Definition cache_type :=
     {| enum_name := "cache_type";
        enum_members := vect_of_list ["imem"; "dmem"];
        enum_bitpatterns := vect_of_list [Ob~0; Ob~1] |}.

  Definition single_bookkeeping_entry :=
    {| struct_name := "single_bookkeeping_entry";
       struct_fields := [("entry", struct_t bookkeeping_row);
                         ("core_id", bits_t 1);
                         ("cache_type", enum_t cache_type)
                        ]
    |}.

  Definition bookkeeping_input :=
    {| struct_name := "bookkeeping_input";
       struct_fields := [("idx", bits_t log_num_sets);
                         ("write_entry", maybe (struct_t single_bookkeeping_entry))
                        ]
    |}.

   Definition ext_bookkeeping_input :=
     {| struct_name := "ext_bookkeeping_input";
        struct_fields := [("get_ready", bits_t 1);
                          ("put_valid", bits_t 1);
                          ("put_request", struct_t bookkeeping_input)]
     |}.

  Definition ext_bookkeeping_output :=
    {| struct_name := "ext_bookkeeping_output";
       struct_fields := [("get_valid", bits_t 1);
                         ("put_ready", bits_t 1);
                         ("get_response", struct_t bookkeeping_entry)]
    |}.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_cache _ => {$ struct_t cache_mem_input ~> struct_t cache_mem_output $}
    | ext_mainmem => {$ struct_t mem_input ~> struct_t mem_output $}
    | ext_uart_read0 => {$ bits_t 1 ~> uart_output $}
    | ext_uart_write0 => {$ uart_input ~> bits_t 1 $}
    | ext_led0 => {$ led_input ~> bits_t 1 $}
    | ext_uart_read1 => {$ bits_t 1 ~> uart_output $}
    | ext_uart_write1 => {$ uart_input ~> bits_t 1 $}
    | ext_led1 => {$ led_input ~> bits_t 1 $}
    | ext_ppp_bookkeeping => {$ struct_t ext_bookkeeping_input ~> struct_t ext_bookkeeping_output $}
    end.

  (* replace with "show" *)
  Definition ext_fn_specs (fn: ext_fn_t) :=
    match fn with
    | ext_cache imem0 => {| efr_name := "ext_cache_imem0"; efr_internal := false |}
    | ext_cache dmem0 => {| efr_name := "ext_cache_dmem0"; efr_internal := false |}
    | ext_cache imem1 => {| efr_name := "ext_cache_imem1"; efr_internal := false |}
    | ext_cache dmem1 => {| efr_name := "ext_cache_dmem1"; efr_internal := false |}
    | ext_mainmem => {| efr_name := "ext_mainmem"; efr_internal := false |}
    | ext_uart_write0 => {| efr_name := "ext_uart_write0"; efr_internal := false |}
    | ext_uart_read0 => {| efr_name := "ext_uart_read0"; efr_internal := false |}
    | ext_led0 => {| efr_name := "ext_led0"; efr_internal := false |}
    | ext_uart_write1 => {| efr_name := "ext_uart_write1"; efr_internal := false |}
    | ext_uart_read1 => {| efr_name := "ext_uart_read1"; efr_internal := false |}
    | ext_led1 => {| efr_name := "ext_led1"; efr_internal := false |}
    | ext_ppp_bookkeeping => {| efr_name := "ext_ppp_bookkeeping"; efr_internal := false |}
    end.

  Instance Show_ext_fn_t : Show ext_fn_t := _.

  (* TODO: temporary and wrong *)
  Definition sigma (fn: ext_fn_t) : Sig_denote (Sigma fn) :=
    match fn with
    | ext_cache _ => fun _ => value_of_bits Bits.zero
    | ext_mainmem => fun _ => value_of_bits Bits.zero
    | ext_uart_write0 => fun _ => value_of_bits Bits.zero
    | ext_uart_read0 => fun _ => value_of_bits Bits.zero
    | ext_led0 => fun _ => value_of_bits Bits.zero
    | ext_uart_write1 => fun _ => value_of_bits Bits.zero
    | ext_uart_read1 => fun _ => value_of_bits Bits.zero
    | ext_led1 => fun _ => value_of_bits Bits.zero
    | ext_ppp_bookkeeping => fun _ => value_of_bits Bits.zero
    end.

  Definition ext : external_sig :=
    {| _ext_fn_t := ext_fn_t;
       _Sigma := Sigma;
       _sigma := sigma;
       _ext_fn_specs := ext_fn_specs
    |}.
End External.

Module EnclaveParams <: EnclaveParameters.
  Import Common.
  Definition enclave_base (eid: enclave_id) : addr_t :=
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end.

  Definition enclave_size (eid: enclave_id) : bits_t 32 :=
    Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

  Definition enclave_bootloader_addr (eid: enclave_id) : addr_t :=
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0
    end.

  Definition shared_region_base (id: shared_id) : addr_t :=
    match id with
    | Shared01 =>
        Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared02 =>
        Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared03 =>
        Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared12 =>
        Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared13 =>
        Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared23 =>
        Ob~0~0~0~0~0~0~0~0~0~1~0~0~0~0~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end.

  Definition shared_region_size : bits_t 32 := Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

  Definition params : enclave_params_sig :=
    {| _enclave_base := enclave_base
     ; _enclave_size := enclave_size
     ; _enclave_bootloader_addr := enclave_bootloader_addr
     ; _shared_region_base := shared_region_base
     ; _shared_region_size := shared_region_size
    |}.


End EnclaveParams.
