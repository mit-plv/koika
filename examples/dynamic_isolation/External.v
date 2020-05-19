Require Import Koika.Frontend.
Require Import Koika.Std.

Require Import DynamicIsolation.Interfaces.

Module OriginalExternal <: External_sig.
  Import Common.
  Inductive memory := imem | dmem.

  Inductive ext_fn_t' :=
  | ext_mem (m: memory)
  | ext_uart_read
  | ext_uart_write
  | ext_led
  .

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
    | ext_uart_write => {| ef_name := "ext_uart_write"; ef_internal := false |}
    | ext_uart_read => {| ef_name := "ext_uart_read"; ef_internal := false |}
    | ext_led => {| ef_name := "ext_led"; ef_internal := false |}
    end.

  Instance Show_ext_fn_t : Show ext_fn_t := _.

End OriginalExternal.


Module External <: External_sig.
  Import Common.

  Inductive cache := imem0 | dmem0 | imem1 | dmem1.

  Inductive ext_fn_t' :=
  | ext_cache (c: cache)
  | ext_mainmem
  | ext_uart_read
  | ext_uart_write
  | ext_led
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
                         ("MSI", maybe (enum_t MSI))] |}.

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

  Definition Bookkeeping_row :=
    {| struct_name := "Bookkeeping_row";
       struct_fields := [("state", enum_t MSI);
                         ("tag", cache_tag_t)]
    |}.

  Definition cache_type :=
    {| enum_name := "cache_type";
       enum_members := vect_of_list ["imem"; "dmem"];
       enum_bitpatterns := vect_of_list [Ob~0; Ob~1] |}.

  Definition bookkeeping_input :=
    {| struct_name := "bookkeeping_input";
       struct_fields := [("idx", bits_t log_num_sets);
                         ("book", maybe (struct_t Bookkeeping_row));
                         ("core_id", bits_t 1);
                         ("cache_type", enum_t cache_type)
                        ]
    |}.

  Definition Sigma (fn: ext_fn_t) :=
    match fn with
    | ext_cache _ => {$ struct_t cache_mem_input ~> struct_t cache_mem_output $}
    | ext_mainmem => {$ struct_t mem_input ~> struct_t mem_output $}
    | ext_uart_read => {$ bits_t 1 ~> uart_output $}
    | ext_uart_write => {$ uart_input ~> bits_t 1 $}
    | ext_led => {$ led_input ~> bits_t 1 $}
    | ext_ppp_bookkeeping => {$ struct_t bookkeeping_input ~> maybe (struct_t Bookkeeping_row) $}
    end.

  Definition ext_fn_specs (fn: ext_fn_t) :=
    match fn with
    | ext_cache imem0 => {| ef_name := "ext_cache_imem0"; ef_internal := false |}
    | ext_cache dmem0 => {| ef_name := "ext_cache_dmem0"; ef_internal := false |}
    | ext_cache imem1 => {| ef_name := "ext_cache_imem1"; ef_internal := false |}
    | ext_cache dmem1 => {| ef_name := "ext_cache_dmem1"; ef_internal := false |}
    | ext_mainmem => {| ef_name := "ext_mainmem"; ef_internal := false |}
    | ext_uart_write => {| ef_name := "ext_uart_write"; ef_internal := false |}
    | ext_uart_read => {| ef_name := "ext_uart_read"; ef_internal := false |}
    | ext_led => {| ef_name := "ext_led"; ef_internal := false |}
    | ext_ppp_bookkeeping => {| ef_name := "ext_ppp_bookkeeping"; ef_internal := false |}
    end.

  Instance Show_ext_fn_t : Show ext_fn_t := _.

End External.

Module EnclaveParams <: EnclaveParameters.

End EnclaveParams.
