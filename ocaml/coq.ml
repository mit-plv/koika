open Common
open Lv
open Format

let (<<<) pp f ppf x =
  pp ppf (f x)

let pp_noop _ppf =
  ()

let pp_raw ppf s =
  fprintf ppf "%s" s

let rec brk n ppf =
  if n = 0 then () else (fprintf ppf "@,"; brk (n - 1) ppf)

let pp_nat ppf n =
  fprintf ppf "%d" n

let pp_quoted ppf s =
  fprintf ppf "\"%s\"" s

let pp_coq_quoted =
  pp_quoted <<< SGALib.Util.string_of_coq_string

let pp_sep s ppf =
  fprintf ppf "%s@ " s

let pp_const s ppf =
  fprintf ppf "%s" s

let pp_pair f1 f2 ppf (x1, x2) =
  fprintf ppf "(@[%a, %a@])" f1 x1 f2 x2

let rec pp_seq pp_sep pp_elem ppf = function
  | [] -> ()
  | [x] -> pp_elem ppf x
  | x :: tl -> pp_elem ppf x; pp_sep ppf; pp_seq pp_sep pp_elem ppf tl

let pp_list pp_elem ppf elems =
  fprintf ppf "[@[%a@]]" (pp_seq (pp_sep "; ") pp_elem) elems

let pp_vector pp_elem ppf elems =
  fprintf ppf "@[<2>vect_of_list %a@]" (pp_list pp_elem) elems

let pp_bit ppf b =
  pp_raw ppf (if b then "~1" else "~0")

let pp_bits ppf bs =
  fprintf ppf "Ob%a" (pp_seq pp_noop pp_bit) (Array.to_list bs)

let pp_type ?(wrap=true) ppf = function
  | Bits_t sz -> fprintf ppf (if wrap then "(bits_t %d)" else "bits_t %d") sz
  | Struct_t sg -> pp_raw ppf sg.struct_name
  | Enum_t sg -> pp_raw ppf sg.enum_name

let pp_enum ppf { enum_name; enum_bitsize; enum_members } =
  let p fmt = fprintf ppf fmt in
  let members, bitpatterns = List.split enum_members in
  p "@[<v>@[<hv 2>Definition %s_sig : enum_sig := {|@ " enum_name;
  p "enum_name := %a;@ " pp_quoted enum_name;
  p "enum_size := %d;@ " (List.length enum_members);
  p "enum_bitsize := %d;@ " enum_bitsize;
  p "enum_members := %a;@ " (pp_vector pp_quoted) members;
  p "enum_bitpatterns := %a;" (pp_vector pp_bits) bitpatterns;
  p "@]@ |}.@ @]";
  p "Definition %s : type := enum_t %s_sig." enum_name enum_name

let pp_struct ppf { struct_name; struct_fields } =
  let p fmt = fprintf ppf fmt in
  p "@[<v>@[<hv 2>Definition %s_sig : struct_sig := {|@ " struct_name;
  p "struct_name := %a;@ " pp_quoted struct_name;
  p "struct_fields := %a;" (pp_list (pp_pair pp_quoted (pp_type ~wrap:false))) struct_fields;
  p "@]@ |}.@ @]";
  p "Definition %s : type := struct_t %s_sig." struct_name struct_name

let pp_inductive pp_constructor ppf (name, constructors) =
  fprintf ppf "@[<v>Inductive %s : Set :=@ %a.@]" name
    (pp_seq (brk 1) (fun ppf c -> fprintf ppf "| %a" pp_constructor c))
    constructors

let pp_reg_name ppf r =
  pp_raw ppf (r.reg_name)

let pp_reg_t ppf (registers: reg_signature list) =
  pp_inductive pp_reg_name ppf ("reg_t", registers)

let pp_rule_name_t ppf (rules: (string * _) list) =
  pp_inductive (pp_raw <<< fst) ppf ("rule_name_t", rules)

let pp_match pp_left pp_right ppf (discr, branches) =
  fprintf ppf "@[<v>match %s with@ %a@ end@]" discr
    (pp_seq (brk 1) (fun ppf v ->
         fprintf ppf "| %a => %a" pp_left v pp_right v))
    branches

let reg_name { reg_name; _ } = reg_name
let reg_init { reg_init; _ } = reg_init
let ffi_name { ffi_name; _ } = ffi_name

let pp_reg_types ppf (registers: reg_signature list) =
  fprintf ppf "@[<v>@[<hv 2>Definition R (r: reg_t): type :=@ ";
  pp_match pp_reg_name (pp_type ~wrap:false <<< reg_type) ppf ("r", registers);
  fprintf ppf "@].@]"

let pp_fn_t ppf extfuns =
  fprintf ppf "@[<v>";
  pp_inductive (pp_raw <<< ffi_name) ppf ("custom_fn_t", extfuns); brk 1 ppf;
  fprintf ppf "Definition ufn_t := interop_ufn_t custom_fn_t.@ ";
  fprintf ppf "Definition fn_t := interop_fn_t custom_fn_t.@]"

let pp_external_sig ppf f =
  fprintf ppf "{{ %a ~> %a ~> %a }}"
    (pp_type ~wrap:false) f.ffi_arg1type
    (pp_type ~wrap:false) f.ffi_arg2type
    (pp_type ~wrap:false) f.ffi_rettype

let pp_internal_sig_arg ppf (nm, tau) =
  fprintf ppf "@[%a@ :: %a@]" pp_quoted nm (pp_type ~wrap:false) tau

let pp_internal_sig ppf (f: _ internal_signature) =
  fprintf ppf "{{{ %a | %a ~> %a }}}"
    pp_quoted f.int_name
    (pp_seq (pp_sep " ~> ") pp_internal_sig_arg) f.int_args
    (pp_type ~wrap:false) f.int_rettype

let pp_fn_types ppf (extfuns: string ffi_signature list) =
  fprintf ppf "@[<hv 2>Definition custom_Sigma (f: custom_fn_t): ExternalSignature :=@ ";
  pp_match (pp_raw <<< ffi_name) (pp_external_sig) ppf ("f", extfuns);
  fprintf ppf "@].@ ";
  fprintf ppf "@[<2>Definition Sigma (fn: fn_t) :=@ interop_Sigma custom_Sigma fn.@]@ ";
  fprintf ppf "@[<2>Definition uSigma := interop_uSigma (fun (fn: custom_fn_t) _ _ => Success fn).@]"

let pp_cast pp_expr ppf (expr, typ) =
  fprintf ppf "(%a <: %s)" pp_expr expr typ

let rec pp_value ppf = function
  | Bits v -> pp_bits ppf v
  | Enum (_, v) -> pp_value ppf (Bits v)
  | Struct (sg, v) ->
     let rec loop ppf = function
       | [] -> fprintf ppf "tt"
       | v :: vs -> pp_pair pp_value loop ppf (v, vs) in
     pp_cast loop ppf (v, sg.struct_name ^ "_sig")

let try_enum_const = function
  | Enum (sg, v) ->
     (match enum_find_field_opt sg v with
      | None -> None
      | Some enumerator -> Some (sg, enumerator))
  | _ -> None

let pp_port ppf = function
  | SGALib.SGA.P0 -> pp_raw ppf "P0"
  | SGALib.SGA.P1 -> pp_raw ppf "P1"

let pp_sig ppf signame =
  fprintf ppf "%s_sig" (SGALib.Util.string_of_coq_string signame)

let pp_app ppf fn fmt =
  fprintf ppf "(@[<2>%s@ " fn;
  kfprintf (fun ppf -> fprintf ppf "@])") ppf fmt

let pp_sga_type ppf tau =
  pp_type ~wrap:true ppf (SGALib.Util.typ_of_sga_type tau)

let rec pp_fn ppf (fn: string ffi_signature SGALib.SGA.interop_ufn_t) =
  match fn with
  | UPrimFn f -> pp_app ppf "UPrimFn" "%a" pp_uprimfn f
  | UCustomFn f -> pp_app ppf "UCustomFn" "%s" f.ffi_name
and pp_uprimfn ppf (f: SGALib.SGA.prim_ufn_t) = match f with
  | UDisplayFn f -> pp_app ppf "UDisplayFn" "%a" pp_prim_display_ufn f
  | UConvFn f -> pp_app ppf "UConvFn" "%a" pp_prim_conv_ufn f
  | UBitsFn f -> pp_app ppf "UBitsFn" "%a" pp_prim_bits_ufn f
  | UStructFn f -> pp_app ppf "UStructFn" "%a" pp_prim_struct_ufn f
and pp_prim_display_ufn ppf (f: SGALib.SGA.prim_display_ufn) = match f with
  | UDisplayUtf8 -> pp_raw ppf "UDisplayUtf8"
  | UDisplayValue -> pp_raw ppf "UDisplayValue"
and pp_prim_conv_ufn ppf (f: SGALib.SGA.prim_conv_ufn) = match f with
  | UEq -> pp_raw ppf "UEq"
  | UInit tau -> pp_app ppf "UInit" "%a" pp_sga_type tau
  | UPack -> pp_raw ppf "UPack"
  | UUnpack tau -> pp_app ppf "UUnpack" "%a" pp_sga_type tau
  | UIgnore -> pp_raw ppf "UIgnore"
and pp_prim_bits_ufn ppf (f: SGALib.SGA.prim_bits_ufn) =
  let pp_raw = pp_raw ppf in
  let pp_app fmt = pp_app ppf fmt in
  match f with
  | USel -> pp_raw "USel"
  | UPart (offset, width) -> pp_app "UPart" "%d@ %d" offset width
  | UPartSubst (offset, width) -> pp_app "UPartSubst" "%d@ %d" offset width
  | UIndexedPart width -> pp_app "UIndexedPart" "%d" width
  | UAnd -> pp_raw "UAnd"
  | UOr -> pp_raw "UOr"
  | UNot -> pp_raw "UNot"
  | ULsl -> pp_raw "ULsl"
  | ULsr -> pp_raw "ULsr"
  | UConcat -> pp_raw "UConcat"
  | UUIntPlus -> pp_raw "UUIntPlus"
  | UZExtL width -> pp_app "UZExtL" "%d" width
  | UZExtR width -> pp_app "UZExtR" "%d" width
and pp_prim_struct_accessor ppf (op: SGALib.SGA.prim_struct_accessor) = match op with
  | GetField -> pp_raw ppf "GetField"
  | SubstField -> pp_raw ppf "SubstField"
and pp_prim_struct_ufn ppf (f: SGALib.SGA.prim_struct_ufn) = match f with
  | UDo (op, f) ->
     pp_app ppf "UDo" "%a@ %a" pp_prim_struct_accessor op pp_coq_quoted f
  | UDoBits (sg, op, f) ->
     pp_app ppf "UDoBits" "%a@ %a@ %a" pp_sig sg.struct_name
       pp_prim_struct_accessor op pp_coq_quoted f

let pp_pos ppf pos =
  pp_quoted ppf (Lv.Pos.to_string pos)

let rec pp_action (position_printer: (Format.formatter -> 'f -> unit) option)
          ppf (a: 'f SGALib.Compilation.translated_action) =
  let open SGALib.Util in
  let pp_app fn fmt = pp_app ppf fn fmt in
  let pp_action = pp_action position_printer in
  match a with
  | UError -> pp_raw ppf "UError"
  | UFail tau -> pp_app "UFail" "%a" pp_sga_type tau
  | UVar v -> pp_app "UVar" "%a" pp_quoted v
  | UConst (tau, v) ->
     let v = value_of_sga_value tau v in
     (match try_enum_const v with
      | Some (sg, enumerator) ->
         pp_app "UConstEnum" "%s_sig@ %a" sg.enum_name pp_quoted enumerator
      | None ->
         pp_app "UConst" "(tau := %a)@ %a" pp_sga_type tau pp_value v)
  | UConstString s ->
     pp_app "UConstString" "%a" pp_coq_quoted s
  | UConstEnum (sg, enumerator) ->
     pp_app "UConstEnum" "%a@ %a" pp_sig sg.enum_name pp_coq_quoted enumerator
  | UAssign (v, a) ->
     pp_app "UAssign" "%a@ %a" pp_quoted v pp_action a
  | USeq (a, b) ->
     pp_app "USeq" "%a@ %a" pp_action a pp_action b
  | UBind (k, v, body) ->
     pp_app "UBind" "%a@ %a@ %a" pp_quoted k pp_action v pp_action body
  | UIf (cond, tb, fb) ->
     pp_app "UIf" "%a@ %a@ %a" pp_action cond pp_action tb pp_action fb
  | URead (p, r) ->
     pp_app "URead" "%a@ %a" pp_port p pp_reg_name r
  | UWrite (p, r, v) ->
     pp_app "UWrite" "%a@ %a@ %a" pp_port p pp_reg_name r pp_action v
  | UCall (fn, a1, a2) ->
     pp_app "UCall" "%a@ %a@ %a" pp_fn fn pp_action a1 pp_action a2
  | UInternalCall (fsig, fbody, args) ->
     let fsig = internal_sig_of_sga_internal_sig fsig in
     pp_app "UInternalCall" "%a@ %a@ %a" pp_internal_sig fsig pp_action fbody (pp_list pp_action) args
  | UAPos (pos, v) ->
     match position_printer with
     | Some pp_pos -> pp_app "UAPos" "%a@ %a" pp_pos pos pp_action v
     | None -> pp_action ppf v

let pp_rule position_printer ppf (name, r) =
  let action = SGALib.Compilation.translate_action r in
  fprintf ppf "@[<2>Definition %s_body : uaction pos_t method_name_t var_t reg_t ufn_t :=@ %a@]."
    name (pp_action position_printer) action

let pp_scheduler position_printer ppf (name, s) =
  let scheduler = SGALib.Compilation.translate_scheduler s in
  let rec loop ppf (s: _ SGALib.SGA.uscheduler) = match s with
    | UDone ->
       pp_raw ppf "UDone"
    | UCons (r, s) ->
       pp_app ppf "UCons" "%a@ %a" pp_raw r loop s
    | UTry (r, s1, s2) ->
       pp_app ppf "UTry" "%a@ @[<v>%a@ %a@]"
         pp_raw r loop s1 loop s2
    | USPos (pos, s) ->
       match position_printer with
       | Some pp_pos -> pp_app ppf "USPos" "%a@ %a" pp_pos pos loop s
       | None -> loop ppf s in
  fprintf ppf "@[<2>Definition %s : scheduler rule_name_t :=@ tc_scheduler @[%a@]@]."
    name loop scheduler;
  brk 2 ppf;
  fprintf ppf "@[<2>Definition %s_circuit : state_transition_circuit rule_name_t R Sigma ContextEnv :=@ " name;
  fprintf ppf "@[<2>compile_scheduler@ interop_opt@ (@[ContextEnv.(create)@ (readRegisters R Sigma)@])@ rules@ %s@].@]" name;
  brk 2 ppf;
  fprintf ppf "@[<2>Definition %s_eval (custom_sigma: forall f, custom_Sigma f)@ : Log R ContextEnv :=@ " name;
  fprintf ppf "@[<2>interp_scheduler@ (ContextEnv.(create) r)@ (interop_sigma custom_sigma)@ rules@ %s@].@]" name

let pp_tc_rules ppf (rules: (string * _) list) =
  fprintf ppf "@[<2>Definition rules :=@ @[<2>tc_rules R Sigma uSigma@ (fun rl => %a)@].@]"
    (pp_match (pp_raw <<< fst) (fun ppf r -> fprintf ppf "%s_body" (fst r)))
    ("rl", rules)

let pp_reg_init_vals ppf (registers: reg_signature list) =
  fprintf ppf "@[<2>Definition r idx : R idx :=@ %a.@]"
    (pp_match pp_reg_name (pp_value <<< reg_init)) ("idx", registers)

let pp_mod ~print_positions ppf ({ name; registers; rules; schedulers }: resolved_module) =
  let position_printer = if print_positions then Some pp_pos else None in
  let name = name.lcnt in
  fprintf ppf "@[<v>@[<v 2>Module %s.@ " name;
  pp_reg_t ppf registers; brk 2 ppf;
  pp_rule_name_t ppf rules; brk 2 ppf;
  pp_reg_types ppf registers; brk 2 ppf;
  pp_reg_init_vals ppf registers; brk 2 ppf;
  pp_seq (brk 2) (pp_rule position_printer) ppf rules; brk 2 ppf;
  pp_tc_rules ppf rules; brk 2 ppf;
  pp_seq (brk 2) (pp_scheduler position_printer) ppf schedulers;
  fprintf ppf "@]@ End %s.@]" name

let pp_preamble ppf =
  fprintf ppf "Require Import SGA.Notations.@ ";
  fprintf ppf "Require Coq.Lists.List.@ ";
  fprintf ppf "Export Coq.Lists.List.ListNotations.@ @ ";
  fprintf ppf "Definition pos_t := string.@ ";
  fprintf ppf "Definition method_name_t := string.@ ";
  fprintf ppf "Definition var_t := string.@ @ ";
  fprintf ppf "Instance DummyPos_pos_t : DummyPos pos_t := {| dummy_pos := \"\" |}."

let _ =
  SGALib.Compilation.debug_printer :=
    { debug_print = (fun a ->
        fprintf (formatter_of_out_channel stderr) "%a@." (pp_action None) a) }

let main out ({ r_types; r_extfuns; r_mods }: Lv.resolved_unit) =
  let types = topo_sort_types (List.map snd (StringMap.bindings r_types.td_all)) in
  let enums, structs = partition_types types in
  let extfuns = List.map (snd << snd) (StringMap.bindings r_extfuns) in
  let ppf = formatter_of_out_channel out in

  fprintf ppf "@[<v>";
  pp_preamble ppf; brk 2 ppf;
  pp_seq (brk 2) pp_enum ppf enums; brk 2 ppf;
  pp_seq (brk 2) pp_struct ppf structs; brk 2 ppf;
  pp_fn_t ppf extfuns; brk 2 ppf;
  pp_fn_types ppf extfuns; brk 2 ppf;
  pp_seq (brk 2) (pp_mod ~print_positions:false) ppf r_mods;
  fprintf ppf "@]@.";
