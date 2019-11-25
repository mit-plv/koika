(*! Coq backend (from Lispy Verilog sources) !*)
open Common
open Frontends.Lv
open Format

(* FIXME quote names *)

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
  pp_quoted <<< Cuttlebone.Util.string_of_coq_string

let pp_sep s ppf =
  fprintf ppf "%s@ " s

let pp_const s ppf =
  fprintf ppf "%s" s

let pp_pair f1 f2 ppf (x1, x2) =
  fprintf ppf "(@[%a,@ %a@])" f1 x1 f2 x2

let rec pp_seq pp_sep pp_elem ppf = function
  | [] -> ()
  | [x] -> pp_elem ppf x
  | x :: tl -> pp_elem ppf x; pp_sep ppf; pp_seq pp_sep pp_elem ppf tl

let rec pp_seq_header pp_sep pp_elem ppf = function
  | [] -> ()
  | x :: tl -> pp_sep ppf; pp_elem ppf x; pp_seq_header pp_sep pp_elem ppf tl

let rec pp_seq_trailer pp_sep pp_elem ppf = function
  | [] -> ()
  | x :: tl -> pp_elem ppf x; pp_sep ppf; pp_seq_trailer pp_sep pp_elem ppf tl

let pp_list pp_elem ppf elems =
  fprintf ppf "[@[%a@]]" (pp_seq (pp_sep "; ") pp_elem) elems

let pp_vect pp_elem ppf elems =
  fprintf ppf "%a%%vect" (pp_list pp_elem) elems

let pp_bool ppf b =
  fprintf ppf (if b then "true" else "false")

let pp_bit ppf b =
  pp_raw ppf (if b then "~1" else "~0")

let pp_bits ppf bs =
  fprintf ppf "Ob%a" (pp_seq pp_noop pp_bit) (Array.to_list bs)

let pp_wrapped wrap pp_inside ppf inside =
  if wrap then fprintf ppf "(%a)" pp_inside inside
  else pp_inside ppf inside

let rec pp_type ~wrap ppf = function
  | Bits_t sz -> pp_wrapped wrap (fun ppf -> fprintf ppf "bits_t %d") ppf sz
  | Struct_t sg -> pp_raw ppf sg.struct_name
  | Enum_t sg -> pp_raw ppf sg.enum_name
  | Array_t sg -> pp_wrapped wrap pp_array_type ppf sg
and pp_array_type ppf { array_type; array_len } =
  let p fmt = fprintf ppf fmt in
  p "{|@ @[";
  p "array_type := %a;@ " (pp_type ~wrap:false) array_type;
  p "array_len := %d" array_len;
  p "@]@ |}"

let pp_type_wrapped = pp_type ~wrap:true
let pp_type_unwrapped = pp_type ~wrap:false

let pp_enum ppf { enum_name; enum_bitsize; enum_members } =
  let p fmt = fprintf ppf fmt in
  let members, bitpatterns = List.split enum_members in
  p "@[<v>@[<hv 2>Definition %s_sig : enum_sig := {|@ " enum_name;
  p "enum_name := %a;@ " pp_quoted enum_name;
  p "enum_size := %d;@ " (List.length enum_members);
  p "enum_bitsize := %d;@ " enum_bitsize;
  p "enum_members := %a;@ " (pp_vect pp_quoted) members;
  p "enum_bitpatterns := %a;" (pp_vect pp_bits) bitpatterns;
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
  fprintf ppf "@[<v>Inductive %s : Set :=%a.@]" name
    (pp_seq_header (brk 1) (fun ppf c -> fprintf ppf "| %a" pp_constructor c))
    constructors

let pp_reg_name ppf r =
  pp_raw ppf (r.reg_name)

let pp_reg_t ppf (registers: reg_signature list) =
  pp_inductive pp_reg_name ppf ("reg_t", registers)

let pp_rule_name_t ppf (rules: (string * _) list) =
  pp_inductive (pp_raw <<< fst) ppf ("rule_name_t", rules)

let pp_match pp_left pp_right ppf (discr, branches) =
  fprintf ppf "@[<v>match %s with%a@ end@]" discr
    (pp_seq_header (brk 1) (fun ppf v ->
         fprintf ppf "| %a => %a" pp_left v pp_right v))
    branches

let reg_name { reg_name; _ } = reg_name
let reg_init { reg_init; _ } = reg_init
let ffi_name { ffi_name; _ } = ffi_name

let pp_reg_types ppf (registers: reg_signature list) =
  fprintf ppf "@[<v>@[<hv 2>Definition R (r: reg_t): type :=@ ";
  pp_match pp_reg_name (pp_type ~wrap:false <<< reg_type) ppf ("r", registers);
  fprintf ppf "@].@]"

let pp_ext_fn_t ppf extfuns =
  fprintf ppf "@[<v>%a@]"
    (pp_inductive (pp_raw <<< ffi_name)) ("ext_fn_t", extfuns)

let pp_external_sig ppf f =
  fprintf ppf "{{ %a ~> %a }}"
    (pp_type ~wrap:false) f.ffi_argtype
    (pp_type ~wrap:false) f.ffi_rettype

let pp_internal_sig_arg ppf (nm, tau) =
  fprintf ppf "@[%a@ :: %a@]" pp_quoted nm (pp_type ~wrap:false) tau

let pp_internal_function ppf (f: _ internal_function) =
  fprintf ppf "{{{ %a | %a ~> %a }}}"
    pp_quoted f.int_name
    (pp_seq (pp_sep " ~> ") pp_internal_sig_arg) f.int_argspec
    (pp_type ~wrap:false) f.int_retType

let pp_ext_fn_Sigma ppf (extfuns: ffi_signature list) =
  fprintf ppf "@[<hv 2>Definition Sigma (f: ext_fn_t): ExternalSignature :=@ %a@]."
    (pp_match (pp_raw <<< ffi_name) pp_external_sig) ("f", extfuns)

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
  | Array (_tau, values) -> (* FIXME does this need a type annotation? *)
     pp_vect pp_value ppf (Array.to_list values)

let try_enum_const = function
  | Enum (sg, v) ->
     (match enum_find_field_opt sg v with
      | None -> None
      | Some enumerator -> Some (sg, enumerator))
  | _ -> None

let pp_port ppf = function
  | P0 -> pp_raw ppf "P0"
  | P1 -> pp_raw ppf "P1"

let pp_signame ppf signame =
  fprintf ppf "%s_sig" signame

let pp_struct_name ppf sg =
  pp_signame ppf sg.struct_name

let pp_extr_struct_name ppf (sg: _ Cuttlebone.Extr.struct_sig') =
  pp_signame ppf (Cuttlebone.Util.string_of_coq_string sg.struct_name)

let pp_app ppf fn fmt =
  fprintf ppf "(@[<2>%s@ " fn;
  kfprintf (fun ppf -> fprintf ppf "@])") ppf fmt

let pp_extr_type ppf tau =
  pp_type ~wrap:true ppf (Cuttlebone.Util.typ_of_extr_type tau)

let pp_extr_array_type ppf sg =
  pp_extr_type ppf (Cuttlebone.Extr.Array_t sg)

let rec pp_display_opts ppf Cuttlebone.Extr.{ display_strings; display_newline; display_style } =
  let p fmt = fprintf ppf fmt in
  p "{|@ @[";
  p "display_strings := %a;@ " pp_bool display_strings;
  p "display_newline := %a;@ " pp_bool display_newline;
  p "display_style := %a" pp_display_style display_style;
  p "@]@ |}"
and pp_display_style ppf = function
  | DBin -> fprintf ppf "dBin"
  | DDec -> fprintf ppf "dDec"
  | DHex -> fprintf ppf "dHex"
  | DFull -> fprintf ppf "dFull"

let rec pp_prim_ufn1 ppf (f: Cuttlebone.Extr.PrimUntyped.ufn1) = match f with
  | UDisplay f -> pp_app ppf "UDisplay" "%a" pp_prim_display_ufn f
  | UConv f -> pp_app ppf "UConv" "%a" pp_prim_uconv f
  | UBits1 f -> pp_app ppf "UBits1" "%a" pp_prim_ubits1 f
  | UStruct1 f -> pp_app ppf "UStruct1" "%a" pp_prim_ustruct1 f
  | UArray1 f -> pp_app ppf "UArray1" "%a" pp_prim_uarray1 f
and pp_prim_display_ufn ppf (f: Cuttlebone.Extr.PrimUntyped.udisplay) = match f with
  | UDisplayUtf8 -> pp_raw ppf "UDisplayUtf8"
  | UDisplayValue opts -> pp_app ppf "UDisplayValue" "%a" pp_display_opts opts
and pp_prim_uconv ppf (f: Cuttlebone.Extr.PrimUntyped.uconv) = match f with
  | UPack -> pp_raw ppf "UPack"
  | UUnpack tau -> pp_app ppf "UUnpack" "%a" pp_extr_type tau
  | UIgnore -> pp_raw ppf "UIgnore"
and pp_prim_ubits1 ppf (f: Cuttlebone.Extr.PrimUntyped.ubits1) =
  let pp_raw = pp_raw ppf in
  let pp_app fmt = pp_app ppf fmt in
  match f with
  | UNot -> pp_raw "UNot"
  | USExt width -> pp_app "USExt" "%d" width
  | UZExtL width -> pp_app "UZExtL" "%d" width
  | UZExtR width -> pp_app "UZExtR" "%d" width
  | URepeat times -> pp_app "URepeat" "%d" times
  | USlice (offset, width) -> pp_app "USlice" "%d@ %d" offset width
and pp_prim_ustruct1 ppf (f: Cuttlebone.Extr.PrimUntyped.ustruct1) = match f with
  | UGetField f -> pp_app ppf "UGetField" "%a" pp_coq_quoted f
  | UGetFieldBits (sg, f) -> pp_app ppf "UGetFieldBits" "%a@ %a" pp_extr_struct_name sg pp_coq_quoted f
and pp_prim_uarray1 ppf (f: Cuttlebone.Extr.PrimUntyped.uarray1) = match f with
  | UGetElement pos -> pp_app ppf "UGetElement" "%d" pos
  | UGetElementBits (sg, pos) -> pp_app ppf "UGetElementBits" "%a@ %d" pp_extr_array_type sg pos

let rec pp_prim_ufn2 ppf (f: Cuttlebone.Extr.PrimUntyped.ufn2) = match f with
  | UEq -> pp_raw ppf "UEq"
  | UBits2 f -> pp_app ppf "UBits2" "%a" pp_prim_ubits2 f
  | UStruct2 f -> pp_app ppf "UStruct2" "%a" pp_prim_ustruct2 f
  | UArray2 f -> pp_app ppf "UArray2" "%a" pp_prim_uarray2 f
and pp_prim_ubits2 ppf (f: Cuttlebone.Extr.PrimUntyped.ubits2) =
  let pp_raw = pp_raw ppf in
  let pp_app fmt = pp_app ppf fmt in
  match f with
  | USel -> pp_raw "USel"
  | USliceSubst (offset, width) -> pp_app "USliceSubst" "%d@ %d" offset width
  | UIndexedSlice width -> pp_app "UIndexedSlice" "%d" width
  | UAnd -> pp_raw "UAnd"
  | UOr -> pp_raw "UOr"
  | UXor -> pp_raw "UXor"
  | ULsl -> pp_raw "ULsl"
  | ULsr -> pp_raw "ULsr"
  | UAsr -> pp_raw "UAsr"
  | UConcat -> pp_raw "UConcat"
  | UPlus -> pp_raw "UPlus"
  | UMinus -> pp_raw "UMinus"
  | UCompare (signed, cmp) -> pp_app "UCompare" "%a@ %a" pp_bool signed pp_cmp cmp
and pp_cmp ppf (cmp: Cuttlebone.Extr.bits_comparison) =
  match cmp with
  | CLt -> pp_raw ppf "cLt"
  | CGt -> pp_raw ppf "cGt"
  | CLe -> pp_raw ppf "cLe"
  | CGe -> pp_raw ppf "cGe"
and pp_prim_ustruct2 ppf (f: Cuttlebone.Extr.PrimUntyped.ustruct2) = match f with
  | USubstField f -> pp_app ppf "USubstField" "%a" pp_coq_quoted f
  | USubstFieldBits (sg, f) -> pp_app ppf "USubstFieldBits" "%a@ %a" pp_extr_struct_name sg pp_coq_quoted f
and pp_prim_uarray2 ppf (f: Cuttlebone.Extr.PrimUntyped.uarray2) = match f with
  | USubstElement pos -> pp_app ppf "USubstElement" "%d" pos
  | USubstElementBits (sg, pos) -> pp_app ppf "USubstElementBits" "%a@ %d" pp_extr_array_type sg pos

let pp_pos ppf pos =
  pp_quoted ppf (Pos.to_string pos)

let pp_maybe_pos print_positions constructor pp ppf a =
  if print_positions then pp_app ppf constructor "%a@ %a" pp_pos a.lpos pp a.lcnt
  else pp ppf a.lcnt

let rec pp_action print_positions ppf (a: ResolvedAST.uaction locd) =
  let pp_action =
    pp_action print_positions in
  let pp_binding =
    pp_pair (pp_quoted <<< lcnt) pp_action in
  let rec pp ppf (a: ResolvedAST.uaction) =
    let pp_app fn fmt = pp_app ppf fn fmt in
    match a with
    | Fail tau -> pp_app "UFail" "%a" pp_type_wrapped tau
    | Var v -> pp_app "UVar" "%a" pp_quoted v
    | Const v ->
       (match try_enum_const v with
        | Some (sg, enumerator) ->
           pp_app "USugar" "%a"
             (fun _ () -> pp_app "UConstEnum" "%s_sig@ %a" sg.enum_name pp_quoted enumerator) ()
        | None ->
           pp_app "UConst" "(tau := %a)@ %a" pp_type_unwrapped (typ_of_value v) pp_value v)
    (* | ConstString s ->
     *    pp_app "UConstString" "%a" pp_quoted s *)
    | Assign (v, a) ->
       pp_app "UAssign" "%a@ %a" pp_quoted v.lcnt pp_action a
    | If (cond, tb, fb) ->
       pp_app "UIf" "%a@ %a@ %a" pp_action cond pp_action tb pp_action fb
    | Read (p, r) ->
       pp_app "URead" "%a@ %a" pp_port p pp_reg_name r.lcnt
    | Write (p, r, v) ->
       pp_app "UWrite" "%a@ %a@ %a" pp_port p pp_reg_name r.lcnt pp_action v
    | Unop { fn; arg } ->
       pp_app "UUnop" "%a@ %a" pp_prim_ufn1 fn.lcnt pp_action arg
    | Binop { fn; a1; a2 } ->
       pp_app "UBinop" "%a@ %a@ %a" pp_prim_ufn2 fn.lcnt pp_action a1 pp_action a2
    | ExternalCall { fn; arg } ->
       pp_app "UExternalCall" "%a@ %a" pp_raw fn.lcnt.ffi_name pp_action arg
    | InternalCall { fn; args } ->
       pp_app "UInternalCall" "%a@ %a" pp_raw fn.int_name (pp_list pp_action) args
    | Sugar u -> pp_app "USugar" "%a" pp_sugar u
  and pp_sugar ppf u =
    let pp_app fn fmt = pp_app ppf fn fmt in
    match u with
    | AstError -> pp_raw ppf "AstError"
    | Skip ->
       pp_raw ppf "USkip"
    | ConstString s ->
       pp_app "UConstString" "%a" pp_quoted s
    | Progn actions ->
       pp_app "UProgn" "%a" (pp_list pp_action) actions
    | Let (bindings, body) ->
       pp_app "ULet" "%a@ %a" (pp_list pp_binding) bindings pp_action body
    | When (cond, body) ->
       pp_app "UWhen" "%a@ %a" pp_action cond pp_action body
    | Switch { operand; default; branches } ->
       pp_app "USwitch" "%a@ %a@ %a" pp_action operand
         pp_action default (pp_list (pp_pair pp_action pp_action)) branches
    | StructInit { sg; fields } ->
       pp_app "UStructInit" "%a@ %a" pp_struct_name sg (pp_list pp_binding) fields
    | ArrayInit { sg; elements } ->
       pp_app "UArrayInit" "%a@ %a" pp_array_type sg (pp_list pp_action) elements in
  pp_maybe_pos print_positions "UAPos" pp ppf a

let pp_rule position_printer ppf (name, action) =
  fprintf ppf "@[<2>Definition %s_body : uaction reg_t ext_fn_t :=@ %a@]."
    name (pp_action position_printer) action

let pp_scheduler print_positions ppf (name, scheduler) =
  let rec loop ppf (s: ResolvedAST.uscheduler locd) =
    let pp ppf (s: ResolvedAST.uscheduler) = match s with
      | Done ->
         pp_raw ppf "UDone"
      | Cons (r, s) ->
         pp_app ppf "UCons" "%a@ %a" pp_raw r.lcnt loop s
      | Try (r, s1, s2) ->
         pp_app ppf "UTry" "%a@ @[<v>%a@ %a@]"
           pp_raw r.lcnt loop s1 loop s2 in
    pp_maybe_pos print_positions "USPos" pp ppf s in
  fprintf ppf "@[<2>Definition %s : scheduler :=@ tc_scheduler @[%a@]@]."
    name loop scheduler;
  brk 2 ppf;
  fprintf ppf "@[<2>Definition %s_circuit : register_update_circuitry R Sigma :=@ " name;
  fprintf ppf "@[<2>compile_scheduler@ rules@ %s@].@]" name;
  brk 2 ppf;
  fprintf ppf "@[<2>Definition %s_eval (sigma: forall f, Sigma f)@ : Log R ContextEnv :=@ " name;
  fprintf ppf "@[<2>interp_scheduler@ (ContextEnv.(create) r)@ sigma@ rules@ %s@].@]" name

let pp_int_fn ~print_positions ppf (_, { int_name; int_argspec; int_retType; int_body }) =
  let p fmt = fprintf ppf fmt in
  p "@[<v>@[<hv 2>Definition %s {reg_t ext_fn_t} : UInternalFunction reg_t ext_fn_t := {|@ " int_name;
  p "int_name := %a;@ " pp_quoted int_name;
  p "int_argspec := %a;@ " (pp_list (pp_pair pp_quoted pp_type_unwrapped)) int_argspec;
  p "int_retType := %a;@ " pp_type_unwrapped int_retType;
  p "int_body := %a;" (pp_action print_positions) int_body;
  p "@]@ |}.@]"

let pp_tc_rules ppf (rules: (string * _) list) =
  fprintf ppf "@[<2>Definition rules :=@ @[<2>tc_rules R Sigma@ (fun rl => %a)@].@]"
    (pp_match (pp_raw <<< fst) (fun ppf r -> fprintf ppf "%s_body" (fst r)))
    ("rl", rules)

let pp_reg_init_vals ppf (registers: reg_signature list) =
  fprintf ppf "@[<2>Definition r idx : R idx :=@ %a.@]"
    (pp_match pp_reg_name (pp_value <<< reg_init)) ("idx", registers)

let pp_mod ~print_positions ppf ({ name; registers; rules; schedulers; _ }: resolved_module) =
  let name = name.lcnt in
  fprintf ppf "@[<v>@[<v 2>Module %s.@ " name;
  pp_reg_t ppf registers; brk 2 ppf;
  pp_rule_name_t ppf rules; brk 2 ppf;
  pp_reg_types ppf registers; brk 2 ppf;
  pp_reg_init_vals ppf registers; brk 2 ppf;
  pp_seq_trailer (brk 2) (pp_rule print_positions) ppf rules;
  pp_tc_rules ppf rules;
  pp_seq_header (brk 2) (pp_scheduler print_positions) ppf schedulers;
  fprintf ppf "@]@ End %s.@]" name

let pp_preamble ppf =
  fprintf ppf "Require Import Koika.Frontend."

let _ =
  ResolvedAST.debug_printer :=
    { debug_print = (fun a ->
        fprintf (formatter_of_out_channel stderr) "%a@."
          (pp_action false) (locd_make (Pos.StrPos "") a)) }

let partition_fns (fns: (string * resolved_fndecl) list) =
  List.fold_right (fun (name, fn) (extf, intf) ->
      match fn with
      | ExternalDecl fn -> (fn :: extf, intf)
      | InternalDecl fn -> (extf, (name, fn) :: intf))
  fns ([], [])

let main out ({ r_types; r_fns; r_mods }: resolved_unit) =
  let types = topo_sort_types (List.map snd (StringMap.bindings r_types.td_all)) in
  let enums, structs = partition_types types in
  let extfuns, intfuns = partition_fns r_fns.fn_ordered in
  let ppf = formatter_of_out_channel out in
  let print_positions = false in

  fprintf ppf "@[<v>";
  pp_preamble ppf; brk 2 ppf;
  pp_seq_trailer (brk 2) pp_enum ppf enums;
  pp_seq_trailer (brk 2) pp_struct ppf structs;
  pp_ext_fn_t ppf extfuns; brk 2 ppf;
  pp_ext_fn_Sigma ppf extfuns;
  pp_seq_header (brk 2) (pp_int_fn ~print_positions) ppf intfuns;
  pp_seq_header (brk 2) (pp_mod ~print_positions) ppf r_mods;
  fprintf ppf "@]@.";
