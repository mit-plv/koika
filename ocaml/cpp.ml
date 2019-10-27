open Common
module SGA = SGALib.SGA

(* #line pragmas make the C++ code harder to read, and they cover too-large a
   scope (in particular, the last #line pragma in a program overrides positions
   for all subsequent code, while we'd want to use the C++ positions for these
   lines) *)
let add_line_pragmas = false

type ('pos_t, 'var_t, 'rule_name_t, 'reg_t, 'ext_fn_t) cpp_rule_t = {
    rl_name: 'rule_name_t;
    rl_footprint: 'reg_t list;
    rl_body: ('pos_t, 'var_t, 'reg_t, 'ext_fn_t) SGA.rule;
  }

type ('pos_t, 'var_t, 'rule_name_t, 'reg_t, 'ext_fn_t) cpp_input_t = {
    cpp_classname: string;
    cpp_header_name: string;

    cpp_pos_of_pos: 'pos_t -> Pos.t;
    cpp_var_names: 'var_t -> string;
    cpp_rule_names: 'rule_name_t -> string;

    cpp_scheduler: ('pos_t, 'rule_name_t) SGA.scheduler;
    cpp_rules: ('pos_t, 'var_t, 'rule_name_t, 'reg_t, 'ext_fn_t) cpp_rule_t list;

    cpp_registers: 'reg_t list;
    cpp_register_sigs: 'reg_t -> reg_signature;
    cpp_ext_sigs: 'ext_fn_t -> ffi_signature;

    cpp_extfuns: string option;
  }

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf

type program_info =
  { mutable pi_committed: bool;
    mutable pi_needs_multiprecision: bool;
    mutable pi_user_types: (string * typ) list;
    pi_ext_funcalls: (Common.ffi_signature, unit) Hashtbl.t }

let fresh_program_info () =
  { pi_committed = false;
    pi_needs_multiprecision = false;
    pi_user_types = [];
    pi_ext_funcalls = Hashtbl.create 50 }

let assert_uncommitted { pi_committed; _ } =
  assert (not pi_committed)

let request_multiprecision pi =
  assert_uncommitted pi;
  pi.pi_needs_multiprecision <- true

let register_type (pi: program_info) nm tau =
  match List.assoc_opt nm pi.pi_user_types with
  | Some tau' ->
     if tau <> tau' then
       failwith (sprintf "Incompatible uses of type name `%s':\n%s\n%s"
                   nm (typ_to_string tau) (typ_to_string tau'))
  | None ->
     assert_uncommitted pi;
     pi.pi_user_types <- (nm, tau) :: pi.pi_user_types

let gensym_prefix = "_"
let gensym, gensym_reset = make_gensym gensym_prefix
(* Mangling takes care of collisions with the gensym *)

module Mangling = struct
  let reserved =
    StringSet.of_list
      ["alignas"; "alignof"; "and"; "and_eq"; "asm"; "atomic_cancel";
       "atomic_commit"; "atomic_noexcept"; "auto"; "bitand"; "bitor"; "bool";
       "break"; "case"; "catch"; "char"; "char8_t"; "char16_t"; "char32_t";
       "class"; "compl"; "concept"; "const"; "consteval"; "constexpr";
       "constinit"; "const_cast"; "continue"; "co_await"; "co_return";
       "co_yield"; "decltype"; "default"; "delete"; "do"; "double";
       "dynamic_cast"; "else"; "enum"; "explicit"; "export"; "extern"; "false";
       "float"; "for"; "friend"; "goto"; "if"; "inline"; "int"; "long";
       "mutable"; "namespace"; "new"; "noexcept"; "not"; "not_eq"; "nullptr";
       "operator"; "or"; "or_eq"; "private"; "protected"; "public"; "reflexpr";
       "register"; "reinterpret_cast"; "requires"; "return"; "short"; "signed";
       "sizeof"; "static"; "static_assert"; "static_cast"; "struct"; "switch";
       "synchronized"; "template"; "this"; "thread_local"; "throw"; "true";
       "try"; "typedef"; "typeid"; "typename"; "union"; "unsigned"; "using";
       "virtual"; "void"; "volatile"; "wchar_t"; "while"; "xor"; "xor_eq"]

  let mangling_prefix = "_renamed"
  let specials_re = Str.regexp (sprintf "^\\(_[A-Z]\\|%s\\|%s\\)" mangling_prefix gensym_prefix)
  let dunder_re = Str.regexp "__+"
  let dunder_anchored_re = Str.regexp "^.*__"
  let dunder_target_re = Str.regexp "_\\(dx\\)\\([0-9]\\)_"
  let valid_name_re = Str.regexp "^[A-Za-z_][A-Za-z0-9_]*"

  let needs_mangling name =
    StringSet.mem name reserved
    || Str.string_match specials_re name 0
    || Str.string_match dunder_anchored_re name 0

  let escape_dunders name =
    let name = Str.global_replace dunder_target_re "_\\10\\2_" name in
    let subst _ = sprintf "_dx%d_" (Str.match_end () - Str.match_beginning ()) in
    Str.global_substitute dunder_re subst name

  let check_valid name =
    if not @@ Str.string_match valid_name_re name 0 then
      failwith (sprintf "Invalid name: `%s'" name)

  let mangle_name ?(prefix="") name =
    check_valid name;
    let unmangled = if prefix = "" then name else prefix ^ "_" ^ name in
    if needs_mangling unmangled then
      escape_dunders (prefix ^ mangling_prefix ^ name)
    else unmangled

  let mangle_register_sig r =
    { r with reg_name = mangle_name r.reg_name }

  let mangle_function_sig f =
    { f with ffi_name = mangle_name f.ffi_name }

  let mangle_unit u =
    { u with (* The prefixes are needed to prevent collisions with ‘prims::’ *)
      cpp_classname = mangle_name ~prefix:"module" u.cpp_classname;
      cpp_rule_names = (fun rl -> rl |> u.cpp_rule_names |> mangle_name ~prefix:"rule");
      cpp_register_sigs = (fun r -> r |> u.cpp_register_sigs |> mangle_register_sig);
      cpp_ext_sigs = (fun f -> f |> u.cpp_ext_sigs |> mangle_function_sig) }
end

let cpp_enum_name pi sg =
  let name = Mangling.mangle_name ~prefix:"enum" sg.enum_name in
  register_type pi name (Enum_t sg); name

let cpp_struct_name pi sg =
  let name = Mangling.mangle_name ~prefix:"struct" sg.struct_name in
  register_type pi sg.struct_name (Struct_t sg); name

let cpp_type_of_type
      (pi: program_info)
      (tau: typ) =
  match tau with
  | Bits_t sz ->
     assert (sz >= 0);
     if sz > 64 then
       request_multiprecision pi;
     if sz = 0 then
       "unit"
     else if sz <= 1024 then
       sprintf "bits<%d>" sz
     else
       failwith (sprintf "Unsupported size: %d" sz)
  | Enum_t sg -> cpp_enum_name pi sg
  | Struct_t sg -> cpp_struct_name pi sg

let cpp_enumerator_name pi ?(enum=None) nm =
  let nm = Mangling.mangle_name nm in
  match enum with
  | None -> nm
  | Some sg -> sprintf "%s::%s" (cpp_enum_name pi sg) nm

let cpp_field_name nm =
  Mangling.mangle_name nm

let register_subtypes (pi: program_info) tau =
  let rec loop tau = match tau with
    | Bits_t sz -> if sz > 64 then request_multiprecision pi
    | Enum_t sg -> ignore (cpp_enum_name pi sg)
    | Struct_t sg -> ignore (cpp_struct_name pi sg);
                     List.iter (loop << snd) sg.struct_fields in
  loop tau

let z_to_hex bitlength z =
  let w = (bitlength + 7) / 8 in
  let fmt = sprintf "%%0#%dx" (w + 2) in
  Z.format fmt z

let cpp_const_init (pi: program_info) sz cst =
  assert (sz >= 0);
  if sz > 64 then
    request_multiprecision pi;
  let cst =
    z_to_hex sz cst in
  if sz = 0 then
    "prims::tt"
  else if sz <= 8 then
    sprintf "UINT8(%s)" cst
  else if sz <= 16 then
    sprintf "UINT16(%s)" cst
  else if sz <= 32 then
    sprintf "UINT32(%s)" cst
  else if sz <= 64 then
    sprintf "UINT64(%s)" cst
  else if sz <= 128 then
    sprintf "UINT128(%s)" cst
  else if sz <= 256 then
    sprintf "UINT256(%s)" cst
  else if sz <= 512 then
    sprintf "UINT512(%s)" cst
  else if sz <= 1024 then
    sprintf "UINT1024(%s)" cst
  else
    failwith (sprintf "Unsupported size: %d" sz)

let cpp_type_needs_allocation _tau =
  false (* boost::multiprecision has literals *)

let assert_bits (tau: typ) =
  match tau with
  | Bits_t sz -> sz
  | _ -> failwith "Expecting bits, not struct or enum"

let cpp_ext_funcall f a =
  (* The current implementation of external functions requires the client to
     pass a class implementing those functions as a template argument.  An
     other approach would have made external functions virtual methods, but
     then they couldn't have been templated functions. *)
  (* The ‘.template’ part ensures that ‘extfuns.xyz<p>()’ is not parsed as a
     comparison. *)
  sprintf "extfuns.template %s(%s)" f a

let cpp_bits1_fn_name (f: SGA.PrimTyped.fbits1) =
  sprintf "prims::%s"
    (match f with
     | Not sz -> sprintf "lnot<%d>" sz
     | ZExtL (sz, width) -> sprintf "zextl<%d, %d>" sz width
     | ZExtR (sz, width) -> sprintf "zextr<%d, %d>" sz width
     | Part (sz, offset, width) -> sprintf "part<%d, %d, %d>" sz offset width)

let cpp_bits2_fn_name (f: SGA.PrimTyped.fbits2) =
  sprintf "prims::%s"
    (match f with
     | And sz -> sprintf "land<%d>" sz
     | Or sz -> sprintf "lor<%d>" sz
     | Xor sz -> sprintf "lxor<%d>" sz
     | Lsl (bits_sz, shift_sz) -> sprintf "lsl<%d, %d>" bits_sz shift_sz
     | Lsr (bits_sz, shift_sz) -> sprintf "lsr<%d, %d>" bits_sz shift_sz
     | Concat (sz1, sz2) -> sprintf "concat<%d, %d>" sz1 sz2
     | Sel sz -> sprintf "sel<%d, %d>" sz (SGALib.SGA.log2 sz)
     | PartSubst (sz, offset, width) -> sprintf "part_subst<%d, %d, %d>" sz offset width
     | IndexedPart (sz, width) -> sprintf "indexed_part<%d, %d, %d>" sz (SGALib.SGA.log2 sz) width
     | Plus sz -> sprintf "plus<%d>" sz
     | Minus sz -> sprintf "minus<%d>" sz
     | EqBits sz -> sprintf "eq<%d>" sz
     | Compare (signed, cmp, sz) ->
        sprintf "%s%s<%d>"
          (if signed then "s" else "")
          (match cmp with CLt -> "lt" | CGt -> "gt" | CLe -> "le" | CGe -> "ge")
          sz)

let cpp_get_preamble () =
  let inc = open_in "preamble.hpp" in
  let preamble = really_input_string inc (in_channel_length inc) in
  close_in inc;
  preamble

let reconstruct_switch action =
  let rec loop v = function
    | SGA.If (_, _,
              SGA.Binop (_,
                         (SGA.PrimTyped.Eq _ | SGA.PrimTyped.Bits2 (SGA.PrimTyped.EqBits _)),
                         SGA.Var (_, v', _, _m),
                         SGA.Const (_, ((SGA.Bits_t _ | SGA.Enum_t _) as tau), cst)),
              tbr, fbr) when (match v with
                              | Some v -> v' = v
                              | None -> true) ->
       let default, branches = match loop (Some v') fbr with
         | Some (_, default, branches) -> default, branches
         | None -> fbr, [] in
       Some (v', default, (SGALib.Util.value_of_sga_value tau cst, tbr) :: branches)
    | _ -> None in
  match loop None action with
  | Some (_, _, [_]) | None -> None
  | res -> res

type target_info =
  { tau: typ; declared: bool; name: var_t }

type assignment_target =
  | NoTarget
  | VarTarget of target_info

type assignment_result =
  | NotAssigned
  | Assigned of var_t
  | PureExpr of string
  | ImpureExpr of string

let compile (type pos_t var_t rule_name_t reg_t ext_fn_t)
      (hpp: (pos_t, var_t, rule_name_t, reg_t, ext_fn_t) cpp_input_t) =
  let buffer = ref (Buffer.create 0) in
  let hpp = Mangling.mangle_unit hpp in

  let nl _ = Buffer.add_string !buffer "\n" in
  let pk k fmt = Printf.kbprintf k !buffer fmt in
  let p fmt = pk nl fmt in
  let pr fmt = pk ignore fmt in
  let p_buffer b = Buffer.add_buffer !buffer b in
  let set_buffer b = let b' = !buffer in buffer := b; b' in

  let program_info = fresh_program_info () in
  let cpp_type_of_type = cpp_type_of_type program_info in
  let cpp_enum_name = cpp_enum_name program_info in
  let cpp_struct_name = cpp_struct_name program_info in
  let cpp_enumerator_name = cpp_enumerator_name program_info in
  let cpp_const_init = cpp_const_init program_info in

  let rec iter_sep sep body = function
    | [] -> ()
    | item :: [] -> body item
    | item :: items -> body item; sep (); iter_sep sep body items in

  let p_comment fmt =
    pr "/* "; pk (fun _ -> pr " */"; nl ()) fmt in

  let p_ifdef condition pbody =
    p "#if%s" condition;
    pbody ();
    p "#endif" in

  let p_scoped header ?(terminator="") pbody =
    p "%s {" header;
    let r = pbody () in
    p "}%s" terminator;
    r in

  let p_fn ~typ ~name ?(args="") ?(annot="") pbody =
    p_scoped (sprintf "%s %s(%s)%s" typ name args annot) pbody in

  let p_includeguard pbody =
    let cpp_define = sprintf "%s_HPP" (String.uppercase_ascii hpp.cpp_classname) in
    p "#ifndef %s" cpp_define;
    p "#define %s" cpp_define;
    nl ();
    pbody ();
    p "#endif" in

  let p_decl' ?(prefix = "") ?(init = None) t name =
    pr "%s" prefix;
    match init with
    | None -> p "%s %s;" t name
    | Some init -> p "%s %s = %s;" t name init in

  let p_decl ?(prefix = "") ?(init = None) tau name =
    p_decl' ~prefix ~init (cpp_type_of_type tau) name in

  let bits_to_Z bits =
    Z.(Array.fold_right (fun b z ->
           (if b then one else zero) + shift_left z 1)
         bits zero) in

  let rec sp_value (v: value) =
    match v with
    | Bits bs -> sp_bits_value bs
    | Enum (sg, v) -> sp_enum_value sg v
    | Struct (sg, fields) -> sp_struct_value sg fields
  and sp_bits_value bs =
    let z = bits_to_Z bs in
    let bitlength = Array.length bs in
    cpp_const_init bitlength z
  and sp_enum_value sg v =
    match enum_find_field_opt sg v with
    | None -> sprintf "static_cast<%s>(%s)" (cpp_enum_name sg) (sp_bits_value v)
    | Some nm -> cpp_enumerator_name ~enum:(Some sg) nm
  and sp_struct_value sg fields =
    let fields = String.concat ", " (List.map sp_value fields) in
    sprintf "%s{ %s }" (cpp_struct_name sg) fields in

  let sp_value_printer = function
    | Bits_t sz -> sprintf "repr<%d>" sz
    | Enum_t _ | Struct_t _ -> "repr" in

  let sp_comparator ?(ns="") = function
    | Bits_t sz -> sprintf "%seq<%d>" ns sz
    | Enum_t _ | Struct_t _ -> ns ^ "eq" in

  let sp_comparison ?(ns="") tau a1 a2 =
    sprintf "%s(%s, %s)" (sp_comparator ~ns tau) a1 a2 in

  (* Not needed: unpack(0) instead *)
  (* let sp_initializer tau =
   *   let bs0 sz = Array.make sz false in
   *   match tau with
   *   | Bits_t sz -> sp_value (Bits (bs0 sz))
   *   | Enum_t sg -> sp_value (Enum (sg, (bs0 sg.enum_bitsize)))
   *   | Struct_t sg -> sprintf "%s {}" (cpp_struct_name sg) in *)

  let sp_parenthesized arg =
    if arg = "" then "" else sprintf "(%s)" arg in

  let sp_packer ?(ns = "") ?(arg = "") tau =
    let parg = sp_parenthesized arg in
    match tau with
    | Bits_t _ -> arg
    | Enum_t _ | Struct_t _ -> sprintf "%spack%s" ns parg in

  let sp_unpacker ?(ns = "") ?(arg = "") tau =
    let parg = sp_parenthesized arg in
    match tau with
    | Bits_t _ -> arg
    | Enum_t sg -> sprintf "%sunpack<%s, %d>%s" ns (cpp_enum_name sg) (enum_sz sg) parg
    | Struct_t sg -> sprintf "%sunpack<%s, %d>%s" ns (cpp_struct_name sg) (struct_sz sg) parg in

  let p_enum_decl sg =
    let esz = enum_sz sg in
    let nm = cpp_enum_name sg in
    if esz = 0 then failwith (sprintf "Enum %s is empty (its members are zero-bits wide)" nm);
    if esz > 64 then failwith (sprintf "Enum %s is too large (its members are %d-bits wide; the limit is 64)" nm esz);
    let decl = sprintf "enum class %s : %s" nm (cpp_type_of_type (Bits_t esz)) in
    p_scoped decl ~terminator:";" (fun () ->
        iter_sep (fun () -> p ", ")
          (fun (name, v) -> p "%s = %s" (cpp_enumerator_name name) (sp_bits_value v)) sg.enum_members) in

  let p_struct_decl sg =
    let decl = sprintf "struct %s" (cpp_struct_name sg) in
    p_scoped decl ~terminator:";" (fun () ->
        List.iter (fun (name, tau) -> p_decl tau (cpp_field_name name)) sg.struct_fields) in

  let p_printer tau =
    let v_arg = "val" in
    let v_tau = cpp_type_of_type tau in
    let v_style = "const repr_style style = repr_style::full" in
    let v_argdecl = sprintf "const %s %s, %s" v_tau v_arg v_style in

    let p_printer pbody =
      p_fn ~typ:"static _unused std::string "
        ~name:"repr" ~args:v_argdecl pbody in

    let p_enum_printer sg =
      p_printer (fun () ->
          p_scoped (sprintf "switch (%s)" v_arg) (fun () ->
              List.iter (fun (nm, _v) ->
                  let lbl = cpp_enumerator_name ~enum:(Some sg) nm in
                  p "case %s: return \"%s::%s\";" lbl sg.enum_name nm) (* unmangled *)
                sg.enum_members;
              let v_sz = typ_sz tau in
              let bits_sz_tau = cpp_type_of_type (Bits_t v_sz) in
              let v_cast = sprintf "static_cast<%s>(%s)" bits_sz_tau v_arg in
              p "default: return \"%s{\" + repr<%d>(%s, style) + \"}\";"
                sg.enum_name v_sz v_cast)) in (* unmangled *)

    let p_struct_printer sg =
      p_printer (fun () ->
          p "std::ostringstream stream;";
          p "stream << \"%s { \";" sg.struct_name; (* unmangled *)
          List.iter (fun (fname, ftau) ->
              p "stream << \"  .%s = \" << %s(%s.%s, style) << \"; \";" (* unmangled *)
                fname (sp_value_printer ftau) v_arg (cpp_field_name fname))
            sg.struct_fields;
          p "stream << \"}\";";
          p "return stream.str();") in

    match tau with
    | Bits_t _ -> ()
    | Enum_t sg -> p_enum_printer sg
    | Struct_t sg -> p_struct_printer sg in

  let p_prims tau =
    let v_sz = typ_sz tau in
    let v_arg, v1, v2 = "val", "v1", "v2" in
    let v_tau = cpp_type_of_type tau in
    let v_argdecl v = sprintf "const %s %s" v_tau v in
    let bits_arg = "bits" in
    let bits_tau = cpp_type_of_type (Bits_t v_sz) in
    let bits_argdecl = sprintf "const %s %s" bits_tau bits_arg in

    let p_eq prbody =
      p_fn ~typ:"static _unused bool "
        ~args:(sprintf "%s, %s" (v_argdecl v1) (v_argdecl v2))
        ~name:"eq" (fun () -> pr "return ("; prbody (); p ");") in
    let p_pack pbody =
      p_fn ~typ:("static _unused " ^ bits_tau)
        ~args:(v_argdecl v_arg) ~name:(sp_packer tau) pbody in
    let p_unpack pbody =
      p_fn ~typ:("template <> _unused " ^ v_tau)
        ~args:bits_argdecl ~name:(sp_unpacker tau) pbody in

    let p_enum_pack _ =
      p_pack (fun () -> p "return static_cast<%s>(%s);" bits_tau v_arg) in

    let p_enum_unpack _ =
      p_unpack (fun () -> p "return static_cast<%s>(%s);" v_tau bits_arg) in

    let p_enum_eq _sg =
      p_eq (fun () -> pr "%s == %s" v1 v2) in

    let sp_field_eq v1 v2 tau field =
      let field = cpp_field_name field in
      sp_comparison tau (v1 ^ "." ^ field) (v2 ^ "." ^ field) in

    let p_struct_eq sg =
      p_eq (fun () -> iter_sep (fun () -> pr " && ") (fun (nm, tau) ->
                          pr "%s" (sp_field_eq v1 v2 tau nm))
                        sg.struct_fields) in

    let p_struct_pack sg =
      let var = "packed" in
      p_pack (fun () ->
          p_decl (Bits_t v_sz) var ~init:(Some (cpp_const_init v_sz Z.zero));
          List.iteri (fun idx (fname, ftau) ->
              let sz = typ_sz ftau in
              let fname = cpp_field_name fname in
              let fval = sprintf "%s.%s" v_arg fname in
              let fpacked = sp_packer ftau ~arg:fval in
              if idx <> 0 then p "%s <<= %d;" var sz;
              p "%s |= %s;" var fpacked)
            sg.struct_fields;
          p "return %s;" var) in

    let p_struct_unpack sg =
      let var = "unpacked" in
      p_unpack (fun () ->
          p_decl tau var ~init:(Some "{}");
          List.fold_right (fun (fname, ftau) offset ->
              let sz = typ_sz ftau in
              let fname = cpp_field_name fname in
              let fval = sprintf "prims::truncate<%d, %d>(%s >> %du)"
                           sz v_sz bits_arg offset in
              let unpacked = sp_unpacker ~arg:fval ftau in
              p "%s.%s = %s;" var fname unpacked;
              offset + sz)
            sg.struct_fields 0 |> ignore;
          p "return %s;" var) in

    match tau with
    | Bits_t _ -> ()
    | Enum_t sg -> p_enum_eq sg; p_enum_pack sg; nl (); p_enum_unpack sg
    | Struct_t sg -> p_struct_eq sg; nl (); p_struct_pack sg; nl (); p_struct_unpack sg in

  let complete_user_types () =
    let reg_typ (_, t) = register_subtypes program_info t in
    List.iter reg_typ program_info.pi_user_types;
    program_info.pi_user_types in

  let p_type_declarations () =
    p "//////////////";
    p "// TYPEDEFS //";
    p "//////////////";
    nl ();
    let types = complete_user_types () in
    let types = topo_sort_types (sort_types (List.map snd types)) in
    let enums, structs = partition_types types in
    List.iter p_enum_decl enums;
    nl ();
    iter_sep nl p_struct_decl structs;
    nl ();
    p_ifdef "ndef SIM_MINIMAL" (fun () ->
        iter_sep nl p_printer types);
    nl ();
    p_scoped "namespace prims" (fun () ->
        iter_sep nl p_prims types) in

  let p_preamble () =
    p "//////////////";
    p "// PREAMBLE //";
    p "//////////////";
    nl ();
    program_info.pi_committed <- true;
    if program_info.pi_needs_multiprecision then (
      p "#define NEEDS_BOOST_MULTIPRECISION";
      nl ());
    p "%s" (cpp_get_preamble ());
  in

  let iter_registers f regs =
    List.iter (fun r -> f (hpp.cpp_register_sigs r)) regs in

  let iter_all_registers =
    let sigs = List.map hpp.cpp_register_sigs hpp.cpp_registers in
    fun f -> List.iter f sigs in

  let p_impl () =
    p "////////////////////";
    p "// IMPLEMENTATION //";
    p "////////////////////";
    nl ();

    let p_sim_class pbody =
      p_scoped (sprintf "template <typename extfuns_t> class %s" hpp.cpp_classname)
        ~terminator:";" pbody in

    let p_state_register r =
      p_decl (reg_type r) r.reg_name in

    let p_dump_register r =
      p "std::cout << \"%s = \" << %s(%s) << std::endl;"
        r.reg_name (sp_value_printer (reg_type r)) r.reg_name in

    let p_state_t () =
      p_scoped "struct state_t" ~terminator:";" (fun () ->
          iter_all_registers p_state_register;
          nl ();
          p_ifdef "ndef SIM_MINIMAL" (fun () ->
              p_fn ~typ:"void" ~name:"dump" ~annot:" const" (fun () ->
                  iter_all_registers p_dump_register))) in

    let p_log_register r =
      p "reg_log_t<%s> %s;" (cpp_type_of_type (reg_type r)) r.reg_name in

    let p_log_t () =
      p_scoped "struct log_t" ~terminator:";" (fun () ->
          iter_all_registers p_log_register) in

    let p_checked prbody =
      pr "CHECK_RETURN(";
      prbody ();
      p ");" in

    let backslash_re =
      Str.regexp "\\\\" in

    let sp_escaped_string s =
      Str.global_replace backslash_re "\\\\\\\\" s in

    let p_pos (pos: Pos.t) =
      if add_line_pragmas then
        match pos with
        | Unknown | StrPos _ | Filename _ -> ()
        | Range (filename, { rbeg = { line; _ }; _ }) ->
           p "#line %d \"%s\"" line (sp_escaped_string filename) in

    let p_rule (rule: (pos_t, var_t, rule_name_t, reg_t, ext_fn_t) cpp_rule_t) =
      gensym_reset ();

      let p_reset () =
        iter_registers (fun { reg_name; _ } ->
            p "log.%s.reset(Log.%s);" reg_name reg_name)
          rule.rl_footprint in

      let p_commit () =
        iter_registers (fun { reg_name; _ } ->
            p "Log.%s = log.%s;" reg_name reg_name)
          rule.rl_footprint;
        p "return true;" in

      let p_declare_target = function
        | VarTarget { tau; declared = false; name } ->
           p_decl tau name;
           VarTarget { tau; declared = true; name }
        | t -> t in

      let gensym_target_info tau prefix =
        { tau; declared = false; name = gensym prefix } in

      let gensym_target tau prefix =
        VarTarget (gensym_target_info tau prefix) in

      let ensure_target tau t =
        match t with
        | NoTarget -> gensym_target_info tau "ignored"
        | VarTarget info -> info in

      let p_ensure_declared tinfo =
        if not tinfo.declared then
          p_decl tinfo.tau tinfo.name;
        tinfo.name in

      let p_assign_expr ?(prefix = "") target result =
        match target, result with
        | VarTarget { declared = true; name; _ }, (PureExpr e | ImpureExpr e) ->
           if name <> e then p "%s = %s;" name e;
           Assigned name
        | VarTarget { tau; name; _ }, (PureExpr e | ImpureExpr e) ->
           p_decl ~prefix ~init:(Some e) tau name;
           Assigned name
        | NoTarget, ImpureExpr e ->
           p "%s;" e; (* Keep impure exprs like extfuns *)
           NotAssigned
        | _, _ -> result
      in

      let must_expr = function
        | (PureExpr _ | ImpureExpr _) as expr -> expr
        | Assigned v -> PureExpr v
        | NotAssigned -> assert false in

      let must_value = function
        | Assigned e | PureExpr e | ImpureExpr e -> e
        | NotAssigned -> assert false (* NotAssigned is only return when NoTarget is passed in *) in

      let is_impure_expr = function
        | ImpureExpr _ -> true
        | _ -> false in

      let taint (dependencies: assignment_result list) = function
        | PureExpr s when List.exists is_impure_expr dependencies -> ImpureExpr s
        | other -> other in

      let p_unop (fn: SGALib.SGA.PrimTyped.fn1) a1 =
        let open SGALib.SGA.PrimTyped in
        match fn with
        | Display fn ->
           let tau, args = match fn with
             | DisplayUtf8 sz -> Bits_t sz, sprintf "%s, repr_style::utf8" a1
             | DisplayValue tau -> SGALib.Util.typ_of_sga_type tau, a1 in
           ImpureExpr (sprintf "prims::display(%s(%s))" (sp_value_printer tau) args)
        | Conv (tau, fn) ->
           let ns = "prims::" in
           let tau = SGALib.Util.typ_of_sga_type tau in
           PureExpr (match fn with
                     | Pack -> sp_packer ~ns ~arg:a1 tau
                     | Unpack -> sp_unpacker ~ns ~arg:a1 tau
                     | Ignore -> sprintf "prims::ignore(%s)" a1)
        | Bits1 fn ->
           PureExpr (sprintf "%s(%s)" (cpp_bits1_fn_name fn) a1)
        | Struct1 (sg, idx) ->
           (* Extraction eliminated the single-constructor struct1 inductive (GetField) *)
           let fname, _tau = SGALib.Util.list_nth sg.struct_fields idx in
           let fname = cpp_field_name (SGALib.Util.string_of_coq_string fname) in
           PureExpr (sprintf "%s.%s" a1 fname)
      in

      let p_binop target (fn: SGALib.SGA.PrimTyped.fn2) a1 a2 =
        let open SGALib.SGA.PrimTyped in
        match fn with
        | Eq tau ->
           PureExpr (sp_comparison ~ns:"prims::" (SGALib.Util.typ_of_sga_type tau) a1 a2)
        | Bits2 fn ->
           PureExpr (sprintf "%s(%s, %s)" (cpp_bits2_fn_name fn) a1 a2)
        | Struct2 (sg, idx) ->
           (* Extraction eliminated the single-constructor struct2 inductive (SusbtField) *)
           let sg = SGALib.Util.struct_sig_of_sga_struct_sig sg in
           let fname, _tau = SGALib.Util.list_nth sg.struct_fields idx in
           let tinfo = ensure_target (Struct_t sg) target in
           let res = p_assign_expr (VarTarget tinfo) (PureExpr a1) in
           p "%s.%s = %s;" tinfo.name (cpp_field_name fname) a2;
           res in

      let assert_no_shadowing sg v tau v_to_string m =
        if SGALib.Util.member_mentions_shadowed_binding sg v tau m then
          failwith (sprintf "Variable %s is shadowed by a later binding, but the program references the original binding." (v_to_string v)) in

      let rec p_action (pos: Pos.t) (target: assignment_target) (rl: (pos_t, var_t, reg_t, _) SGA.action) =
        p_pos pos;
        match rl with
        | SGA.Fail (_, _) ->
           p "return false;";
           (match target with
            | NoTarget -> NotAssigned
            | VarTarget { declared = true; name; _ } -> Assigned name
            | VarTarget { tau; _ } ->
               PureExpr (sprintf "prims::unreachable<%s>()" (cpp_type_of_type tau)))
        | SGA.Var (sg, v, tau, m) ->
           assert_no_shadowing sg v tau hpp.cpp_var_names m;
           PureExpr (hpp.cpp_var_names v)
        | SGA.Const (_, tau, cst) ->
           let res = PureExpr (sp_value (SGALib.Util.value_of_sga_value tau cst)) in
           if cpp_type_needs_allocation tau then
             let ctarget = gensym_target (SGALib.Util.typ_of_sga_type tau) "cst" in
             must_expr (p_assign_expr ~prefix:"static const" ctarget res)
           else res
        | SGA.Assign (sg, v, tau, m, ex) ->
           assert_no_shadowing sg v tau hpp.cpp_var_names m;
           let vtarget = VarTarget { tau = SGALib.Util.typ_of_sga_type tau;
                                     declared = true; name = hpp.cpp_var_names v } in
           p_assign_and_ignore vtarget (p_action pos vtarget ex);
           p_assign_expr target (PureExpr "prims::tt")
        | SGA.Seq (_, _, a1, a2) ->
           p_assign_and_ignore NoTarget (p_action pos NoTarget a1);
           p_action pos target a2
        | SGA.Bind (_, tau, _, v, expr, rl) ->
           let target = p_declare_target target in
           p_scoped "/* bind */" (fun () ->
               p_bound_var_assign pos tau v expr;
               p_assign_expr target (p_action pos target rl))
        | SGA.If (_, _, cond, tbr, fbr) ->
           let target = p_declare_target target in
           (match reconstruct_switch rl with
            | Some (var, default, branches) ->
               p_switch pos target var default branches
            | None ->
               let ctarget = gensym_target (Bits_t 1) "c" in
               let cexpr = p_action pos ctarget cond in
               (p_scoped (sprintf "if (bool(%s))" (must_value cexpr))
                  (fun () -> p_assign_and_ignore target (p_action pos target tbr)));
               p_scoped "else"
                 (fun () -> p_assign_expr target (p_action pos target fbr)))
        | SGA.Read (_, port, reg) ->
           let r = hpp.cpp_register_sigs reg in
           let var = p_ensure_declared (ensure_target (reg_type r) target) in
           p_checked (fun () ->
               match port with
               | P0 -> pr "log.%s.read0(&%s, state.%s, Log.%s.rwset)" r.reg_name var r.reg_name r.reg_name
               | P1 -> pr "log.%s.read1(&%s, Log.%s.rwset)" r.reg_name var r.reg_name);
           Assigned var
        | SGA.Write (_, port, reg, expr) ->
           let r = hpp.cpp_register_sigs reg in
           let vt = gensym_target (reg_type r) "v" in
           let v = must_value (p_action pos vt expr) in
           let fn_name = match port with
             | P0 -> "write0"
             | P1 -> "write1" in
           p_checked (fun () ->
               pr "log.%s.%s(%s, Log.%s.rwset)"
                 r.reg_name fn_name v r.reg_name);
           p_assign_expr target (PureExpr "prims::tt")
        | SGA.Unop (_, fn, a) ->
           let fsig = SGALib.SGA.PrimSignatures.coq_Sigma1 fn in
           let a = p_action pos (gensym_target (SGALib.Util.argType 1 fsig 0) "x") a in
           taint [a] (p_unop fn (must_value a))
        | SGA.Binop (_, fn, a1, a2) ->
           let fsig = SGALib.SGA.PrimSignatures.coq_Sigma2 fn in
           let a1 = p_action pos (gensym_target (SGALib.Util.argType 2 fsig 0) "x") a1 in
           let a2 = p_action pos (gensym_target (SGALib.Util.argType 2 fsig 1) "y") a2 in
           taint [a1; a2] (p_binop target fn (must_value a1) (must_value a2))
        | SGA.ExternalCall (_, fn, a) ->
           let ffi = hpp.cpp_ext_sigs fn in
           let a = p_action pos (gensym_target ffi.ffi_argtype "x") a in
           Hashtbl.replace program_info.pi_ext_funcalls ffi ();
           ImpureExpr (cpp_ext_funcall ffi.ffi_name (must_value a))
        | SGA.APos (_, _, pos, a) ->
           p_action (hpp.cpp_pos_of_pos pos) target a
      and p_switch pos target var default branches =
        let rec loop = function
          | [] ->
             p "default:";
             p_assign_expr target (p_action pos target default);
          | (const, action) :: branches ->
             p "case %s:" (sp_value const);
             p_assign_and_ignore target (p_action pos target action);
             p "break;";
             loop branches in
        p_scoped (sprintf "switch (%s)" (hpp.cpp_var_names var)) (fun () ->
            loop branches)
      and p_bound_var_assign pos tau v expr =
        let needs_tmp = SGALib.Util.action_mentions_var v expr in
        let tau = SGALib.Util.typ_of_sga_type tau in
        let vtarget = VarTarget { tau; declared = false; name = hpp.cpp_var_names v } in
        let expr =
          if needs_tmp then
            (* ‘int x = x + 1;’ doesn't work in C++ (basic.scope.pdecl), so if
               the rhs uses a variable with name ‘v’ we need a temp variable. *)
            let vtmp = gensym_target tau "tmp" in
            must_expr (p_assign_expr vtmp (p_action pos vtmp expr))
          else p_action pos vtarget expr in
        p_assign_and_ignore vtarget expr
      and p_assign_and_ignore target expr =
        ignore (p_assign_expr target expr) in

      p_fn ~typ:"bool" ~name:(hpp.cpp_rule_names rule.rl_name) (fun () ->
          p_reset ();
          nl ();
          p_assign_and_ignore NoTarget (p_action Pos.Unknown NoTarget rule.rl_body);
          nl ();
          p_commit ()) in

    let p_constructor () =
      let p_init_data0 { reg_name = nm; _ } =
        p "Log.%s.data0 = state.%s;" nm nm in
      p_fn ~typ:"explicit" ~name:hpp.cpp_classname
        ~args:"const state_t init" ~annot:" : state(init)"
        (fun () -> iter_all_registers p_init_data0) in

    let rec p_scheduler pos s =
      p_pos pos;
      match s with
      | SGA.Done -> ()
      | SGA.Cons (rl_name, s) ->
         p "%s();" (hpp.cpp_rule_names rl_name);
         p_scheduler pos s
      | SGA.Try (rl_name, s1, s2) ->
         p_scoped (sprintf "if (%s())" (hpp.cpp_rule_names rl_name)) (fun () -> p_scheduler pos s1);
         p_scoped "else" (fun () -> p_scheduler pos s2)
      | SGA.SPos (pos, s) ->
         p_scheduler (hpp.cpp_pos_of_pos pos) s in

    let p_cycle () =
      let p_commit_register r =
        p "state.%s = Log.%s.commit();" r.reg_name r.reg_name in
      p_fn ~typ:"void" ~name:"cycle" (fun () ->
          p_scheduler Pos.Unknown hpp.cpp_scheduler;
          iter_all_registers p_commit_register) in

    let p_run () =
      let typ = sprintf "template<typename T> %s&" hpp.cpp_classname in
      p_fn ~typ ~name:"run" ~args:"T ncycles" (fun () ->
          p_scoped "for (T cycle_id = 0; cycle_id < ncycles; cycle_id++)"
            (fun () -> p "cycle();");
          p "return *this;") in

    let p_snapshot () =
      p_fn ~typ:"state_t" ~name:"snapshot" (fun () -> p "return state;") in

    p_sim_class (fun () ->
        p "public:";
        p_state_t ();
        nl ();

        p "private:";
        p_log_t ();
        nl ();
        p "log_t Log;";
        p "log_t log;";
        p "state_t state;";
        p "extfuns_t extfuns;";
        nl ();
        iter_sep nl p_rule hpp.cpp_rules;
        nl ();

        p "public:";
        p_constructor ();
        nl ();
        p_cycle ();
        nl ();
        p_run ();
        nl ();
        p_snapshot ();
        nl ()) in

  let with_output_to_buffer (pbody: unit -> unit) =
    let buf = set_buffer (Buffer.create 4096) in
    pbody ();
    set_buffer buf in

  let p_hpp () =
    let impl = with_output_to_buffer p_impl in
    let typedefs = with_output_to_buffer p_type_declarations in
    p_includeguard (fun () ->
        p_preamble ();
        nl ();
        p_buffer typedefs;
        nl ();
        p_buffer impl;
        nl ()) in

  let p_extfun_decl { ffi_name; ffi_argtype; ffi_rettype } =
    let sp_arg typ = sprintf "const %s arg" (cpp_type_of_type typ) in
    let typ = cpp_type_of_type ffi_rettype in
    p_comment "%s %s(%s);" typ ffi_name (sp_arg ffi_argtype) in

  let p_cpp () =
    p "#include \"%s.hpp\"" hpp.cpp_header_name;
    nl ();

    (match hpp.cpp_extfuns with
     | Some cpp -> p "%s" cpp
     | None ->
        p_scoped "class extfuns" ~terminator:";" (fun () ->
            p "public:";
            p_comment "External methods (if any) should be implemented here.";
            if Hashtbl.length program_info.pi_ext_funcalls > 0 then
              (p_comment "Approximate signatures are provided below for convenience.";
               let fns = List.of_seq (Hashtbl.to_seq_keys program_info.pi_ext_funcalls) in
               List.iter p_extfun_decl (List.sort compare fns))));
    nl ();

    p "using sim_t = %s<extfuns>;" hpp.cpp_classname;
    nl ();

    let ull = "unsigned long long int" in
    let state_t = sprintf "sim_t::state_t" in

    p_fn ~typ:state_t ~name:"init_and_run" ~args:(sprintf "%s ncycles" ull) (fun () ->
        p_scoped (sprintf "%s init = " state_t)
          ~terminator:";" (fun () ->
            iter_all_registers (fun rn ->
                p ".%s = %s," rn.reg_name (sp_value rn.reg_init)));
        nl ();
        p "sim_t simulator(init);" ;
        p "simulator.run(ncycles);";
        p "return simulator.snapshot();");
    nl ();

    p_ifdef "ndef SIM_MINIMAL" (fun () ->
        p_fn ~typ:"int" ~name:"main" ~args:"int argc, char** argv" (fun () ->
            p_decl' ~init:(Some "1000") ull "ncycles";
            p_scoped "if (argc >= 2) " (fun () ->
                p "ncycles = std::stoull(argv[1]);");
            nl ();
            p "sim_t::state_t snapshot = init_and_run(ncycles);";
            p "snapshot.dump();";
            p "return 0;")) in

  let buf_cpp = with_output_to_buffer p_cpp in
  let buf_hpp = with_output_to_buffer p_hpp in
  (buf_hpp, buf_cpp)

let action_footprint a =
  let m = Hashtbl.create 25 in

  let rec action_footprint = function
    | SGA.Fail _ -> ()
    | SGA.Var _ | SGA.Const _ -> ()
    | SGA.Assign (_, _, _, _, ex) ->
       action_footprint ex
    | SGA.If (_, _, _, r1, r2)
      | SGA.Seq (_, _, r1, r2) ->
       action_footprint r1;
       action_footprint r2
    | SGA.Bind (_, _, _, _, ex, a) ->
       action_footprint ex;
       action_footprint a
    | SGA.Read (_, _, r) -> Hashtbl.replace m r ()
    | SGA.Write (_, _, r, ex) ->
       Hashtbl.replace m r ();
       action_footprint ex
    | SGA.Unop (_, _, arg) ->
       action_footprint arg
    | SGA.Binop (_, _, a1, a2) ->
       action_footprint a1; action_footprint a2
    | SGA.ExternalCall (_, _, arg) ->
       action_footprint arg
    | SGA.APos (_, _, _, a) ->
       action_footprint a in

  action_footprint a;
  List.of_seq (Hashtbl.to_seq_keys m)

let cpp_rule_of_action (rl_name, (_kind, rl_body)) =
  { rl_name; rl_body; rl_footprint = action_footprint rl_body }

let input_of_compile_unit classname (cu: 'f SGALib.Compilation.compile_unit) =
  { cpp_classname = classname;
    cpp_header_name = classname;
    cpp_pos_of_pos = cu.c_pos_of_pos;
    cpp_var_names = (fun x -> x);
    cpp_rule_names = (fun rl -> rl);
    cpp_scheduler = cu.c_scheduler;
    cpp_rules = List.map cpp_rule_of_action cu.c_rules;
    cpp_registers = cu.c_registers;
    cpp_register_sigs = (fun r -> r);
    cpp_ext_sigs = (fun f -> f);
    cpp_extfuns = cu.c_cpp_preamble; }

let collect_rules sched =
  let rec loop acc = function
  | SGA.Done -> List.rev acc
  | SGA.Cons (rl, s) -> loop (rl :: acc) s
  | SGA.Try (rl, l, r) -> loop (loop (rl :: acc) l) r
  | SGA.SPos (_, s) -> loop acc s
  in loop [] sched

let cpp_rule_of_sga_package_rule (s: _ SGALib.SGA.sga_package_t) (rn: Obj.t) =
  cpp_rule_of_action (rn, (`Internal, s.sga_rules rn))

let input_of_sim_package (type ext_fn_t) (sp: (_, _, _, _, ext_fn_t) SGALib.SGA.sim_package_t)
    : (_, Obj.t, Obj.t, Obj.t, ext_fn_t) cpp_input_t =
  let sga = sp.sp_pkg in
  let rules = collect_rules sga.sga_scheduler in
  let classname = SGALib.Util.string_of_coq_string sga.sga_module_name in
  let ext_fn_name f = SGALib.Util.string_of_coq_string (sp.sp_ext_fn_names f) in
  { cpp_classname = classname;
    cpp_header_name = classname;
    cpp_pos_of_pos = (fun _ -> Pos.Unknown);
    cpp_var_names = (fun x -> SGALib.Util.string_of_coq_string (sp.sp_var_names x));
    cpp_rule_names = (fun rn -> SGALib.Util.string_of_coq_string (sga.sga_rule_names rn));
    cpp_scheduler = sga.sga_scheduler;
    cpp_rules = List.map (cpp_rule_of_sga_package_rule sga) rules;
    cpp_registers = sga.sga_reg_finite.finite_elements;
    cpp_register_sigs = SGALib.Util.reg_sigs_of_sga_package sga;
    cpp_ext_sigs = (fun f -> SGALib.Util.ffi_sig_of_sga_external_sig (ext_fn_name f) (sga.sga_ext_fn_types f));
    cpp_extfuns = (match sp.sp_extfuns with
                   | None -> None
                   | Some s -> Some (SGALib.Util.string_of_coq_string s)); }

let command ?(verbose=false) exe args =
  (* FIXME use Unix.open_process_args instead of Filename.quote (OCaml 4.08) *)
  let qargs = List.map Filename.quote (exe :: args) in
  let cmd = String.concat " " qargs in
  let time = Unix.gettimeofday () in
  if verbose then Printf.eprintf ">> %s\n%!" cmd;
  ignore (Sys.command cmd);
  if verbose then Printf.eprintf "   (%.2f s)\n%!" (Unix.gettimeofday () -. time)

let clang_format fname =
  command "clang-format" ["-i"; fname]

let compile_cpp fname =
  let srcname = fname ^ ".cpp" in
  let exename = fname ^ ".exe" in
  command ~verbose:true "g++" ["-O3"; "-Wall"; "-Wextra"; "-fno-stack-protector"; srcname; "-o"; exename]

let write_cpp fname ext buf =
  let fname = fname ^ ext in
  Common.with_output_to_file fname (fun out -> Buffer.output_buffer out buf);
  clang_format fname

let main target_fname (kind: [> `Cpp | `Hpp | `Exe]) (cu: _ cpp_input_t) =
  let hpp, cpp = compile cu in
  if kind = `Hpp || kind = `Exe then
    write_cpp target_fname ".hpp" hpp;
  if kind = `Cpp || kind = `Exe then
    write_cpp target_fname ".cpp" cpp;
  if kind = `Exe then
    compile_cpp target_fname
