open Common
module SGA = SGALib.SGA

type ('name_t, 'var_t, 'reg_t, 'fn_t) cpp_rule_t = {
    rl_name: 'name_t;
    rl_footprint: 'reg_t list;
    rl_body: ('var_t, 'reg_t, 'fn_t) SGA.rule;
  }

type ('prim, 'name_t, 'var_t, 'reg_t, 'fn_t) cpp_input_t = {
    cpp_classname: string;
    cpp_scheduler: 'name_t SGA.scheduler;

    cpp_var_names: 'var_t -> string;

    cpp_rules: ('name_t, 'var_t, 'reg_t, 'fn_t) cpp_rule_t list;
    cpp_rule_names: 'name_t -> string;

    cpp_registers: 'reg_t list;
    cpp_register_sigs: 'reg_t -> reg_signature;
    cpp_function_sigs: 'fn_t -> ('prim, string) fun_id_t ffi_signature;

    cpp_extfuns: string option;
  }

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf

let register_type (user_types: (string * typ) list ref) nm tau =
  match List.assoc_opt nm !user_types with
  | Some tau' ->
     if tau <> tau' then
       failwith (sprintf "Incompatible uses of type name `%s':\n%s\n%s"
                   nm (typ_to_string tau) (typ_to_string tau'))
  | None -> user_types := (nm, tau) :: !user_types

module Mangling = struct
  let specials =
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

  let special_prefix_re = Str.regexp "_[A-Z]"
  let dunder_re = Str.regexp "__"
  let dunder_escape_re = Str.regexp "_\\(xxx+\\)_"

  let needs_mangling name =
    StringSet.mem name specials
    || Str.string_match special_prefix_re name 0
    || Str.string_match dunder_re name 0

  let escape_dunders name =
    let name = ref name in
    while Str.string_match dunder_re !name 0 do
      name := Str.global_replace dunder_escape_re "_\\1x_" !name
    done;
    !name

  let mangle_name name =
    if needs_mangling name then
      "_mangled_" ^ escape_dunders name
    else name

  let mangle_register_sig r =
    { r with reg_name = mangle_name r.reg_name }

  let mangle_function_sig f =
    { f with ffi_name = match f.ffi_name with
                        | CustomFn f -> CustomFn (mangle_name f)
                        | PrimFn f -> PrimFn f }

  let mangle_unit u =
    { u with
      cpp_classname = mangle_name u.cpp_classname;
      cpp_rule_names = (fun rl -> rl |> u.cpp_rule_names |> mangle_name);
      cpp_register_sigs = (fun r -> r |> u.cpp_register_sigs |> mangle_register_sig);
      cpp_function_sigs = (fun f -> f |> u.cpp_function_sigs |> mangle_function_sig) }
end

let cpp_type_of_type
      (user_types: (string * typ) list ref)
      (needs_multiprecision: bool ref)
      (tau: typ) =
  match tau with
  | Bits_t sz ->
     assert (sz >= 0);
     if sz > 64 then
       needs_multiprecision := true;
     if sz = 0 then
       "unit_t"
     else if sz <= 1024 then
       sprintf "uint_t<%d>" sz
     else
       failwith (sprintf "Unsupported size: %d" sz)
  | Enum_t sg ->
     register_type user_types sg.enum_name tau;
     sprintf "enum_%s" sg.enum_name
  | Struct_t sg ->
     register_type user_types sg.struct_name tau;
     sprintf "struct_%s" sg.struct_name

let register_subtypes
      (user_types: (string * typ) list ref)
      (needs_multiprecision: bool ref)
      tau =
  let rec loop tau = match tau with
    | Bits_t sz ->
       if sz > 64 then needs_multiprecision := true;
    | Enum_t sg ->
       register_type user_types sg.enum_name tau;
    | Struct_t sg ->
       register_type user_types sg.struct_name tau;
       List.iter (loop << snd) sg.struct_fields in
  loop tau

let cpp_struct_name user_types needs_multiprecision sg =
  cpp_type_of_type user_types needs_multiprecision (Struct_t sg)

let cpp_enum_name user_types needs_multiprecision sg =
  cpp_type_of_type user_types needs_multiprecision (Enum_t sg)

let cpp_const_init (needs_multiprecision: bool ref) sz cst =
  assert (sz >= 0);
  if sz > 64 then
    needs_multiprecision := true;
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

let cpp_custom_fn_name f =
  (* The current implementation of external functions requires the client to
     pass a class implementing those functions as a template argument.  An
     other approach would have made custom functions virtual methods, but
     then they couldn't have taken template arguments. *)
  (* The ‘.template’ part ensures that ‘extfuns.xyz<p>()’ is not parsed as a
     comparison. *)
  sprintf "extfuns.template %s" f

let cpp_bits_fn_name f tau1 tau2 =
  let sz1 = assert_bits tau1 in
  let sz2 = assert_bits tau2 in
  sprintf "prims::%s"
    (match f with
     | SGA.Sel _sz -> sprintf "sel<%d, %d>" sz1 sz2
     | SGA.Part (_sz, offset, width) -> sprintf "part<%d, %d, %d>" sz1 offset width
     | SGA.PartSubst (_sz, offset, width) -> sprintf "part_subst<%d, %d, %d>" sz1 offset width
     | SGA.IndexedPart (_sz, width) -> sprintf "indexed_part<%d, %d, %d>" sz1 sz2 width
     | SGA.And _sz -> sprintf "land<%d>" sz1
     | SGA.Or _sz -> sprintf "lor<%d>" sz1
     | SGA.Not _sz -> sprintf "lnot<%d>" sz1
     | SGA.Lsl (_sz, _places) -> sprintf "lsl<%d, %d>" sz1 sz2
     | SGA.Lsr (_sz, _places) -> sprintf "lsr<%d, %d>" sz1 sz2
     | SGA.EqBits _sz -> sprintf "eq<%d>" sz1
     | SGA.Concat (_sz1, _sz2) -> sprintf "concat<%d, %d>" sz1 sz2
     | SGA.ZExtL (_sz, width) -> sprintf "zextl<%d, %d>" sz1 width
     | SGA.ZExtR (_sz, width) -> sprintf "zextr<%d, %d>" sz1 width
     | SGA.UIntPlus _sz -> sprintf "plus<%d>" sz1)

let cpp_preamble =
  let inc = open_in "preamble.hpp" in
  let preamble = really_input_string inc (in_channel_length inc) in
  close_in inc;
  preamble

let reconstruct_switch sigs action =
  let rec loop v = function
    | SGA.If (_, _,
              SGA.Call (_,
                        fn,
                        SGA.Var (_, v', _, _m),
                        SGA.Const (_, ((SGA.Bits_t _ | SGA.Enum_t _) as tau), cst)),
              tbr, fbr) when (match v with
                              | Some v -> v' = v
                              | None -> true) ->
       (match sigs fn with
        | { ffi_name = PrimFn (SGA.BitsFn (SGA.EqBits _) | SGA.ConvFn (_, SGA.Eq)); _ } ->
           let default, branches = match loop (Some v') fbr with
             | Some (_, default, branches) -> default, branches
             | None -> fbr, [] in
           Some (v', default, (SGALib.Util.value_of_sga_value tau cst, tbr) :: branches)
        | _ -> None)
    | _ -> None in
  match loop None action with
  | Some (_, _, [_]) | None -> None
  | res -> res

let gensym, gensym_reset =
  make_gensym ()

type target_info =
  { tau: typ; declared: bool; name: var_t }

type assignment_target =
  | NoTarget
  | VarTarget of target_info

type assignment_result =
  | NotAssigned
  | Assigned of var_t
  | PureExpr of string

let compile (type name_t var_t reg_t)
      (hpp: (_, name_t, var_t, reg_t, _) cpp_input_t) =
  let buffer = ref (Buffer.create 0) in
  let hpp = Mangling.mangle_unit hpp in

  let nl _ = Buffer.add_string !buffer "\n" in
  let pk k fmt = Printf.kbprintf k !buffer fmt in
  let p fmt = pk nl fmt in
  let pr fmt = pk ignore fmt in
  let p_buffer b = Buffer.add_buffer !buffer b in
  let set_buffer b = let b' = !buffer in buffer := b; b' in

  let needs_multiprecision = ref false in
  let user_types = ref [] in
  let custom_funcalls = Hashtbl.create 50 in

  let cpp_type_of_type =
    cpp_type_of_type user_types needs_multiprecision in
  let cpp_enum_name =
    cpp_enum_name user_types needs_multiprecision in
  let cpp_struct_name =
    cpp_struct_name user_types needs_multiprecision in
  let cpp_const_init =
    cpp_const_init needs_multiprecision in

  let classname =
    sprintf "sim_%s" hpp.cpp_classname in

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
    let cpp_define = sprintf "%s_HPP" (String.uppercase_ascii classname) in
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
    let bs_size = Array.length bs in
    let w = (bs_size + 7) / 8 in
    let fmt = sprintf "%%0#%dx" (w + 2) in
    cpp_const_init bs_size (Z.format fmt (bits_to_Z bs))
  and sp_enum_value sg v =
    match enum_find_field_opt sg v with
    | None -> sprintf "static_cast<%s>(%s)" (cpp_enum_name sg) (sp_bits_value v)
    | Some nm -> sprintf "%s::%s" (cpp_enum_name sg) nm
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

  let sp_initializer tau =
    let bs0 sz = Array.make sz false in
    match tau with
    | Bits_t sz -> sp_value (Bits (bs0 sz))
    | Enum_t sg -> sp_value (Enum (sg, (bs0 sg.enum_bitsize)))
    | Struct_t sg -> sprintf "%s {}" (cpp_struct_name sg) in

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
    if esz = 0 then failwith (sprintf "Enum %s is empty" nm);
    if esz > 64 then failwith (sprintf "Enum %s is too large (%d > 64)" nm esz);
    let decl = sprintf "enum class %s : %s" nm (cpp_type_of_type (Bits_t esz)) in
    p_scoped decl ~terminator:";" (fun () ->
        iter_sep (fun () -> p ", ")
          (fun (name, v) -> p "%s = %s" name (sp_bits_value v)) sg.enum_members) in

  let p_struct_decl sg =
    let decl = sprintf "struct %s" (cpp_struct_name sg) in
    p_scoped decl ~terminator:";" (fun () ->
        List.iter (fun (name, tau) -> p_decl tau name) sg.struct_fields) in

  let attr_unused =
    "__attribute__((unused))" in

  let p_printer tau =
    let v_arg = "val" in
    let v_tau = cpp_type_of_type tau in
    let v_argdecl = sprintf "const %s %s" v_tau v_arg in

    let p_printer pbody =
      p_fn ~typ:("static std::string " ^ attr_unused)
        ~name:"repr" ~args:v_argdecl pbody in

    let p_enum_printer sg =
      p_printer (fun () ->
          p_scoped (sprintf "switch (%s)" v_arg) (fun () ->
              List.iter (fun (nm, _v) ->
                  let lbl = (cpp_enum_name sg) ^ "::" ^ nm in
                  p "case %s: return \"%s\";" lbl lbl)
                sg.enum_members;
              let v_sz = typ_sz tau in
              let bits_sz_tau = cpp_type_of_type (Bits_t v_sz) in
              let v_cast = sprintf "static_cast<%s>(%s)" bits_sz_tau v_arg in
              p "default: return \"%s{\" + repr<%d>(%s) + \"}\";"
                (cpp_enum_name sg) v_sz v_cast)) in

    let p_struct_printer sg =
      p_printer (fun () ->
          p "std::ostringstream stream;";
          p "stream << \"%s { \";" v_tau;
          List.iter (fun (fname, ftau) ->
              p "stream << \"  .%s = \" << %s(%s.%s) << \"; \";"
                fname (sp_value_printer ftau) v_arg fname)
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
      p_fn ~typ:("static bool " ^ attr_unused)
        ~args:(sprintf "%s, %s" (v_argdecl v1) (v_argdecl v2))
        ~name:"eq" (fun () -> pr "return ("; prbody (); p ");") in
    let p_pack pbody =
      p_fn ~typ:("static " ^ bits_tau ^ " " ^ attr_unused)
        ~args:(v_argdecl v_arg) ~name:(sp_packer tau) pbody in
    let p_unpack pbody =
      p_fn ~typ:("template <> " ^ v_tau ^ " " ^ attr_unused)
        ~args:bits_argdecl ~name:(sp_unpacker tau) pbody in

    let p_enum_pack _ =
      p_pack (fun () -> p "return static_cast<%s>(%s);" bits_tau v_arg) in

    let p_enum_unpack _ =
      p_unpack (fun () -> p "return static_cast<%s>(%s);" v_tau bits_arg) in

    let p_enum_eq _sg =
      p_eq (fun () -> pr "%s == %s" v1 v2) in

    let sp_field_eq v1 v2 tau field =
      sp_comparison tau (v1 ^ "." ^ field) (v2 ^ "." ^ field) in

    let p_struct_eq sg =
      p_eq (fun () -> iter_sep (fun () -> pr " && ") (fun (nm, tau) ->
                          pr "%s" (sp_field_eq v1 v2 tau nm))
                        sg.struct_fields) in

    let p_struct_pack sg =
      let var = "packed" in
      p_pack (fun () ->
          p_decl (Bits_t v_sz) var ~init:(Some (cpp_const_init v_sz "0"));
          List.iteri (fun idx (fname, ftau) ->
              let sz = typ_sz ftau in
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

  let p_type_declarations types =
    let types = topo_sort_types (sort_types types) in
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
    if !needs_multiprecision then (
      p "#define NEEDS_BOOST_MULTIPRECISION";
      nl ());
    p "%s" cpp_preamble;
    nl ();
    let reg_typ (_, t) = register_subtypes user_types needs_multiprecision t in
    List.iter reg_typ !user_types;
    p_type_declarations !user_types;
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
      p_scoped (sprintf "template <typename extfuns_t> class %s" classname)
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

    let p_rule (rule: (name_t, var_t, reg_t, _) cpp_rule_t) =
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

      let gensym_target tau prefix =
        VarTarget { tau; declared = false; name = gensym prefix } in

      let ensure_target tau t =
        match t with
        | NoTarget -> { declared = false; name = gensym "ignored"; tau }
        | VarTarget info -> info in

      let p_ensure_declared tinfo =
        if not tinfo.declared then
          p_decl tinfo.tau tinfo.name;
        tinfo.name in

      let p_assign_pure ?(prefix = "") target result =
        (match target, result with
         | VarTarget { declared = true; name; _ }, PureExpr e ->
            p "%s = %s;" name e;
            Assigned name
         | VarTarget { tau; name; _ }, PureExpr e ->
            p_decl ~prefix ~init:(Some e) tau name;
            Assigned name
         | _, _ ->
            result) in

      let must_expr = function
        | PureExpr e -> e
        | Assigned v -> v
        | NotAssigned -> assert false in

      let p_funcall target fn a1 a2 =
        let { ffi_name; ffi_arg1type = tau1; ffi_arg2type = tau2; _ } = fn in
        match ffi_name with
        | CustomFn f ->
           Hashtbl.replace custom_funcalls f fn;
           PureExpr (sprintf "%s(%s, %s)" (cpp_custom_fn_name f) a1 a2)
        | PrimFn (SGA.ConvFn (tau, fn)) ->
           let ns = "prims::" in
           let tau = SGALib.Util.typ_of_sga_type tau in
           PureExpr (match fn with
                     | SGA.Eq -> sp_comparison ~ns tau a1 a2
                     | SGA.Init -> sp_initializer tau
                     | SGA.Pack -> sp_packer ~ns ~arg:a1 tau
                     | SGA.Unpack -> sp_unpacker ~ns ~arg:a1 tau)
        | PrimFn (SGA.BitsFn f) ->
           PureExpr (sprintf "%s(%s, %s)" (cpp_bits_fn_name f tau1 tau2) a1 a2)
        | PrimFn (SGA.StructFn (sg, ac, idx)) ->
           let sg = SGALib.Util.struct_sig_of_sga_struct_sig sg in
           let field, _tau = SGALib.Util.list_nth sg.struct_fields idx in
           match ac with
           | SGA.GetField -> PureExpr (sprintf "%s.%s" a1 field)
           | SGA.SubstField ->
              let tinfo = ensure_target (Struct_t sg) target in
              let res = p_assign_pure (VarTarget tinfo) (PureExpr a1) in
              p "%s.%s = %s;" tinfo.name field a2;
              res in

      let assert_no_shadowing v v_to_string m =
        if SGALib.Util.member_references_shadowed_binding m then
          failwith (sprintf "Variable %s is shadowed by a later binding, but the program references the original binding." (v_to_string v)) in

      let rec p_action (target: assignment_target) (rl: (var_t, reg_t, _) SGA.action) =
        match rl with
        | SGA.Fail (_, _) ->
           p "return false;";
           (match target with
            | NoTarget -> NotAssigned
            | VarTarget { declared = true; name; _ } -> Assigned name
            | VarTarget { tau; _ } ->
               PureExpr (sprintf "prims::unreachable<%s>()" (cpp_type_of_type tau)))
        | SGA.Var (_, v, _tau, m) ->
           assert_no_shadowing v hpp.cpp_var_names m;
           PureExpr (hpp.cpp_var_names v)
        | SGA.Const (_, tau, cst) ->
           let res = PureExpr (sp_value (SGALib.Util.value_of_sga_value tau cst)) in
           if cpp_type_needs_allocation tau then
             let ctarget = gensym_target (SGALib.Util.typ_of_sga_type tau) "cst" in
             let e = must_expr (p_assign_pure ~prefix:"static const" ctarget res) in
             PureExpr e
           else res
        | SGA.Assign (_, v, tau, m, ex) ->
           assert_no_shadowing v hpp.cpp_var_names m;
           let vtarget = VarTarget { tau = SGALib.Util.typ_of_sga_type tau;
                                     declared = true; name = hpp.cpp_var_names v } in
           ignore (p_assign_pure vtarget (p_action vtarget ex));
           p_assign_pure target (PureExpr "prims::tt")
        | SGA.Seq (_, _, a1, a2) ->
           ignore (p_action NoTarget a1);
           p_action target a2
        | SGA.Bind (_, tau, _, v, ex, rl) ->
           let target = p_declare_target target in
           p_scoped "/* bind */" (fun () ->
               let vtarget = VarTarget { tau = SGALib.Util.typ_of_sga_type tau;
                                         declared = false; name = hpp.cpp_var_names v } in
               ignore (p_assign_pure vtarget (p_action vtarget ex));
               p_assign_pure target (p_action target rl))
        | SGA.If (_, _, cond, tbr, fbr) ->
           let target = p_declare_target target in
           (match reconstruct_switch hpp.cpp_function_sigs rl with
            | Some (var, default, branches) ->
               p_switch target var default branches
            | None ->
               let ctarget = gensym_target (Bits_t 1) "c" in
               let cexpr = p_action ctarget cond in
               ignore (p_scoped (sprintf "if (bool(%s))" (must_expr cexpr))
                         (fun () -> p_assign_pure target (p_action target tbr)));
               p_scoped "else"
                 (fun () -> p_assign_pure target (p_action target fbr)))
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
           let v = must_expr (p_action vt expr) in
           let fn_name = match port with
             | P0 -> "write0"
             | P1 -> "write1" in
           p_checked (fun () ->
               pr "log.%s.%s(%s, Log.%s.rwset)"
                 r.reg_name fn_name v r.reg_name);
           p_assign_pure target (PureExpr "prims::tt")
        | SGA.Call (_, fn, arg1, arg2) ->
           let f = hpp.cpp_function_sigs fn in
           let a1 = must_expr (p_action (gensym_target f.ffi_arg1type "x") arg1) in
           let a2 = must_expr (p_action (gensym_target f.ffi_arg2type "y") arg2) in
           p_funcall target f a1 a2
      and p_switch target var default branches =
        let rec loop = function
          | [] ->
             p "default:";
             p_assign_pure target (p_action target default);
          | (const, action) :: branches ->
             p "case %s:" (sp_value const);
             ignore (p_assign_pure target (p_action target action));
             p "break;";
             loop branches in
        p_scoped (sprintf "switch (%s)" (hpp.cpp_var_names var)) (fun () ->
            loop branches) in

      p_fn ~typ:"bool" ~name:("rule_" ^ hpp.cpp_rule_names rule.rl_name) (fun () ->
          p_reset ();
          nl ();
          ignore (p_action NoTarget rule.rl_body);
          nl ();
          p_commit ()) in

    let p_constructor () =
      let p_init_data0 { reg_name = nm; _ } =
        p "Log.%s.data0 = state.%s;" nm nm in
      p_fn ~typ:"explicit" ~name:classname
        ~args:"const state_t init" ~annot:" : state(init)"
        (fun () -> iter_all_registers p_init_data0) in

    let rec p_scheduler = function
      | SGA.Done -> ()
      | SGA.Cons (rl_name, s) ->
         p "rule_%s();" (hpp.cpp_rule_names rl_name);
         p_scheduler s
      | SGA.Try (rl_name, s1, s2) ->
         p_scoped (sprintf "if (rule_%s())" (hpp.cpp_rule_names rl_name)) (fun () -> p_scheduler s1);
         p_scoped "else" (fun () -> p_scheduler s2) in

    let p_cycle () =
      let p_commit_register r =
        p "state.%s = Log.%s.commit();" r.reg_name r.reg_name in
      p_fn ~typ:"void" ~name:"cycle" (fun () ->
          p_scheduler hpp.cpp_scheduler;
          iter_all_registers p_commit_register) in

    let p_run () =
      let typ = sprintf "template<typename T> %s&" classname in
      p_fn ~typ ~name:"run" ~args:"T ncycles" (fun () ->
          p_scoped "for (T cycle_id = 0; cycle_id < ncycles; cycle_id++)"
            (fun () -> p "cycle();");
          p "return *this;") in

    let p_observe () =
      p_fn ~typ:"state_t" ~name:"observe" (fun () -> p "return state;") in

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
        p_observe ();
        nl ()) in

  let with_output_to_buffer (pbody: unit -> unit) =
    let buf = set_buffer (Buffer.create 4096) in
    pbody ();
    set_buffer buf in

  let p_hpp () =
    let impl = with_output_to_buffer p_impl in
    p_includeguard (fun () ->
        p_preamble ();
        nl ();
        p_buffer impl;
        nl ()) in

  let p_extfun_decl (name, { ffi_arg1type; ffi_arg2type; ffi_rettype; _ }) =
    let sp_arg i typ = sprintf "const %s a%d" (cpp_type_of_type typ) i in
    let args = sprintf "%s, %s" (sp_arg 1 ffi_arg1type) (sp_arg 2 ffi_arg2type) in
    let typ = cpp_type_of_type ffi_rettype in
    p_comment "%s %s(%s);" typ name args in

  let p_cpp () =
    p "#include \"%s.hpp\"" hpp.cpp_classname;
    nl ();

    (match hpp.cpp_extfuns with
     | Some cpp -> p "%s" cpp
     | None ->
        p_scoped "class extfuns" ~terminator:";" (fun () ->
            p "public:";
            p_comment "External methods (if any) can be implemented here.";
            p_comment "Approximate signatures are provided below for convenience.";
            let fns = List.of_seq (Hashtbl.to_seq custom_funcalls) in
            let cmp f1 f2 = compare (fst f1) (fst f2) in
            List.iter p_extfun_decl (List.sort cmp fns)));
    nl ();

    let classtype =
      sprintf "%s<extfuns>" classname in

    let ull = "unsigned long long int" in
    let state_t = sprintf "%s::state_t" classtype in

    p_fn ~typ:state_t ~name:"run" ~args:(sprintf "%s ncycles" ull) (fun () ->
        p_scoped (sprintf "%s init = " state_t)
          ~terminator:";" (fun () ->
            iter_all_registers (fun rn ->
                p ".%s = %s," rn.reg_name (sp_value rn.reg_init)));
        nl ();
        p "%s simulator(init);" classtype;
        p "return simulator.run(ncycles).observe();");
    nl ();

    p_ifdef "ndef SIM_MINIMAL" (fun () ->
        p_fn ~typ:"int" ~name:"main" ~args:"int argc, char** argv" (fun () ->
            p_decl' ~init:(Some "1000") ull "ncycles";
            p_scoped "if (argc >= 2) " (fun () ->
                p "ncycles = std::stoull(argv[1]);");
            nl ();
            p "run(ncycles).dump();";
            p "return 0;")) in

  let buf_hpp = with_output_to_buffer p_hpp in
  let buf_cpp = with_output_to_buffer p_cpp in
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
    | SGA.Call (_, _, ex1, ex2) ->
       action_footprint ex1;
       action_footprint ex2 in

  action_footprint a;
  List.of_seq (Hashtbl.to_seq_keys m)

let cpp_rule_of_action (rl_name, rl_body) =
  { rl_name; rl_body; rl_footprint = action_footprint rl_body }

let input_of_compile_unit classname ({ c_registers; c_scheduler; c_rules }: SGALib.Compilation.compile_unit) =
  { cpp_classname = classname;
    cpp_rule_names = (fun rl -> rl);
    cpp_rules = List.map cpp_rule_of_action c_rules;
    cpp_scheduler = c_scheduler;
    cpp_registers = c_registers;
    cpp_register_sigs = (fun r -> r);
    cpp_function_sigs = SGALib.Util.ffi_sig_of_interop_fn ~custom_fn_info:(fun f -> f);
    cpp_var_names = (fun x -> x);
    cpp_extfuns = None; }

let collect_rules sched =
  let rec loop acc = function
  | SGA.Done -> List.rev acc
  | SGA.Cons (rl, s) -> loop (rl :: acc) s
  | SGA.Try (rl, l, r) -> loop (loop (rl :: acc) l) r
  in loop [] sched

let cpp_rule_of_sga_package_rule (s: _ SGALib.SGA.sga_package_t) (rn: Obj.t) =
  cpp_rule_of_action (rn, s.sga_rules rn)

let input_of_sim_package (sp: _ SGALib.SGA.sim_package_t)
    : (SGA.prim_fn_t, Obj.t, Obj.t, Obj.t, string SGA.interop_fn_t) cpp_input_t =
  let sga = sp.sp_pkg in
  let rules = collect_rules sga.sga_scheduler in
  let custom_fn_names f = SGALib.Util.string_of_coq_string (sp.sp_custom_fn_names f) in
  { cpp_classname = SGALib.Util.string_of_coq_string sga.sga_module_name;
    cpp_rule_names = (fun rn -> SGALib.Util.string_of_coq_string (sp.sp_rule_names rn));
    cpp_rules = List.map (cpp_rule_of_sga_package_rule sga) rules;
    cpp_scheduler = sga.sga_scheduler;
    cpp_registers = sga.sga_reg_finite.finite_elements;
    cpp_register_sigs = SGALib.Util.reg_sigs_of_sga_package sga;
    cpp_function_sigs = SGALib.Util.fn_sigs_of_sga_package custom_fn_names sga;
    cpp_var_names = (fun x -> SGALib.Util.string_of_coq_string (sp.sp_var_names x));
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
  command ~verbose:true "g++" ["-O3"; "-Wall"; "-Wextra"; srcname; "-o"; exename]

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
