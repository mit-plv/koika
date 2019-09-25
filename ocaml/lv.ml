open Common

let sprintf = Printf.sprintf

module Pos = struct
  type t =
    | StrPos of string
    | Filename of string
    | SexpPos of string * Parsexp.Positions.pos
    | SexpRange of string * Parsexp.Positions.range

  let range_to_string begpos endpos =
    if begpos = endpos then sprintf "%d" begpos
    else sprintf "%d-%d" begpos endpos

  (* Emacs expects columns to start at 1 in compilation output *)
  let to_string = function
    | StrPos s -> s
    | Filename f ->
       sprintf "%s:?:?" f
    | SexpPos (fname, { line; col; _ }) ->
       sprintf "%s:%d:%d" fname line (col + 1)
    | SexpRange (fname, { start_pos; end_pos }) ->
       let line = range_to_string start_pos.line end_pos.line in
       let col = range_to_string (start_pos.col + 1) (end_pos.col + 1) in
       sprintf "%s:%s:%s" fname line col
end

type nonrec 'a locd = (Pos.t, 'a) locd

let locd_make lpos lcnt =
  { lpos; lcnt }

let locd_of_pair (pos, x) =
  locd_make pos x

type unresolved_value =
  | UBits of bool array
  | UEnum of { name: string option; field: string }

type unresolved_rule =
  string locd * ((Pos.t, unresolved_value, string, string) action) locd

type unresolved_scheduler =
  string locd * (Pos.t scheduler) locd

type unresolved_register =
  string locd * unresolved_value locd

type unresolved_module = {
    m_name: string locd;
    m_registers: unresolved_register list;
    m_rules: unresolved_rule list;
    m_schedulers: unresolved_scheduler list;
  }

type unresolved_typedecl =
  | Enum_u of { name: string locd; bitsize: int locd; members: (string locd * bits_value locd) list }
  | Struct_u of { name: string locd; fields: (string locd * unresolved_type locd) list }
and unresolved_type =
  | Bits_u of int
  | Unknown_u of string

type unresolved_extfun = {
    name: string locd;
    argtypes: unresolved_type locd list;
    rettype: unresolved_type locd
  }

type typedecls = {
    enums: enum_sig StringMap.t;
    structs: struct_sig StringMap.t;
    enum_fields: enum_sig StringMap.t;
    all: typ StringMap.t
  }

type unresolved_unit = {
    types: unresolved_typedecl locd list;
    extfuns: unresolved_extfun list;
    mods: unresolved_module locd list;
  }

type resolved_module = {
    registers: reg_signature list;
    rules: (string * Pos.t SGALib.Compilation.raw_action) list;
    scheduler: Pos.t SGALib.Compilation.raw_scheduler
  }

exception Error of Pos.t err_contents

let check_result = function
  | Ok cs -> cs
  | Error err -> raise (Error err)

let parse_error (epos: Pos.t) emsg =
  raise (Error { epos; ekind = `ParseError; emsg })

let resolution_error (epos: Pos.t) emsg =
  raise (Error { epos; ekind = `ResolutionError; emsg = emsg })

let name_error epos ?(extra="") msg =
  raise (Error { epos; ekind = `NameError; emsg = msg ^ extra })

let unbound_error (epos: Pos.t) ?(bound=[]) kind name =
  let msg = sprintf "Unbound %s: `%s'" kind name in
  let lst = String.concat ", " (List.sort compare bound) in
  let extra = if bound = [] then "" else sprintf " (expecting one of %s)" lst in
  name_error epos ~extra msg

let type_error (epos: Pos.t) emsg =
  raise (Error { epos; ekind = `TypeError; emsg })

let untyped_number_error (pos: Pos.t) n =
  type_error pos (sprintf "Missing size annotation on number `%d'" n)

let symbol_error (pos: Pos.t) s =
  type_error pos (sprintf "Unexpected symbol `%s'" s)

let expect_cons loc msg = function
  | [] -> parse_error loc (Printf.sprintf "Missing %s" msg)
  | hd :: tl -> hd, tl

let rec list_const n x =
  if n = 0 then [] else x :: list_const (n - 1) x

type 'f sexp =
  | Atom of { loc: 'f; atom: string }
  | List of { loc: 'f; elements: 'f sexp list }

let read_cst_sexps fname =
  let wrap_loc loc =
    Pos.SexpRange (fname, loc) in
  let rec drop_comments (s: Parsexp.Cst.t_or_comment) =
    match s with
    | Parsexp.Cst.Sexp (Parsexp.Cst.Atom { loc; atom; _ }) ->
       Some (Atom  { loc = wrap_loc loc; atom })
    | Parsexp.Cst.Sexp (Parsexp.Cst.List { loc; elements }) ->
       Some (List { loc = wrap_loc loc;
                    elements = Base.List.filter_map ~f:drop_comments elements })
    | Parsexp.Cst.Comment _ -> None in
  match Parsexp.Many_cst.parse_string (Stdio.In_channel.read_all fname) with
  | Ok sexps ->
     Base.List.filter_map ~f:drop_comments sexps
  | Error err ->
     let pos = Parsexp.Parse_error.position err in
     let msg = Parsexp.Parse_error.message err in
     parse_error (Pos.SexpPos (fname, pos)) msg

let read_annotated_sexps fname =
  let rec commit_annots loc (s: Base.Sexp.t) =
    match s with
    | Atom atom ->
       Atom { loc; atom }
    | List [Atom "<>"; Atom annot; body] ->
       commit_annots (Pos.StrPos annot) body
    | List (Atom "<>" :: _) ->
       let msg = sprintf "Bad use of <>: %s" (Base.Sexp.to_string s) in
       parse_error (Pos.Filename fname) msg
    | List elements ->
       List { loc; elements = List.map (commit_annots loc) elements } in
  match Parsexp.Many.parse_string (Stdio.In_channel.read_all fname) with
  | Ok sexps ->
     List.map (commit_annots (Pos.Filename fname)) sexps
  | Error err ->
     let pos = Parsexp.Parse_error.position err in
     let msg = Parsexp.Parse_error.message err in
     parse_error (Pos.SexpPos (fname, pos)) msg

let keys s =
  StringMap.fold (fun k _ acc -> k :: acc) s []

let first_duplicate keyfn ls =
  let rec loop acc = function
    | [] -> None
    | x :: xs ->
       let key = keyfn x in
       if StringSet.mem key acc then Some x
       else loop (StringSet.add key acc) xs in
  loop StringSet.empty ls

let check_no_duplicates msg keyfn ls =
  (match first_duplicate keyfn ls with
   | Some (nm, _) -> parse_error nm.lpos (sprintf "Duplicate %s: `%s'" msg nm.lcnt)
   | None -> ())

let add_or_raise k v m errf =
  match StringMap.find_opt k m with
  | Some v' -> errf k v v'
  | None -> StringMap.add k v m

let gensym, gensym_reset =
  make_gensym ()

let parse fname sexps =
  Printf.printf "Parsing %s\n%!" fname;
  let expect_single loc kind where = function
    | [] ->
       parse_error loc
         (sprintf "No %s found in %s" kind where)
    | _ :: _ :: _ ->
       parse_error loc
         (sprintf "More than one %s found in %s" kind where)
    | [x] -> x in
  let num_fmt =
    "(number format: size'number)" in
  let expect_atom msg = function
    | List { loc; _ } ->
       parse_error loc
         (sprintf "Expecting %s, but got a list" msg)
    | Atom { loc; atom } ->
       (loc, atom) in
  let expect_list msg = function
    | Atom { loc; atom } ->
       parse_error loc
         (sprintf "Expecting %s, but got `%s'" msg atom)
    | List { loc; elements } ->
       (loc, elements) in
  let expect_nil = function
    | [] -> ()
    | List { loc; _ } :: _ -> parse_error loc "Unexpected list"
    | Atom { loc; _ } :: _ -> parse_error loc "Unexpected atom" in
  let expect_pair loc msg1 msg2 lst =
    let x1, lst = expect_cons loc msg1 lst in
    let x2, lst = expect_cons loc msg2 lst in
    expect_nil lst;
    (x1, x2) in
  let rec expect_pairs msg = function
    | [] -> []
    | h1 :: h2 :: tl -> (h1, h2) :: expect_pairs msg tl
    | [(Atom { loc; _ } | List { loc; _ } )] ->
       parse_error loc (sprintf "Missing %s after this element" msg) in
  let expect_constant csts c =
    let quote x = "`" ^ x ^ "'" in
    let optstrs = List.map (quote << fst) csts in
    let msg = match optstrs with
      | [c] -> c
      | _ -> sprintf "one of %s" (String.concat ", " optstrs) in
    let loc, s = expect_atom msg c in
    match List.assoc_opt s csts with
    | None -> parse_error loc (sprintf "Expecting %s, got `%s'" msg s)
    | Some x -> loc, x in
  let bits_const_re =
    Str.regexp "^\\([0-9]+\\)'\\(b[01]*\\|h[0-9a-fA-F]*\\|[0-9]+\\)$" in
  let name_re_str =
    (* Must not start with __ to not clash w/ our gensym *)
    "[a-z][a-zA-Z0-9_]*" in
  let ident_re = Str.regexp (sprintf "^%s$" name_re_str) in
  let underscore_re = Str.regexp "_" in
  let leading_h_re = Str.regexp "^h" in
  let try_variable var =
    if Str.string_match ident_re var 0 then Some var else None in
  let try_number' loc a =
    let a = Str.global_replace underscore_re "" a in
    if Str.string_match bits_const_re a 0 then
      let sizestr = Str.matched_group 1 a in
      let size = try int_of_string sizestr
                 with Failure _ ->
                   parse_error loc (sprintf "Unparsable size annotation: `%s'" sizestr) in
      let numstr = Str.matched_group 2 a in
      let num = Z.of_string ("0" ^ (Str.replace_first leading_h_re "x" numstr)) in
      let bits = if size = 0 && num = Z.zero then ""
                 else Z.format "%b" num in
      let nbits = String.length bits in
      if nbits > size then
        parse_error loc (sprintf "Number `%s' (%d'b%s) does not fit in %d bit(s)"
                           numstr nbits bits size)
      else
        let padding = list_const (size - nbits) false in
        let char2bool = function '0' -> false | '1' -> true | _ -> assert false in
        let bits = List.of_seq (String.to_seq bits) in
        let bools = List.append (List.rev_map char2bool bits) padding in
        Some (`Const (Array.of_list bools))
    else match int_of_string_opt a with
         | Some n -> Some (`Num n)
         | None -> None in
  let try_number loc = function
    | "true" -> Some (`Const [|true|])
    | "false" -> Some (`Const [|false|])
    | a -> try_number' loc a in
  let keyword_re = Str.regexp (sprintf "^:\\(%s\\)$" name_re_str) in
  let try_keyword nm =
    if Str.string_match keyword_re nm 0 then Some (Str.matched_group 1 nm)
    else None in
  let enumerator_re = Str.regexp (sprintf "^\\(%s\\)::\\(%s\\)$" name_re_str name_re_str) in
  let try_enumerator nm =
    if Str.string_match enumerator_re nm 0 then
      Some (Some (Str.matched_group 1 nm), Str.matched_group 2 nm)
    else match try_keyword nm with
         | Some k -> Some (None, k)
         | None -> None in
  let symbol_re = Str.regexp (sprintf "^'\\(%s\\)$" name_re_str) in
  let try_symbol nm =
    if Str.string_match symbol_re nm 0 then Some (Str.matched_group 1 nm)
    else None in
  let expect_literal loc a =
    match try_enumerator a with
    | Some (Some _ as name, field) -> Const (UEnum { name; field })
    | Some (None, kwd) -> Keyword kwd
    | None ->
       match try_symbol a with
       | Some name -> Symbol name
       | None ->
          match try_number loc a with
          | Some (`Num n) -> Num n
          | Some (`Const bs) -> Const (UBits bs)
          | None ->
             match try_variable a with
             | Some var -> Var var
             | None ->
                let msg = sprintf "Cannot parse `%s' as a literal (number, variable, symbol or keyword)" a in
                parse_error loc msg in
  let try_bits loc v =
    match try_number loc v with
    | Some (`Const c) -> Some c
    | Some (`Num n) -> untyped_number_error loc n
    | _ -> None in
  let expect_bits msg v =
    let loc, sbits = expect_atom msg v in
    match try_bits loc sbits with
    | Some c -> loc, c
    | _ -> parse_error loc (sprintf "Expecting a bits constant (e.g. 2'b01), got `%s' %s" sbits num_fmt) in
  let expect_const msg v =
    let loc, scst = expect_atom msg v in
    (loc,
     match try_bits loc scst with
     | Some c -> UBits c
     | None ->
        match try_enumerator scst with
        | Some (name, field) -> UEnum { name; field }
        | None -> parse_error loc "Expecting a bits constant (e.g. 16'hffff) or an enumerator (eg proto::ipv4)") in
  let expect_keyword msg nm =
    let loc, nm = expect_atom msg nm in
    match try_keyword nm with
    | Some k -> loc, k
    | None -> parse_error loc (sprintf "Expecting %s starting with a colon (:), got `%s'" msg nm) in
  let expect_type = function (* (bit 16), typename *)
    | Atom { loc; atom } ->
       (loc, Unknown_u atom)
    | List { loc; elements } ->
       let hd, sizes = expect_cons loc "a type" elements in
       let _ = expect_constant [("bits", ())] hd in
       let loc, szstr = expect_atom "a size" (expect_single loc "size" "bit type" sizes) in
       match try_number loc szstr with
       | Some (`Num size) -> (loc, Bits_u size)
       | _ -> parse_error loc (sprintf "Expecting a bit size, got `%s'" szstr) in
  let expect_funapp loc kind elements =
    let hd, args = expect_cons loc kind elements in
    let loc_hd, hd = expect_atom (sprintf "a %s name" kind) hd in
    loc_hd, hd, args in
  let fail_num_re =
    Str.regexp "\\([^ \t]+\\)'fail" in
  let rec expect_action = function
    | Atom { loc; atom } ->
       locd_make loc
         (match atom with
          | "skip" -> Skip
          | "fail" -> Fail 0
          | atom ->
             if Str.string_match fail_num_re atom 0 then
               let numstr = Str.matched_group 1 atom in
               (match int_of_string_opt numstr with
                | Some sz -> Fail sz
                | None -> parse_error loc (sprintf "Cannot parse %s as a number" numstr))
             else
               expect_literal loc atom)
    | List { loc; elements } ->
       let loc_hd, hd, args = expect_funapp loc "constructor or function" (elements) in
       locd_make loc
         (match hd with
          | "progn" ->
             Progn (List.map expect_action args)
          | "let" ->
             let bindings, body = expect_cons loc "let bindings" args in
             Let (expect_let_bindings bindings, List.map expect_action body)
          | "if" ->
             let cond, body = expect_cons loc "if condition" args in
             let tbranch, fbranches = expect_cons loc "if branch" body in
             If (expect_action cond, expect_action tbranch,
                 List.map expect_action fbranches)
          | "when" ->
             let cond, body = expect_cons loc "when condition" args in
             When (expect_action cond, List.map expect_action body)
          | "write.0" | "write.1" ->
             let reg, body = expect_cons loc "register name" args in
             let port = int_of_string (String.sub hd (String.length hd - 1) 1) in
             Write (port, locd_of_pair (expect_atom "a register name" reg),
                    expect_action (expect_single loc "value" "write expression" body))
          | "read.0" | "read.1" ->
             let reg = expect_single loc "register name" "read expression" args in
             let port = int_of_string (String.sub hd (String.length hd - 1) 1) in
             Read (port, locd_of_pair (expect_atom "a register name" reg))
          | "switch" ->
             let operand, branches = expect_cons loc "switch operand" args in
             let branches = List.map expect_switch_branch branches in
             let operand = expect_action operand in
             (match build_switch_body branches with
              | Some (default, branches) -> Switch { operand; default; branches }
              | None -> parse_error loc "Empty switch")
          | _ ->
             let args = List.map expect_action args in
             Call (locd_make loc_hd hd, args))
  and expect_switch_branch branch =
    let loc, lst = expect_list "switch case" branch in
    let lbl, body = expect_cons loc "case label" lst in
    let lbl = match lbl with
      | Atom { loc; atom = "_" } -> `AnyLabel loc
      | _ -> let loc, cst = expect_const "a case label" lbl in
             `SomeLabel (locd_make loc (Const cst)) in
    (lbl, locd_make loc (Progn (List.map expect_action body)))
  and build_switch_body branches =
    List.fold_right (fun (lbl, (branch: _ action locd)) acc ->
        match acc, lbl with
        | None, `AnyLabel _ ->
           Some (branch, [])
        | None, `SomeLabel l ->
           parse_error l.lpos "Last case of switch must be default (_)"
        | Some _, `AnyLabel loc  ->
           parse_error loc "Duplicated default case in switch"
        | Some (default, branches), `SomeLabel l ->
           Some (default, (l, branch) :: branches))
      branches None
  and expect_let_binding b =
    let loc, b = expect_list "a let binding" b in
    let var, values = expect_cons loc "identifier" b in
    let loc_v, var = expect_atom "an identifier" var in
    match try_variable var with
    | None -> parse_error loc_v (sprintf "Cannot parse `%s' as an identifier" var)
    | Some var ->
       let value = expect_single loc "value" "let binding" values in
       let value = expect_action value in
       (locd_make loc_v var, value)
  and expect_let_bindings bs =
    let _, bs = expect_list "let bindings" bs in
    List.map expect_let_binding bs in
  let expect_register name init_val =
    (name, locd_of_pair (expect_const "an initial value" init_val)) in
  let expect_actions loc body =
    locd_make loc (Progn (List.map expect_action body)) in
  let rec expect_scheduler : Pos.t sexp -> Pos.t scheduler locd = function
    | (Atom _) as a ->
       locd_of_pair (expect_constant [("done", Done)] a)
    | List { loc; elements } ->
       let loc_hd, hd, args = expect_funapp loc "constructor" (elements) in
       locd_make loc
         (match hd with
          | "sequence" ->
             Sequence (List.map (locd_of_pair << (expect_atom "a rule name")) args)
          | "try" ->
             let rname, args = expect_cons loc "rule name" args in
             let s1, s2 = expect_pair loc "subscheduler 1" "subscheduler 2" args in
             Try (locd_of_pair (expect_atom "a rule name" rname),
                  expect_scheduler s1,
                  expect_scheduler s2)
          | _ ->
             parse_error loc_hd (sprintf "Unexpected in scheduler: `%s'" hd)) in
  let expect_enum_field (name, value) = (* (:a 2'b00) *)
    (* let name, value = expect_pair loc "enumerator" "enumerator value" lst in *)
    (expect_keyword "an enumerator" name |> locd_of_pair,
     expect_bits "an enumerator value" value |> locd_of_pair) in
  let check_size sz { lpos; lcnt } =
    let sz' = Array.length lcnt in
    if sz' <> sz then
      parse_error lpos
        (sprintf "Inconsistent sizes in enum: expecting `bits %d', got `bits %d'" sz sz') in
  let expect_enum name loc body = (* ((:true 1'b1) (:false 1'b0) …) *)
    let members = List.map expect_enum_field (expect_pairs "enumerator value" body) in
    let (_, eval), _ = expect_cons loc "enumerator (empty enums are not supported)" members in
    let bitsize = Array.length eval.lcnt in
    List.iter ((check_size bitsize) << snd) members;
    locd_make loc (Enum_u { name; bitsize = locd_make eval.lpos bitsize; members }) in
  let expect_struct_field (name, typ) = (* (:label, typename) *)
    (expect_keyword "a field name" name |> locd_of_pair, expect_type typ |> locd_of_pair) in
  let expect_struct name loc body = (* ((:kind kind) (:imm (bits 12) …) *)
    let fields = List.map expect_struct_field (expect_pairs "field type" body) in
    check_no_duplicates "field in struct" (fun (nm, _) -> nm.lcnt) fields;
    locd_make loc (Struct_u { name; fields }) in
  let expect_extfun name loc body =
    let args, rettype = expect_pair loc "argument declarations" "return type" body in
    let _, args = expect_list "argument declarations" args in
    let argtypes = List.map (locd_of_pair << expect_type) args in
    let rettype = locd_of_pair (expect_type rettype) in
    { name; argtypes; rettype } in
  let rec expect_decl d skind expected =
    let d_loc, d = expect_list ("a " ^ skind) d in
    let kind, name_body = expect_cons d_loc skind d in
    let _, kind = expect_constant expected kind in
    let name, body = expect_cons d_loc "name" name_body in
    let name = locd_of_pair (expect_atom "a name" name) in
    Printf.printf "Processing decl %s\n%!" name.lcnt;
    (d_loc,
     match kind with
     | `Enum ->
        `Enum (expect_enum name d_loc body)
     | `Struct ->
        `Struct (expect_struct name d_loc body)
     | `Extfun ->
        `Extfun (expect_extfun name d_loc body)
     | `Module ->
        `Module (expect_module name d_loc body)
     | `Register ->
        `Register (expect_register name (expect_single d_loc "value" "register initialization" body))
     | `Rule ->
        `Rule (name, expect_actions d_loc body)
     | `Scheduler ->
        `Scheduler (name, expect_scheduler (expect_single d_loc "body" "scheduler declaration" body)))
  and expect_module m_name loc body =
    let expected = [("register", `Register); ("rule", `Rule); ("scheduler", `Scheduler)] in
    let m =
      List.fold_left (fun m decl ->
          match expect_decl decl "register, rule, or scheduler declaration" expected |> snd with
          | `Register r -> { m with m_registers = r :: m.m_registers }
          | `Rule r -> { m with m_rules = r :: m.m_rules }
          | `Scheduler s -> { m with m_schedulers = s :: m.m_schedulers }
          | _ -> assert false)
        { m_name; m_registers = []; m_rules = []; m_schedulers = [] } body in
    check_no_duplicates "register" (fun (nm, _) -> nm.lcnt) m.m_registers;
    check_no_duplicates "rule" (fun (nm, _) -> nm.lcnt) m.m_rules;
    check_no_duplicates "scheduler" (fun (nm, _) -> nm.lcnt) m.m_schedulers;
    let m_scheduler = expect_single loc "scheduler"
                        (sprintf "module `%s'" m_name.lcnt) m.m_schedulers in
    locd_make loc
      { m with m_registers = List.rev m.m_registers;
               m_rules = List.rev m.m_rules;
               m_schedulers = [m_scheduler] } in
  let expected_toplevel =
    [("enum", `Enum); ("struct", `Struct); ("extfun", `Extfun); ("module", `Module)] in
  let { types; extfuns; mods } =
    List.fold_left (fun u sexp ->
        match expect_decl sexp "module, type, or extfun declaration" expected_toplevel |> snd with
        | `Enum e -> { u with types = e :: u.types }
        | `Struct s -> { u with types = s :: u.types }
        | `Extfun fn -> { u with extfuns = fn :: u.extfuns }
        | `Module m -> { u with mods = m :: u.mods }
        | _ -> assert false)
      { types = []; extfuns = []; mods = [] } sexps in
  { types = List.rev types;
    extfuns = List.rev extfuns;
    mods = List.rev mods }

let rexpect_num = function
  | { lpos; lcnt = Num n; _} -> lpos, n
  | { lpos; _ } -> parse_error lpos "Expecting a type level constant"

let rexpect_keyword msg = function
  | { lpos; lcnt = Keyword s ; _} -> lpos, s
  | { lpos; _ } -> parse_error lpos (sprintf "Expecting a keyword (%s)" msg)

let rexpect_symbol msg = function
  | { lpos; lcnt = Symbol s } -> lpos, s
  | { lpos; _ } -> parse_error lpos (sprintf "Expecting a symbol (%s)" msg)

let rexpect_arg k loc args =
  let a, args = expect_cons loc "argument" args in
  k a, args

let types_empty =
  { enums = StringMap.empty;
    enum_fields = StringMap.empty;
    structs = StringMap.empty;
    all = StringMap.empty }

let types_add loc tau_r types =
  let err k kd1 kd2 =
    resolution_error loc
      (sprintf "Duplicate name: %s `%s' previously declared as %s" kd1 k kd2) in
  let name, tau, types = match tau_r with
    | `Enum sg ->
       let name = sg.enum_name in
       name, Enum_t sg,
       { types with enums = add_or_raise name sg types.enums
                              (fun k _ _ -> err k "enum" "enum");
                    enum_fields = List.fold_left (fun fields field ->
                                      add_or_raise field sg fields
                                        (fun k _ _ -> err k "enumerator" "enumerator"))
                                    types.enum_fields (List.map fst sg.enum_members) }
    | `Struct sg ->
       let name = sg.struct_name in
       name, Struct_t sg,
       { types with structs = add_or_raise name sg types.structs
                                (fun k _ _ -> err k "struct" "struct") } in
  { types with all = add_or_raise name tau types.all
                       (fun k v v' -> err k (kind_to_str v) (kind_to_str v')) }

let resolve_type types { lpos; lcnt: unresolved_type } =
  match lcnt with
  | Bits_u sz -> Bits_t sz
  | Unknown_u nm ->
     match StringMap.find_opt nm types.all with
     | Some tau -> tau
     | None ->
        unbound_error lpos ~bound:(keys types.all) "type" nm

let resolve_typedecl types (typ: unresolved_typedecl locd) =
  let resolve_struct_field_type (nm, tau) =
    (nm.lcnt, resolve_type types tau) in
  match typ.lcnt with
  | Enum_u { name; bitsize; members } ->
     `Enum { enum_name = name.lcnt; enum_bitsize = bitsize.lcnt;
             enum_members = List.map (fun (n, t) -> n.lcnt, t.lcnt) members }
  | Struct_u { name; fields } ->
     let struct_fields = List.map resolve_struct_field_type fields in
     `Struct { struct_name = name.lcnt; struct_fields }

let resolve_typedecls types =
  List.fold_left (fun types t ->
      let typ = resolve_typedecl types t in
      types_add t.lpos typ types)
    types_empty types

let core_primitives =
  let open SGALib.SGA in
  let conv_fn f = UPrimFn (UConvFn f) in
  let struct_fn f = UPrimFn (UStructFn f) in
  [("eq", (`Fn (conv_fn UEq), 2));
   ("=", (`Fn (conv_fn UEq), 2));
   ("new", (`TypeFn (fun tau -> conv_fn (UInit tau)), 0));
   ("pack", (`Fn (conv_fn UPack), 1));
   ("unpack", (`TypeFn (fun tau -> conv_fn (UUnpack tau)), 1));
   ("get", (`FieldFn (fun f -> struct_fn (UDo (GetField, f))) , 1));
   ("update", (`FieldFn (fun f -> struct_fn (UDo (SubstField, f))), 2));
   ("get-bits", (`StructFn (fun sg f -> struct_fn (UDoBits (sg, GetField, f))), 1));
   ("update-bits", (`StructFn (fun sg f -> struct_fn (UDoBits (sg, SubstField, f))), 2))]
  |> List.to_seq |> StringMap.of_seq

let bits_primitives =
  let open SGALib.SGA in
  [("sel", (`Prim0 USel, 2));
   ("and", (`Prim0 UAnd, 2));
   ("&", (`Prim0 UAnd, 2));
   ("or", (`Prim0 UOr, 2));
   ("|", (`Prim0 UOr, 2));
   ("not", (`Prim0 UNot, 1));
   ("~", (`Prim0 UNot, 1));
   ("lsl", (`Prim0 ULsl, 2));
   ("<<", (`Prim0 ULsl, 2));
   ("lsr", (`Prim0 ULsr, 2));
   (">>", (`Prim0 ULsr, 2));
   ("concat", (`Prim0 UConcat, 2));
   ("uintplus", (`Prim0 UUIntPlus, 2));
   ("+", (`Prim0 UUIntPlus, 2));
   ("zextl", (`Prim1 (fun n -> UZExtL n), 1));
   ("zextr", (`Prim1 (fun n -> UZExtR n), 1));
   ("indexed-part", (`Prim1 (fun n -> UIndexedPart n), 2));
   ("part", (`Prim2 (fun n n' -> UPart (n, n')), 1));
   ("part-subst", (`Prim2 (fun n n' -> UPart (n, n')), 2))]
  |> List.to_seq |> StringMap.of_seq

let resolve_extfun_decl types { name; argtypes; rettype } =
  let unit_u = locd_make name.lpos (Bits_u 0) in
  if StringMap.mem name.lcnt bits_primitives then
    name_error name.lpos "External function name `%s' conflicts with existing primitive.";
  let nargs, a1, a2 = match argtypes with
    | [] -> 0, unit_u, unit_u
    | [t] -> 1, t, unit_u
    | [x; y] -> 2, x, y
    | _ -> parse_error name.lpos ("External functions with more than 2 arguments are not supported" ^
                                    " (consider using a struct to pass more arguments)") in
  name.lcnt, (nargs, { ffi_name = name.lcnt;
                       ffi_arg1type = resolve_type types a1;
                       ffi_arg2type = resolve_type types a2;
                       ffi_rettype = resolve_type types rettype })

let resolve_value types { lpos; lcnt } =
  let resolve_enum_field sg field =
    match List.assoc_opt field sg.enum_members with
    | Some bs -> Enum (sg, bs)
    | None -> unbound_error lpos ~bound:(List.map fst sg.enum_members)
                (sprintf "enumerator in type `%s'" sg.enum_name) field in
  match lcnt with
  | UBits bs -> Bits bs
  | UEnum { name = Some nm; field } ->
     (match StringMap.find_opt nm types.all with
      | Some (Enum_t sg) -> resolve_enum_field sg field
      | Some tau -> type_error lpos (sprintf "Type `%s' is not an enum" (typ_to_string tau))
      | None -> unbound_error lpos ~bound:(keys types.enums) "enum" nm)
  | UEnum { name = None; field } ->
     (* LATER allow enums to share an enumerator and flag ambiguities *)
     (match StringMap.find_opt field types.enum_fields with
      | Some sg -> resolve_enum_field sg field
      | None -> unbound_error lpos ~bound:(keys types.enum_fields) "enumerator" field)

let try_resolve_bits_fn loc name args =
  let bits_fn nm = SGALib.SGA.UPrimFn (SGALib.SGA.UBitsFn nm) in
  match StringMap.find_opt name bits_primitives with
  | Some (fn, nargs) ->
     Some (match fn with
           | `Prim0 fn ->
              bits_fn fn, nargs, args
           | `Prim1 fn ->
              let (_, n), args = rexpect_arg rexpect_num loc args in
              bits_fn (fn n), nargs, args
           | `Prim2 fn ->
              let (_, n), args = rexpect_arg rexpect_num loc args in
              let (_, n'), args = rexpect_arg rexpect_num loc args in
              bits_fn (fn n n'), nargs, args)
  | None -> None

let try_resolve_primitive types loc name args =
  let must_struct_t loc nm = function
    | Struct_t sg -> SGALib.Util.sga_struct_sig_of_struct_sig sg
    | tau -> type_error loc (sprintf "Expecting a struct name, but `%s' is `%s'"
                               nm (kind_to_str ~pre:true tau)) in
  let rexpect_type args =
    let (loc, t), args = rexpect_arg (rexpect_symbol "a type name") loc args in
    let tau = resolve_type types (locd_make loc (Unknown_u t)) in
    loc, t, tau, args in
  let rexpect_field args =
    let (_, f), args = rexpect_arg (rexpect_keyword "a struct field") loc args in
    SGALib.Util.coq_string_of_string f, args in
  match StringMap.find_opt name core_primitives with
  | Some (fn, nargs) ->
     Some (match fn with
           | `Fn fn ->
              fn, nargs, args
           | `TypeFn fn ->
              let _, _, t, args = rexpect_type args in
              (fn (SGALib.Util.sga_type_of_typ t)), nargs, args
           | `FieldFn fn ->
              let f, args = rexpect_field args in
              (fn f), nargs, args
           | `StructFn fn ->
              let loc, nm, t, args = rexpect_type args in
              let f, args = rexpect_field args in
              (fn (must_struct_t loc nm t) f), nargs, args)
  | None -> try_resolve_bits_fn loc name args

let try_resolve_extfun extfuns name args =
  match StringMap.find_opt name extfuns with
  | Some (nargs, fn) -> Some (SGALib.SGA.UCustomFn fn, nargs, args)
  | None -> None

let resolve_function types extfuns { lpos; lcnt = name } args =
  let fn, nargs, args =
    match try_resolve_primitive types lpos name args with
    | Some r -> r
    | None -> match try_resolve_extfun extfuns name args with
              | Some r -> r
              | None -> let bound = List.concat [keys core_primitives; keys bits_primitives; keys extfuns] in
                        unbound_error lpos ~bound "function" name in
  assert (nargs <= 2);
  if List.length args <> nargs then
    type_error lpos (sprintf "Function `%s' takes %d arguments" name nargs)
  else
    let padding = list_const (2 - nargs) { lpos; lcnt = Const (UBits [||]) } in
    { lpos; lcnt = fn }, List.append args padding

let resolve_rule types extfuns registers ((nm, action): unresolved_rule) =
  let find_register { lpos; lcnt = name } =
    match List.find_opt (fun rsig -> rsig.reg_name = name) registers with
    | Some rsig -> { lpos; lcnt = rsig }
    | None -> unbound_error lpos "register" name in
  let rec resolve_action ({ lpos; lcnt }: (Pos.t, unresolved_value, string, string) action locd) =
    { lpos;
      lcnt = match lcnt with
             | Skip -> Skip
             | Fail sz -> Fail sz
             | Var v -> Var v
             | Num n -> untyped_number_error lpos n
             | Symbol s -> symbol_error lpos s
             | Keyword k ->
                let v = UEnum { name = None; field = k } in
                Const (resolve_value types (locd_make lpos v))
             | Const v -> Const (resolve_value types (locd_make lpos v))
             | Progn rs -> Progn (List.map resolve_action rs)
             | Let (bs, body) ->
                Let (List.map (fun (var, expr) -> (var, resolve_action expr)) bs,
                     List.map resolve_action body)
             | If (c, l, rs) ->
                If (resolve_action c,
                    resolve_action l,
                    List.map resolve_action rs)
             | When (c, rs) ->
                When (resolve_action c, List.map resolve_action rs)
             | Switch { operand; default; branches } ->
                Switch { operand = resolve_action operand;
                         default = resolve_action default;
                         branches = List.map (fun (lbl, br) ->
                                        resolve_action lbl, resolve_action br)
                                      branches }
             | Read (port, r) ->
                Read (port, find_register r)
             | Write (port, r, v) ->
                Write (port, find_register r, resolve_action v)
             | Call (fn, args) ->
                let fn, args = resolve_function types extfuns fn args in
                Call (fn, List.map resolve_action args) } in
  (nm.lcnt, resolve_action action)

let resolve_register types (name, init) =
  { reg_name = name.lcnt;
    reg_init = resolve_value types init }

let resolve_scheduler rules (s: Pos.t scheduler locd) =
  let check_rule { lpos; lcnt = name } =
    if not (List.mem_assoc name rules) then
      unbound_error lpos "rule" name in
  let rec check_scheduler ({ lcnt; _ }: Pos.t scheduler locd) =
    match lcnt with
    | Done -> ()
    | Sequence rs ->
       List.iter check_rule rs
    | Try (r, s1, s2) ->
       check_rule r;
       check_scheduler s1;
       check_scheduler s2 in
  check_scheduler s; s

let resolve_module types (extfuns: (int * string ffi_signature) StringMap.t)
      { lcnt = { m_registers; m_rules; m_schedulers; _ }; _ } =
  let registers = List.map (resolve_register types) m_registers in
  let rules = List.map (resolve_rule types extfuns registers) m_rules in
  let scheduler = resolve_scheduler rules (List.hd m_schedulers |> snd) in
  { registers; rules; scheduler }

let resolve { types; extfuns; mods } =
  let types = resolve_typedecls types in
  let extfuns = extfuns |> List.to_seq |> Seq.map (resolve_extfun_decl types) |> StringMap.of_seq in
  List.map (resolve_module types extfuns) mods

let typecheck { registers; rules; scheduler } =
  let open SGALib.Compilation in
  let tc_rule (nm, r) = (nm, check_result (typecheck_rule r)) in
  let c_rules = List.map tc_rule rules in
  let c_scheduler = SGALib.Compilation.typecheck_scheduler scheduler in
  { c_registers = registers; c_rules; c_scheduler }
