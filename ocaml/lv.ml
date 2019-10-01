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

type unresolved_enum = {
    name: string;
    field: string
  }

type unresolved_value =
  | UBits of bool array
  | UEnum of unresolved_enum

type unresolved_typedecl =
  | Enum_u of { name: string locd; bitsize: int locd; members: (string locd * bits_value locd) list }
  | Struct_u of { name: string locd; fields: (string locd * unresolved_type locd) list }
and unresolved_type =
  | Bits_u of int
  | Unknown_u of string

type unresolved_literal =
  | Var of var_t
  | Fail of unresolved_type
  | Num of (string * int)
  | Symbol of string
  | Keyword of string
  | Enumerator of { name: string; field: string }
  | Const of unresolved_value

type unresolved_action =
  (Pos.t, unresolved_literal, string, string) action

type unresolved_rule =
  string locd * unresolved_action locd

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

type unresolved_extfun = {
    ext_name: string locd;
    ext_argtypes: unresolved_type locd list;
    ext_rettype: unresolved_type locd
  }

type typedecls = {
    td_enums: enum_sig StringMap.t;
    td_structs: struct_sig StringMap.t;
    td_enumerators: enum_sig StringMap.t;
    td_all: typ StringMap.t
  }

type unresolved_unit = {
    types: unresolved_typedecl locd list;
    extfuns: unresolved_extfun list;
    mods: unresolved_module locd list;
  }

type resolved_extfun =
  int * string ffi_signature

type resolved_module = {
    name: string locd;
    registers: reg_signature list;
    rules: (string * Pos.t SGALib.Compilation.raw_action) list;
    schedulers: (string * Pos.t SGALib.Compilation.raw_scheduler) list
  }

type resolved_unit = {
    r_types: typedecls;
    r_extfuns: resolved_extfun StringMap.t;
    r_mods: resolved_module list;
  }

exception Errors of Pos.t err_contents list

module Delay = struct
  let buffer = ref []
  let delay_errors = ref 0

  let buffer_errors errs =
    buffer := errs :: !buffer

  let reset_buffered_errors () =
    let buffered = List.flatten (List.rev !buffer) in
    buffer := [];
    buffered

  let raise_buffered_errors () =
    let buffered = reset_buffered_errors () in
    if buffered <> [] then raise (Errors buffered)

  let with_delayed_errors f =
    incr delay_errors;
    Base.Exn.protect ~f:(fun () ->
        try let result = f () in
            raise_buffered_errors ();
            result
        with Errors errs ->
              buffer_errors errs;
              raise (Errors (reset_buffered_errors ())))
      ~finally:(fun () -> decr delay_errors)

  let with_delayed_errors_1 f x = with_delayed_errors (fun () -> f x)
  let with_delayed_errors_2 f x y = with_delayed_errors (fun () -> f x y)
  let with_delayed_errors_3 f x y z = with_delayed_errors (fun () -> f x y z)

  let apply1_default default f x1 = try f x1 with Errors errs -> buffer_errors errs; default
  let apply2_default default f x1 x2 = try f x1 x2 with Errors errs -> buffer_errors errs; default
  let apply3_default default f x1 x2 x3 = try f x1 x2 x3 with Errors errs -> buffer_errors errs; default
  let apply4_default default f x1 x2 x3 x4 = try f x1 x2 x3 x4 with Errors errs -> buffer_errors errs; default
  let apply1 f x1 = apply1_default () f x1
  let apply2 f x1 x2 = apply2_default () f x1 x2
  let apply3 f x1 x2 x3 = apply3_default () f x1 x2 x3
  let apply4 f x1 x2 x3 x4 = apply4_default () f x1 x2 x3 x4

  let rec iter f = function
    | [] -> ()
    | x :: l -> apply1 f x; iter f l

  let rec map f = function
    | [] -> []
    | x :: xs ->
       let fx = try [f x] with Errors errs -> buffer_errors errs; [] in
       fx @ (map f xs)

  let rec fold_left f acc l =
    match l with
    | [] -> acc
    | x :: l ->
       let acc = try f acc x with Errors errs -> buffer_errors errs; acc in
       fold_left f acc l

  let rec fold_right f l acc =
    match l with
    | [] -> acc
    | x :: l ->
       let acc = fold_right f l acc in
       try f x acc with Errors errs -> buffer_errors errs; acc

  let maybe_delay fdelay fnodelay =
    if !delay_errors > 0 then fdelay else fnodelay

  let apply1_default default f x1 =
    maybe_delay apply1_default (fun _ f x1 -> f x1) default f x1
  let apply2_default default f x1 x2 =
    maybe_delay apply2_default (fun _ f x1 x2 -> f x1 x2) default f x1 x2
  let apply3_default default f x1 x2 x3 =
    maybe_delay apply3_default (fun _ f x1 x2 x3 -> f x1 x2 x3) default f x1 x2 x3
  let apply4_default default f x1 x2 x3 x4 =
    maybe_delay apply4_default (fun _ f x1 x2 x3 x4 -> f x1 x2 x3 x4) default f x1 x2 x3 x4
  let apply1 f x1 =
    maybe_delay apply1 (fun f x1 -> f x1) f x1
  let apply2 f x1 x2 =
    maybe_delay apply2 (fun f x1 x2 -> f x1 x2) f x1 x2
  let apply3 f x1 x2 x3 =
    maybe_delay apply3 (fun f x1 x2 x3 -> f x1 x2 x3) f x1 x2 x3
  let apply4 f x1 x2 x3 x4 =
    maybe_delay apply4 (fun f x1 x2 x3 x4 -> f x1 x2 x3 x4) f x1 x2 x3 x4

  let iter f xs = maybe_delay iter List.iter f xs
  let map f xs = maybe_delay map List.map f xs
  let fold_left f acc l = maybe_delay fold_left List.fold_left f acc l
  let fold_right f l acc = maybe_delay fold_right List.fold_right f l acc
end

let error err = raise (Errors [err])

let check_result = function
  | Ok cs -> cs
  | Error err -> error err

let parse_error (epos: Pos.t) emsg =
  error { epos; ekind = `ParseError; emsg }

let resolution_error (epos: Pos.t) emsg =
  error { epos; ekind = `ResolutionError; emsg = emsg }

let name_error epos ?(extra="") msg =
  error { epos; ekind = `NameError; emsg = msg ^ extra }

let quote x = "`" ^ x ^ "'"

let unbound_error (epos: Pos.t) ?(bound=[]) kind name =
  let msg = sprintf "Unbound %s: `%s'" kind name in
  let lst = String.concat ", " (List.map quote (List.sort compare bound)) in
  let extra = match bound with
    | [] -> "" | [x] -> sprintf " (expecting `%s')" x
    | _ -> sprintf " (expecting one of %s)" lst in
  name_error epos ~extra msg

let type_error (epos: Pos.t) emsg =
  error { epos; ekind = `TypeError; emsg }

let untyped_number_error (pos: Pos.t) s =
  type_error pos (sprintf "Missing size annotation on number `%s'" s)

let symbol_error (pos: Pos.t) s =
  type_error pos (sprintf "Unexpected symbol `%s'" s)

let expect_cons loc msg = function
  | [] -> parse_error loc (Printf.sprintf "Missing %s" msg)
  | hd :: tl -> hd, tl

let rec gather_pairs = function
  | [] -> []
  | [x1] -> [`Single x1]
  | x1 :: x2 :: tl -> `Pair (x1, x2) :: gather_pairs tl

let rec list_const n x =
  if n = 0 then [] else x :: list_const (n - 1) x

type 'f sexp =
  | Atom of { loc: 'f; atom: string }
  | List of { loc: 'f; elements: 'f sexp list }

let sexp_pos = function
  | Atom { loc; _ } | List { loc; _ } -> loc

let read_all fname =
  if fname = "-" then Stdio.In_channel.input_all Stdio.stdin
  else Stdio.In_channel.read_all fname

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
  match Parsexp.Many_cst.parse_string (read_all fname) with
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
  match Parsexp.Many.parse_string (read_all fname) with
  | Ok sexps ->
     List.map (commit_annots (Pos.Filename fname)) sexps
  | Error err ->
     let pos = Parsexp.Parse_error.position err in
     let msg = Parsexp.Parse_error.message err in
     parse_error (Pos.SexpPos (fname, pos)) msg

let keys s =
  StringMap.fold (fun k _ acc -> k :: acc) s []

let multimap_add k v m =
  let vs = match StringMap.find_opt k m with Some vs -> vs | None -> [] in
  StringMap.add k (v :: vs) m

let multimap_of_locds keyfn xs =
  List.fold_left (fun map x ->
      let { lcnt = k; lpos = v } = keyfn x in multimap_add k v map)
    StringMap.empty xs

let check_no_duplicates msg keyfn ls =
  StringMap.iter (fun k positions ->
      Delay.iter (fun lpos ->
          name_error lpos (sprintf "Duplicate %s: `%s'" msg k))
        (List.tl (List.rev positions)))
    (multimap_of_locds keyfn ls)

let gensym, gensym_reset =
  make_gensym ()

(* Must not start with __ to not clash w/ our gensym *)
let name_re_str = "[a-z][a-zA-Z0-9_]*"
let ident_re = Str.regexp (sprintf "^%s$" name_re_str)

let try_variable var =
  if Str.string_match ident_re var 0 then Some var else None

let bits_const_re = Str.regexp "^\\([0-9]+\\)'\\(b[01]*\\|h[0-9a-fA-F]*\\|[0-9]+\\)$"
let underscore_re = Str.regexp "_"
let leading_h_re = Str.regexp "^h"

let try_plain_int n =
  int_of_string_opt n

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
  else match try_plain_int a with
       | Some n -> Some (`Num n)
       | None -> None

let try_number loc = function
  | "true" -> Some (`Const [|true|])
  | "false" -> Some (`Const [|false|])
  | a -> try_number' loc a

let keyword_re = Str.regexp (sprintf "^:\\(%s\\)$" name_re_str)

let try_keyword nm =
  if Str.string_match keyword_re nm 0 then Some (Str.matched_group 1 nm)
  else None

let enumerator_re = Str.regexp (sprintf "^\\(\\|%s\\)::\\(%s\\)$" name_re_str name_re_str)

let try_enumerator nm =
  if Str.string_match enumerator_re nm 0 then
    Some { name = Str.matched_group 1 nm; field = Str.matched_group 2 nm }
  else None

let symbol_re = Str.regexp (sprintf "^'\\(%s\\)$" name_re_str)

let try_symbol nm =
  if Str.string_match symbol_re nm 0 then Some (Str.matched_group 1 nm)
  else None

let parse sexps =
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
  let expect_pairs msg f1 f2 xs =
    Delay.map (function
        | `Pair (x1, x2) -> (f1 x1, f2 x2)
        | `Single x1 -> ignore (f1 x1); parse_error (sexp_pos x1) (sprintf "Missing %s after this element" msg))
      (gather_pairs xs) in
  let expect_constant csts c =
    let optstrs = List.map (quote << fst) csts in
    let msg = match optstrs with
      | [c] -> c
      | _ -> sprintf "one of %s" (String.concat ", " optstrs) in
    let loc, s = expect_atom msg c in
    match List.assoc_opt s csts with
    | None -> parse_error loc (sprintf "Expecting %s, got `%s'" msg s)
    | Some x -> loc, x in
  let expect_literal loc a =
    match try_enumerator a with
    | Some { name; field } -> Enumerator { name; field }
    | None ->
       match try_keyword a with
       | Some name -> Keyword name
       | None ->
          match try_symbol a with
          | Some name -> Symbol name
          | None ->
             match try_number loc a with
             | Some (`Num n) -> Num (a, n)
             | Some (`Const bs) -> Const (UBits bs)
             | None ->
                match try_variable a with
                | Some var -> Var var
                | None ->
                   let msg = sprintf "Cannot parse `%s' as a literal (number, variable, symbol or keyword)" a in
                   parse_error loc msg in
  let expect_identifier msg v =
    let loc, v = expect_atom msg v in
    match try_variable v with
    | Some v -> loc, v
    | None -> parse_error loc (sprintf "Cannot parse `%s' as %s" v msg) in
  let try_bits loc v =
    match try_number loc v with
    | Some (`Const c) -> Some c
    | _ -> None in
  let expect_bits msg v =
    let loc, sbits = expect_atom msg v in
    match try_number loc sbits with
    | Some (`Const c) -> loc, c
    | Some (`Num _) -> untyped_number_error loc sbits
    | _ -> parse_error loc (sprintf "Expecting a bits constant (e.g. 2'b01), got `%s' %s" sbits num_fmt) in
  let expect_const msg v =
    let loc, scst = expect_atom msg v in
    (loc,
     match try_bits loc scst with
     | Some c -> UBits c
     | None ->
        match try_enumerator scst with
        | Some { name; field } -> UEnum { name; field }
        | None -> parse_error loc "Expecting a bits constant (e.g. 16'hffff) or an enumerator (eg proto::ipv4)") in
  let expect_keyword loc msg nm =
    match try_keyword nm with
    | Some k -> k
    | None -> parse_error loc (sprintf "Expecting %s starting with a colon (:), got `%s'" msg nm) in
  let expect_enumerator loc nm =
    match try_enumerator nm with
    | Some ev -> ev
    | None -> parse_error loc (sprintf "Expecting an enumerator (format: abc::xyz or ::xyz), got `%s'" nm) in
  let expect_type ?(bits_raw=false) = function (* (bit 16), 'typename *)
    | Atom { loc; atom } ->
       (match try_symbol atom with
        | Some s -> locd_make loc (Unknown_u s)
        | None ->
           match try_plain_int atom with
           | Some n when bits_raw -> locd_make loc (Bits_u n)
           | _ -> parse_error loc (sprintf "Expecting a quoted type name, got `%s'" atom))
    | List { loc; elements } ->
       let hd, sizes = expect_cons loc "type" elements in
       let _ = expect_constant [("bits", ())] hd in
       let loc, szstr = expect_atom "a size" (expect_single loc "size" "bit type" sizes) in
       match try_plain_int szstr with
       | Some size -> locd_make loc (Bits_u size)
       | _ -> parse_error loc (sprintf "Expecting a type-level integer (e.g. 32), got `%s'" szstr) in
  let expect_funapp loc kind elements =
    let hd, args = expect_cons loc kind elements in
    let loc_hd, hd = expect_atom (sprintf "a %s name" kind) hd in
    loc_hd, hd, args in
  let rec expect_action_nodelay = function
    | Atom { loc; atom } ->
       locd_make loc
         (match atom with
          | "skip" -> Skip
          | "fail" -> Fail (Bits_t 0)
          | atom -> Lit (expect_literal loc atom))
    | List { loc; elements } ->
       let loc_hd, hd, args = expect_funapp loc "constructor or function" (elements) in
       locd_make loc
         (match hd with
          | "fail" ->
             (match args with
              | [] -> Common.Fail (Bits_t 0)
              | [arg] -> Lit (Fail (expect_type ~bits_raw:true arg).lcnt)
              | _ -> parse_error loc (sprintf "Fail takes 1 argument"))
          | "setq" ->
             let var, body = expect_cons loc "variable name" args in
             let value = expect_action (expect_single loc "value" "write expression" body) in
             Assign (locd_of_pair (expect_identifier "an variable name" var), value)
          | "progn" ->
             Progn (List.map expect_action args)
          | "let" ->
             let bindings, body = expect_cons loc "let bindings" args in
             let bindings = expect_let_bindings bindings in
             let body = List.map expect_action body in
             Let (bindings, body)
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
             Write (port, locd_of_pair (expect_identifier "a register name" reg),
                    expect_action (expect_single loc "value" "write expression" body))
          | "read.0" | "read.1" ->
             let reg = expect_single loc "register name" "read expression" args in
             let port = int_of_string (String.sub hd (String.length hd - 1) 1) in
             Read (port, locd_of_pair (expect_identifier "a register name" reg))
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
  and expect_action s =
    Delay.apply1_default { lpos = sexp_pos s; lcnt = Invalid } expect_action_nodelay s
  and expect_switch_branch branch =
    let loc, lst = expect_list "switch case" branch in
    let lbl, body = expect_cons loc "case label" lst in
    let lbl = match lbl with
      | Atom { loc; atom = "_" } -> `AnyLabel loc
      | _ -> let loc, cst = expect_const "a case label" lbl in
             `SomeLabel (locd_make loc (Lit (Const cst))) in
    (lbl, locd_make loc (Progn (List.map expect_action body)))
  and build_switch_body branches =
    Delay.fold_right (fun (lbl, (branch: _ action locd)) acc ->
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
    let loc_v, var = expect_identifier "an identifier" var in
    let value = expect_single loc "value" "let binding" values in
    let value = expect_action value in
    (locd_make loc_v var, value)
  and expect_let_bindings bs =
    let _, bs = expect_list "let bindings" bs in
    Delay.map expect_let_binding bs in
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
             Sequence (Delay.map (locd_of_pair << (expect_identifier "a rule name")) args)
          | "try" ->
             let rname, args = expect_cons loc "rule name" args in
             let s1, s2 = expect_pair loc "subscheduler 1" "subscheduler 2" args in
             Try (locd_of_pair (expect_identifier "a rule name" rname),
                  expect_scheduler s1,
                  expect_scheduler s2)
          | _ ->
             parse_error loc_hd (sprintf "Unexpected in scheduler: `%s'" hd)) in
  let expect_unqualified_enumerator enumerator = (* :a *)
    let loc, enumerator = expect_atom "an enumerator" enumerator in
    let { name; field } = expect_enumerator loc enumerator in
    if name <> "" then
      parse_error loc (sprintf "Expecting an unqualified enumerator (format: ::xyz), got `%s'" enumerator);
    locd_make loc field in
  let expect_enumerator_value value =
    expect_bits "an enumerator value" value |> locd_of_pair in
  let check_size sz { lpos; lcnt } =
    let sz' = Array.length lcnt in
    if sz' <> sz then
      parse_error lpos
        (sprintf "Inconsistent sizes in enum: expecting `bits %d', got `bits %d'" sz sz') in
  let expect_enum name loc body = (* ((:true 1'b1) (:false 1'b0) …) *)
    let members = expect_pairs "enumerator value" expect_unqualified_enumerator expect_enumerator_value body in
    let (_, eval), _ = expect_cons loc "enumerator (empty enums are not supported)" members in
    let bitsize = Array.length eval.lcnt in
    Delay.iter ((check_size bitsize) << snd) members;
    Delay.apply3 check_no_duplicates "enumerator name in struct" fst members;
    locd_make loc (Enum_u { name; bitsize = locd_make eval.lpos bitsize; members }) in
  let expect_struct_field_name name = (* :label *)
    let loc, name = expect_atom "a field name" name in
    locd_make loc (expect_keyword loc "a field name" name) in
  let expect_struct name loc body = (* ((:kind kind) (:imm (bits 12) …) *)
    let fields = expect_pairs "field type" expect_struct_field_name expect_type body in
    Delay.apply3 check_no_duplicates "field in struct" fst fields;
    locd_make loc (Struct_u { name; fields }) in
  let expect_extfun ext_name loc body =
    let args, rettype = expect_pair loc "argument declarations" "return type" body in
    let _, args = expect_list "argument declarations" args in
    let ext_argtypes = Delay.map expect_type args in
    let ext_rettype = expect_type rettype in
    { ext_name; ext_argtypes; ext_rettype } in
  let rec expect_decl d skind expected =
    let d_loc, d = expect_list ("a " ^ skind) d in
    let kind, name_body = expect_cons d_loc skind d in
    let _, kind = expect_constant expected kind in
    let name, body = expect_cons d_loc "name" name_body in
    let name = locd_of_pair (expect_identifier "an identifier" name) in
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
    let { m_name; m_registers; m_rules; m_schedulers } =
      Delay.fold_left (fun m decl ->
          match expect_decl decl "register, rule, or scheduler declaration" expected |> snd with
          | `Register r -> { m with m_registers = r :: m.m_registers }
          | `Rule r -> { m with m_rules = r :: m.m_rules }
          | `Scheduler s -> { m with m_schedulers = s :: m.m_schedulers }
          | _ -> assert false)
        { m_name; m_registers = []; m_rules = []; m_schedulers = [] } body in
    let m_registers, m_rules, m_schedulers =
      List.rev m_registers, List.rev m_rules, List.rev m_schedulers in
    Delay.apply3 check_no_duplicates "register" fst m_registers;
    Delay.apply3 check_no_duplicates "rule" fst m_rules;
    Delay.apply3 check_no_duplicates "scheduler" fst m_schedulers;
    locd_make loc { m_name; m_registers; m_rules; m_schedulers } in
  let expected_toplevel =
    [("enum", `Enum); ("struct", `Struct); ("extfun", `Extfun); ("module", `Module)] in
  let { types; extfuns; mods } =
    Delay.fold_left (fun u sexp ->
        match expect_decl sexp "module, type, or extfun declaration" expected_toplevel |> snd with
        | `Enum e -> { u with types = e :: u.types }
        | `Struct s -> { u with types = s :: u.types }
        | `Extfun fn -> { u with extfuns = fn :: u.extfuns }
        | `Module m -> { u with mods = m :: u.mods }
        | _ -> assert false)
      { types = []; extfuns = []; mods = [] } sexps in
  let types, extfuns, mods = List.rev types, List.rev extfuns, List.rev mods in
  Delay.apply3 check_no_duplicates "module" (fun m -> m.lcnt.m_name) mods;
  Delay.apply3 check_no_duplicates "external function" (fun fn -> fn.ext_name) extfuns;
  { types; extfuns; mods }

let rexpect_num = function
  | { lpos; lcnt = Lit (Num n); _} -> lpos, n
  | { lpos; _ } -> parse_error lpos "Expecting a type-level integer"

let rexpect_keyword msg = function
  | { lpos; lcnt = Lit (Keyword s); _} -> lpos, s
  | { lpos; _ } -> parse_error lpos (sprintf "Expecting a keyword (%s)" msg)

let rexpect_symbol msg = function
  | { lpos; lcnt = Lit (Symbol s) } -> lpos, s
  | { lpos; _ } -> parse_error lpos (sprintf "Expecting a symbol (%s)" msg)

let rexpect_arg k loc (args: unresolved_action locd list) =
  let a, args = expect_cons loc "argument" args in
  k a, args

let types_empty =
  { td_enums = StringMap.empty;
    td_enumerators = StringMap.empty;
    td_structs = StringMap.empty;
    td_all = StringMap.empty }

let types_add tau_r types =
  match tau_r with
  | Bits_t _ -> types
  | Enum_t sg ->
     { types with td_all = StringMap.add sg.enum_name tau_r types.td_all;
                  td_enums = StringMap.add sg.enum_name sg types.td_enums;
                  td_enumerators = List.fold_left (fun acc (field, _) ->
                                       StringMap.add field sg acc)
                                     types.td_enumerators sg.enum_members }
  | Struct_t sg ->
     { types with td_all = StringMap.add sg.struct_name tau_r types.td_all;
                  td_structs = StringMap.add sg.struct_name sg types.td_structs }


let resolve_type types { lpos; lcnt: unresolved_type } =
  match lcnt with
  | Bits_u sz -> Bits_t sz
  | Unknown_u nm ->
     match StringMap.find_opt nm types.td_all with
     | Some tau -> tau
     | None ->
        unbound_error lpos ~bound:(keys types.td_all) "type" nm

let assert_unique_type types nm kind =
  match StringMap.find_opt nm.lcnt types.td_all with
  | Some tau ->
     name_error nm.lpos
       (sprintf "Duplicate type name: %s `%s' previously declared (as %s)" kind nm.lcnt (kind_to_str tau))
  | None -> ()

let resolve_typedecl types (typ: unresolved_typedecl locd) =
  (* Struct fields and enumerators don't have to be globally unique *)
  let resolve_struct_field_type (nm, tau) = (nm.lcnt, resolve_type types tau) in
  let resolve_enum_member (nm, v) = (nm.lcnt, v.lcnt) in
  match typ.lcnt with
  | Enum_u { name; bitsize; members } ->
     assert_unique_type types name "enum";
     Enum_t { enum_name = name.lcnt; enum_bitsize = bitsize.lcnt;
              enum_members = Delay.map resolve_enum_member members }
  | Struct_u { name; fields } ->
     assert_unique_type types name "struct";
     let struct_fields = Delay.map resolve_struct_field_type fields in
     Struct_t { struct_name = name.lcnt; struct_fields }

let resolve_typedecls types =
  Delay.fold_left (fun types t ->
      let typ = resolve_typedecl types t in
      types_add typ types)
    types_empty types

let core_primitives =
  let open SGALib.SGA in
  let conv_fn f = UPrimFn (UConvFn f) in
  let struct_fn f = UPrimFn (UStructFn f) in
  [("eq", (`Fn (conv_fn UEq), 2));
   ("=", (`Fn (conv_fn UEq), 2));
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

let all_primitives =
  let names m = List.to_seq (keys m) in
  StringSet.empty
  |> StringSet.add_seq (names core_primitives)
  |> StringSet.add_seq (names bits_primitives)

let resolve_extfun_decl types { ext_name; ext_argtypes; ext_rettype } =
  let unit_u = locd_make ext_name.lpos (Bits_u 0) in
  if StringSet.mem ext_name.lcnt all_primitives then
    name_error ext_name.lpos (sprintf "External function name `%s' conflicts with existing primitive." ext_name.lcnt);
  let nargs, a1, a2 = match ext_argtypes with
    | [] -> 0, unit_u, unit_u
    | [t] -> 1, t, unit_u
    | [x; y] -> 2, x, y
    | _ -> parse_error ext_name.lpos ("External functions with more than 2 arguments are not supported" ^
                                        " (consider using a struct to pass more arguments)") in
  ext_name.lcnt, (nargs, { ffi_name = ext_name.lcnt;
                           ffi_arg1type = resolve_type types a1;
                           ffi_arg2type = resolve_type types a2;
                           ffi_rettype = resolve_type types ext_rettype })

let resolve_value types { lpos; lcnt } =
  let resolve_enum_field sg field =
    match List.assoc_opt field sg.enum_members with
    | Some bs -> Enum (sg, bs)
    | None -> unbound_error lpos ~bound:(List.map fst sg.enum_members)
                (sprintf "enumerator in type `%s'" sg.enum_name) field in
  match lcnt with
  | UBits bs -> Bits bs
  | UEnum { name = ""; field } ->
     (match StringMap.find_opt field types.td_enumerators with
      | Some sg -> resolve_enum_field sg field
      | None -> unbound_error lpos ~bound:(keys types.td_enumerators) "enumerator" field)
  | UEnum { name; field } ->
     (match StringMap.find_opt name types.td_all with
      | Some (Enum_t sg) -> resolve_enum_field sg field
      | Some tau -> type_error lpos (sprintf "Type `%s' is not an enum" (typ_to_string tau))
      | None -> unbound_error lpos ~bound:(keys types.td_enums) "enum" name)

let try_resolve_bits_fn { lpos; lcnt = name } args =
  let bits_fn nm = SGALib.SGA.UPrimFn (SGALib.SGA.UBitsFn nm) in
  match StringMap.find_opt name bits_primitives with
  | Some (fn, nargs) ->
     Some (match fn with
           | `Prim0 fn ->
              bits_fn fn, nargs, args
           | `Prim1 fn ->
              let (_, (_, n)), args = rexpect_arg rexpect_num lpos args in
              bits_fn (fn n), nargs, args
           | `Prim2 fn ->
              let (_, (_, n)), args = rexpect_arg rexpect_num lpos args in
              let (_, (_, n')), args = rexpect_arg rexpect_num lpos args in
              bits_fn (fn n n'), nargs, args)
  | None -> None

let rexpect_pairs msg f1 f2 xs =
  Delay.map (function
      | `Pair (h1, h2) -> (f1 h1, f2 h2)
      | `Single h1 -> ignore (f1 h1); parse_error h1.lpos (sprintf "Missing %s after this element" msg))
    (gather_pairs xs)

let rexpect_type loc types (args: unresolved_action locd list) =
  let (loc, t), args = rexpect_arg (rexpect_symbol "a type name") loc args in
  let tau = resolve_type types (locd_make loc (Unknown_u t)) in
  loc, t, tau, args

let try_resolve_primitive types name args =
  let must_struct_t loc nm = function
    | Struct_t sg -> SGALib.Util.sga_struct_sig_of_struct_sig sg
    | tau -> type_error loc (sprintf "Expecting a struct name, but `%s' is `%s'"
                               nm (kind_to_str ~pre:true tau)) in
  let rexpect_field args =
    let (_, f), args = rexpect_arg (rexpect_keyword "a struct field") name.lpos args in
    SGALib.Util.coq_string_of_string f, args in
  match StringMap.find_opt name.lcnt core_primitives with
  | Some (fn, nargs) ->
     Some (match fn with
           | `Fn fn ->
              fn, nargs, args
           | `TypeFn fn ->
              let _, _, t, args = rexpect_type name.lpos types args in
              fn (SGALib.Util.sga_type_of_typ t), nargs, args
           | `FieldFn fn ->
              let f, args = rexpect_field args in
              fn f, nargs, args
           | `StructFn fn ->
              let loc, nm, t, args = rexpect_type name.lpos types args in
              let f, args = rexpect_field args in
              fn (must_struct_t loc nm t) f, nargs, args)
  | None -> try_resolve_bits_fn name args

let try_resolve_extfun extfuns name args =
  match StringMap.find_opt name.lcnt extfuns with
  | Some (nargs, fn) -> Some (SGALib.SGA.UCustomFn fn, nargs, args)
  | None -> None

let literal_tt = Lit (Const (UBits [||]))

let try_resolve_special_function types name (args: unresolved_action locd list) =
  match name.lcnt with
  | "new" ->
     let loc, nm, tau, args = rexpect_type name.lpos types args in
     let sga_tau = SGALib.Util.sga_type_of_typ tau in
     let uinit = SGALib.SGA.(UPrimFn (UConvFn (UInit sga_tau))) in
     (match tau with
      | Bits_t sz ->
         resolution_error loc
           (sprintf "Use %d'0 instead of (new '%s ...) to create a bits value" sz nm)
      | Enum_t { enum_name; enum_bitsize; _ } ->
         resolution_error loc
           (sprintf "Use (unpack '%s %d'0) instead of (new '%s ...) to create an enum value"
              enum_name enum_bitsize nm)
      | Struct_t sg ->
         let expect_field_name nm =
           locd_of_pair (rexpect_keyword "a field name" nm) in
         let expect_field_val x = x in
         let tt = { lpos = loc; lcnt = literal_tt } in
         Some (match rexpect_pairs "value" expect_field_name expect_field_val args with
               | [] -> `Call (locd_make loc uinit, tt, tt)
               | fields -> `StructInit (sg, fields)))
  | _ -> None

let pad_function_call lpos name fn nargs (args: unresolved_action locd list) =
  assert (nargs <= 2);
  if List.length args <> nargs then
    type_error lpos (sprintf "Function `%s' takes %d arguments" name nargs)
  else
    let tt = { lpos; lcnt = literal_tt } in
    let a1, a2 = match args with
      | [] -> tt, tt
      | [a1] -> a1, tt
      | [a1; a2] -> a1, a2
      | _ -> assert false in
    `Call ({ lpos; lcnt = fn }, a1, a2)

let resolve_function types extfuns name (args: unresolved_action locd list) =
  match try_resolve_special_function types name args with
  | Some ast -> ast
  | None ->
     let (fn, nargs, args) =
       match try_resolve_primitive types name args with
       | Some r -> r
       | None -> match try_resolve_extfun extfuns name args with
                 | Some r -> r
                 | None -> let bound = List.concat [keys core_primitives; keys bits_primitives; keys extfuns] in
                           unbound_error name.lpos ~bound "function" name.lcnt in
     pad_function_call name.lpos name.lcnt fn nargs args

let resolve_rule types extfuns registers ((nm, action): unresolved_rule) =
  let find_register { lpos; lcnt = name } =
    match List.find_opt (fun rsig -> rsig.reg_name = name) registers with
    | Some rsig -> { lpos; lcnt = rsig }
    | None -> unbound_error lpos "register" name in
  let rec resolve_struct_fields fields =
    List.map (fun (nm, v) -> nm, resolve_action v) fields
  and resolve_action_nodelay ({ lpos; lcnt }: unresolved_action locd) =
    { lpos;
      lcnt = match lcnt with
             | Skip -> Skip
             | Invalid -> Invalid
             | Fail sz -> Fail sz
             | Lit (Fail tau) -> Fail (resolve_type types (locd_make lpos tau))
             | Lit (Var v) -> Lit (Common.Var v)
             | Lit (Num (s, _)) -> untyped_number_error lpos s
             | Lit (Symbol s) -> symbol_error lpos s
             | Lit (Keyword k) -> parse_error lpos (sprintf "Unexpected keyword: `%s'" k)
             | Lit (Enumerator { name; field }) ->
                let v = UEnum { name; field } in
                Lit (Common.Const (resolve_value types (locd_make lpos v)))
             | Lit (Const v) -> Lit (Common.Const (resolve_value types (locd_make lpos v)))
             | Assign (v, a) -> Assign (v, resolve_action a)
             | StructInit (sg, fields) ->
                StructInit (sg, resolve_struct_fields fields)
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
                (match resolve_function types extfuns fn args with
                 | `Call (fn, a1, a2) ->
                    Call (fn, [resolve_action a1; resolve_action a2])
                 | `StructInit (sg, fields) ->
                    StructInit (sg, resolve_struct_fields fields)) }
  and resolve_action l =
    Delay.apply1_default { l with lcnt = Invalid } resolve_action_nodelay l in
  (nm.lcnt, resolve_action action)

let resolve_register types (name, init) =
  { reg_name = name.lcnt;
    reg_init = resolve_value types init }

let resolve_scheduler rules ((nm, s): unresolved_scheduler) =
  let check_rule { lpos; lcnt = name } =
    if not (List.mem_assoc name rules) then
      unbound_error lpos "rule" name in
  let rec check_scheduler ({ lcnt; _ }: Pos.t scheduler locd) =
    match lcnt with
    | Done -> ()
    | Sequence rs ->
       Delay.iter check_rule rs
    | Try (r, s1, s2) ->
       Delay.apply1 check_rule r;
       Delay.apply1 check_scheduler s1;
       Delay.apply1 check_scheduler s2 in
  check_scheduler s; (nm.lcnt, s)

let resolve_module types (extfuns: (int * string ffi_signature) StringMap.t)
      { lpos; lcnt = { m_name; m_registers; m_rules; m_schedulers; _ } } =
  let registers = Delay.map (resolve_register types) m_registers in
  let rules = Delay.map (resolve_rule types extfuns registers) m_rules in
  let schedulers = Delay.map (resolve_scheduler rules) m_schedulers in
  { name = { m_name with lpos }; registers; rules; schedulers }

let resolve { types; extfuns; mods } =
  let r_types = resolve_typedecls types in
  let r_extfuns = extfuns |> Delay.map (resolve_extfun_decl r_types) |> List.to_seq |> StringMap.of_seq in
  let r_mods = Delay.map (resolve_module r_types r_extfuns) mods in
  { r_types; r_extfuns; r_mods }

let typecheck_module { name; registers; rules; schedulers } =
  let open SGALib.Compilation in
  let tc_rule (nm, r) = (nm, check_result (typecheck_rule r)) in
  let c_rules = Delay.map tc_rule rules in
  let schedulers = Delay.map (typecheck_scheduler << snd) schedulers in
  if schedulers = [] then resolution_error name.lpos (sprintf "Missing scheduler in module `%s'" name.lcnt);
  { c_registers = registers; c_rules; c_scheduler = List.hd schedulers }

let typecheck resolved =
  Delay.map typecheck_module resolved.r_mods
