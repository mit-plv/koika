open Common

let lcnt x = x.lcnt
let sprintf = Printf.sprintf

module Pos = struct
  type t =
    | StrPos of string
    | Filename of string
    | SexpRange of string * Parsexp.Positions.range

  let compare p1 p2 =
    match p1, p2 with
    | StrPos _, StrPos _ -> 0 (* Use reporting order *)
    | StrPos _, _ -> -1 | _, StrPos _ -> 1
    | Filename f1, Filename f2 -> compare f1 f2
    | Filename _, _ -> -1 | _, Filename _ -> 1
    | SexpRange (f1, rng1), SexpRange (f2, rng2) ->
       match compare f1 f2 with
       | 0 -> Parsexp.Positions.compare_range rng1 rng2
       | n -> n

  let range_to_string begpos endpos =
    if begpos = endpos then sprintf "%d" begpos
    else sprintf "%d-%d" begpos endpos

  (* Emacs expects columns to start at 1 in compilation output *)
  let to_string = function
    | StrPos s -> s
    | Filename f ->
       sprintf "%s:0:1" f
    | SexpRange (fname, { start_pos; end_pos }) ->
       let line = range_to_string start_pos.line end_pos.line in
       let col = range_to_string (start_pos.col + 1) (end_pos.col + 1) in
       sprintf "%s:%s:%s" fname line col
end

type nonrec 'a locd = (Pos.t, 'a) locd

type unresolved_enumerator = {
    enum: string;
    constructor: string
  }

type unresolved_value =
  | UBits of bool array
  | UEnum of unresolved_enumerator

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
  | Enumerator of { enum: string; constructor: string }
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

let quote x = "‘" ^ x ^ "’"
let fquote () = quote

let one_of_str candidates =
  match candidates with
  | [] -> "" | [x] -> quote x
  | _ -> let candidates = candidates |> List.map quote |> String.concat ", " in
         sprintf "one of %s" candidates

let in_scope_str candidates =
  match candidates with
  | [] -> "none in scope"
  | _ -> let candidates = candidates |> List.map quote |> String.concat ", " in
         sprintf "in scope: %s" candidates

module Errors = struct
  module ParseErrors = struct
    type t =
      | SexpError of { msg: string }
      | BadPosAnnot of { sexp: Base.Sexp.t }
      | BadBitsSize of { size: string }
      | Overflow of { numstr: string; bits: string; size: int }

    let to_string = function
      | SexpError { msg } -> String.capitalize_ascii msg
      | BadPosAnnot { sexp } ->
         sprintf "Bad use of <>: %s" (Base.Sexp.to_string sexp)
      | BadBitsSize { size } ->
         sprintf "Unparseable size annotation: %s" (quote size)
      | Overflow { numstr; bits; size } ->
         sprintf "Number %a (%d'b%s) does not fit in %d bit(s)"
           fquote numstr (String.length bits) bits size
  end

  module SyntaxErrors = struct
    type t =
      | MissingSize of { number: string }
      | MissingElement of { kind: string }
      | MissingElementIn of { kind: string; where: string }
      | MissingPairElement of { kind2: string }
      | TooManyElementsIn of { kind: string; where: string }
      | ExpectingNil of { kind: string }
      | UnexpectedList of { expected: string }
      | UnexpectedAtom of { expected: string; atom: string }
      | UnexpectedSymbol of { symbol: string }
      | UnexpectedKeyword of { keyword: string }
      | BadChoice of { atom: string; expected: string list }
      | BadLiteral of { atom: string }
      | BadBitsLiteral of { atom: string }
      | BadIdentifier of { kind: string; atom: string }
      | BadConst of { atom: string }
      | BadKeyword of { kind: string; atom: string }
      | BadEnumerator of { atom: string }
      | BadType of { atom: string }
      | BadBitsSizeInType of { atom: string }
      | BadIntParam of { obj: string }
      | BadKeywordParam of { obj: string; kind: string }
      | BadSymbolParam of { obj: string; kind: string }
      | EmptySwitch
      | EarlyDefaultInSwitch
      | MissingDefaultInSwitch
      | DuplicateDefaultInSwitch
      | QualifiedEnumeratorInDecl of { enum: string; constructor: string }
      | TooManyArgumentsInExtfunDecl

    let to_string = function
      | MissingSize { number } ->
         sprintf "Missing size annotation on number %s" (quote number)
      | MissingElement { kind } ->
         sprintf "Missing %s" kind
      | MissingElementIn { kind; where } ->
         sprintf "No %s found in %s" kind where
      | MissingPairElement { kind2 } ->
         sprintf "Missing %s after this element" kind2
      | TooManyElementsIn { kind; where } ->
         sprintf "More than one %s found in %s" kind where
      | ExpectingNil { kind } ->
         sprintf "Unexpected %s" kind
      | UnexpectedList { expected } ->
         sprintf "Expecting %s, but got a list" expected
      | UnexpectedAtom { expected; atom } ->
         sprintf "Expecting a list (%s), got %a" expected fquote atom
      | UnexpectedSymbol { symbol } ->
         sprintf "Unexpected symbol %s" (quote symbol)
      | UnexpectedKeyword { keyword } ->
         sprintf "Unexpected keyword %s" (quote keyword)
      | BadChoice { atom; expected } ->
         sprintf "Expecting %s, got %a" (one_of_str expected) fquote atom
      | BadLiteral { atom } ->
         sprintf "Expecting a literal (a number, variable, symbol or keyword), got %a" fquote atom
      | BadBitsLiteral { atom } ->
         sprintf "Expecting a sized literal (e.g. 2'b01 or 8'42), got %a" fquote atom
      | BadIdentifier { kind; atom } ->
         sprintf "Expecting an identifier (%s), got %a" kind fquote atom
      | BadConst { atom } ->
         sprintf "Expecting a sized literal (e.g. 8'hff) or an enumerator (eg proto::ipv4), got %a" fquote atom
      | BadKeyword { kind; atom } ->
         sprintf "Expecting a keyword (%s, starting with a colon), got %a" kind fquote atom
      | BadEnumerator { atom } ->
         sprintf "Expecting an enumerator (format: abc::xyz or ::xyz), got %a" fquote atom
      | BadType { atom } ->
         sprintf "Expecting a type name (e.g. (bits 16) or 'xyz) got %a" fquote atom
      | BadBitsSizeInType { atom } ->
         sprintf "Expecting a bit size (e.g. 32), got %a" fquote atom
      | BadIntParam { obj } ->
         sprintf "This %s should be an integer" obj
      | BadKeywordParam { obj; kind } ->
         sprintf "This %s should be a keyword (%s, starting with a colon)" obj kind
      | BadSymbolParam { obj; kind } ->
         sprintf "This %s should be a symbol (%s, starting with a quote)" obj kind
      | EmptySwitch ->
         "No valid branch in switch: not sure what to return"
      | EarlyDefaultInSwitch ->
         "Default case (_) in switch precedes other branches; move it to the end"
      | MissingDefaultInSwitch ->
         "Missing default case (_) in switch"
      | DuplicateDefaultInSwitch ->
         "Duplicated default case (_) in switch"
      | QualifiedEnumeratorInDecl { enum; constructor } ->
         sprintf "Enumerator declarations should not be qualified: try %a instead of %a"
           fquote ("::" ^ constructor) fquote (enum ^ "::" ^ constructor)
      | TooManyArgumentsInExtfunDecl ->
         "External functions with more than 2 arguments are not supported" ^
           " (consider using a struct to pass more arguments)"
  end

  module NameErrors = struct
    type t =
      | Unbound of { kind: string; prefix: string; name: string; candidates: string list }
      | Duplicate of { kind: string; name: string }
      | DuplicateTypeName of { name: string; kind: string; previous: typ }
      | ExtfunShadowsPrimitive of { ext_name: string }
      | MissingScheduler of { modname: string }
      | MissingModule

    let to_string = function
      | Unbound { kind; prefix; name; candidates } ->
         let candidates =
           if candidates = [] then ""
           else sprintf " (%s)" (in_scope_str (List.map (fun c -> prefix ^ c) candidates)) in
         sprintf "Unbound %s: %a%s" kind fquote (prefix ^ name) candidates
      | Duplicate { kind; name } ->
         sprintf "Duplicate %s: %a" kind fquote name
      | DuplicateTypeName { name; kind; previous } ->
         sprintf "Duplicate type name: %s %a previously declared (as %s)" kind fquote name (kind_to_str previous)
      | ExtfunShadowsPrimitive { ext_name } ->
         sprintf "External function name %a conflicts with existing primitive" fquote ext_name
      | MissingScheduler { modname } ->
         sprintf "Missing scheduler in module %a" fquote modname
      | MissingModule ->
         "No modules declared"
  end

  module TypeErrors = struct
    type t =
      | BadArgumentCount of { fn: string; expected: int; given: int }
      | InconsistentEnumeratorSizes of { expected: int; actual: int }
      | BadKind of { name: string; expected: string; actual_type: typ }

    let to_string = function
      | BadArgumentCount { fn; expected; given } ->
         sprintf "Function %s takes %d arguments (%d given)" fn expected given
      | InconsistentEnumeratorSizes { expected; actual } ->
         sprintf "Inconsistent sizes in enum: expecting %a, got %a"
           fquote (sprintf "bits %d" expected) fquote (sprintf "bits %d" actual)
      | BadKind { name; expected: string; actual_type } ->
         sprintf "Type %a is %s, not %s" fquote name (kind_to_str actual_type) expected
  end

  module TypeInferenceErrors = struct
    type t = string SGALib.Util.sga_error_message

    let classify (msg: t) =
      match msg with
      | ExplicitErrorInAst -> `TypeError
      | UnboundVariable _ -> `NameError
      | UnboundField _ -> `NameError
      | UnboundEnumMember _ -> `NameError
      | IncorrectRuleType _ -> `TypeError
      | TooManyArguments _ -> `SyntaxError
      | TooFewArguments _ -> `SyntaxError
      | TypeMismatch _ -> `TypeError
      | KindMismatch _ -> `TypeError

    let to_string (msg: t) =
      match msg with
      | ExplicitErrorInAst ->
         "Untypeable term (likely due to an ill-typed subterm)"
      | UnboundVariable { var } ->
         sprintf "Unbound variable %a" fquote var
      | UnboundField { field; sg } ->
         sprintf "Unbound field %a in %s" fquote field (struct_sig_to_string sg)
      | UnboundEnumMember { name; sg } ->
         sprintf "Enumerator %a is not a member of %s" fquote name (enum_sig_to_string sg)
      | IncorrectRuleType { actual } ->
         sprintf "This expression has type %a, but rules are expected to have type unit (bits 0)"
           fquote (typ_to_string actual)
      | TooManyArguments { name; actual; expected } ->
         sprintf "Too many arguments in call to %a: expected %d, got %d"
           fquote name expected actual
      | TooFewArguments { name; actual; expected } ->
         sprintf "Too few arguments in call to %a: expected %d, got %d"
           fquote name expected actual
      | TypeMismatch { expected; actual } ->
         sprintf "This term has type %a, but %a was expected"
           fquote (typ_to_string actual) fquote (typ_to_string expected)
      | KindMismatch { actual; expected } ->
         sprintf "This term has type %a, but kind %a was expected"
           fquote (typ_to_string actual) fquote expected
  end

  module Warnings = struct
    type t =
      | BadInitBits of { init: string; size: int }
      | BadInitEnum of { init: string; name: string; bitsize: int }

    let to_string = function
      | BadInitBits { init; size } ->
         sprintf "Use %d'0 instead of (new '%s ...) to create a 0-initialized bits" size init
      | BadInitEnum { init; name; bitsize } ->
         sprintf "Use unpack (e.g. (unpack '%s %d'0)) or an enumerator literal (e.g. ::xyz) instead of (new '%s ...) to create an enum value" name bitsize init
  end

  type err =
    | EParse of ParseErrors.t
    | ESyntax of SyntaxErrors.t
    | EName of NameErrors.t
    | EType of TypeErrors.t
    | ETypeInference of TypeInferenceErrors.t
    | EWarn of Warnings.t

  let classify = function
    | EParse _ -> `ParseError
    | ESyntax _ -> `SyntaxError
    | EName _ -> `NameError
    | EType _ -> `TypeError
    | ETypeInference err -> TypeInferenceErrors.classify err
    | EWarn _ -> `Warning

  let err_to_string = function
    | EParse err -> ParseErrors.to_string err
    | ESyntax err -> SyntaxErrors.to_string err
    | EName err -> NameErrors.to_string err
    | EType err -> TypeErrors.to_string err
    | ETypeInference err -> TypeInferenceErrors.to_string err
    | EWarn wrn -> Warnings.to_string wrn

  type error = { epos: Pos.t; emsg: err }

  let compare e1 e2 =
    match Pos.compare e1.epos e2.epos with
    | 0 -> compare e1.emsg e2.emsg
    | n -> n

  let to_string { epos; emsg } =
    sprintf "%s: %s: %s"
      (Pos.to_string epos)
      (match (classify emsg) with
       | `Warning -> "Warning"
       | `ParseError -> "Parse error"
       | `SyntaxError -> "Syntax error"
       | `NameError -> "Name error"
       | `TypeError -> "Type error")
      (err_to_string emsg)

  let collected_warnings : error list ref = ref []
  let fetch_warnings () =
    let warnings = !collected_warnings in
    collected_warnings := [];
    warnings

  exception Errors of error list
  let warning epos emsg = collected_warnings := { epos; emsg = EWarn emsg } :: !collected_warnings
end

open Errors
open Warnings

module Delay = struct
  let buffer = ref []
  let delay_errors = ref 0

  let handle_exn = function
    | Errors errs when !delay_errors > 0 -> buffer := errs :: !buffer
    | exn -> raise exn

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
        with (Errors _) as exn ->
          handle_exn exn;
          raise (Errors (reset_buffered_errors ())))
      ~finally:(fun () -> decr delay_errors)

  let with_exn_handler f x =
    try f x with exn -> handle_exn exn

  let apply1_default default f x1 = try f x1 with exn -> handle_exn exn; default
  let apply2_default default f x1 x2 = try f x1 x2 with exn -> handle_exn exn; default
  let apply3_default default f x1 x2 x3 = try f x1 x2 x3 with exn -> handle_exn exn; default
  let apply4_default default f x1 x2 x3 x4 = try f x1 x2 x3 x4 with exn -> handle_exn exn; default
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
       let fx = try [f x] with exn -> handle_exn exn; [] in
       fx @ (map f xs)

  let rec fold_left f acc l =
    match l with
    | [] -> acc
    | x :: l ->
       let acc = try f acc x with exn -> handle_exn exn; acc in
       fold_left f acc l

  let rec fold_right f l acc =
    match l with
    | [] -> acc
    | x :: l ->
       let acc = fold_right f l acc in
       try f x acc with exn -> handle_exn exn; acc

  let maybe f x =
    apply1_default None (fun x -> Some (f x)) x
end

let error ?default epos emsg =
  let exn = Errors [{ epos; emsg }] in
  match default with
  | Some v -> Delay.handle_exn exn; v
  | None -> raise exn
let parse_error ?default epos emsg = error ?default epos (EParse emsg)
let syntax_error ?default epos emsg = error ?default epos (ESyntax emsg)
let name_error ?default epos msg = error ?default epos (EName msg)
let type_error ?default epos msg = error ?default epos (EType msg)
let type_inference_error ?default epos emsg = error ?default epos (ETypeInference emsg)

module Dups(OT: Map.OrderedType) = struct
  module M = Map.Make(OT)

  let multimap_add k v m =
    let vs = match M.find_opt k m with Some vs -> vs | None -> [] in
    M.add k (v :: vs) m

  let multimap_of_locds keyfn xs =
    List.fold_left (fun map x ->
        let { lcnt = k; lpos } = keyfn x in multimap_add k (x, lpos) map)
      M.empty xs

  let check kind (keyfn: 'a -> OT.t locd) strfn xs =
    M.iter (fun _ positions ->
        Delay.iter (fun (x, lpos) ->
            name_error lpos @@ Duplicate { kind; name = (strfn x) })
          (List.tl (List.rev positions)))
      (multimap_of_locds keyfn xs)
end

module StringDuplicates = Dups(OrderedString)
module BitsDuplicates = Dups(struct type t = bool array let compare = Pervasives.compare end)

let expect_cons loc kind = function
  | [] -> syntax_error loc @@ MissingElement { kind }
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

module DelayedReader (P: Parsexp.Eager_parser) = struct
  exception GotSexp of P.parsed_value * Parsexp.Positions.pos

  let parse_string fname source =
    let open Parsexp in
    let got_sexp state parsed_value =
      raise_notrace (GotSexp (parsed_value, P.State.Read_only.position state)) in
    let state =
      P.State.create ~no_sexp_is_error:false got_sexp in
    let feed pos =
      try
        let len = String.length source - pos in
        P.feed_substring state ~pos ~len source P.Stack.empty |> P.feed_eoi state
      with Parse_error err ->
        let pos = Parse_error.position err in
        let range = Positions.{ start_pos = pos; end_pos = pos } in
        let msg = Parse_error.message err in
        parse_error (Pos.SexpRange (fname, range)) @@ SexpError { msg } in
    let rec read_sexps pos =
      P.State.reset ~pos state;
      try Delay.apply1 feed pos.offset; []
      with GotSexp (sexp, last_pos) -> sexp :: read_sexps last_pos in
    read_sexps (P.State.position state)
end

module DelayedReader_plain = DelayedReader (Parsexp.Eager)
module DelayedReader_cst = DelayedReader (Parsexp.Eager_cst)

let read_cst_sexps fname =
  let wrap_loc loc =
    Pos.SexpRange (fname, loc) in
  let rec drop_comments (s: Parsexp.Cst.t_or_comment) =
    match s with
    | Parsexp.Cst.Sexp (Parsexp.Cst.Atom { loc; atom; _ }) ->
       Some (Atom { loc = wrap_loc loc; atom })
    | Parsexp.Cst.Sexp (Parsexp.Cst.List { loc; elements }) ->
       Some (List { loc = wrap_loc loc;
                    elements = Base.List.filter_map ~f:drop_comments elements })
    | Parsexp.Cst.Comment _ -> None in
  DelayedReader_cst.parse_string fname (read_all fname)
  |> Base.List.filter_map ~f:drop_comments

let read_annotated_sexps fname =
  let rec commit_annots loc (sexp: Base.Sexp.t) =
    match sexp with
    | Atom atom ->
       Atom { loc; atom }
    | List [Atom "<>"; Atom annot; body] ->
       commit_annots (Pos.StrPos annot) body
    | List (Atom "<>" :: _) ->
       parse_error (Pos.Filename fname) @@ BadPosAnnot { sexp }
    | List elements ->
       List { loc; elements = List.map (commit_annots loc) elements } in
  DelayedReader_plain.parse_string fname (read_all fname)
  |> Delay.map (commit_annots (Pos.Filename fname))

let keys s =
  StringMap.fold (fun k _ acc -> k :: acc) s [] |> List.rev

let gensym_prefix = "_lvs_"
let gensym, gensym_reset = make_gensym gensym_prefix

let mangling_prefix = "_lv_"
let needs_mangling_re = Str.regexp (sprintf "^\\(%s\\|%s\\)" gensym_prefix mangling_prefix)
let mangle name =
  if Str.string_match needs_mangling_re name 0 then
    mangling_prefix ^ name
  else name

let name_re_str = "_\\|_?[a-zA-Z][a-zA-Z0-9_]*"
let ident_re = Str.regexp (sprintf "^%s$" name_re_str)

let try_variable var =
  if Str.string_match ident_re var 0 then Some (mangle var) else None

let bits_const_re = Str.regexp "^\\([0-9]+\\)'\\(b[01]*\\|h[0-9a-fA-F]*\\|[0-9]+\\)$"
let underscore_re = Str.regexp "_"
let leading_h_re = Str.regexp "^h"

let try_plain_int n =
  int_of_string_opt n

let try_number' loc a =
  let a = Str.global_replace underscore_re "" a in
  if Str.string_match bits_const_re a 0 then
    let size = Str.matched_group 1 a in
    let size = try int_of_string size
               with Failure _ ->
                 parse_error loc @@ BadBitsSize { size } in
    let numstr = Str.matched_group 2 a in
    let num = Z.of_string ("0" ^ (Str.replace_first leading_h_re "x" numstr)) in
    let bits = if size = 0 && num = Z.zero then ""
               else Z.format "%b" num in
    let nbits = String.length bits in
    if nbits > size then
      parse_error loc @@ Overflow { numstr; bits; size }
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
    Some { enum = Str.matched_group 1 nm; constructor = Str.matched_group 2 nm }
  else None

let symbol_re = Str.regexp (sprintf "^'\\(%s\\)$" name_re_str)

let try_symbol nm =
  if Str.string_match symbol_re nm 0 then Some (Str.matched_group 1 nm)
  else None

let language_constructs =
  [("fail", `Fail);
   ("setq", `Setq);
   ("progn", `Progn);
   ("let", `Let);
   ("if", `If);
   ("when", `When);
   ("write.0" , `Write 0);
   ("write.1", `Write 1);
   ("read.0" , `Read 0);
   ("read.1", `Read 1);
   ("switch", `Switch)]
  |> List.to_seq |> StringMap.of_seq

let parse (sexps: Pos.t sexp list) =
  let expect_single loc kind where = function
    | [] ->
       syntax_error loc
         (MissingElementIn { kind; where })
    | _ :: _ :: _ ->
       syntax_error loc
         (TooManyElementsIn { kind; where })
    | [x] -> x in
  let expect_atom expected = function
    | List { loc; _ } ->
       syntax_error loc @@ UnexpectedList { expected }
    | Atom { loc; atom } ->
       (loc, atom) in
  let expect_list expected = function
    | Atom { loc; atom } ->
       syntax_error loc @@ UnexpectedAtom { atom; expected }
    | List { loc; elements } ->
       (loc, elements) in
  let expect_nil = function
    | [] -> ()
    | List { loc; _ } :: _ -> syntax_error loc @@ ExpectingNil { kind = "list" }
    | Atom { loc; _ } :: _ -> syntax_error loc @@ ExpectingNil { kind = "atom" } in
  let expect_pair loc msg1 msg2 lst =
    let x1, lst = expect_cons loc msg1 lst in
    let x2, lst = expect_cons loc msg2 lst in
    expect_nil lst;
    (x1, x2) in
  let expect_pairs kind2 f1 f2 xs =
    Delay.map (function
        | `Pair (x1, x2) -> (f1 x1, f2 x2)
        | `Single x1 -> ignore (f1 x1); syntax_error (sexp_pos x1) @@ MissingPairElement { kind2 })
      (gather_pairs xs) in
  let expect_constant loc csts atom =
    match List.assoc_opt atom csts with
    | None -> syntax_error loc @@ BadChoice { atom; expected = List.map fst csts }
    | Some x -> x in
  let expect_constant_atom csts c =
    let candidates = List.map fst csts in
    let loc, s = expect_atom (one_of_str candidates) c in
    loc, expect_constant loc csts s in
  let expect_literal loc a =
    match try_enumerator a with
    | Some { enum; constructor } -> Enumerator { enum; constructor }
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
                | None -> syntax_error loc @@ BadLiteral { atom = a } in
  let expect_identifier kind v =
    let loc, atom = expect_atom kind v in
    match try_variable atom with
    | Some v -> loc, v
    | None -> syntax_error loc @@ BadIdentifier { kind; atom } in
  let try_bits loc v =
    match try_number loc v with
    | Some (`Const c) -> Some c
    | _ -> None in
  let expect_bits msg v =
    let loc, atom = expect_atom msg v in
    match try_number loc atom with
    | Some (`Const c) -> loc, (atom, c)
    | Some (`Num _) -> syntax_error loc @@ MissingSize { number = atom }
    | _ -> syntax_error loc @@ BadBitsLiteral { atom } in
  let expect_const msg v =
    let loc, atom = expect_atom msg v in
    (loc,
     match try_bits loc atom with
     | Some c -> UBits c
     | None ->
        match try_enumerator atom with
        | Some { enum; constructor } -> UEnum { enum; constructor }
        | None -> syntax_error loc @@ BadConst { atom }) in
  let expect_keyword loc kind atom =
    match try_keyword atom with
    | Some k -> k
    | None -> syntax_error loc @@ BadKeyword { kind; atom } in
  let expect_enumerator loc atom =
    match try_enumerator atom with
    | Some ev -> ev
    | None -> syntax_error loc @@ BadEnumerator { atom } in
  let expect_type ?(bits_raw=false) = function (* (bit 16), 'typename *)
    | Atom { loc; atom = "unit" } ->
       locd_make loc (Bits_u 0)
    | Atom { loc; atom } ->
       locd_make loc
         (match try_symbol atom with
          | Some s -> Unknown_u s
          | None ->
             match try_plain_int atom with
             | Some n when bits_raw -> Bits_u n
             | _ -> syntax_error loc @@ BadType { atom })
    | List { loc; elements } ->
       let hd, sizes = expect_cons loc "type" elements in
       let _ = expect_constant_atom [("bits", ())] hd in
       let loc, szstr = expect_atom "a size" (expect_single loc "size" "bit type" sizes) in
       match try_plain_int szstr with
       | Some size -> locd_make loc (Bits_u size)
       | _ -> syntax_error loc @@ BadBitsSizeInType { atom = szstr } in
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
         (match StringMap.find_opt hd language_constructs with
          | Some fn ->
             (match fn with
              | `Fail ->
                 (match args with
                  | [] -> Common.Fail (Bits_t 0)
                  | [arg] -> Lit (Fail (expect_type ~bits_raw:true arg).lcnt)
                  | _ -> type_error loc @@ BadArgumentCount { fn = "fail"; expected = 1; given = List.length args })
              | `Setq ->
                 let var, body = expect_cons loc "variable name" args in
                 let value = expect_action (expect_single loc "value" "assignment" body) in
                 Assign (locd_of_pair (expect_identifier "a variable name" var), value)
              | `Progn ->
                 Progn (List.map expect_action args)
              | `Let ->
                 let bindings, body = expect_cons loc "let bindings" args in
                 let bindings = expect_let_bindings bindings in
                 let body = List.map expect_action body in
                 Let (bindings, body)
              | `If ->
                 let cond, body = expect_cons loc "condition of conditional expression" args in
                 let tbranch, fbranches = expect_cons loc "true branch of conditional expression" body in
                 If (expect_action cond, expect_action tbranch,
                     List.map expect_action fbranches)
              | `When ->
                 let cond, body = expect_cons loc "condition of conditional expression" args in
                 When (expect_action cond, List.map expect_action body)
              | `Write port ->
                 let reg, body = expect_cons loc "register name" args in
                 Write (port, locd_of_pair (expect_identifier "a register name" reg),
                        expect_action (expect_single loc "value" "call to write" body))
              | `Read port ->
                 let reg = expect_single loc "register name" "call to write" args in
                 Read (port, locd_of_pair (expect_identifier "a register name" reg))
              | `Switch ->
                 let operand, branches = expect_cons loc "switch operand" args in
                 let branches = List.map expect_switch_branch branches in
                 let operand = expect_action operand in
                 let binder = gensym "switch_operand" in
                 (match build_switch_body branches with
                  | (Some default, branches) ->
                     Switch { binder; operand; default; branches }
                  | None, [] -> syntax_error loc @@ EmptySwitch
                  | None, branches ->
                     let default = { lpos = loc; lcnt = Invalid } in
                     let default = syntax_error ~default loc MissingDefaultInSwitch in
                     Switch { binder; operand; default; branches }))
          | None ->
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
    Delay.fold_right (fun (lbl, (branch: _ action locd)) (default, branches) ->
        match default, branches, lbl with
        | None, [], `AnyLabel _ ->
           (Some branch, [])
        | None, _, `AnyLabel loc ->
           syntax_error loc @@ EarlyDefaultInSwitch
        | Some _, _, `AnyLabel loc  ->
           syntax_error loc @@ DuplicateDefaultInSwitch
        | _, _, `SomeLabel l ->
           (default, (l, branch) :: branches))
      branches (None, [])
  and expect_let_binding b =
    let loc, b = expect_list "a let binding" b in
    let var, values = expect_cons loc "identifier" b in
    let loc_v, var = expect_identifier "a variable name" var in
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
    | Atom { loc; atom } ->
       locd_make loc (expect_constant loc [("done", Done)] atom)
    | List { loc; elements } ->
       let loc_hd, hd, args = expect_funapp loc "constructor" (elements) in
       let hd = expect_constant loc_hd [("sequence", `Sequence); ("try", `Try)] hd in
       locd_make loc
         (match hd with
          | `Sequence ->
             Sequence (Delay.map (locd_of_pair << (expect_identifier "a rule name")) args)
          | `Try ->
             let rname, args = expect_cons loc "rule name" args in
             let s1, s2 = expect_pair loc "subscheduler 1" "subscheduler 2" args in
             Try (locd_of_pair (expect_identifier "a rule name" rname),
                  expect_scheduler s1,
                  expect_scheduler s2)) in
  let expect_unqualified_enumerator enumerator = (* ::a *)
    let loc, enumerator = expect_atom "an enumerator" enumerator in
    let { enum; constructor } = expect_enumerator loc enumerator in
    if enum <> "" then
      syntax_error loc @@ QualifiedEnumeratorInDecl { enum = enum; constructor };
    locd_make loc constructor in
  let expect_enumerator_value value =
    let (loc, (s, bs)) = expect_bits "an enumerator value" value in
    (s, locd_make loc bs) in
  let check_size sz { lpos; lcnt } =
    let sz' = Array.length lcnt in
    if sz' <> sz then
      type_error lpos @@ InconsistentEnumeratorSizes { expected = sz; actual = sz' } in
  let expect_enum name loc body = (* ((:true 1'b1) (:false 1'b0) …) *)
    let members = expect_pairs "enumerator value" expect_unqualified_enumerator expect_enumerator_value body in
    let (_, (_, first)), _ = expect_cons loc "enumerator (empty enums are not supported)" members in
    let bitsize = Array.length first.lcnt in
    Delay.iter ((check_size bitsize) << snd << snd) members;
    Delay.apply4 StringDuplicates.check "enumerator name in enum" fst (lcnt << fst) members;
    Delay.apply4 BitsDuplicates.check "value in enum" (snd << snd) (fst << snd) members;
    let members = List.map (fun (nm, (_, bs)) -> (nm, bs)) members in
    locd_make loc (Enum_u { name; bitsize = locd_make first.lpos bitsize; members }) in
  let expect_struct_field_name name = (* :label *)
    let loc, name = expect_atom "a field name" name in
    locd_make loc (expect_keyword loc "a field name" name) in
  let expect_struct name loc body = (* ((:kind kind) (:imm (bits 12) …) *)
    let fields = expect_pairs "field type" expect_struct_field_name expect_type body in
    Delay.apply4 StringDuplicates.check "field in struct" fst (lcnt << fst) fields;
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
    let _, kind = expect_constant_atom expected kind in
    let name, body = expect_cons d_loc "name" name_body in
    let name = locd_of_pair (expect_identifier "a name" name) in
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
    Delay.apply4 StringDuplicates.check "register" fst (lcnt << fst) m_registers;
    Delay.apply4 StringDuplicates.check "rule" fst (lcnt << fst) m_rules;
    Delay.apply4 StringDuplicates.check "scheduler" fst (lcnt << fst) m_schedulers;
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
  Delay.apply4 StringDuplicates.check "module" (fun m -> m.lcnt.m_name) (fun m -> m.lcnt.m_name.lcnt) mods;
  Delay.apply4 StringDuplicates.check "external function" (fun fn -> fn.ext_name) (fun fn -> fn.ext_name.lcnt) extfuns;
  { types; extfuns; mods }

let rexpect_num obj =
  function
  | { lpos; lcnt = Lit (Num n); _} -> lpos, n
  | { lpos; _ } -> syntax_error lpos @@ BadIntParam { obj }

let rexpect_keyword kind obj = function
  | { lpos; lcnt = Lit (Keyword s); _} -> lpos, s
  | { lpos; _ } -> syntax_error lpos @@ BadKeywordParam { obj; kind }

let rexpect_symbol kind obj = function
  | { lpos; lcnt = Lit (Symbol s) } -> lpos, s
  | { lpos; _ } -> syntax_error lpos @@ BadSymbolParam { obj; kind }

let rexpect_param k loc (args: unresolved_action locd list) =
  let obj = "parameter" in
  let a, args = expect_cons loc obj args in
  k obj a, args

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
  | Unknown_u name ->
     match StringMap.find_opt name types.td_all with
     | Some tau -> tau
     | None -> name_error lpos @@ Unbound { kind = "type"; prefix = "'"; name; candidates = keys types.td_all }

let assert_unique_type types { lpos; lcnt = name } kind =
  match StringMap.find_opt name types.td_all with
  | Some tau -> name_error lpos @@ DuplicateTypeName { kind; name; previous = tau }
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

let special_primitives =
  [("init", `Init)]
  |> List.to_seq |> StringMap.of_seq

let core_primitives =
  let open SGALib.SGA in
  let conv_fn f = UPrimFn (UConvFn f) in
  let struct_fn f = UPrimFn (UStructFn f) in
  [("eq", (`Fn (conv_fn UEq), 2));
   ("=", (`Fn (conv_fn UEq), 2));
   ("pack", (`Fn (conv_fn UPack), 1));
   ("unpack", (`TypeFn (fun tau -> conv_fn (UUnpack tau)), 1));
   ("ignore", (`Fn (conv_fn UIgnore), 1));
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

let all_primitive_names =
  List.concat [keys language_constructs; keys special_primitives;
               keys core_primitives; keys bits_primitives]

let all_primitives =
  StringSet.of_list all_primitive_names

let resolve_extfun_decl types { ext_name; ext_argtypes; ext_rettype } =
  let unit_u = locd_make ext_name.lpos (Bits_u 0) in
  if StringSet.mem ext_name.lcnt all_primitives then
    name_error ext_name.lpos @@ ExtfunShadowsPrimitive { ext_name = ext_name.lcnt };
  let nargs, a1, a2 = match ext_argtypes with
    | [] -> 0, unit_u, unit_u
    | [t] -> 1, t, unit_u
    | [x; y] -> 2, x, y
    | _ -> syntax_error ext_name.lpos @@ TooManyArgumentsInExtfunDecl in
  ext_name.lcnt, (nargs, { ffi_name = ext_name.lcnt;
                           ffi_arg1type = resolve_type types a1;
                           ffi_arg2type = resolve_type types a2;
                           ffi_rettype = resolve_type types ext_rettype })

let resolve_value types { lpos; lcnt } =
  let resolve_enum_constructor sg field =
    match List.assoc_opt field sg.enum_members with
    | Some bs -> Enum (sg, bs)
    | None -> let kind = sprintf "enumerator in type %a" fquote sg.enum_name in
              name_error lpos @@ Unbound { kind; prefix = "::"; name = field;
                                           candidates = List.map fst sg.enum_members } in
  match lcnt with
  | UBits bs -> Bits bs
  | UEnum { enum = ""; constructor } ->
     (match StringMap.find_opt constructor types.td_enumerators with
      | Some sg -> resolve_enum_constructor sg constructor
      | None -> name_error lpos @@ Unbound { kind = "enumerator"; prefix = "::";
                                             name = constructor; candidates = keys types.td_enumerators })
  | UEnum { enum; constructor } ->
     (match StringMap.find_opt enum types.td_all with
      | Some (Enum_t sg) -> resolve_enum_constructor sg constructor
      | Some tau -> type_error lpos @@ BadKind { name = enum; actual_type = tau; expected = "an enum" }
      | None -> name_error lpos @@ Unbound { kind = "enum"; prefix = ""; name = enum; candidates = keys types.td_enums })

let try_resolve_bits_fn { lpos; lcnt = name } args =
  let bits_fn nm = SGALib.SGA.UPrimFn (SGALib.SGA.UBitsFn nm) in
  match StringMap.find_opt name bits_primitives with
  | Some (fn, nargs) ->
     Some (match fn with
           | `Prim0 fn ->
              bits_fn fn, nargs, args
           | `Prim1 fn ->
              let (_, (_, n)), args = rexpect_param rexpect_num lpos args in
              bits_fn (fn n), nargs, args
           | `Prim2 fn ->
              let (_, (_, n)), args = rexpect_param rexpect_num lpos args in
              let (_, (_, n')), args = rexpect_param rexpect_num lpos args in
              bits_fn (fn n n'), nargs, args)
  | None -> None

let rexpect_pairs kind2 f1 f2 xs =
  Delay.map (function
      | `Pair (h1, h2) -> (f1 h1, f2 h2)
      | `Single h1 -> ignore (f1 h1); syntax_error h1.lpos @@ MissingPairElement { kind2 })
    (gather_pairs xs)

let rexpect_type loc types (args: unresolved_action locd list) =
  let (loc, t), args = rexpect_param (rexpect_symbol "a type name") loc args in
  let tau = resolve_type types (locd_make loc (Unknown_u t)) in
  loc, t, tau, args

let try_resolve_primitive types name args =
  let must_struct_t loc name = function
    | Struct_t sg -> SGALib.Util.sga_struct_sig_of_struct_sig sg
    | tau -> type_error loc @@ BadKind { name; actual_type = tau; expected = "a struct" } in
  let rexpect_field args =
    let (_, f), args = rexpect_param (rexpect_keyword "a struct field") name.lpos args in
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

let try_resolve_special_primitive types name (args: unresolved_action locd list) =
  match StringMap.find_opt name.lcnt special_primitives with
  | Some `Init ->
     let loc, nm, tau, args = rexpect_type name.lpos types args in
     let sga_tau = SGALib.Util.sga_type_of_typ tau in
     let uinit = SGALib.SGA.(UPrimFn (UConvFn (UInit sga_tau))) in
     let tt = { lpos = loc; lcnt = literal_tt } in
     let uinit_call = `Call (locd_make loc uinit, tt, tt) in
     (match tau with
      | Bits_t sz ->
         warning name.lpos @@ BadInitBits { init = nm; size = sz };
         Some uinit_call
      | Enum_t { enum_name; enum_bitsize; _ } ->
         warning name.lpos @@ BadInitEnum { init = nm; name = enum_name; bitsize = enum_bitsize };
         Some uinit_call
      | Struct_t sg ->
         let expect_field_name nm =
           locd_of_pair (rexpect_keyword "initializer parameter" "a field name" nm) in
         let expect_field_val x = x in
         Some (match rexpect_pairs "value" expect_field_name expect_field_val args with
               | [] -> uinit_call
               | fields -> `StructInit (sg, fields)))
  | _ -> None

let pad_function_call lpos name fn nargs (args: unresolved_action locd list) =
  assert (nargs <= 2);
  let given = List.length args in
  if given <> nargs then
    type_error lpos @@ BadArgumentCount { fn = name; expected = nargs; given }
  else
    let tt = { lpos; lcnt = literal_tt } in
    let a1, a2 = match args with
      | [] -> tt, tt
      | [a1] -> a1, tt
      | [a1; a2] -> a1, a2
      | _ -> assert false in
    `Call ({ lpos; lcnt = fn }, a1, a2)

let resolve_function types extfuns name (args: unresolved_action locd list) =
  match try_resolve_special_primitive types name args with
  | Some ast -> ast
  | None ->
     let (fn, nargs, args) =
       match try_resolve_primitive types name args with
       | Some r -> r
       | None -> match try_resolve_extfun extfuns name args with
                 | Some r -> r
                 | None -> let candidates = all_primitive_names in
                           name_error name.lpos @@ Unbound { kind = "function"; prefix = ""; name = name.lcnt; candidates } in
     pad_function_call name.lpos name.lcnt fn nargs args

let resolve_rule types extfuns registers ((nm, action): unresolved_rule) =
  let find_register { lpos; lcnt = name } =
    match List.find_opt (fun rsig -> rsig.reg_name = name) registers with
    | Some rsig -> { lpos; lcnt = rsig }
    | None -> name_error lpos @@ Unbound { kind = "register"; prefix = ""; name; candidates = [] } in
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
             | Lit (Num (s, _)) -> syntax_error lpos @@ MissingSize { number = s }
             | Lit (Symbol symbol) -> syntax_error lpos @@ UnexpectedSymbol { symbol }
             | Lit (Keyword keyword) -> syntax_error lpos @@ UnexpectedKeyword { keyword }
             | Lit (Enumerator { enum; constructor }) ->
                let v = UEnum { enum; constructor } in
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
             | Switch { binder; operand; default; branches } ->
                Switch { binder;
                         operand = resolve_action operand;
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
      name_error lpos @@ Unbound { kind = "rule"; prefix = ""; name; candidates = [] } in
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

let check_result = function
  | Ok cs -> cs
  | Error (epos, emsg) -> type_inference_error epos emsg

let typecheck_module { name; registers; rules; schedulers } =
  let open SGALib.Compilation in
  let tc_rule (nm, r) = (nm, (`InternalRule, check_result (typecheck_rule r))) in
  let c_rules = Delay.map tc_rule rules in
  let schedulers = Delay.map (typecheck_scheduler << snd) schedulers in
  if schedulers = [] then name_error name.lpos @@ MissingScheduler { modname = name.lcnt };
  { c_registers = registers; c_rules; c_scheduler = List.hd schedulers }

let typecheck resolved =
  Delay.map typecheck_module resolved.r_mods
