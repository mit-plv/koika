(*! Lispy Verilog frontend !*)
open Common

let lcnt x = x.lcnt
let sprintf = Printf.sprintf

type nonrec 'a locd = (Pos.t, 'a) locd

let pos_of_sexp_pos ({ line; col; _ }: Parsexp.Positions.pos) =
  Pos.{ line; col }

let range_of_sexp_range ({ start_pos; end_pos }: Parsexp.Positions.range) =
  Pos.{ rbeg = pos_of_sexp_pos start_pos;
        rend = pos_of_sexp_pos end_pos }

module UnresolvedAST = struct
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
    | String_u
    | Array_u of unresolved_type locd * int option
    | Unknown_u of string

  type unresolved_literal =
    | Var of var_t
    | Fail of unresolved_type
    | Num of (string * int)
    | Type of unresolved_type
    | String of string
    | Keyword of string
    | Enumerator of { enum: string; constructor: string }
    | Const of unresolved_value

  type unresolved_action =
    | Fail of typ
    | Assign of (var_t locd * unresolved_action locd)
    | If of unresolved_action locd * unresolved_action locd * unresolved_action locd list
    | Read of port_t * unresolved_reg_name locd
    | Write of port_t * unresolved_reg_name locd * unresolved_action locd
    (* Sugar on Coq side *)
    | AstError
    | Skip
    | Progn of unresolved_action locd list
    | Let of (var_t locd * unresolved_action locd) list * unresolved_action locd list
    | When of unresolved_action locd * unresolved_action locd list
    | Switch of { operand: unresolved_action locd;
                  default: unresolved_action locd;
                  branches: (unresolved_action locd * unresolved_action locd) list }
    (* Not in Coq-side AST *)
    | Lit of unresolved_literal
    | Call of { fn: string locd; args: unresolved_action locd list }
  and unresolved_reg_name = string

  type unresolved_scheduler =
    | Done
    | Cons of rule_name_t locd * unresolved_scheduler locd
    | Try of rule_name_t locd * unresolved_scheduler locd * unresolved_scheduler locd
end

module ResolvedAST = struct
  open Cuttlebone
  open Compilation

  type uaction =
    | Fail of typ
    | Var of var_t
    | Const of value
    | Assign of (var_t locd * uaction locd)
    | If of uaction locd * uaction locd * uaction locd
    | Read of port_t * reg_signature locd
    | Write of port_t * reg_signature locd * uaction locd
    | Unop of { fn: (Extr.PrimUntyped.ufn1) locd; arg: uaction locd }
    | Binop of { fn: (Extr.PrimUntyped.ufn2) locd; a1: uaction locd; a2: uaction locd }
    | ExternalCall of { fn: (ffi_signature) locd; arg: uaction locd }
    | InternalCall of { fn: uaction locd internal_function; args: uaction locd list }
    | Sugar of usugar
  and usugar =
    | AstError
    | Skip
    | ConstString of string
    | Progn of uaction locd list
    | Let of (var_t locd * uaction locd) list * uaction locd
    | When of uaction locd * uaction locd
    | Switch of { operand: uaction locd;
                  default: uaction locd;
                  branches: (uaction locd * uaction locd) list }
    | StructInit of { sg: struct_sig; fields: (string locd * uaction locd) list }
    | ArrayInit of { sg: array_sig; elements: uaction locd list }

  type uscheduler = UnresolvedAST.unresolved_scheduler

  let rec translate_action ({ lpos; lcnt }: uaction locd) : Pos.t extr_uaction =
    Extr.UAPos
      (lpos,
       match lcnt with
       | Fail tau -> UFail (Util.extr_type_of_typ tau)
       | Var v -> UVar v
       | Const v -> let tau, v = Util.extr_value_of_value v in UConst (tau, v)
       | Assign (v, expr) -> Extr.UAssign (v.lcnt, translate_action expr)
       | If (e, l, r) -> Extr.UIf (translate_action e, translate_action l, translate_action r)
       | Read (port, reg) -> Extr.URead (translate_port port, reg.lcnt)
       | Write (port, reg, v) -> Extr.UWrite (translate_port port, reg.lcnt, translate_action v)
       | Unop { fn; arg } -> UUnop (fn.lcnt, translate_action arg)
       | Binop { fn; a1; a2 } -> UBinop (fn.lcnt, translate_action a1, translate_action a2)
       | ExternalCall { fn; arg } -> UExternalCall (fn.lcnt, translate_action arg)
       | InternalCall { fn; args } ->
          UInternalCall
            (Util.extr_intfun_of_intfun translate_action fn,
             List.map translate_action args)
       | Sugar u ->
          Extr.USugar
            (match u with
             | AstError -> UErrorInAst
             | Skip -> USkip
             | ConstString str -> UConstString (Cuttlebone.Util.coq_string_of_string str)
             | Progn rs ->
                UProgn (List.map translate_action rs)
             | Let (bs, body) ->
                let bindings = List.map (fun (var, a) -> var.lcnt, translate_action a) bs in
                ULet (bindings, translate_action body)
             | When (e, body) ->
                UWhen (translate_action e, translate_action body)
             | Switch { operand; default; branches } ->
                let branches = List.map (fun (lbl, br) -> translate_action lbl, translate_action br) branches in
                USwitch (translate_action operand, translate_action default, branches)
             | StructInit { sg; fields } ->
                let fields = List.map (fun (nm, v) -> Util.coq_string_of_string nm.lcnt, translate_action v) fields in
                UStructInit (Util.extr_struct_sig_of_struct_sig sg, fields)
             | ArrayInit { sg; elements } ->
                let elements = List.map translate_action elements in
                UArrayInit (Util.extr_type_of_typ sg.array_type, elements)))

  let rec translate_scheduler ({ lpos; lcnt }: uscheduler locd) =
    Extr.SPos
      (lpos,
       match lcnt with
       | Done -> Extr.Done
       | Cons (r, s) ->
          Extr.Cons (r.lcnt, translate_scheduler s)
       | Try (r, s1, s2) ->
          Extr.Try (r.lcnt, translate_scheduler s1, translate_scheduler s2))

  let typecheck_rule (raw_ast: uaction locd) : (Pos.t extr_action, (Pos.t * _)) result =
    typecheck_rule raw_ast.lpos (translate_action raw_ast)

  type debug_printer = { debug_print: uaction -> unit }
  let debug_printer : debug_printer ref =
    ref { debug_print = (fun _ -> Printf.eprintf "No printer installed\n%!") }
end

open UnresolvedAST

type unresolved_rule = unresolved_action
type unresolved_register = unresolved_value

type unresolved_module = {
    m_name: string locd;
    m_registers: (string locd * unresolved_register locd) list;
    m_rules: (string locd * unresolved_rule locd) list;
    m_schedulers: (string locd * unresolved_scheduler locd) list;
    m_cpp_preamble: string list;
  }

type unresolved_fn_body =
  | ExternalUfn
  | InternalUfn of unresolved_action locd

type unresolved_fn =
  { ufn_name: string locd;
    ufn_signature: (string locd * unresolved_type locd) list;
    ufn_rettype: unresolved_type locd;
    ufn_body: unresolved_fn_body }

type typedecls = {
    td_enums: enum_sig StringMap.t;
    td_structs: struct_sig StringMap.t;
    td_enumerators: enum_sig StringMap.t;
    td_all: typ StringMap.t
  }

type unresolved_unit = {
    types: unresolved_typedecl locd list;
    fns: unresolved_fn list;
    mods: unresolved_module locd list;
  }

type resolved_extfun = ffi_signature

type resolved_defun =
  ResolvedAST.uaction locd internal_function

type resolved_fn =
  | FnExternal of ffi_signature
  | FnInternal of resolved_defun
  | FnUnop of Cuttlebone.Extr.PrimUntyped.ufn1
  | FnBinop of Cuttlebone.Extr.PrimUntyped.ufn2
  | FnStructInit of { sg: struct_sig; field_names: string locd list }
  | FnArrayInit of { sg: array_sig }
  | FnStringInit of string

type resolved_fndecl =
  | ExternalDecl of resolved_extfun
  | InternalDecl of resolved_defun

type resolved_module = {
    name: string locd;
    registers: reg_signature list;
    rules: (string * ResolvedAST.uaction locd) list;
    schedulers: (string * ResolvedAST.uscheduler locd) list;
    cpp_preamble: string list
  }

type fndecls = {
    fn_ordered: (string * resolved_fndecl) list;
    fn_all: resolved_fndecl StringMap.t
  }

type resolved_unit = {
    r_types: typedecls;
    r_fns: fndecls;
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

type 'f sexp =
  | Atom of { loc: 'f; atom: string }
  | List of { loc: 'f; elements: 'f sexp list }

let sexp_pos = function
  | Atom { loc; _ } | List { loc; _ } -> loc

module Errors = struct
  module ParseErrors = struct
    type t =
      | BadPosAnnot
      | SexpError of { msg: string }
      | BadBitsSize of { size: string }
      | Overflow of { numstr: string; bits: string; size: int }

    let to_string = function
      | BadPosAnnot ->
         "Bad use of <>"
      | SexpError { msg } ->
         String.capitalize_ascii msg
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
      | ExpectingNil of { kind: string; prev: string }
      | UnexpectedList of { expected: string }
      | UnexpectedAtom of { expected: string; atom: string }
      | UnexpectedType of { typ: typ }
      | UnexpectedString of { str: string }
      | UnexpectedKeyword of { keyword: string }
      | BadChoice of { atom: string; expected: string list }
      | BadLiteral of { atom: string }
      | BadBitsLiteral of { atom: string }
      | ReservedIdentifier of { kind: string; atom: string }
      | BadIdentifier of { kind: string; atom: string }
      | BadConst of { atom: string }
      | BadKeyword of { kind: string; atom: string }
      | BadEnumerator of { atom: string }
      | BadType of { atom: string }
      | BadSizeInType of { atom: string }
      | BadIntParam of { obj: string; kind: string option }
      | BadKeywordParam of { obj: string; kind: string }
      | BadStringParam of { obj: string }
      | BadTypeParam of { obj: string; kind: string }
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
      | ExpectingNil { kind; prev } ->
         sprintf "Unexpected %s after %s" kind prev
      | UnexpectedList { expected } ->
         sprintf "Expecting %s, but got a list" expected
      | UnexpectedAtom { expected; atom } ->
         sprintf "Expecting a list (%s), got %a" expected fquote atom
      | UnexpectedType { typ } ->
         sprintf "Unexpected type %s" (typ_name typ)
      | UnexpectedString { str } ->
         sprintf "Unexpected string %a" fquote str
      | UnexpectedKeyword { keyword } ->
         sprintf "Unexpected keyword %a" fquote keyword
      | BadChoice { atom; expected } ->
         sprintf "Expecting %s, got %a" (one_of_str expected) fquote atom
      | BadLiteral { atom } ->
         sprintf "Expecting a literal (a number, variable, symbol or keyword), got %a" fquote atom
      | BadBitsLiteral { atom } ->
         sprintf "Expecting a sized literal (e.g. 2'b01 or 8'42), got %a" fquote atom
      | BadIdentifier { kind; atom } ->
         sprintf "Expecting an identifier (%s), got %a" kind fquote atom
      | ReservedIdentifier { kind; atom } ->
         sprintf "%a is a reserved; it cannot be used as %s" fquote atom kind
      | BadConst { atom } ->
         sprintf "Expecting a sized literal (e.g. 8'hff) or an enumerator (eg proto::ipv4), got %a" fquote atom
      | BadKeyword { kind; atom } ->
         sprintf "Expecting a keyword (%s, starting with a colon), got %a" kind fquote atom
      | BadEnumerator { atom } ->
         sprintf "Expecting an enumerator (format: abc::xyz or ::xyz), got %a" fquote atom
      | BadType { atom } ->
         sprintf "Expecting a type name (e.g. (bits 16) or 'xyz) got %a" fquote atom
      | BadSizeInType { atom } ->
         sprintf "Expecting a size (e.g. 32), got %a" fquote atom
      | BadIntParam { obj; kind } ->
         sprintf "This %s should be an integer%s" obj
           (match kind with Some k -> sprintf " (%s)" k | None -> "")
      | BadKeywordParam { obj; kind } ->
         sprintf "This %s should be a keyword (%s, starting with a colon)" obj kind
      | BadStringParam { obj } ->
         sprintf "This %s should be a string" obj
      | BadTypeParam { obj; kind } ->
         sprintf "This %s should be a type (%s, such as bool, (array 5 (bits 8)), or a type name starting with a quote)" obj kind
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
         "External fns must take a single argument (use a struct to pass multiple arguments)"
  end

  module NameErrors = struct
    type t =
      | Unbound of { kind: string; prefix: string; name: string; candidates: string list }
      | Duplicate of { kind: string; name: string }
      | DuplicateTypeName of { name: string; kind: string; previous: typ }
      | FnShadowsPrimitive of { ext_name: string }
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
      | FnShadowsPrimitive { ext_name } ->
         sprintf "Function name %a conflicts with existing primitive" fquote ext_name
      | MissingScheduler { modname } ->
         sprintf "Missing scheduler in module %a" fquote modname
      | MissingModule ->
         "No modules declared"
  end

  module TypeErrors = struct
    type t =
      | BadArgumentCount of { fn: string; expected: int; given: int }
      | InconsistentEnumeratorSizes of { expected: int; actual: int }
      | BadKind of { expected: string; actual_type: typ }
      | ArrayLengthMismatch of { expected: int; actual: int }
      | MissingArraySize
      | MissingStringSize

    let to_string = function
      | BadArgumentCount { fn; expected; given } ->
         sprintf "Function %s takes %d arguments (%d given)" fn expected given
      | InconsistentEnumeratorSizes { expected; actual } ->
         sprintf "Inconsistent sizes in enum: expecting %a, got %a"
           fquote (sprintf "bits %d" expected) fquote (sprintf "bits %d" actual)
      | BadKind { expected: string; actual_type } ->
         sprintf "Got type %s but expected %s" (typ_name actual_type) expected
      | ArrayLengthMismatch { expected; actual } ->
         sprintf "This array has %d element(s) instead of the expected %d" actual expected
      | MissingArraySize ->
         sprintf "Missing size in array type"
      | MissingStringSize ->
         sprintf "Missing size in string type; use (array char ...) instead"
  end

  module TypeInferenceErrors = struct
    type t = string Cuttlebone.Util.extr_error_message

    let classify (msg: t) =
      match msg with
      | ExplicitErrorInAst -> `TypeError
      | SugaredConstructorInAst -> `SyntaxError
      | UnboundVariable _ -> `NameError
      | OutOfBounds _ -> `TypeError
      | UnboundField _ -> `NameError
      | UnboundEnumMember _ -> `NameError
      | TooManyArguments _ -> `SyntaxError
      | TooFewArguments _ -> `SyntaxError
      | TypeMismatch _ -> `TypeError
      | KindMismatch _ -> `TypeError

    let to_string (msg: t) =
      match msg with
      | ExplicitErrorInAst ->
         "Untypeable term (likely due to an ill-typed subterm)"
      | SugaredConstructorInAst ->
         "Improper desugaring (this is a bug; please report it)"
      | UnboundVariable { var } ->
         sprintf "Unbound variable %a" fquote var
      | OutOfBounds { pos; sg } ->
         sprintf "Index %d is not in range [0 .. %d)" pos sg.array_len
      | UnboundField { field; sg } ->
         sprintf "Unbound field %a in %s" fquote field (struct_sig_to_string sg)
      | UnboundEnumMember { name; sg } ->
         sprintf "Enumerator %a is not a member of %s" fquote name (enum_sig_to_string sg)
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
           fquote actual fquote expected
  end

  module Warnings = struct
    type t = NoWarning
    let to_string _ = ""
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
(* open Warnings *)

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
module BitsDuplicates = Dups(struct type t = bool array let compare = poly_cmp end)

let expect_cons loc kind = function
  | [] -> syntax_error loc @@ MissingElement { kind }
  | hd :: tl -> hd, tl

let expect_single loc kind where = function
  | [] -> syntax_error loc (MissingElementIn { kind; where })
  | _ :: _ :: _ -> syntax_error loc (TooManyElementsIn { kind; where })
  | [x] -> x

let rec gather_pairs = function
  | [] -> []
  | [x1] -> [`Single x1]
  | x1 :: x2 :: tl -> `Pair (x1, x2) :: gather_pairs tl

let rec list_const n x =
  if n = 0 then [] else x :: list_const (n - 1) x

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
        parse_error (Pos.Range (fname, range_of_sexp_range range)) @@ SexpError { msg } in
    let rec read_sexps pos =
      P.State.reset ~pos state;
      try Delay.apply1 feed pos.offset; []
      with GotSexp (sexp, last_pos) -> sexp :: read_sexps last_pos in
    read_sexps (P.State.position state)
end

module DelayedReader_plain = DelayedReader (Parsexp.Eager)
module DelayedReader_cst = DelayedReader (Parsexp.Eager_cst)

let read_sexps fname =
  let open Parsexp in
  let wrap_loc loc =
    Pos.Range (fname, range_of_sexp_range loc) in
  let rec translate_ast (s: Cst.t_or_comment) =
    match s with
    | Comment _ -> None
    | Sexp (Atom { loc; atom; _ }) ->
       Some (Atom { loc = wrap_loc loc; atom })
    | Sexp (List { loc; elements }) ->
       Some (List { loc = wrap_loc loc;
                    elements = Base.List.filter_map ~f:translate_ast elements }) in
  let commit_annotation annot (sexp: Pos.t sexp) =
    match annot with
    | None -> sexp
    | Some loc ->
       match sexp with
       | Atom { atom; _ } -> Atom { loc; atom }
       | List { elements; _ } -> List { loc; elements } in
  let rec commit_annotations ?(annot: Pos.t option) (sexp: Pos.t sexp) =
    commit_annotation annot
      (match sexp with
       | Atom _ -> sexp
       | List { elements = [Atom { atom = "<>"; _ }; Atom { atom = annot; _ }; body]; _ } ->
          commit_annotations ~annot:(Pos.StrPos annot) body
       | List { elements = (Atom { atom = "<>"; _ } :: _); loc } ->
          parse_error loc @@ BadPosAnnot
       | List { loc; elements } ->
          List { loc; elements = List.map (commit_annotations ?annot) elements })
  in
  DelayedReader_cst.parse_string fname (read_all fname)
  |> Base.List.filter_map ~f:translate_ast
  |> Base.List.map ~f:commit_annotations

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
let forbidden_vars = StringSet.of_list ["true"; "false"]

let try_variable var =
  if not (Str.string_match ident_re var 0) then
    `InvalidIdentifier
  else if StringSet.mem var forbidden_vars then
    `ReservedIdentifier
  else `ValidIdentifier (mangle var)

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
   ("write.0" , `Write P0);
   ("write.1", `Write P1);
   ("read.0" , `Read P0);
   ("read.1", `Read P1);
   ("switch", `Switch)]
  |> StringMap.of_list

let type_names =
  [("unit", Bits_u 0);
   ("bool", Bits_u 1);
   ("char", Bits_u 8);
   ("string", String_u)]
  |> StringMap.of_list

let type_constructors =
  [("bits", `Bits); ("array", `Array)]

let parse (sexps: Pos.t sexp list) =
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
  let expect_nil prev = function
    | [] -> ()
    | List { loc; _ } :: _ -> syntax_error loc @@ ExpectingNil { prev; kind = "list" }
    | Atom { loc; _ } :: _ -> syntax_error loc @@ ExpectingNil { prev; kind = "atom" } in
  let expect_pair loc kind1 kind2 lst =
    let x1, lst = expect_cons loc kind1 lst in
    let x2, lst = expect_cons loc kind2 lst in
    expect_nil (sprintf "%s and %s" kind1 kind2) lst;
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
  let expect_identifier kind v =
    let loc, atom = expect_atom kind v in
    match try_variable atom with
    | `ValidIdentifier v -> locd_make loc v
    | `ReservedIdentifier -> syntax_error loc @@ ReservedIdentifier { kind; atom }
    | `InvalidIdentifier -> syntax_error loc @@ BadIdentifier { kind; atom } in
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
  let rec expect_type ?(bits_raw=false) = function (* (bit 16), (array 3 (bit 15)), 'typename *)
    | Atom { loc; atom } ->
       locd_make loc
         (match StringMap.find_opt atom type_names with
          | Some tau -> tau
          | None ->
             match try_symbol atom with
             | Some s -> Unknown_u s
             | None ->
                match try_plain_int atom with
                | Some n when bits_raw -> Bits_u n
                | _ -> syntax_error loc @@ BadType { atom })
    | List { loc; elements } ->
       let expect_size_arg loc args =
         let sz, args = expect_cons loc "size" args in
         let loc, szstr = expect_atom "a size" sz in
         match try_plain_int szstr with
         | Some size -> size, args
         | _ -> syntax_error loc @@ BadSizeInType { atom = szstr } in
       let hd, args = expect_cons loc "type" elements in
       let loc, kind = expect_constant_atom type_constructors hd in
       locd_make loc
         (match kind with
          | `Bits -> let sz, args = expect_size_arg loc args in
                     expect_nil "argument" args;
                     Bits_u sz
          | `Array -> let tau, args = expect_cons loc "element type" args in
                      let tau = expect_type ~bits_raw:false tau in
                      if args = [] then Array_u (tau, None)
                      else let sz, args = expect_size_arg loc args in
                           expect_nil "argument" args;
                           Array_u (tau, Some sz)) in
  let try_type ?(bits_raw=false) sexp =
    try Some (expect_type ~bits_raw sexp)
    with Errors _ -> None in
  let expect_literal loc a =
    match try_enumerator a with
    | Some { enum; constructor } -> Enumerator { enum; constructor }
    | None ->
       match try_keyword a with
       | Some name -> Keyword name
       | None ->
          match try_number loc a with
          | Some (`Num n) -> Num (a, n)
          | Some (`Const bs) -> Const (UBits bs)
          | None ->
             match try_variable a with
             | `ValidIdentifier var -> Var var
             | `InvalidIdentifier -> String a (* FIXME use a parser that distinguishes strings and atoms *)
             | `ReservedIdentifier ->
                syntax_error loc @@ ReservedIdentifier { atom = a; kind = "a string or variable name" } in
  let expect_funapp loc kind elements =
    let hd, args = expect_cons loc kind elements in
    let loc_hd, hd = expect_atom (sprintf "a %s name" kind) hd in
    loc_hd, hd, args in
  let rec expect_action_nodelay action =
    match action with
    | Atom { loc; atom } ->
       locd_make loc
         (match atom with       (* FIXME disallow these var names *)
          | "skip" -> Skip
          | "fail" -> Fail (Bits_t 0)
          | atom -> match try_type action with
                    | Some tau -> Lit (Type tau.lcnt)
                    | None -> Lit (expect_literal loc atom))
    | List { loc; elements } ->
       let loc_hd, hd, args = expect_funapp loc "constructor or function" (elements) in
       locd_make loc
         (match StringMap.find_opt hd language_constructs with
          | Some fn ->
             (match fn with
              | `Fail ->
                 (match args with
                  | [] -> Fail (Bits_t 0)
                  | [arg] -> Lit (Fail (expect_type ~bits_raw:true arg).lcnt)
                  | _ -> type_error loc @@ BadArgumentCount { fn = "fail"; expected = 1; given = List.length args })
              | `Setq ->
                 let var, body = expect_cons loc "variable name" args in
                 let value = expect_action (expect_single loc "value" "assignment" body) in
                 Assign (expect_identifier "a variable name" var, value)
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
                 Write (port, expect_identifier "a register name" reg,
                        expect_action (expect_single loc "value" "call to write" body))
              | `Read port ->
                 let reg = expect_single loc "register name" "call to write" args in
                 Read (port, expect_identifier "a register name" reg)
              | `Switch ->
                 let inspected, branches = expect_cons loc "switch operand" args in
                 let branches = List.map expect_switch_branch branches in
                 let inspected = expect_action inspected in
                 let binder = gensym "switch_operand" in
                 let operand = locd_make inspected.lpos (Lit (Var binder)) in
                 let switch = match build_switch_body branches with
                   | (Some default, branches) ->
                      Switch { operand; default; branches }
                   | None, [] -> syntax_error loc @@ EmptySwitch
                   | None, branches ->
                      let default = { lpos = loc; lcnt = AstError } in
                      let default = syntax_error ~default loc MissingDefaultInSwitch in
                      Switch { operand; default; branches } in
                 Let ([(locd_make operand.lpos binder, inspected)],
                      [locd_make loc switch]))
          | None ->
             if List.mem_assoc hd type_constructors then
               Lit (Type (expect_type action).lcnt)
             else
               let args = List.map expect_action args in
               Call { fn = locd_make loc_hd hd; args })
  and expect_action s =
    Delay.apply1_default { lpos = sexp_pos s; lcnt = AstError } expect_action_nodelay s
  and expect_switch_branch branch =
    let loc, lst = expect_list "switch case" branch in
    let lbl, body = expect_cons loc "case label" lst in
    let lbl = match lbl with
      | Atom { loc; atom = "_" } -> `AnyLabel loc
      | _ -> let loc, cst = expect_const "a case label" lbl in
             `SomeLabel (locd_make loc (Lit (Const cst))) in
    (lbl, locd_make loc (Progn (List.map expect_action body)))
  and build_switch_body branches =
    Delay.fold_right (fun (lbl, (branch: unresolved_action locd)) (default, branches) ->
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
    let var = expect_identifier "a variable name" var in
    let value = expect_single loc "value" "let binding" values in
    let value = expect_action value in
    (var, value)
  and expect_let_bindings bs =
    let _, bs = expect_list "let bindings" bs in
    Delay.map expect_let_binding bs in
  let expect_decl_name loc body =
    let name, body = expect_cons loc "name" body in
    (expect_identifier "a name" name, body) in
  let expect_register d_loc body =
    let name, body = expect_decl_name d_loc body in
    let init_val = expect_single d_loc "value" "register initialization" body in
    (name, locd_of_pair (expect_const "an initial value" init_val)) in
  let expect_actions (loc: Pos.t) body =
    locd_make loc (Progn (List.map expect_action body)) in
  let rec expect_scheduler_body : Pos.t sexp -> unresolved_scheduler locd = function
    | Atom { loc; atom } ->
       locd_make loc (expect_constant loc [("done", Done)] atom)
    | List { loc; elements } -> (* FIXME put these in special list *)
       let loc_hd, hd, args = expect_funapp loc "constructor" (elements) in
       let hd = expect_constant loc_hd [("sequence", `Sequence); ("try", `Try)] hd in
       locd_make loc
         (match hd with
          | `Sequence ->
             let rules = Delay.map (expect_identifier "a rule name") args in
             List.fold_right (fun rl s -> Cons (rl, locd_make loc s)) rules Done
          | `Try ->
             let rname, args = expect_cons loc "rule name" args in
             let s1, s2 = expect_pair loc "subscheduler 1" "subscheduler 2" args in
             Try (expect_identifier "a rule name" rname,
                  expect_scheduler_body s1,
                  expect_scheduler_body s2)) in
  let expect_scheduler loc body =
    let name, body = expect_decl_name loc body in
    name, expect_scheduler_body (expect_single loc "body" "scheduler declaration" body) in
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
  let expect_enum loc body = (* ((:true 1'b1) (:false 1'b0) …) *)
    let name, body = expect_decl_name loc body in
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
  let expect_struct loc body = (* ((:kind kind) (:imm (bits 12) …) *)
    let name, body = expect_decl_name loc body in
    let fields = expect_pairs "field type" expect_struct_field_name expect_type body in
    Delay.apply4 StringDuplicates.check "field in struct" fst (lcnt << fst) fields;
    locd_make loc (Struct_u { name; fields }) in
  let expect_argspec s =
    let loc, s = expect_list "argument specification" s in
    let nm, tau = expect_pair loc "argument name" "argument type" s in
    (expect_identifier "argument name" nm ,
     expect_type ~bits_raw:false tau) in
  let expect_fn_decl needs_body loc body =
    let ufn_name, body = expect_decl_name loc body in
    let args, body = expect_cons loc "function signature" body in
    let rettype, body = expect_cons loc "return type" body in
    let _, args = expect_list "function signature" args in
    let ufn_signature = Delay.map expect_argspec args in
    let ufn_rettype = expect_type rettype in
    let ufn_body =
      if needs_body then InternalUfn (expect_actions loc body)
      else (expect_nil "argument list" body; ExternalUfn) in
    { ufn_name; ufn_signature; ufn_rettype; ufn_body } in
  let expect_rule loc body =
    let name, body = expect_decl_name loc body in
    (name, expect_actions loc body) in
  let expect_cpp_preamble loc body =
    snd @@ expect_atom "preamble declaration"
             (expect_single loc "string" "preamble declaration" body) in
  let rec expect_decl d skind expected =
    let d_loc, d = expect_list ("a " ^ skind) d in
    let kind, decl_body = expect_cons d_loc skind d in
    let _, kind = expect_constant_atom expected kind in
    (d_loc,
     match kind with
     | `Enum ->
        `Enum (expect_enum d_loc decl_body)
     | `Struct ->
        `Struct (expect_struct d_loc decl_body)
     | `Defun ->
        `Fn (expect_fn_decl true d_loc decl_body)
     | `Extfun ->
        `Fn (expect_fn_decl false d_loc decl_body)
     | `Module ->
        `Module (expect_module d_loc decl_body)
     | `Register ->
        `Register (expect_register d_loc decl_body)
     | `Rule ->
        `Rule (expect_rule d_loc decl_body)
     | `Scheduler ->
        `Scheduler (expect_scheduler d_loc decl_body)
     | `CppPreamble ->
        `CppPreamble (expect_cpp_preamble d_loc decl_body))
  and expect_module loc body =
    let m_name, body = expect_decl_name loc body in
    let expected = [("register", `Register); ("rule", `Rule);
                    ("scheduler", `Scheduler); ("cpp-preamble", `CppPreamble)] in
    let { m_name; m_registers; m_rules; m_schedulers; m_cpp_preamble } =
      Delay.fold_left (fun m decl ->
          match expect_decl decl "register, rule, or scheduler declaration" expected |> snd with
          | `Register r -> { m with m_registers = r :: m.m_registers }
          | `Rule r -> { m with m_rules = r :: m.m_rules }
          | `Scheduler s -> { m with m_schedulers = s :: m.m_schedulers }
          | `CppPreamble s -> { m with m_cpp_preamble = s :: m.m_cpp_preamble }
          | _ -> assert false)
        { m_name; m_registers = []; m_rules = []; m_schedulers = [];
          m_cpp_preamble = [] } body in
    let m_registers, m_rules, m_schedulers, m_cpp_preamble =
      List.rev m_registers, List.rev m_rules, List.rev m_schedulers, List.rev m_cpp_preamble in
    Delay.apply4 StringDuplicates.check "register" fst (lcnt << fst) m_registers;
    Delay.apply4 StringDuplicates.check "rule" fst (lcnt << fst) m_rules;
    Delay.apply4 StringDuplicates.check "scheduler" fst (lcnt << fst) m_schedulers;
    locd_make loc { m_name; m_registers; m_rules; m_schedulers; m_cpp_preamble } in
  let expected_toplevel =
    [("enum", `Enum); ("struct", `Struct);
     ("defun", `Defun); ("extfun", `Extfun);
     ("module", `Module)] in
  let { types; fns; mods } =
    Delay.fold_left (fun u sexp ->
        match expect_decl sexp "module, type, or extfun declaration" expected_toplevel |> snd with
        | `Enum e -> { u with types = e :: u.types }
        | `Struct s -> { u with types = s :: u.types }
        | `Fn fn -> { u with fns = fn :: u.fns }
        | `Module m -> { u with mods = m :: u.mods }
        | _ -> assert false)
      { types = []; fns = []; mods = [] } sexps in
  let types, fns, mods = List.rev types, List.rev fns, List.rev mods in
  Delay.apply4 StringDuplicates.check
    "module" (fun m -> m.lcnt.m_name) (fun m -> m.lcnt.m_name.lcnt) mods;
  Delay.apply4 StringDuplicates.check
    "external function" (fun fn -> fn.ufn_name) (fun fn -> fn.ufn_name.lcnt) fns;
  { types; fns; mods }

let rexpect_num ?kind obj =
  function
  | { lpos; lcnt = Lit (Num n); _} -> lpos, n
  | { lpos; _ } -> syntax_error lpos @@ BadIntParam { obj; kind }

let rexpect_keyword kind obj = function
  | { lpos; lcnt = Lit (Keyword s); _} -> lpos, s
  | { lpos; _ } -> syntax_error lpos @@ BadKeywordParam { obj; kind }

let rexpect_string obj = function
  | { lpos; lcnt = Lit (Var s | String s); _} -> lpos, s
  | { lpos; _ } -> syntax_error lpos @@ BadStringParam { obj }

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
  | Bits_t _ | Array_t _ -> types
  | Enum_t sg ->
     { types with td_all = StringMap.add sg.enum_name tau_r types.td_all;
                  td_enums = StringMap.add sg.enum_name sg types.td_enums;
                  td_enumerators = List.fold_left (fun acc (field, _) ->
                                       StringMap.add field sg acc)
                                     types.td_enumerators sg.enum_members }
  | Struct_t sg ->
     { types with td_all = StringMap.add sg.struct_name tau_r types.td_all;
                  td_structs = StringMap.add sg.struct_name sg types.td_structs }


let rec resolve_type types { lpos; lcnt: unresolved_type } =
  match lcnt with
  | Bits_u sz -> Bits_t sz
  | String_u ->
     type_error lpos @@ MissingStringSize
  | Array_u (tau, Some len) ->
     Array_t { array_len = len;
               array_type = resolve_type types tau }
  | Array_u (_, None) ->
     type_error lpos @@ MissingArraySize
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
  |> StringMap.of_list

let core_primitives =
  let open Cuttlebone.Extr.PrimUntyped in
  let unop fn = FnUnop fn in
  let binop fn = FnBinop fn in
  let display_opts display_newline : Cuttlebone.Extr.display_options =
    { display_strings = true; display_style = DFull; display_newline } in
  [("eq", `Fn (binop (UEq false)));
   ("=", `Fn (binop (UEq false)));
   ("neq", `Fn (binop (UEq true)));
   ("!=", `Fn (binop (UEq true)));
   ("pack", `Fn (unop (UConv UPack)));
   ("unpack", `TypeFn (fun tau -> unop (UConv (UUnpack tau))));
   ("ignore", `Fn (unop (UConv UIgnore)));
   ("get", `FieldFn (fun f -> unop (UStruct1 (UGetField f))));
   ("update", `FieldFn (fun f -> binop (UStruct2 (USubstField f))));
   ("get-bits", `StructFn (fun sg f -> unop (UStruct1 (UGetFieldBits (sg, f)))));
   ("update-bits", `StructFn (fun sg f -> binop (UStruct2 (USubstFieldBits (sg, f)))));
   ("aref", `ElementFn (fun pos -> unop (UArray1 (UGetElement pos))));
   ("asubst", `ElementFn (fun pos -> binop (UArray2 (USubstElement pos))));
   ("aref-bits", `ArrayFn (fun sg pos -> unop (UArray1 (UGetElementBits (sg, pos)))));
   ("asubst-bits", `ArrayFn (fun sg pos -> binop (UArray2 (USubstElementBits (sg, pos)))));
   ("disp", `Fn (unop (UDisplay (UDisplayValue (display_opts false)))));
   ("displn", `Fn (unop (UDisplay (UDisplayValue (display_opts true)))));
   ("print", `Fn (unop (UDisplay UDisplayUtf8)))]
  |> StringMap.of_list

let bits_primitives =
  let open Cuttlebone.Extr.PrimUntyped in
  let unop fn = FnUnop (UBits1 fn) in
  let binop fn = FnBinop (UBits2 fn) in
  [("sel", `Prim0 (binop USel));
   ("and", `Prim0 (binop UAnd));
   ("&", `Prim0 (binop UAnd));
   ("or", `Prim0 (binop UOr));
   ("|", `Prim0 (binop UOr));
   ("xor", `Prim0 (binop UXor));
   ("^", `Prim0 (binop UXor));
   ("not", `Prim0 (unop UNot));
   ("~", `Prim0 (unop UNot));
   ("lsl", `Prim0 (binop ULsl));
   ("<<", `Prim0 (binop ULsl));
   ("lsr", `Prim0 (binop ULsr));
   (">>", `Prim0 (binop ULsr));
   ("asr", `Prim0 (binop UAsr));
   (">>>", `Prim0 (binop UAsr));
   ("concat", `Prim0 (binop UConcat));
   ("+", `Prim0 (binop UPlus));
   ("-", `Prim0 (binop UMinus));
   ("*", `Prim0 (binop UMul));
   ("<", `Prim0 (binop (UCompare (false, CLt))));
   (">", `Prim0 (binop (UCompare (false, CGt))));
   ("<=", `Prim0 (binop (UCompare (false, CLe))));
   (">=", `Prim0 (binop (UCompare (false, CGe))));
   ("<s", `Prim0 (binop (UCompare (true, CLt))));
   (">s", `Prim0 (binop (UCompare (true, CGt))));
   ("<s=", `Prim0 (binop (UCompare (true, CLe))));
   (">s=", `Prim0 (binop (UCompare (true, CGe))));
   ("sext", `Prim1 (fun n -> unop (USExt n)));
   ("zextl", `Prim1 (fun n -> unop (UZExtL n)));
   ("zextr", `Prim1 (fun n -> unop (UZExtR n)));
   ("repeat", `Prim1 (fun n -> unop (URepeat n)));
   ("indexed-slice", `Prim1 (fun n -> binop (UIndexedSlice n)));
   ("slice", `Prim2 (fun n n' -> unop (USlice (n, n'))));
   ("slice-subst", `Prim2 (fun n n' -> unop (USlice (n, n'))))]
  |> StringMap.of_list

let all_primitive_names =
  List.concat [keys language_constructs; keys special_primitives;
               keys core_primitives; keys bits_primitives]

let all_primitives =
  StringSet.of_list all_primitive_names

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
      | Some tau -> type_error lpos @@ BadKind { actual_type = tau; expected = "an enum" }
      | None -> name_error lpos @@ Unbound { kind = "enum"; prefix = ""; name = enum; candidates = keys types.td_enums })

let try_resolve_bits_fn { lpos; lcnt = name } args =
  match StringMap.find_opt name bits_primitives with
  | Some fn ->
     Some (match fn with
           | `Prim0 fn ->
              (fn, args)
           | `Prim1 fn ->
              let (_, (_, n)), args = rexpect_param rexpect_num lpos args in
              (fn n, args)
           | `Prim2 fn ->
              let (_, (_, n)), args = rexpect_param rexpect_num lpos args in
              let (_, (_, n')), args = rexpect_param rexpect_num lpos args in
              (fn n n', args))
  | None -> None

let rexpect_pairs kind2 f1 f2 xs =
  Delay.map (function
      | `Pair (h1, h2) -> (f1 h1, f2 h2)
      | `Single h1 -> ignore (f1 h1); syntax_error h1.lpos @@ MissingPairElement { kind2 })
    (gather_pairs xs)

let rexpect_unresolved_type kind obj = function
  | { lpos; lcnt = Lit (Type tau) } -> lpos, tau
  | { lpos; _ } -> syntax_error lpos @@ BadTypeParam { obj; kind }

let rexpect_unresolved_type_param loc (args: unresolved_action locd list) =
  rexpect_param (rexpect_unresolved_type "a type") loc args

let rexpect_type_param loc types (args: unresolved_action locd list) =
  let (loc, tau), args = rexpect_unresolved_type_param loc args in
  let tau = resolve_type types (locd_make loc tau) in
  loc, tau, args

let must_struct_t loc = function
  | Struct_t sg -> Cuttlebone.Util.extr_struct_sig_of_struct_sig sg
  | tau -> type_error loc @@ BadKind { actual_type = tau; expected = "a struct" }

let must_array_t loc = function
  | Array_t sg -> Cuttlebone.Util.extr_array_sig_of_array_sig sg
  | tau -> type_error loc @@ BadKind { actual_type = tau; expected = "an array" }

let try_resolve_primitive types name args =
  let rexpect_field args =
    let (_, f), args = rexpect_param (rexpect_keyword "a struct field") name.lpos args in
    Cuttlebone.Util.coq_string_of_string f, args in
  let rexpect_pos args =
    let (_, (_, pos)), args = rexpect_param (rexpect_num ~kind:"an array index") name.lpos args in
    pos, args in
  match StringMap.find_opt name.lcnt core_primitives with
  | Some fn ->
     Some (match fn with
           | `Fn fn ->
              (fn, args)
           | `TypeFn fn ->
              let _, t, args = rexpect_type_param name.lpos types args in
              (fn (Cuttlebone.Util.extr_type_of_typ t), args)
           | `FieldFn fn ->
              let f, args = rexpect_field args in
              (fn f, args)
           | `StructFn fn ->
              let loc, t, args = rexpect_type_param name.lpos types args in
              let f, args = rexpect_field args in
              (fn (must_struct_t loc t) f, args)
           | `ElementFn fn ->
              let f, args = rexpect_pos args in
              (fn f, args)
           | `ArrayFn fn ->
              let loc, t, args = rexpect_type_param name.lpos types args in
              let f, args = rexpect_pos args in
              (fn (must_array_t loc t) f, args))
  | None -> try_resolve_bits_fn name args

let add_array_size sz = function
  | Array_u (tau, None) -> Array_u (tau, Some sz)
  | (String_u | Array_u (_, Some _) | Bits_u _ | Unknown_u _) as tau -> tau

let try_resolve_special_primitive types name (args: unresolved_action locd list) =
  match StringMap.find_opt name.lcnt special_primitives with
  | None -> None
  | Some `Init ->
     let (loc, utau), args = rexpect_unresolved_type_param name.lpos args in
     if utau = String_u then
       let lit = expect_single name.lpos "string" "init" args in
       let _, str = rexpect_string "parameter" lit in
       Some (FnStringInit str, [])
     else
       let args_len = List.length args in
       let utau = add_array_size args_len utau in
       let tau = resolve_type types (locd_make loc utau) in
       match tau with
       | Struct_t sg ->
          let expect_field_name nm =
            locd_of_pair (rexpect_keyword "initializer parameter" "a field name" nm) in
          let expect_field_val x = x in
          let fields = rexpect_pairs "value" expect_field_name expect_field_val args in
          let field_names, actions = List.split fields in
          Some (FnStructInit { sg; field_names }, actions)
       | Array_t sg ->
          if args_len <> sg.array_len then
            type_error loc @@ ArrayLengthMismatch { expected = sg.array_len; actual = args_len };
          Some (FnArrayInit { sg }, args)
       | Bits_t _ | Enum_t _ ->
          type_error loc @@ BadKind { actual_type = tau;
                                      expected = "a struct or an array" }

let resolve_function types fns name (args: unresolved_action locd list)
  : resolved_fn * unresolved_action locd list =
  match try_resolve_special_primitive types name args with
  | Some resolved -> resolved
  | None ->
     match try_resolve_primitive types name args with
     | Some (fn, args) -> (fn, args)
     | None ->
        match StringMap.find_opt name.lcnt fns with
        | Some (InternalDecl fn) -> (FnInternal fn, args)
        | Some (ExternalDecl ext) -> (FnExternal ext, args)
        | None -> let candidates = all_primitive_names in
                  name_error name.lpos @@
                    Unbound { kind = "function"; prefix = "";
                              name = name.lcnt; candidates }

let rec assemble_assoc_binop_chain loc (fn: Cuttlebone.Extr.PrimUntyped.ufn2 locd) a1 args =
  match args with
  | [] -> a1.lcnt
  | [a2] -> ResolvedAST.Binop { fn; a1; a2 }
  | a2 :: args -> ResolvedAST.Binop { fn; a1; a2 = locd_make loc (assemble_assoc_binop_chain loc fn a2 args) }

let assemble_binop_chain name (fn: Cuttlebone.Extr.PrimUntyped.ufn2) args =
  let bad_arg_count nexpected given =
    type_error name.lpos @@ BadArgumentCount { fn = name.lcnt; expected = nexpected; given } in
  let assoc_ops =
    let open Cuttlebone.Extr.PrimUntyped in
    [UBits2 UPlus; UBits2 UAnd; UBits2 UOr] in
  let fn_locd = locd_make name.lpos fn in
  match args with (* FIXME: expected arg counts should be more flexible *)
  | a :: args when List.mem fn assoc_ops ->
     assemble_assoc_binop_chain name.lpos fn_locd a args
  | a1 :: a2 :: _ -> ResolvedAST.Binop { fn = fn_locd; a1; a2 }
  | _ -> bad_arg_count 2 0

let assemble_resolved_funcall name (fn: resolved_fn) (args: ResolvedAST.uaction locd list) =
  let given = List.length args in
  let bad_arg_count nexpected =
    type_error name.lpos @@ BadArgumentCount { fn = name.lcnt; expected = nexpected; given } in
  let addloc fn = { lpos = name.lpos; lcnt = fn } in
  match fn with
  | FnExternal fn ->
     let arg = match args with
       | [] -> addloc (ResolvedAST.Const (Bits [||]))
       | [arg] -> arg
       | _ -> bad_arg_count 1 in
     ResolvedAST.ExternalCall { fn = addloc fn; arg }
  | FnInternal fn ->
     InternalCall { fn; args }
  | FnUnop fn ->
     (match args with
      | [arg] -> Unop { fn = addloc fn; arg }
      | _ -> bad_arg_count 1)
  | FnBinop fn ->
     assemble_binop_chain name fn args
  | FnStructInit { sg; field_names } ->
     Sugar (StructInit { sg; fields = List.combine field_names args })
  | FnArrayInit { sg } ->
     Sugar (ArrayInit { sg; elements = args })
  | FnStringInit str ->
     Sugar (ConstString str)

let resolve_register_reference registers { lpos; lcnt = name } =
  match List.find_opt (fun rsig -> rsig.reg_name = name) registers with
  | Some rsig -> { lpos; lcnt = rsig }
  | None -> name_error lpos @@ Unbound { kind = "register"; prefix = ""; name; candidates = [] }

let rec resolve_struct_fields types fns registers fields =
  List.map (fun (nm, v) -> nm, resolve_action types fns registers v) fields
and resolve_action_nodelay types fns registers ({ lpos; lcnt }: unresolved_action locd)
  : ResolvedAST.uaction locd =
  let resolve_action = resolve_action types fns registers in
  let resolve_actions_nodelay = resolve_actions_nodelay types fns registers lpos in
  { lpos;
    lcnt = match lcnt with
           | Fail sz -> Fail sz
           | Lit (Fail tau) -> Fail (resolve_type types (locd_make lpos tau))
           | Lit (Var v) -> ResolvedAST.Var v
           | Lit (Num (s, _)) -> syntax_error lpos @@ MissingSize { number = s }
           | Lit (Type typ) ->
              let typ = resolve_type types (locd_make lpos typ) in
              syntax_error lpos @@ UnexpectedType { typ }
           | Lit (String str) -> syntax_error lpos @@ UnexpectedString { str }
           | Lit (Keyword keyword) -> syntax_error lpos @@ UnexpectedKeyword { keyword }
           | Lit (Enumerator { enum; constructor }) ->
              let v = UEnum { enum; constructor } in
              ResolvedAST.Const (resolve_value types (locd_make lpos v))
           | Lit (Const v) -> ResolvedAST.Const (resolve_value types (locd_make lpos v))
           | Assign (v, a) -> Assign (v, resolve_action a)
           | If (c, l, rs) ->
              If (resolve_action c,
                  resolve_action l,
                  resolve_actions_nodelay rs)
           | Read (port, r) ->
              Read (port, resolve_register_reference registers r)
           | Write (port, r, v) ->
              Write (port, resolve_register_reference registers r, resolve_action v)
           (* Sugar *)
           | Progn rs -> Sugar (Progn (List.map resolve_action rs))
           | Let (bs, body) ->
              Sugar (Let (List.map (fun (var, expr) -> (var, resolve_action expr)) bs,
                           resolve_actions_nodelay body))
           | AstError -> Sugar AstError
           | Skip -> Sugar Skip
           | When (c, rs) ->
              Sugar (When (resolve_action c, resolve_actions_nodelay rs))
           | Switch { operand; default; branches } ->
              Sugar (Switch { operand = resolve_action operand;
                              default = resolve_action default;
                              branches = List.map (fun (lbl, br) ->
                                             resolve_action lbl, resolve_action br)
                                           branches })
           | Call { fn; args } ->
              let resolved_fn, args = resolve_function types fns fn args in
              assemble_resolved_funcall fn resolved_fn (List.map resolve_action args) }
and resolve_actions_nodelay (types: typedecls) fns registers lpos actions =
  match List.map (resolve_action types fns registers) actions with
  | [] -> locd_make lpos (ResolvedAST.Sugar Skip)
  | [a] -> a
  | actions -> locd_make lpos (ResolvedAST.Sugar (Progn actions))
and resolve_action types fns registers l
    : ResolvedAST.uaction locd =
  Delay.apply4_default { l with lcnt = ResolvedAST.Sugar AstError }
    resolve_action_nodelay types fns registers l

let resolve_rule types fns registers ((nm, action): _ * unresolved_rule locd) =
  (nm.lcnt, resolve_action types fns registers action)

let resolve_fn_decl types fns { ufn_name; ufn_signature; ufn_rettype; ufn_body }
    : string * resolved_fndecl =
  if StringSet.mem ufn_name.lcnt all_primitives then
    name_error ufn_name.lpos @@ FnShadowsPrimitive { ext_name = ufn_name.lcnt };
  let args = Delay.map (fun (nm, tau) -> nm.lcnt, resolve_type types tau) ufn_signature in
  let rettype = resolve_type types ufn_rettype in
  (ufn_name.lcnt,
   match ufn_body with
   | InternalUfn body ->
      let body = resolve_action types fns [] body in
      InternalDecl { int_name = ufn_name.lcnt;
                     int_retSig = rettype;
                     int_argspec = args;
                     int_body = body }
   | ExternalUfn ->
      let unit_t = Bits_t 0 in
      let ffi_argtype = match List.map snd args with
        | [] -> unit_t
        | [t] -> t
        | _ -> syntax_error ufn_name.lpos @@ TooManyArgumentsInExtfunDecl in
      ExternalDecl { ffi_name = ufn_name.lcnt;
                     ffi_argtype;
                     ffi_rettype = rettype })

let resolve_register types (name, init) =
  { reg_name = name.lcnt;
    reg_init = resolve_value types init }

let resolve_scheduler rules ((nm, s): string locd * unresolved_scheduler locd) =
  let check_rule { lpos; lcnt = name } =
    if not (List.mem_assoc name rules) then
      name_error lpos @@ Unbound { kind = "rule"; prefix = ""; name; candidates = [] } in
  let rec check_scheduler ({ lcnt; _ }: ResolvedAST.uscheduler locd) =
    match lcnt with
    | Done -> ()
    | Cons (r, s) ->
       Delay.apply1 check_rule r;
       Delay.apply1 check_scheduler s
    | Try (r, s1, s2) ->
       Delay.apply1 check_rule r;
       Delay.apply1 check_scheduler s1;
       Delay.apply1 check_scheduler s2 in
  check_scheduler s; (nm.lcnt, s)

let resolve_module types (fns: resolved_fndecl StringMap.t)
      { lpos; lcnt = { m_name; m_registers; m_rules; m_schedulers; m_cpp_preamble } } =
  let registers = Delay.map (resolve_register types) m_registers in
  let rules = Delay.map (resolve_rule types fns registers) m_rules in
  let schedulers = Delay.map (resolve_scheduler rules) m_schedulers in
  { name = { m_name with lpos }; registers; rules; schedulers;
    cpp_preamble = m_cpp_preamble }

let resolve_fndecls types fns =
  Delay.fold_left (fun (fns: fndecls) ufn ->
      let nm, fn = resolve_fn_decl types fns.fn_all ufn in
      { fn_ordered = (nm, fn) :: fns.fn_ordered;
        fn_all = StringMap.add nm fn fns.fn_all })
    { fn_all = StringMap.empty; fn_ordered = [] } fns

let resolve { types; fns; mods } =
  let r_types = resolve_typedecls types in
  let r_fns = resolve_fndecls r_types fns in
  let r_mods = Delay.map (resolve_module r_types r_fns.fn_all) mods in
  { r_types; r_fns; r_mods }

let check_result = function
  | Ok cs -> cs
  | Error (epos, emsg) -> type_inference_error epos emsg

let typecheck_module { name; cpp_preamble; registers; rules; schedulers }
  : Pos.t Cuttlebone.Compilation.compile_unit =
  let tc_rule (nm, r) = (nm, (`InternalRule, check_result (ResolvedAST.typecheck_rule r))) in
  let c_rules = Delay.map tc_rule rules in
  let schedulers = Delay.map (ResolvedAST.translate_scheduler << snd) schedulers in
  if schedulers = [] then name_error name.lpos @@ MissingScheduler { modname = name.lcnt };
  { c_modname = name.lcnt;
    c_registers = registers;
    c_rules;
    c_scheduler = List.hd schedulers;
    c_cpp_preamble = (match cpp_preamble with
                      | [] -> None
                      | strs -> Some (String.concat "\n" strs));
    c_pos_of_pos = (fun pos -> pos) }

let typecheck resolved =
  Delay.map typecheck_module resolved.r_mods

let first_compile_unit in_path mods =
  match mods with
  | [] -> name_error (Pos.Filename in_path) @@ MissingModule
  | md :: _ -> md

let load src_fpath =
  let resolved, typechecked =
    Delay.with_delayed_errors (fun () ->
        let resolved =  resolve (parse (read_sexps src_fpath)) in
        resolved, typecheck resolved) in
  resolved, first_compile_unit src_fpath typechecked

let describe_language () =
  let open List in
  let atom x = Base.Sexp.Atom x in
  let list xs = Base.Sexp.List xs in
  let atomlist xs = list (map atom xs) in
  let pair k v = list [atom k; atomlist (sort poly_cmp v)] in
  list [pair "language-constructs" (keys language_constructs);
        pair "type-names" (keys type_names);
        pair "core-primitives" (keys special_primitives @ keys core_primitives);
        pair "bits-primitives" (keys bits_primitives);
        pair "reserved-identifiers" (StringSet.elements forbidden_vars)]
