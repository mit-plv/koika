open Common

type 'f smod = {
    m_name: ('f, string) locd;
    m_registers: (('f, string) locd * ('f, bool list) locd) list;
    m_rules: (('f, string) locd * ('f, ('f, string, string) action) locd) list;
    m_scheduler: ('f, string) locd * ('f, 'f scheduler) locd
  }

let sprintf = Printf.sprintf

module Pos = struct
  type t =
    | StrPos of string
    | Filename of string
    | SexpPos of string * Parsexp.Positions.pos
    | SexpRange of string * Parsexp.Positions.range

  let to_string = function
    | StrPos s -> s
    | Filename f ->
       sprintf "%s:?:?" f
    | SexpPos (fname, { line; col; _ }) ->
       sprintf "%s:%d:%d" fname line col
    | SexpRange (fname, { start_pos; end_pos }) ->
       sprintf "%s:%d-%d:%d-%d" fname
         start_pos.line end_pos.line start_pos.col end_pos.col
end

exception Error of Pos.t err_contents

let parse_error (epos: Pos.t) emsg =
  raise (Error { epos; ekind = `ParseError; emsg })

let name_error (epos: Pos.t) kind name =
  raise (Error { epos; ekind = `NameError;
                 emsg = sprintf "Unbound %s: `%s'" kind name })

let type_error (epos: Pos.t) emsg =
  raise (Error { epos; ekind = `TypeError; emsg })

let untyped_number_error (pos: Pos.t) n =
  type_error pos (sprintf "Missing size annotation on number `%d'" n)

let expect_cons loc msg = function
  | [] ->
     parse_error loc (Printf.sprintf "Missing %s" msg)
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
  let locd_make lpos lcnt =
    { lpos; lcnt } in
  let locd_of_pair (pos, x) =
    locd_make pos x in
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
  let expect_constant csts c =
    let quote x = "`" ^ x ^ "'" in
    let optstrs = List.map (fun x -> quote (fst x)) csts in
    let msg = sprintf "one of %s" (String.concat ", " optstrs) in
    let loc, s = expect_atom msg c in
    match List.assoc_opt s csts with
    | None -> parse_error loc (sprintf "Expecting %s, got `%s'" msg s)
    | Some x -> loc, x in
  let bits_const_re =
    Str.regexp "^\\([0-9]+\\)'\\(b[01]*\\|h[0-9a-fA-F]*\\|[0-9]+\\)$" in
  let ident_re =
    Str.regexp "^[a-z][a-zA-Z0-9_]*$" in
  let underscore_re =
    Str.regexp "_" in
  let leading_h_re =
    Str.regexp "^h" in
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
      let bits = if size = 0 && num = Z.zero then []
                 else List.of_seq (String.to_seq (Z.format "%b" num)) in
      let nbits = List.length bits in
      if nbits > size then
        parse_error loc (sprintf "Number `%s' does not fit in %d bit(s)" numstr size)
      else
        let padding = list_const (size - nbits) false in
        let char2bool = function '0' -> false | '1' -> true | _ -> assert false in
        let bools = List.append (List.rev_map char2bool bits) padding in
        Some (Const bools)
    else match int_of_string_opt a with
         | Some n -> Some (Num n)
         | None -> None in
  let try_number loc = function
    | "true" -> Some (Const [true])
    | "false" -> Some (Const [false])
    | a -> try_number' loc a in
  let expect_number_or_var loc a =
    match try_number loc a with
    | Some c -> c
    | None ->
       match try_variable a with
       | Some var -> Var var
       | None ->
          let msg = sprintf "Cannot parse `%s' as a number or identifier %s" a num_fmt in
          parse_error loc msg in
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
               expect_number_or_var loc atom)
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
          | "write#0" | "write#1" ->
             let reg, body = expect_cons loc "register name" args in
             let port = int_of_string (String.sub hd (String.length hd - 1) 1) in
             Write (port, locd_of_pair (expect_atom "a register name" reg),
                    expect_action (expect_single loc "value" "write expression" body))
          | "read#0" | "read#1" ->
             let reg, body = expect_cons loc "register name" args in
             let port = int_of_string (String.sub hd (String.length hd - 1) 1) in
             let () = expect_nil body in
             Read (port, locd_of_pair (expect_atom "a register name" reg))
          | _ ->
             let args = List.map expect_action args in
             Call (locd_make loc_hd hd, args))
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
  let expect_register init_val =
    (* let loc, taus = expect_list "a type declaration" taus in
     * let bit, sizes = expect_cons loc "a type declaration" taus in
     * let _ = expect_constant [("bit", ())] bit in
     * let size = expect_single loc "size" "type declaration" sizes in
     * let sloc, size = expect_atom "size" size in
     * try locd_make sloc (int_of_string size)
     * with Failure _ ->
     *   parse_error loc (sprintf "Unparsable size %s" size) in *)
    let loc, init_val = expect_atom "an initial value" init_val in
    match try_number loc init_val with
    | Some (Const c) -> locd_make loc c
    | Some (Num n) -> untyped_number_error loc n
    | _ -> parse_error loc (sprintf "Expecting a number, got `%s' %s" init_val num_fmt) in
  let expect_actions loc body =
    locd_make loc (Progn (List.map expect_action body)) in
  let rec expect_scheduler : 'f sexp -> ('f, 'f scheduler) locd = function
    | (Atom _) as a ->
       locd_of_pair (expect_constant [("done", Done)] a)
    | List { loc; elements } ->
       let loc_hd, hd, args = expect_funapp loc "constructor" (elements) in
       locd_make loc
         (match hd with
          | "sequence" ->
             Sequence (List.map (fun a -> locd_of_pair (expect_atom "a rule name" a)) args)
          | "try" ->
             let rname, args = expect_cons loc "rule name" args in
             let s1, args = expect_cons loc "subscheduler 1" args in
             let s2, args = expect_cons loc "subscheduler 2" args in
             let _ = expect_nil args in
             Try (locd_of_pair (expect_atom "a rule name" rname),
                  expect_scheduler s1,
                  expect_scheduler s2)
          | _ ->
             parse_error loc_hd (sprintf "Unexpected in scheduler: `%s'" hd)) in
  let rec expect_decl d skind =
    let d_loc, d = expect_list ("a " ^ skind) d in
    let kind, name_body = expect_cons d_loc skind d in
    let csts = [("rule", `Rule); ("scheduler", `Scheduler);
                ("register", `Register); ("module", `Module)] in
    let _, kind = expect_constant csts kind in
    let name, body = expect_cons d_loc "name" name_body in
    let name = locd_of_pair (expect_atom "a name" name) in
    Printf.printf "Processing decl %s\n%!" name.lcnt;
    (d_loc,
     match kind with
     | `Register ->
        `Register (name, expect_register (expect_single d_loc "value" "register initialization" body))
     | `Module ->
        `Module (expect_module name d_loc body)
     | `Rule ->
        `Rule (name, expect_actions d_loc body)
     | `Scheduler ->
        `Scheduler (name, expect_scheduler (expect_single d_loc "body" "scheduler declaration" body)))
  and expect_module m_name m_loc body =
    let registers, rules,  schedulers =
      List.fold_left (fun (registers, rules, schedulers) decl ->
          match expect_decl decl "register, rule, or scheduler declaration" with
          | _, `Register r -> (r :: registers, rules, schedulers)
          | _, `Rule r -> (registers, r :: rules, schedulers)
          | _, `Scheduler s -> (registers, rules, s :: schedulers)
          | loc, `Module _ -> parse_error loc "Unexpected nested module declaration")
        ([], [], []) body in
    let m_scheduler = expect_single m_loc "scheduler"
                        (sprintf "module `%s'" m_name.lcnt) schedulers in
    { m_name;
      m_registers = List.rev registers;
      m_rules = List.rev rules;
      m_scheduler } in
  List.map (fun sexp ->
      match expect_decl sexp "module declaration" with
      | _, `Module { m_registers; m_rules; m_scheduler; _ } ->
         let registers = List.map (fun (nm, init) ->
                             let bs_size = List.length init.lcnt in
                             { reg_name = nm.lcnt;
                               reg_size = bs_size;
                               reg_init_val = { bs_size; bs_bits = init.lcnt } })
                           m_registers in
         (* FIXME: handle functions in generic way *)
         (registers, m_rules, m_scheduler)
      | loc, kind ->
         parse_error loc (sprintf "Unexpected %s at top level"
                            (match kind with
                             | `Register _ -> "register"
                             | `Module _ -> assert false
                             | `Rule _ -> "rule"
                             | `Scheduler _ -> "scheduler")))
    sexps

let resolve_rule fname registers rule =
  let find_register { lpos; lcnt = name } =
    match List.find_opt (fun rsig -> rsig.reg_name = name) registers with
    | Some rsig -> { lpos; lcnt = rsig }
    | None -> name_error lpos "register" name in
  let w0 = { lpos = Pos.Filename fname; lcnt = Const [] } in
  let find_function { lpos; lcnt = name } args =
    (* FIXME generalize to custom function definitions *)
    let (fn, nargs, args): SGALib.SGA.prim_ufn_t * int * _ =
      match name with
      | "sel" -> USel, 2, args
      | "and" | "&" -> UAnd, 2, args
      | "or" | "|" -> UOr, 2, args
      | "not" | "~" -> UNot, 1, args
      | "lsl" | "<<" -> ULsl, 2, args
      | "lsr" | ">>" -> ULsr, 2, args
      | "eq" | "=" -> UEq, 2, args
      | "concat" -> UConcat, 2, args
      | "uintplus" | "+" -> UUIntPlus, 2, args
      | "part" | "zextl" | "zextr" ->
         (match expect_cons lpos "argument" args with
          | { lcnt = Num n; _}, args ->
             (match name with
              | "part" -> UPart n, 2, args
              | "zextl" -> UZExtL n, 1, args
              | "zextr" -> UZExtR n, 1, args
              | _ -> assert false)
          | { lpos; _ }, _ -> parse_error lpos "Expecting a type-level constant")
      | _ -> name_error lpos "function" name in
    assert (nargs <= 2);
    if List.length args <> nargs then
      type_error lpos (sprintf "Function `%s' takes %d arguments" name nargs)
    else
      let padding = list_const (2 - nargs) w0 in
      { lpos; lcnt = SGALib.SGA.UPrimFn fn }, List.append args padding in
  let rec resolve_action ({ lpos; lcnt }: ('f, ('f, string, string) action) locd) =
    { lpos;
      lcnt = match lcnt with
             | Skip -> Skip
             | Fail sz -> Fail sz
             | Var v -> Var v
             | Num n -> untyped_number_error lpos n
             | Const bs -> Const bs
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
             | Read (port, r) ->
                Read (port, find_register r)
             | Write (port, r, v) ->
                Write (port, find_register r, resolve_action v)
             | Call (fn, args) ->
                let fn, args = find_function fn args in
                Call (fn, List.map resolve_action args) } in
  resolve_action rule

let resolve_scheduler rules (s: ('f, 'f scheduler) locd) =
  let check_rule { lpos; lcnt = name } =
    if not (List.mem_assoc name rules) then
      name_error lpos "rule" name in
  let rec check_scheduler ({ lcnt; _ }: ('f, 'f scheduler) locd) =
    match lcnt with
    | Done -> ()
    | Sequence rs ->
       List.iter check_rule rs
    | Try (r, s1, s2) ->
       check_rule r;
       check_scheduler s1;
       check_scheduler s2 in
  check_scheduler s; s

type cli_opts = {
    cli_in_fname: string;
    cli_out_fname: string;
    cli_frontend: [`Sexps | `Annotated];
    cli_backend: [`Dot | `Verilog | `Cpp | `Hpp]
  }

let check_result = function
  | Ok cs -> cs
  | Error err -> raise (Error err)

let run { cli_in_fname; cli_out_fname; cli_frontend; cli_backend } : unit =
  try
    let sexps =
      match cli_frontend with
      | `Annotated -> read_annotated_sexps cli_in_fname
      | `Sexps -> read_cst_sexps cli_in_fname in
    (match parse cli_in_fname sexps with
     | (registers, rules, scheduler) :: _ ->
        let c_rules =
          List.map (fun (nm, r) ->
              let r = resolve_rule cli_in_fname registers r in
              (nm.lcnt, check_result (SGALib.Compilation.typecheck_rule r)))
            rules in
        let c_scheduler =
          let s = resolve_scheduler c_rules (snd scheduler) in
          SGALib.Compilation.typecheck_scheduler s in
        let c_unit : SGALib.Compilation.compile_unit =
          { c_scheduler; c_rules; c_registers = registers } in
        (match cli_backend with
         | (`Hpp | `Cpp) as kd ->
            Stdio.Out_channel.with_file cli_out_fname ~f:(fun out ->
                let basename = Core.Filename.basename cli_in_fname in
                let cls, _ = Core.Filename.split_extension basename in
                Backends.Cpp.main out kd (Backends.Cpp.input_of_compile_unit cls c_unit);
                Common.clang_format cli_out_fname)
         | `Verilog | `Dot ->
            let graph =
              let circuits = SGALib.Compilation.compile c_unit in
              let di = SGALib.Util.make_dedup_input registers circuits in
              SGALib.Graphs.dedup_circuit di in
            Stdio.Out_channel.with_file cli_out_fname ~f:(fun out ->
                (match cli_backend with
                 | `Hpp | `Cpp -> assert false
                 | `Dot -> Backends.Dot.main
                 | `Verilog -> Backends.Verilog.main) out graph))
     | [] -> parse_error (Pos.Filename cli_in_fname) "No modules declared")
  with Error { epos; ekind; emsg } ->
    Printf.eprintf "%s: %s: %s\n"
      (Pos.to_string epos)
      (match ekind with
       | `ParseError -> "Parse error"
       | `NameError -> "Name error"
       | `TypeError -> "Type error")
      emsg;
    exit 1

let backend_of_fname fname =
  match Core.Filename.split_extension fname with
  | _, Some "v" -> `Verilog
  | _, Some "dot" -> `Dot
  | _, Some "hpp" -> `Hpp
  | _, _ -> failwith "Output file must have extension .v, .dot, or .hpp"

let cli =
  let open Core in
  Command.basic
    ~summary:"Compile simultaneous guarded actions to a circuit"
    Command.Let_syntax.(
    let%map_open
        cli_in_fname = anon ("input" %: string)
    and cli_out_fname = anon ("output" %: string)
    and annotated = flag "--annotated" no_arg ~doc:"Recognize '<>' annotations"
    in fun () ->
       run { cli_in_fname; cli_out_fname;
             cli_frontend = if annotated then `Annotated else `Sexps;
             cli_backend = backend_of_fname cli_out_fname })

let _ =
  (* run { cli_in_fname = "collatz.lv"; cli_out_fname = "collatz.v";
   *       cli_frontend = `Sexps; cli_backend = `Verilog } *)
  Core.Command.run cli

(* let command =
 *   let open Core in
 *   Command.basic
 *     ~summary:"Compile simultaneous guarded actions to a circuit"
 *     Command.Let_syntax.(
 *       let%map_open
 *           cli_in_fname = anon ("input" %: string)
 *       and cli_out_fname = anon ("output" %: string)
 *       in
 *       fun () ->
 *       Printf.printf "%s %s\n%!" cli_in_fname cli_out_fname)
 *
 * let () =
 *   Core.Command.run command *)
