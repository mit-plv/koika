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

    cpp_function_sigs: 'fn_t -> 'prim ffi_signature;
  }

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf

let cpp_type_of_size sz =
  assert (sz >= 0);
  if sz <= 64 then
    sprintf "uint_t<%d>::t" sz
  else
    failwith (sprintf "Unsupported size: %d" sz)

let cpp_const_init sz cst =
  assert (sz >= 0);
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
  else
    failwith (sprintf "Unsupported size: %d" sz)

let cpp_fn_name = function
  | { ffi_name = CustomFn f; _ } ->
     (* The current implementation of external functions requires the client to
        pass a class implementing those functions as a template argument.  An
        other approach would have made custom functions virtual methods, but
        then they couldn't have taken template arguments. *)
     (* The ‘.template’ part ensures that ‘extfuns.xyz<p>()’ is not parsed as a
        comparison. *)
     sprintf "extfuns.template %s" f
  | { ffi_name = PrimFn f; ffi_arg1size = sz1; ffi_arg2size = sz2; _ } ->
     sprintf "prims::%s"
       (match f with
        | SGA.Sel _logsz -> sprintf "sel<%d, %d>" sz1 sz2
        | SGA.Part (_logsz, _width) -> failwith "FIXME: part"
        | SGA.And _sz -> sprintf "land<%d>" sz1
        | SGA.Or _sz -> sprintf "lor<%d>" sz1
        | SGA.Not _sz -> sprintf "lnot<%d>" sz1
        | SGA.Lsl (_sz, _places) -> sprintf "lsl<%d, %d>" sz1 sz2
        | SGA.Lsr (_sz, _places) -> sprintf "lsr<%d, %d>" sz1 sz2
        | SGA.Eq _sz -> sprintf "eq<%d>" sz1
        | SGA.Concat (_sz1, _sz2) -> sprintf "concat<%d, %d>" sz1 sz2
        | SGA.ZExtL (_sz, _nzeroes) -> failwith "FIXME: zextl"
        | SGA.ZExtR (_sz, _nzeroes) -> failwith "FIXME: zextr"
        | SGA.UIntPlus _sz -> sprintf "plus<%d>" sz1)

let cpp_preamble =
  let inc = open_in "preamble.hpp" in
  let preamble = really_input_string inc (in_channel_length inc) in
  close_in inc;
  preamble

let gensym, gensym_reset =
  let state = Hashtbl.create 8 in
  let reset () =
    Hashtbl.clear state in
  let next prefix =
    let counter =
      match Hashtbl.find_opt state prefix with
      | None -> 0
      | Some n -> n in
    if counter = max_int then failwith "gensym";
    Hashtbl.replace state prefix (succ counter);
    sprintf "_%s%d" prefix counter in
  (next, reset)

type assignment_target =
  | NoTarget
  | VarTarget of { sz: size_t; declared: bool; name: var_t }

type assignment_result =
  | NotAssigned
  | Assigned of var_t
  | PureExpr of string

let writeout (type name_t var_t reg_t) out (hpp: (_, name_t, var_t, reg_t, _) cpp_input_t) =
  let nl _ = output_string out "\n" in
  let p fmt = Printf.kfprintf nl out fmt in
  let pr fmt = Printf.fprintf out fmt in

  let p_scoped header ?(terminator="") pbody =
    p "%s {" header;
    let r = pbody () in
    p "}%s" terminator;
    r in

  let p_fn typ name ?(args="") ?(annot="") pbody =
    p_scoped (sprintf "%s %s(%s)%s" typ name args annot) pbody in

  let p_includeguard pbody =
    let cpp_define = sprintf "SIM_%s_HPP" (String.capitalize_ascii hpp.cpp_classname) in
    p "#ifndef %s" cpp_define;
    p "#define %s" cpp_define;
    nl ();
    pbody ();
    p "#endif" in

  let p_preamble () =
    p "//////////////";
    p "// PREAMBLE //";
    p "//////////////";
    nl ();
    p "%s" cpp_preamble in

  let p_impl () =
    p "////////////////////";
    p "// IMPLEMENTATION //";
    p "////////////////////";
    nl ();

    let p_class pbody =
      p_scoped (sprintf "template <typename extfuns_t> class %s" hpp.cpp_classname)
        ~terminator:";" pbody in

    let iter_registers f regs =
      List.iter (fun r -> f (hpp.cpp_register_sigs r)) regs in

    let iter_all_registers =
      let sigs = List.map hpp.cpp_register_sigs hpp.cpp_registers in
      fun f -> List.iter f sigs in

    let p_state_register r =
      p "%s %s;" (cpp_type_of_size r.reg_size) r.reg_name in

    let p_state_t () =
      let p_printf_register { reg_name; _ } =
        p "std::cout << \"%s = \" << %s << std::endl;" reg_name reg_name in
      p_scoped "struct state_t" ~terminator:";" (fun () ->
          iter_all_registers p_state_register;
          nl ();
          p_fn "void" "dump" ~annot:" const" (fun () ->
              iter_all_registers p_printf_register)) in

    let p_log_register r =
      p "reg_log_t<%d> %s;" r.reg_size r.reg_name in

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

      let sp_const sz bits =
        let bs = SGALib.Util.bits_const_of_bits sz bits in
        let s = SGALib.Util.string_of_bits ~mode:`Cpp bs in
        cpp_const_init sz s in

      let p_decl sz name =
        p "%s %s;" (cpp_type_of_size sz) name in

      let p_declare_target = function
        | VarTarget { sz; declared = false; name } ->
           p_decl sz name;
           VarTarget { sz; declared = true; name }
        | t -> t in

      let gensym_target sz prefix =
        VarTarget { sz; declared = false; name = gensym prefix } in

      let p_ensure_target sz t =
        let declared, var =
          match t with
          | NoTarget -> false, gensym "ignored"
          | VarTarget { declared; name; _ } -> declared, name in
        if not declared then
          p_decl sz var;
        var in

      let p_assign_pure target result =
        (match target, result with
         | VarTarget { declared = true; name; _ }, PureExpr e ->
            p "%s = %s;" name e;
            Assigned name
         | VarTarget { sz; name; _ }, PureExpr e ->
            p "%s %s = %s;" (cpp_type_of_size sz) name e;
            Assigned name
         | _, _ ->
            result) in

      let must_expr = function
        | PureExpr e -> e
        | Assigned v -> v
        | NotAssigned -> assert false in

      let rec p_action (target: assignment_target) (rl: (var_t, reg_t, _) SGA.action) =
        match rl with
        | SGA.Fail (_, _) ->
           p "return false;";
           (match target with
            | NoTarget -> NotAssigned
            | VarTarget { declared = true; name; _ } -> Assigned name
            | VarTarget { sz; _ } -> PureExpr (sprintf "prims::unreachable<%d>()" sz))
        | SGA.Var (_, v, _, _m) ->
           PureExpr (hpp.cpp_var_names v) (* FIXME fail if reference isn't to latest binding of v *)
        | SGA.Const (_, sz, cst) ->
           PureExpr (sp_const sz cst)
        | SGA.Seq (_, _, a1, a2) ->
           ignore (p_action NoTarget a1);
           p_action target a2
        | SGA.Bind (_, sz, _, v, ex, rl) ->
           let target = p_declare_target target in
           p_scoped "/* bind */" (fun () ->
               let vtarget = VarTarget { sz; declared = false; name = hpp.cpp_var_names v } in
               ignore (p_assign_pure vtarget (p_action vtarget ex));
               p_assign_pure target (p_action target rl))
        | SGA.If (_, _, cond, tbr, fbr) ->
           let ctarget = gensym_target 1 "c" in
           let cexpr = p_action ctarget cond in
           let target = p_declare_target target in
           ignore (p_scoped (sprintf "if (bool(%s))" (must_expr cexpr))
                     (fun () -> p_assign_pure target (p_action target tbr)));
           p_scoped "else"
             (fun () -> p_assign_pure target (p_action target fbr))
        | SGA.Read (_, port, reg) ->
           let { reg_name; reg_size; _ } = hpp.cpp_register_sigs reg in
           let var = p_ensure_target reg_size target in
           p_checked (fun () ->
               match port with
               | P0 -> pr "log.%s.read0(&%s, state.%s, Log.%s.rwset)" reg_name var reg_name reg_name
               | P1 -> pr "log.%s.read1(&%s, Log.%s.rwset)" reg_name var reg_name);
           Assigned var
        | SGA.Write (_, port, reg, expr) ->
           let r = hpp.cpp_register_sigs reg in
           let reg = hpp.cpp_register_sigs reg in
           let vt = gensym_target reg.reg_size "v" in
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
           let a1 = must_expr (p_action (gensym_target f.ffi_arg1size "x") arg1) in
           let a2 = must_expr (p_action (gensym_target f.ffi_arg2size "y") arg2) in
           PureExpr (sprintf "%s(%s, %s)" (cpp_fn_name f) a1 a2) in

      p_fn "bool" ("rule_" ^ hpp.cpp_rule_names rule.rl_name) (fun () ->
          p_reset ();
          nl ();
          ignore (p_action NoTarget rule.rl_body);
          nl ();
          p_commit ());
      nl () in

    let p_constructor () =
      let p_init_data0 { reg_name = nm; _ } =
        p "Log.%s.data0 = state.%s;" nm nm in
      p_fn "explicit" hpp.cpp_classname
        ~args:"state_t init" ~annot:" : state(init)"
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
      p_fn "void" "cycle" (fun () ->
          p_scheduler hpp.cpp_scheduler;
          iter_all_registers p_commit_register) in

    let p_run () =
      p_fn "template<typename T> void" "run" ~args:"T ncycles" (fun () ->
          p_scoped "for (T cycle_id = 0; cycle_id < ncycles; cycle_id++)"
            (fun () -> p "cycle();")) in

    let p_observe () =
      p_fn "state_t" "observe" (fun () -> p "return state;") in

    p_class (fun () ->
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
        List.iter p_rule hpp.cpp_rules;
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
  p_includeguard (fun () ->
      p_preamble ();
      nl ();
      p_impl ();
      nl ())

let action_footprint a =
  let m = Hashtbl.create 25 in

  let rec action_footprint = function
    | SGA.Fail _ -> ()
    | SGA.Var _ | SGA.Const _ -> ()
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
    cpp_function_sigs = SGALib.Util.ffi_signature_of_interop_fn;
    cpp_var_names = fun x -> x }

let collect_rules sched =
  let rec loop acc = function
  | SGA.Done -> List.rev acc
  | SGA.Cons (rl, s) -> loop (rl :: acc) s
  | SGA.Try (rl, l, r) -> loop (loop (rl :: acc) l) r
  in loop [] sched

let cpp_rule_of_sga_package_rule (s: SGALib.SGA.sga_package_t) (rn: Obj.t) =
  cpp_rule_of_action (rn, s.sga_rules rn)

let input_of_sga_package (s: SGALib.SGA.sga_package_t)
    : (SGA.prim_fn_t, Obj.t, Obj.t, Obj.t, 'custom_t SGA.interop_fn_t) cpp_input_t =
  let rules = collect_rules s.sga_scheduler in
  { cpp_classname = SGALib.Util.string_of_coq_string s.sga_module_name;
    cpp_rule_names = (fun rn -> SGALib.Util.string_of_coq_string (s.sga_rule_names rn));
    cpp_rules = List.map (cpp_rule_of_sga_package_rule s) rules;
    cpp_scheduler = s.sga_scheduler;
    cpp_registers = s.sga_reg_finite.finite_elems;
    cpp_register_sigs = SGALib.Util.reg_sigs_of_sga_package s;
    cpp_function_sigs = SGALib.Util.fn_sigs_of_sga_package s;
    cpp_var_names = fun x -> SGALib.Util.string_of_coq_string (s.sga_var_names x) }

let main (out: out_channel) (cu: _ cpp_input_t) =
  writeout out cu
