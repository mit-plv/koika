open Common
module SGA = SGALib.SGA

type ('reg_t, 'fn_t) cpp_rule_t = {
    rl_name: string;
    rl_footprint: reg_signature list;
    rl_body: (string, 'reg_t, 'fn_t) SGA.rule;
  }

type ('prim, 'reg_t, 'fn_t) cpp_input_t = {
    cpp_classname: string;
    cpp_scheduler: string SGA.scheduler;
    cpp_rules: ('reg_t, 'fn_t) cpp_rule_t list;
    cpp_register_names: 'reg_t list;
    cpp_registers: 'reg_t -> reg_signature;
    cpp_functions: 'fn_t -> 'prim ffi_signature
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
    sprintf "UINT8_C(%s)" cst
  else if sz <= 16 then
    sprintf "UINT16_C(%s)" cst
  else if sz <= 32 then
    sprintf "UINT32_C(%s)" cst
  else if sz <= 64 then
    sprintf "UINT64_C(%s)" cst
  else
    failwith (sprintf "Unsupported size: %d" sz)

let cpp_fn_name = function
  | { ffi_name = CustomFn _; _ } ->
     failwith "FIXME: Custom functions not supported"
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

let writeout out (hpp: _ cpp_input_t) =
  let nl _ = output_string out "\n" in
  let p fmt = Printf.kfprintf nl out fmt in
  let pr fmt = Printf.fprintf out fmt in

  let p_scoped header ?terminator:(terminator="") pbody =
    p "%s {" header;
    pbody ();
    p "}%s" terminator in

  let p_fn typ name ?args:(args="") ?annot:(annot="") pbody =
    p_scoped (sprintf "%s %s(%s)%s" typ name args annot) pbody in

  let p_ifdef pbody =
    let cpp_define = sprintf "%s_HPP" hpp.cpp_classname in
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
      p_scoped (sprintf "class %s" hpp.cpp_classname) ~terminator:";" pbody in

    let iter_registers =
      let sigs = List.map hpp.cpp_registers hpp.cpp_register_names in
      fun f -> List.iter f sigs in

    let p_state_register r =
      p "%s %s;" (cpp_type_of_size r.reg_size) r.reg_name in

    let p_state_t () =
      let p_printf_register { reg_name; _ } =
        p "std::cout << \"%s = \" << %s << std::endl;" reg_name reg_name in
      p_scoped "struct state_t" ~terminator:";" (fun () ->
          iter_registers p_state_register;
          nl ();
          p_fn "void" "dump" ~annot:" const" (fun () ->
              iter_registers p_printf_register)) in

    let p_log_register r =
      p "reg_log_t<%d> %s;" r.reg_size r.reg_name in

    let p_log_t () =
      p_scoped "struct log_t" ~terminator:";" (fun () ->
          iter_registers p_log_register) in

    let p_checked prbody =
      pr "CHECK_RETURN(";
      prbody ();
      p ");" in

    let p_rule (rule: _ cpp_rule_t) =
      gensym_reset ();

      let p_reset () =
        List.iter (fun { reg_name; _ } ->
            p "log.%s.reset(Log.%s);" reg_name reg_name)
          rule.rl_footprint in

      let p_commit () =
        List.iter (fun { reg_name; _ } ->
            p "Log.%s = log.%s;" reg_name reg_name;
            p "return true;")
          rule.rl_footprint in

      let p_assign target exprval =
        match target with
        | None -> ()
        | Some target ->
           pr "%s = %s;" target exprval;
           nl () in

      let sp_const sz bits =
        let bs = SGALib.Util.bits_const_of_bits sz bits in
        let s = SGALib.Util.string_of_bits ~mode:`Cpp bs in
        cpp_const_init sz s in

      let p_decl sz name =
        p "%s %s;" (cpp_type_of_size sz) name in

      let p_gensym sz prefix =
        let v = gensym prefix in
        p_decl sz v;
        v in

      let ensure_target sz = function
        | Some t -> t
        | None -> p_gensym sz "ignored" in

      let rec p_action (target: var_t option) = function
        | SGA.Fail (_, _) ->
           p "return false;";
        | SGA.Var (_, v, _, _) ->
           p_assign target v
        | SGA.Const (_, sz, cst) ->
           p_assign target (sp_const sz cst)
        | SGA.Seq (_, _, a1, a2) ->
           p_action None a1;
           p_action target a2
        | SGA.Bind (_, sz, _, v, ex, rl) ->
           p_scoped "/* bind */" (fun () ->
               p_decl sz v;
               p_action (Some v) ex;
               p_action target rl)
        | SGA.If (_, _, cond, tbr, fbr) ->
           let cvar = p_gensym 1 "c" in
           p_action (Some cvar) cond;
           p_scoped (sprintf "if (%s)" cvar) (fun () -> p_action target tbr);
           p_scoped "else" (fun () -> p_action target fbr)
        | SGA.Read (_, port, reg) ->
           let { reg_name; reg_size; _ } = hpp.cpp_registers reg in
           let var = ensure_target reg_size target in
           p_checked (fun () ->
               match port with
               | P0 -> pr "log.%s.read0(&%s, state.%s, Log.%s.rwset)" reg_name var reg_name reg_name
               | P1 -> pr "log.%s.read1(&%s, Log.%s.rwset)" reg_name var reg_name)
        | SGA.Write (_, port, reg, expr) ->
           let r = hpp.cpp_registers reg in
           let valvar = p_gensym r.reg_size "v" in
           p_action (Some valvar) expr;
           let fn_name = match port with
             | P0 -> "write0"
             | P1 -> "write1" in
           p_checked (fun () ->
               pr "log.%s.%s(%s, Log.%s.rwset)"
                 r.reg_name fn_name valvar r.reg_name);
           p_assign target "prims::tt"
        | SGA.Call (_, fn, arg1, arg2) ->
           let f = hpp.cpp_functions fn in
           let a1 = p_gensym f.ffi_arg1size "x" in
           let a2 = p_gensym f.ffi_arg2size "y" in
           p_action (Some a1) arg1;
           p_action (Some a2) arg2;
           p_assign target (sprintf "%s(%s, %s)" (cpp_fn_name f) a1 a2) in

      p_fn "bool" rule.rl_name (fun () ->
          p_reset ();
          nl ();
          p_action None rule.rl_body;
          nl ();
          p_commit ());
      nl () in

    let p_constructor () =
      let p_init_data0 { reg_name = nm; _ } =
        p "Log.%s.data0 = state.%s;" nm nm in
      p_fn "explicit" hpp.cpp_classname
        ~args:"state_t init" ~annot:" : Log(), log(), state(init)"
        (fun () -> iter_registers p_init_data0) in

    let rec p_scheduler = function
      | SGA.Done -> ()
      | SGA.Cons (rl_name, s) ->
         p "rule_%s();" rl_name;
         p_scheduler s
      | SGA.Try (rl_name, s1, s2) ->
         p_scoped (sprintf "if (rule_%s())" rl_name) (fun () -> p_scheduler s1);
         p_scoped "else" (fun () -> p_scheduler s2) in

    let p_cycle () =
      let p_commit_register r =
        p "state.%s = Log.%s.commit();" r.reg_name r.reg_name in
      p_fn "void" "cycle" (fun () ->
          p_scheduler hpp.cpp_scheduler;
          iter_registers p_commit_register) in

    let p_run () =
      p_fn "void" "run" ~args:"std::uint64_t ncycles" (fun () ->
          p_scoped "for (std::uint64_t cycle_id = 0; cycle_id < ncycles; cycle_id++)"
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
        nl ();
        List.iter p_rule hpp.cpp_rules;

        p "public:";
        p_constructor ();
        nl ();
        p_cycle ();
        nl ();
        p_run ();
        nl ();
        p_observe ();
        nl ()) in
  p_ifdef (fun () ->
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

let input_of_compile_unit classname ({ c_registers; c_scheduler; c_rules }: SGALib.Compilation.compile_unit) =
  let tr_rule (name, rl_body) =
    { rl_name = "rule_" ^ name ;
      rl_body; rl_footprint = action_footprint rl_body } in
  { cpp_classname = classname;
    cpp_rules = List.map tr_rule c_rules;
    cpp_scheduler = c_scheduler;
    cpp_register_names = c_registers;
    cpp_registers = (fun r -> r);
    cpp_functions = (fun fn ->
      match fn with
      | SGA.PrimFn fn -> SGALib.Util.ffi_signature_of_interop_fn
                           (PrimFn fn) (SGA.prim_Sigma fn)
      | SGA.CustomFn _ -> failwith "FIXME: Custom functions not supported") }

let main (out: out_channel) (cu: _ cpp_input_t) =
  writeout out cu
