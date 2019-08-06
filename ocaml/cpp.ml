open Common

type ('reg_t, 'fn_t) rule_t = {
    rl_name: string;
    rl_footprint: 'reg_t list;
    rl_body: (string, 'reg_t, 'fn_t) SGALib.SGA.rule;
  }

type ('prim, 'reg_t, 'fn_t) cpp_input_t = {
    h_classname: string;
    h_rules: ('reg_t, 'fn_t) rule_t list;
    h_register_names: 'reg_t list;
    h_registers: 'reg_t -> reg_signature;
    h_functions: 'fn_t -> 'prim ffi_signature
  }

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf

let cpp_type_of_size sz =
  assert (sz >= 0);
  if sz = 0 then
    "prims::unit_t"             (* FIXME *)
  else if sz = 1 then
    "std::bool"
  else if sz <= 8 then
    "std::uint8_t"
  else if sz <= 16 then
    "std::uint16_t"
  else if sz <= 32 then
    "std::uint32_t"
  else if sz <= 64 then
    "std::uint64_t"
  else
    (* The following two are not universally supported *)
    (* else if sz <= 128 then
     *   "std::uint128_t"
     * else if sz <= 256 then
     *   "std::uint256_t" *)
    failwith (Printf.sprintf "Unsupported size: %d" sz)

let cpp_const_init_fn sz =
  assert (sz >= 0);
  if sz = 0 then
    "UNIT"             (* FIXME *)
  else if sz = 1 then
    "std::bool"
  else if sz <= 8 then
    "UINT8_C"
  else if sz <= 16 then
    "UINT16_C"
  else if sz <= 32 then
    "UINT32_C"
  else if sz <= 64 then
    "UINT64_C"
  else
    failwith (Printf.sprintf "Unsupported size: %d" sz)

let h_preamble =
  "FIXME: PREAMBLE"

let gensym =
  let state = Hashtbl.create 8 in
  fun prefix ->
  let counter =
    match Hashtbl.find_opt state prefix with
    | None -> 0
    | Some n -> n in
  if counter = max_int then failwith "gensym";
  Hashtbl.replace state prefix (succ counter);
  sprintf "%s%d" prefix counter

let writeout out hpp =
  let nl _ = output_string out "\n" in
  let p fmt = Printf.kfprintf nl out fmt in
  let pr fmt = Printf.fprintf out fmt in

  let p_scoped header pbody =
    p "%s {" header;
    pbody ();
    p "}" in

  let p_fn typ name ?args:(args="") ?annot:(annot="") pbody =
    p_scoped (sprintf "%s %s(%s)%s" typ name args annot) pbody in

  let p_ifdef pbody =
    let h_define = sprintf "__%s_HPP__" hpp.h_classname in
    p "#ifndef %s" h_define;
    p "#define %s" h_define;
    nl ();
    pbody ();
    p "#endif" in

  let p_preamble () =
    p "//////////////";
    p "// PREAMBLE //";
    p "//////////////";
    nl ();
    p "%s" h_preamble in

  let p_impl () =
    p "////////////////////";
    p "// IMPLEMENTATION //";
    p "////////////////////";

    let p_class pbody =
      p_scoped (sprintf "class %s" hpp.h_classname) pbody in

    let p_state_register rn =
      let r = hpp.h_registers rn in
      p "%s %s;" (cpp_type_of_size r.reg_size) r.reg_name in

    let p_state_t () =
      let p_printf_register rn =
        let name = (hpp.h_registers rn).reg_name in
        p "std::cout << \"%s = \" << %s << std::endl;" name name in
      p_scoped "struct state_t" (fun () ->
          List.iter p_state_register hpp.h_register_names;
          nl ();
          p_fn "void" "dump" (fun () ->
              List.iter p_printf_register hpp.h_register_names)) in

    let p_expr sz var expr =
      let p_assign sz target prexpr =
        pr "%s %s = " (cpp_type_of_size sz) target;
        prexpr ();
        pr ";";
        nl () in

      let pr_const bits =
        let b = SGALib.Util.bits_const_of_bits bits in
        1 in

      let p_expr' sz var expr = function
        | SGA.Var (v, sz', _) ->
           assert (sz = sz');
           p_assign sz var (fun () -> pr "%s" v)
        | SGA.Const (sz, cst) ->
           p_assign sz var (fun () ->
               pr "%s(" (cpp_const_init_fn sz);
               pr_const cst;
               pr ")")
        | SGA.Read (port, reg) ->
           let r = hpp.h_registers reg in
           let fn_name = match port with
             | P0 -> "read0"
             | P1 -> "read1" in
           assert (sz = r.reg_size);
           p "%s %s;" (cpp_type_of_size sz) var;
           p_checked (fun () ->
               pr "log.%s.%s(&%s, Log.%s)"
                 r.reg_name fn_name var r.reg_name)
        | SGA.Call (fn, arg1, arg2) ->
           let v1 = gensym "arg1_" in
           let v2 = gensym "arg2_" in
           let f = hpp.h_functions fn in
           p_expr f.ffi_arg1size v1 arg1;
           p_expr f.ffi_arg2size v2 arg2;
           p_assign sz var (fun () ->
               pr "%s(%s, %s)" (cpp_fn_name f.ffi_name) v1 v2)
      in p_expr' sz var expr'

    let p_rule rule =
      let p_checked prbody =
        pr "CHECK_RETURN(";
        prbody ();
        pr ")" in

      let p_reset () =
        List.iter (fun { reg_name; _ } ->
            p "log.%s.reset(Log.%s);" reg_name reg_name)
          rule.rl_footprint in

      let p_commit () =
        List.iter (fun { reg_name; _ } ->
            p "Log.%s = log.%s;" reg_name reg_name)
          rule.rl_footprint in

      let rec p_rule_body = function
        | SGA.Skip _ ->
           p ""
        | SGA.Fail _ ->
           p "return;"
        | SGA.Seq (_, r1, r2) ->
           p_rule_body r1;
           p_rule_body r2
        | SGA.Bind (_, sz, v, ex, rl) ->
           (* FIXME make sure name doesn't start with our prefix *)
           p_scoped "/* bind */" (fun () ->
               p_expr sz v ex;
               p_rule_body rl)
        | SGA.If (_, e, r1, r2) ->
           p_scoped "/* if */" (fun () ->
               let c = gensym "cond" in
               p_expr 1 c e;
               p_scoped (sprintf "if (%s)" c) (fun () -> p_rule_body r1);
               p_scoped "else" (fun () -> p_rule_body r2))
        | SGA.Write (_, port, reg, expr) ->
           let e = gensym "write_expr" in
           let r = hpp.h_registers reg in
           p_expr r.reg_size e expr;
           let fn_name = match port with
             | P0 -> "write0"
             | P1 -> "write1" in
           p_checked (fun () ->
               pr "log.%s.%s(%s, Log.%s)"
                 r.reg_name fn_name e r.reg_name) in
      p_fn "void" rule.rl_name (fun () ->
          p_reset ();
          nl ();
          p_rule_body rule.rl_body;
          nl ();
          p_commit ()) in
    let p_constructor () =
      p_fn "explicit" hpp.h_classname
        ~args:"state_t init" ~annot:" : Log(), log(), state(init)"
        (fun () -> p "Log.r0.data0 = state.r0;") in

    let p_cycle () =
      p_fn "void" "cycle" (fun () ->
          List.iter (fun { rl_name; _ } -> p "%s();" rl_name) hpp.h_rules;
          p "state.r0 = Log.r0.commit();") in

    let p_run () =
      p_fn "void" "run" ~args:"std::uint64_t ncycles" (fun () ->
          p_scoped "for (std::uint64_t cycle_id = 0; cycle_id < ncycles; cycle_id++)"
            (fun () -> p "  cycle();")) in

    let p_observe () =
      p_fn "void" "observe" (fun () -> p "return state;") in

    p_class (fun () ->
        p "public:";
        p_state_t ();
        nl ();

        p "private:";
        p "log_t Log";
        p "log_t log";
        p "state_t state";
        nl ();
        List.iter p_rule hpp.h_rules;

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

let main (out: out_channel) (cu: _ cpp_input_t) =
  writeout out cu
