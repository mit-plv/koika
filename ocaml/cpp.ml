type register_t = {
    r_name: string;
    r_size: int;
    r_type: string;
  }

type rule_t = {
    rl_name: string;
    rl_footprint: register_t list;
    rl_body: unit;
  }

type h_file_t = {
    h_preamble: string;
    h_classname: string;
    h_rules: rule_t list;
    h_registers: register_t list
  }

let sprintf = Printf.sprintf
let fprintf = Printf.fprintf

let cpp_type_of_size sz =
  assert (sz >= 0);
  if sz = 0 then
    "prims::unit_t"
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
  (* The following two are not universally supported *)
  (* else if sz <= 128 then
   *   "std::uint128_t"
   * else if sz <= 256 then
   *   "std::uint256_t" *)
  else
    failwith (Printf.sprintf "Unsupported size: %d" sz)

let writeout out hpp =
  let nl _ = output_string out "\n" in
  let p fmt = Printf.kfprintf nl out fmt in

  let p_fn typ name ?args:(args="") ?annot:(annot="") pbody =
    p "%s %s(%s)%s {" typ name args annot;
    pbody ();
    p "}" in

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
    p "%s" hpp.h_preamble in

  let p_impl () =
    p "////////////////////";
    p "// IMPLEMENTATION //";
    p "////////////////////";

    let p_class pbody =
      p "class %s {" hpp.h_classname;
      pbody ();
      p "}" in

    let p_state_register r =
      p "%s %s;" r.r_type r.r_name in

    let p_state_t () =
      let p_printf_register r =
        p "std::cout << \"%s = \" << %s << std::endl;"
          r.r_name r.r_name in
      p "struct state_t {";
      List.iter p_state_register hpp.h_registers;
      nl ();
      p_fn "void" "dump" (fun () ->
        List.iter p_printf_register hpp.h_registers);
      p "}" in

    let p_rule rule =
      let p_reset () =
          List.iter (fun r ->
              p "log.%s.reset(Log.%s);" r.r_name r.r_name)
            rule.rl_footprint in
      let p_commit () =
          List.iter (fun r ->
              p "Log.%s = log.%s;" r.r_name r.r_name)
            rule.rl_footprint in
      let p_rule_body body =
        p "FIXME" in
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
          p "for (std::uint64_t cycle_id = 0; cycle_id < ncycles; cycle_id++) {";
          p "  cycle();";
          p "}") in

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

let main (out: out_channel) (cu: SGALib.Compilation.compile_unit) =
  writeout out {
      h_preamble = "FIXME";
      h_classname = failwith "FIXME";
      h_rules = failwith "FIXME";
      h_registers = failwith "FIXME";
    }
