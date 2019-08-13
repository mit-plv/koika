open SGALib

let writeout name ext fn input =
  Stdio.Out_channel.with_file (name ^ ext) ~f:(fun out -> fn out input)

let coq_main (sga_pkg: SGA.sga_package_t) =
  let circuit_pkg = Compilation.circuit_package_of_sga_package sga_pkg in
  let di = Util.dedup_input_of_circuit_package circuit_pkg in
  let modname = Util.string_of_coq_string sga_pkg.sga_module_name in
  let circuit = Graphs.dedup_circuit di in
  writeout modname ".v" Backends.Verilog.main circuit;
  writeout modname ".dot" Backends.Dot.main circuit;
  let cpp_input = Backends.Cpp.input_of_sga_package sga_pkg in
  let cpp out kind = Backends.Cpp.main out kind cpp_input in
  writeout modname ".hpp" cpp `Hpp;
  Common.clang_format (modname ^ ".hpp");
  writeout modname ".cpp" cpp `Cpp;
  Common.clang_format (modname ^ ".cpp")
