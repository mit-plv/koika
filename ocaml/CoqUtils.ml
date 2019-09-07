open SGALib

let writeout name ext fn input =
  Common.with_output_to_file (name ^ ext) (fun out -> fn out input)

let coq_main (sga_pkg: SGA.sga_package_t) =
  let circuit_pkg = Compilation.circuit_package_of_sga_package sga_pkg in
  let di = Util.dedup_input_of_circuit_package circuit_pkg in
  let modname = Util.string_of_coq_string sga_pkg.sga_module_name in
  let circuit = Graphs.dedup_circuit di in
  Backends.Cpp.main modname `Exe (Backends.Cpp.input_of_sga_package sga_pkg);
  writeout modname ".dot" Backends.Dot.main circuit;
  writeout modname ".v" Backends.Verilog.main circuit;
