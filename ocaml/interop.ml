open Cuttlebone

let fname ?directory (pkg: _ Extr.koika_package_t) ext =
  let modname = Util.string_of_coq_string pkg.koika_module_name in
  let dirname = match directory with Some d -> [d] | None -> [] in
  let fname = Printf.sprintf "%s%s" modname ext in
  String.concat "/" (dirname @ [fname])

let compile_simulation ?directory (kp: _ Extr.koika_package_t) (sp: _ Extr.sim_package_t) =
  Backends.Cpp.main (fname ?directory kp "") `Exe (Backends.Cpp.input_of_sim_package kp sp)

let compile_circuits ?directory (kp: _ Extr.koika_package_t) (vp: _ Extr.verilog_package_t) =
  let circuit = Graphs.graph_of_verilog_package kp vp in
  Common.with_output_to_file (fname ?directory kp ".dot") Backends.Dot.main circuit;
  Common.with_output_to_file (fname ?directory kp ".v") (Backends.Verilog.main (Util.string_of_coq_string kp.koika_module_name)) circuit

let compile_all ?directory
      ({ ip_koika; ip_verilog; ip_sim }: Extr.interop_package_t) =
  compile_simulation ?directory ip_koika ip_sim;
  compile_circuits ?directory ip_koika ip_verilog
