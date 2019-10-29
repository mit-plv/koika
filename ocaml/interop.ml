open Core

let writeout fname fn circuit =
  Common.with_output_to_file fname (fun out -> fn out circuit)

let fname ?directory (pkg: _ Coq.sga_package_t) ext =
  let modname = Util.string_of_coq_string pkg.sga_module_name in
  let dirname = match directory with Some d -> [d] | None -> [] in
  let fname = Printf.sprintf "%s%s" modname ext in
  String.concat "/" (dirname @ [fname])

let compile_simulation ?directory (sga: _ Core.Coq.sga_package_t) (sp: _ Coq.sim_package_t) =
  Backends.Cpp.main (fname ?directory sga "") `Exe (Backends.Cpp.input_of_sim_package sga sp)

let compile_circuits ?directory (sga: _ Core.Coq.sga_package_t) (vp: _ Coq.verilog_package_t) =
  let circuit = Graphs.graph_of_verilog_package sga vp in
  writeout (fname ?directory sga ".dot") Backends.Dot.main circuit;
  writeout (fname ?directory sga ".v") Backends.Verilog.main circuit

let compile_all ?directory
      (sga: _ Core.Coq.sga_package_t)
      (sp: _ Coq.sim_package_t)
      (vp: _ Coq.verilog_package_t) =
  compile_simulation ?directory sga sp;
  compile_circuits ?directory sga vp
