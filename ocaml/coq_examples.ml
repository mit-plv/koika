open SGALib

let fname (pkg: _ SGA.sga_package_t) ext =
  let modname = Util.string_of_coq_string pkg.sga_module_name in
  Printf.sprintf "examples/coq/%s%s" modname ext

let do_sim (sp: _ SGA.sim_package_t) =
  let sga = sp.sp_pkg in
  Backends.Cpp.main (fname sga "") `Exe (Backends.Cpp.input_of_sim_package (Obj.magic sp))

let writeout fname fn circuit =
  Common.with_output_to_file fname (fun out -> fn out circuit)

let do_verilog (vp: _ SGA.verilog_package_t) =
  let circuit = Graphs.graph_of_verilog_package vp in
  writeout (fname vp.vp_pkg ".dot") Backends.Dot.main circuit;
  writeout (fname vp.vp_pkg ".v") Backends.Verilog.main circuit

let coq_main ?(sim = true) ?(verilog = true) ({ vp; sp; _ }: SGA.demo_package_t) =
  if sim then do_sim sp;
  if verilog then do_verilog vp

let package_matches filter (p: SGA.demo_package_t) =
  let modname = SGALib.Util.string_of_coq_string p.sga.sga_module_name in
  try ignore (Str.search_forward filter modname 0); true
  with Not_found -> false

let mkdir dirname =
  try Unix.mkdir dirname 0o644
  with Unix.Unix_error(Unix.EEXIST, _, _) -> ()

let _ =
  let open SGALib.SGA in
  mkdir "examples"; mkdir "examples/coq";
  let filter = Str.regexp (try Sys.argv.(1) with Invalid_argument _ -> "") in
  let packages = List.filter (package_matches filter) demo_packages in
  List.iter coq_main packages
