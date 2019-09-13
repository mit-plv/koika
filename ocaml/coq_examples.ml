open SGALib

let modname (pkg: _ SGA.sga_package_t) =
  Util.string_of_coq_string pkg.sga_module_name

let do_sim (sp: _ SGA.sim_package_t) =
  let sga = sp.sp_pkg in
  Backends.Cpp.main (modname sga) `Exe (Backends.Cpp.input_of_sim_package (Obj.magic sp))

let writeout name ext fn circuit =
  Common.with_output_to_file (name ^ ext) (fun out -> fn out circuit)

let do_verilog (vp: _ SGA.verilog_package_t) =
  let circuit = Graphs.graph_of_verilog_package vp in
  let modname = modname vp.vp_pkg in
  writeout modname ".dot" Backends.Dot.main circuit;
  writeout modname ".v" Backends.Verilog.main circuit

let coq_main ?(sim = true) ?(verilog = true) ({ vp; sp; _ }: SGA.demo_package_t) =
  Printf.eprintf ">> Compiling %s\n%!" (modname vp.vp_pkg);
  if sim then do_sim sp;
  if verilog then do_verilog vp

let mkcd dirname =
  (try Unix.mkdir dirname 0o644
   with Unix.Unix_error(Unix.EEXIST, _, _) -> ());
  Sys.chdir dirname

let _ =
  let open SGALib.SGA in
  mkcd "examples"; mkcd "coq";
  List.iter (fun dp -> coq_main ~verilog:false dp) demo_packages
