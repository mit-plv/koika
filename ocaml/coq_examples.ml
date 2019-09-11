let mkcd dirname =
  (try Unix.mkdir dirname 0o644
   with Unix.Unix_error(Unix.EEXIST, _, _) -> ());
  Sys.chdir dirname

let _ =
  let open SGALib.SGA in
  mkcd "examples"; mkcd "coq";
  List.iter (fun dp -> CoqUtils.coq_main ~verilog:false dp) demo_packages
