let _ =
  let open SGALib.SGA in
  List.iter (fun dp -> CoqUtils.coq_main ~verilog:false dp) demo_packages
