let _  =
  let circuit =
    SGALib.Util.dedup_input_of_verilogPackage SGALib.SGA.Collatz.package
    |> SGALib.Graphs.dedup_circuit in
  Backends.Dot.main stderr circuit;
  Backends.Verilog.main stdout circuit
