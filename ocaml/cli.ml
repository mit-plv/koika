open Common

let ast_of_tokens tokens =
  Obj.magic ()

let tokens_of_stream stream =
  Obj.magic ()

let stream_of_fname fname =
  Obj.magic ()

let parse fname =
  fname
  |> stream_of_fname
  |> tokens_of_stream
  |> ast_of_tokens

type cli_opts = {
    cli_in_fname: string;
    cli_out_fname: string;
    cli_backend: [`Dot | `Verilog]
  }

let cli (k: cli_opts -> unit) =
  let open Core in
  let open Command.Spec in
  let open Command.Param in
  let backend_of_fname fname =
    match Core.Filename.split_extension fname with
    | _, Some ".v" -> `Verilog
    | _, Some ".dot" -> `Dot
    | _, _ -> failwith "Unsupported extension" in
  Command.basic
    ~summary:"Compile simultaneous guarded actions to a circuit"
    Command.Let_syntax.(
    let%map_open
        cli_in_fname = anon ("input" %: string)
    and cli_out_fname = anon ("output" %: string)
    in fun () ->
       k { cli_in_fname; cli_out_fname;
           cli_backend = backend_of_fname cli_out_fname })

let run { cli_in_fname; cli_out_fname; cli_backend } : unit =
  try
    let tc_unit, ast =
      parse cli_in_fname in
    let circuits =
      SGALib.Compilation.compile tc_unit ast in
    let graph =
      SGALib.Graphs.dedup_circuit (SGALib.Util.dedup_input_of_tc_unit tc_unit circuits) in
    Stdio.Out_channel.with_file cli_out_fname ~f:(fun out ->
        match cli_backend with
        | `Dot -> Backends.Dot.main out graph
        | `Verilog -> Backends.Verilog.main out graph)
  with Error { epos; ekind; emsg } ->
    Printf.eprintf "%s:%d:%d: %s: %s"
      epos.pos_fname epos.pos_lnum epos.pos_cnum
      (match ekind with
       | `ParseError -> "Parse error"
       | `NameError -> "Name error"
       | `TypeError -> "Type error")
      emsg;
    exit 1

let main () =
  Core.Command.run (cli run)
