open Common
open Lv

type cli_opts = {
    cli_in_fname: string;
    cli_out_fname: string;
    cli_frontend: [`Sexps | `Annotated];
    cli_backend: [`All | `Dot | `Verilog | `Cpp | `Hpp | `Exe]
  }

let exts_to_backends =
  [("v", `Verilog);
   ("dot", `Dot);
   ("hpp", `Hpp);
   ("cpp", `Cpp);
   ("exe", `Exe);
   ("all", `All)]

let backends_to_exts =
  List.map (fun (x, y) -> (y, x)) exts_to_backends

let all_backends =
  (* Exe implies Hpp and Cpp *)
  [`Verilog; `Dot; `Exe]

let backend_of_fname fname =
  let fail () =
    failwith "Output file must have extension .v, .dot, .hpp, .cpp, .exe, or .all" in
  match Core.Filename.split_extension fname with
  | _, None -> fail ()
  | _, Some ext ->
     match List.assoc_opt ext exts_to_backends with
     | None -> fail ()
     | Some backend -> backend

let ext_of_backend backend =
  List.assoc backend backends_to_exts

let rec run_backend backend out_fname c_unit =
  let fname_noext, _ = Core.Filename.split_extension out_fname in
  match backend with
  | `All ->
     let new_fname backend = fname_noext ^ "." ^ ext_of_backend backend in
     let run_one backend = run_backend backend (new_fname backend) c_unit in
     List.iter run_one all_backends
  | (`Hpp | `Cpp | `Exe) as kd ->
     let cls = Core.Filename.basename fname_noext in
     Backends.Cpp.main fname_noext kd (Backends.Cpp.input_of_compile_unit cls c_unit)
  | (`Verilog | `Dot) as backend ->
     let graph = SGALib.Graphs.graph_of_compile_unit c_unit in
     Stdio.Out_channel.with_file out_fname ~f:(fun out ->
         (match backend with
          | `Dot -> Backends.Dot.main
          | `Verilog -> Backends.Verilog.main) out graph)

let run { cli_in_fname; cli_out_fname; cli_frontend; cli_backend } : unit =
  try
    let sexps =
      match cli_frontend with
      | `Annotated -> read_annotated_sexps cli_in_fname
      | `Sexps -> read_cst_sexps cli_in_fname in
    match resolve (parse cli_in_fname sexps) with
    | [] -> parse_error (Pos.Filename cli_in_fname) "No modules declared"
    | rmod :: _ -> run_backend cli_backend cli_out_fname (typecheck rmod)
  with Error { epos; ekind; emsg } ->
    Printf.eprintf "%s: %s: %s\n"
      (Pos.to_string epos)
      (match ekind with
       | `ParseError -> "Parse error"
       | `NameError -> "Name error"
       | `ResolutionError -> "Resolution error"
       | `TypeError -> "Type error")
      emsg;
    exit 1

let cli =
  let open Core in
  Command.basic
    ~summary:"Compile simultaneous guarded actions to a circuit"
    Command.Let_syntax.(
    let%map_open
        cli_in_fname = anon ("input" %: string)
    and cli_out_fname = anon ("output" %: string)
    and annotated = flag "--annotated" no_arg ~doc:"Recognize '<>' annotations"
    in fun () ->
       run { cli_in_fname; cli_out_fname;
             cli_frontend = if annotated then `Annotated else `Sexps;
             cli_backend = backend_of_fname cli_out_fname })

let _ =
  (* run { cli_in_fname = "collatz.lv"; cli_out_fname = "collatz.v";
   *       cli_frontend = `Sexps; cli_backend = `Verilog } *)
  Core.Command.run cli
