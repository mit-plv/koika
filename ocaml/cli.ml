open Common
open Lv

type backend =
  [`Coq | `Verilog | `Dot | `Hpp | `Cpp | `Exe | `All]

type cli_opts = {
    cli_in_fname: string;
    cli_out_fname: string;
    cli_frontend: [`Sexps | `Annotated];
    cli_backend: backend
  }

let exts_to_backends : (string * backend) list =
  [("coq.v", `Coq);
   ("verilog.v", `Verilog);
   ("dot", `Dot);
   ("hpp", `Hpp);
   ("cpp", `Cpp);
   ("exe", `Exe);
   ("all", `All)]

let backends_to_exts =
  List.map (fun (x, y) -> (y, x)) exts_to_backends

let all_backends =
  (* Exe implies Hpp and Cpp *)
  [`Coq; `Verilog; `Dot; `Exe]

let exts, ext_re =
  let exts = List.map fst exts_to_backends in
  let cases = String.concat "\\|" exts in
  exts, Str.regexp (sprintf "^\\(.*\\)\\.\\(%s\\)$" cases)

let split_extension fname =
  let fail () =
    let exts = String.concat ", " exts in
    failwith (sprintf "Output file must have one of the following extensions: %s" exts) in
  if Str.string_match ext_re fname 0 then
    (Str.matched_group 1 fname, Str.matched_group 2 fname)
  else fail ()

let backend_of_fname fname =
  let _, ext = split_extension fname in
  List.assoc ext exts_to_backends

let ext_of_backend backend =
  List.assoc backend backends_to_exts

let rec run_backend backend out_fname resolved c_unit =
  let fname_noext, _ = split_extension out_fname in
  match backend with
  | `All ->
     let new_fname backend = fname_noext ^ "." ^ ext_of_backend backend in
     let run_one backend = run_backend backend (new_fname backend) resolved c_unit in
     List.iter run_one all_backends
  | `Coq ->
     Stdio.Out_channel.with_file out_fname ~f:(fun out ->
         Backends.Coq.main out resolved)
  | (`Hpp | `Cpp | `Exe) as kd ->
     let cls = Core.Filename.basename fname_noext in
     Backends.Cpp.main fname_noext kd (Backends.Cpp.input_of_compile_unit cls (Lazy.force c_unit))
  | (`Verilog | `Dot) as backend ->
     let graph = SGALib.Graphs.graph_of_compile_unit (Lazy.force c_unit) in
     Stdio.Out_channel.with_file out_fname ~f:(fun out ->
         (match backend with
          | `Dot -> Backends.Dot.main
          | `Verilog -> Backends.Verilog.main) out graph)

let first_compile_unit in_fname mods =
  match mods with
  | [] -> parse_error (Pos.Filename in_fname) "No modules declared"
  | md :: _ -> md

let run { cli_in_fname; cli_out_fname; cli_frontend; cli_backend } : unit =
  try
    let sexps =
      match cli_frontend with
      | `Annotated -> read_annotated_sexps cli_in_fname
      | `Sexps -> read_cst_sexps cli_in_fname in
    let resolved = resolve (parse cli_in_fname sexps) in
    let c_unit = lazy (first_compile_unit cli_in_fname (typecheck resolved)) in
    run_backend cli_backend cli_out_fname resolved c_unit
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
