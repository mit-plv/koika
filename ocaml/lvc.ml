open Common
open Printf
open Frontends

type backend =
  [`Coq | `Verilog | `Dot | `Hpp | `Cpp | `Exe | `All]

type cli_opts = {
    cli_in_fname: string;
    cli_out_fname: string;
    cli_frontend: [`Sexps | `Annotated];
    cli_backend: backend option
  }

let suffixes_to_backends : (string * backend) list =
  [("_coq.v", `Coq);
   ("_verilog.v", `Verilog);
   (".dot", `Dot);
   (".hpp", `Hpp);
   (".cpp", `Cpp);
   (".exe", `Exe);
   (".all", `All)]

let backends_to_suffixes =
  List.map (fun (x, y) -> (y, x)) suffixes_to_backends

let all_backends =
  (* Exe implies Hpp and Cpp *)
  [`Coq; `Verilog; `Dot; `Exe]

let suffixes, suffix_re =
  let suffixes = List.map (Str.quote << fst) suffixes_to_backends in
  let cases = String.concat "\\|" suffixes in
  suffixes, Str.regexp (sprintf "^\\(.*\\)\\(%s\\)$" cases)

let split_suffix fname =
  let fail () =
    let suffixes = String.concat ", " suffixes in
    failwith (sprintf "Output file must have one of the following suffixes: %s" suffixes) in
  if Str.string_match suffix_re fname 0 then
    (Str.matched_group 1 fname, Str.matched_group 2 fname)
  else fail ()

let backend_of_fname fname =
  if fname = "-" then None
  else let _, suffix = split_suffix fname in
       Some (List.assoc suffix suffixes_to_backends)

let suffix_of_backend backend =
  List.assoc backend backends_to_suffixes

let rec run_backend backend out_fname resolved c_unit =
  let fname_prefix, _ = split_suffix out_fname in
  match backend with
  | `All ->
     let new_fname backend = fname_prefix ^ suffix_of_backend backend in
     let run_one backend = run_backend backend (new_fname backend) resolved c_unit in
     List.iter run_one all_backends
  | `Coq ->
     with_output_to_file out_fname (fun out ->
         Backends.Coq.main out resolved)
  | (`Hpp | `Cpp | `Exe) as kd ->
     let cls = Core.Filename.basename fname_prefix in
     Backends.Cpp.main fname_prefix kd (Backends.Cpp.input_of_compile_unit cls c_unit)
  | (`Verilog | `Dot) as backend ->
     let graph = Cuttlebone.Graphs.graph_of_compile_unit c_unit in
     with_output_to_file out_fname (fun out ->
         (match backend with
          | `Dot -> Backends.Dot.main
          | `Verilog -> (Backends.Verilog.main fname_prefix)) out graph)

let first_compile_unit in_fname mods =
  match mods with
  | [] -> Lv.name_error (Pos.Filename in_fname) @@ MissingModule
  | md :: _ -> md

let print_errors_and_warnings errs =
  let errs_with_warnings = List.rev_append (Lv.Errors.fetch_warnings ()) errs in
  List.iter (Printf.eprintf "%s\n" << Lv.Errors.to_string)
    (List.stable_sort Lv.Errors.compare errs_with_warnings)

let run { cli_in_fname; cli_out_fname; cli_frontend; cli_backend } : unit =
  let open Lv in
  let cli_in_fname =
    if cli_in_fname = "-" then "-"
    else Core.Filename.realpath cli_in_fname in
  let read =
    match cli_frontend with
    | `Annotated -> read_annotated_sexps
    | `Sexps -> read_cst_sexps in
  try
    let resolved, typechecked =
      Delay.with_delayed_errors (fun () ->
          let resolved =  resolve (parse (read cli_in_fname)) in
          resolved, typecheck resolved) in
    let c_unit = first_compile_unit cli_in_fname typechecked in
    print_errors_and_warnings [];
    (match cli_backend with
     | Some backend -> run_backend backend cli_out_fname resolved c_unit
     | None -> ());
  with Lv.Errors.Errors errs ->
    print_errors_and_warnings errs;
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
