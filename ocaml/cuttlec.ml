open Common
open Printf
open Frontends

type frontend =
  [`CoqPkg | `LV]

type backend =
  [`Coq | `Verilog | `Dot | `Hpp | `Cpp | `Exe]

let all_backends =
  (* Exe implies Hpp and Cpp *)
  [`Coq; `Verilog; `Dot; `Exe]

let backends : (backend * (string * string)) list =
  [(`Dot, ("dot", ".dot"));
   (`Hpp, ("hpp", ".hpp"));
   (`Cpp, ("cpp", ".cpp"));
   (`Exe, ("exe", ".exe"));
   (`Coq, ("coq", "_coq.v"));
   (`Verilog, ("verilog", "_verilog.v"))]

let suffix_of_backend backend =
  snd (List.assoc backend backends)

let suffixes_to_frontends : (string * frontend) list =
  [(".cmxs", `CoqPkg);
   (".lv", `LV)]

let split_suffix label suffixes fname =
  let rec loop = function
    | [] ->
       let suffixes = String.concat ", " (List.map fst suffixes) in
       failwith (sprintf "%s: expecting one of the following suffixes: %s" label suffixes)
    | (suffix, v) :: more ->
       if Filename.check_suffix fname suffix then
         (Filename.chop_suffix fname suffix, v)
       else
         loop more
  in loop suffixes

let assoc_suffix label known_suffixes stdio_default fpath =
  if fpath = "-" then (fpath, stdio_default)
  else split_suffix label known_suffixes fpath

let frontend_of_path fpath =
  assoc_suffix "frontend" suffixes_to_frontends `LV fpath

type config = {
    cnf_modname: string;
    cnf_src_path: string;
    cnf_dst_prefix: string;
  }

type ('pos_t, 'var_t, 'rule_name_t, 'reg_t, 'ext_fn_t) package = {
    pkg_lv: Lv.resolved_unit lazy_t;
    pkg_cpp: ('pos_t, 'var_t, 'rule_name_t, 'reg_t, 'ext_fn_t) Backends.Cpp.cpp_input_t lazy_t;
    pkg_graph: Cuttlebone.Graphs.circuit_graph lazy_t;
  }

exception UnsupportedOutput of string

let output_fname backend cnf =
  cnf.cnf_dst_prefix ^ suffix_of_backend backend

let run_backend' backend cnf pkg =
  match backend with
  | `Coq ->
     let lv = Lazy.force pkg.pkg_lv in
     with_output_to_file (output_fname backend cnf) Backends.Coq.main lv
  | (`Hpp | `Cpp | `Exe) as kd ->
     let cpp = Lazy.force pkg.pkg_cpp in
     Backends.Cpp.main cnf.cnf_dst_prefix kd cpp
  | (`Verilog | `Dot) as backend ->
     let graph = Lazy.force pkg.pkg_graph in
     with_output_to_file (output_fname backend cnf)
       (match backend with
        | `Dot -> Backends.Dot.main
        | `Verilog -> Backends.Verilog.main cnf.cnf_modname) graph

let pstderr fmt =
  Printf.kfprintf (fun out -> fprintf out "\n") stderr fmt

let quit fmt =
  Printf.kfprintf (fun out -> fprintf out "\n"; exit 1) stderr fmt

let run_backend backend cnf pkg =
  try run_backend' backend cnf pkg
  with UnsupportedOutput msg ->
    quit "%s" msg

let run_backends backends cnf pkg =
  List.iter (fun b -> run_backend b cnf pkg) backends

let first_compile_unit in_path mods =
  match mods with
  | [] -> Lv.name_error (Pos.Filename in_path) @@ MissingModule
  | md :: _ -> md

let print_errors_and_warnings errs =
  let errs_with_warnings = List.rev_append (Lv.Errors.fetch_warnings ()) errs in
  List.iter (pstderr "%s" << Lv.Errors.to_string)
    (List.stable_sort Lv.Errors.compare errs_with_warnings)

let dynlink_interop_packages in_path : Cuttlebone.Extr.interop_package_t list =
  (try
     Dynlink.loadfile_private in_path;
   with Dynlink.Error err ->
     quit "Dynlink error: %s" (Dynlink.error_message err));
  Registry.reset ()

let run (frontend: frontend) (backends: backend list) (cnf: config) =
  match frontend with
  | `LV ->
     let open Lv in
     (try
       let resolved, typechecked =
         Delay.with_delayed_errors (fun () ->
             let resolved =  resolve (parse (read_sexps cnf.cnf_src_path)) in
             resolved, typecheck resolved) in
       let c_unit = first_compile_unit cnf.cnf_src_path typechecked in
       print_errors_and_warnings [];
       run_backends backends cnf
         { pkg_lv = lazy resolved;
           pkg_cpp = lazy (Backends.Cpp.input_of_compile_unit cnf.cnf_modname c_unit);
           pkg_graph = lazy (Cuttlebone.Graphs.graph_of_compile_unit c_unit) }
     with Lv.Errors.Errors errs ->
       print_errors_and_warnings errs;
       exit 1)
  | `CoqPkg ->
     match dynlink_interop_packages cnf.cnf_src_path with
     | [] -> quit "Package %s does not export Koika modules" cnf.cnf_src_path
     | ip :: _ ->
        run_backends backends cnf
          { pkg_lv = lazy (raise (UnsupportedOutput "Coq output is only supported from LV input."));
            pkg_cpp = lazy (Backends.Cpp.input_of_sim_package ip.ip_koika ip.ip_sim);
            pkg_graph = lazy (Cuttlebone.Graphs.graph_of_verilog_package ip.ip_koika ip.ip_verilog) }

let backend_of_spec spec =
  let found (backend, (spec', _)) =
    if spec' = spec then Some backend else None in
  match Core.List.find_map backends ~f:found with
  | None -> quit "Unexpected output format: %s" spec
  | Some backend -> backend

let parse_output_spec spec =
  List.map backend_of_spec (String.split_on_char ',' spec)

let run_cli src_path output_specs =
  let modpath, frontend = frontend_of_path src_path in
  let modname = Core.Filename.basename modpath in
  let backends = Core.List.concat_map ~f:parse_output_spec output_specs in
  let src_path = match src_path with
    | "-" -> "-"
    | _ -> Core.Filename.realpath src_path in
  run frontend backends { cnf_modname = modname;
                          cnf_src_path = src_path;
                          cnf_dst_prefix = modpath }

let cli =
  let open Core in
  Command.basic
    ~summary:"Compile Koika programs"
    Command.Let_syntax.(
    let%map_open
        src_path = anon ("input" %: Filename.arg_type)
    and output_specs = flag "-T" (listed string) ~doc:"fmt output in this format"
    in fun () -> run_cli src_path output_specs)

let _ =
  Core.Command.run cli
