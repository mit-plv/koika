open Common
open Printf
open Frontends

type frontend =
  [`CoqPkg | `LV]

type backend =
  [`Coq | `Verilog | `Dot | `Hpp | `Cpp | `Exe | `All]

let suffixes_to_backends : (string * backend) list =
  [("_coq.v", `Coq);
   ("_verilog.v", `Verilog);
   (".dot", `Dot);
   (".hpp", `Hpp);
   (".cpp", `Cpp);
   (".exe", `Exe);
   (".all", `All)]

let suffixes_to_frontends : (string * frontend) list =
  [(".cmxs", `CoqPkg);
   (".lv", `LV)]

let backends_to_suffixes =
  List.map (fun (x, y) -> (y, x)) suffixes_to_backends

let all_backends =
  (* Exe implies Hpp and Cpp *)
  [`Coq; `Verilog; `Dot; `Exe]

let split_suffix label suffixes fname =
  let rec loop = function
    | [] ->
       let suffixes = String.concat ", " (List.map fst suffixes) in
       failwith (sprintf "%s: expecting one of the following suffixes: %s" label suffixes)
    | (suffix, v) :: more ->
       if Filename.check_suffix fname suffix then
         let slen = String.length suffix in
         (String.sub fname 0 (String.length fname - slen), v)
       else
         loop more
  in loop suffixes

let suffix_of_backend backend =
  List.assoc backend backends_to_suffixes

let assoc_suffix label known_suffixes stdio_default fpath =
  if fpath = "-" then (fpath, stdio_default)
  else split_suffix label known_suffixes fpath

let backend_of_path fpath =
  assoc_suffix "backend" suffixes_to_backends `Verilog fpath

let frontend_of_path fpath =
  snd (assoc_suffix "frontend" suffixes_to_frontends `LV fpath)

type config = {
    cnf_src_path: string;
    cnf_dst_path: string;
    cnf_modname: string;
    cnf_dst_path_prefix: string;
  }

type ('pos_t, 'var_t, 'rule_name_t, 'reg_t, 'ext_fn_t) package = {
    pkg_lv: Lv.resolved_unit lazy_t;
    pkg_cpp: ('pos_t, 'var_t, 'rule_name_t, 'reg_t, 'ext_fn_t) Backends.Cpp.cpp_input_t lazy_t;
    pkg_graph: Cuttlebone.Graphs.circuit_graph lazy_t;
  }

let set_dst_path backend cnf =
  let cnf_dst_path = cnf.cnf_dst_path_prefix ^ suffix_of_backend backend in
  { cnf with cnf_dst_path }

exception UnsupportedOutput of string

let rec run_backend' backend cnf pkg =
  match backend with
  | `All ->
     let run_one backend =
       try run_backend' backend (set_dst_path backend cnf) pkg
       with UnsupportedOutput _ -> () in
     List.iter run_one all_backends
  | `Coq ->
     let lv = Lazy.force pkg.pkg_lv in
     with_output_to_file cnf.cnf_dst_path Backends.Coq.main lv
  | (`Hpp | `Cpp | `Exe) as kd ->
     let cpp = Lazy.force pkg.pkg_cpp in
     Backends.Cpp.main cnf.cnf_dst_path_prefix kd cpp
  | (`Verilog | `Dot) as backend ->
     let graph = Lazy.force pkg.pkg_graph in
     with_output_to_file cnf.cnf_dst_path
       (match backend with
        | `Dot -> Backends.Dot.main
        | `Verilog -> Backends.Verilog.main cnf.cnf_modname) graph

let pstderr fmt =
  Printf.kfprintf (fun out -> output_string out "\n") stderr fmt

let run_backend backend cnf pkg =
  try run_backend' backend cnf pkg
  with UnsupportedOutput msg ->
    pstderr "%s" msg; exit 1

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
     pstderr "Dynlink error: %s" (Dynlink.error_message err); exit 1);
  Registry.reset ()

let run (frontend: frontend) (backend: backend) (cnf: config) =
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
       run_backend backend cnf
         { pkg_lv = lazy resolved;
           pkg_cpp = lazy (Backends.Cpp.input_of_compile_unit cnf.cnf_modname c_unit);
           pkg_graph = lazy (Cuttlebone.Graphs.graph_of_compile_unit c_unit) }
     with Lv.Errors.Errors errs ->
       print_errors_and_warnings errs;
       exit 1)
  | `CoqPkg ->
     match dynlink_interop_packages cnf.cnf_src_path with
     | [] -> pstderr "Package %s does not export Koika modules" cnf.cnf_src_path; exit 1
     | ip :: _ ->
        run_backend backend cnf
          { pkg_lv = lazy (raise (UnsupportedOutput "Coq output is only supported from LV input."));
            pkg_cpp = lazy (Backends.Cpp.input_of_sim_package ip.ip_koika ip.ip_sim);
            pkg_graph = lazy (Cuttlebone.Graphs.graph_of_verilog_package ip.ip_koika ip.ip_verilog) }

let run_cli src_path dst_path =
  let frontend = frontend_of_path src_path in
  let dst_path_prefix, backend = backend_of_path dst_path in
  let src_path = match src_path with
    | "-" -> "-"
    | _ -> Core.Filename.realpath src_path in
  let modname = Core.Filename.basename dst_path_prefix in
  run frontend backend { cnf_src_path = src_path;
                         cnf_dst_path = dst_path;
                         cnf_modname = modname;
                         cnf_dst_path_prefix = dst_path_prefix }

let cli =
  let open Core in
  Command.basic
    ~summary:"Compile simultaneous guarded actions to a circuit"
    Command.Let_syntax.(
    let%map_open
        src_path = anon ("input" %: string)
    and dst_path = anon ("output" %: string)
    in fun () -> run_cli src_path dst_path)

let _ =
  Core.Command.run cli
