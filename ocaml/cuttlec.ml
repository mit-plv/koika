(*! Command line interface to the compilers !*)
open Common
open Printf
open Frontends

type frontend =
  CoqPkg | LV | ExtractedML

type backend =
  [`Coq | `Verilator | `Makefile | `Verilog | `Dot | `Hpp | `Cpp | `Opt]

let all_backends (f: frontend) : backend list =
  let shared = [`Verilator; `Makefile; `Verilog; `Dot; `Hpp; `Cpp] in
  match f with
  | LV -> `Coq :: shared
  | CoqPkg | ExtractedML -> shared

let backends : (backend * (string * string)) list =
  [(`Dot, ("dot", ".dot"));
   (`Hpp, ("hpp", ".hpp"));
   (`Cpp, ("cpp", ".cpp"));
   (`Opt, ("opt", ".opt"));
   (`Coq, ("coq", "_coq.v"));
   (`Verilog, ("verilog", "_verilog.v"));
   (`Verilator, ("verilator", "verilator.cpp"))]

let name_of_backend backend =
  match backend with
  | `Makefile -> "makefile"
  | _ -> fst (List.assoc backend backends)

let suffix_of_backend backend =
  snd (List.assoc backend backends)

let suffixes_to_frontends : (string * frontend) list =
  [(".lv", LV);
   (".cmxs", CoqPkg);
   (".kpkg", CoqPkg);
   (".kobj", CoqPkg);
   (".ml", ExtractedML)]

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
  assoc_suffix "frontend" suffixes_to_frontends LV fpath

type config = {
    cnf_src_fpath: string;
    cnf_dst_dpath: string;
  }

type package = {
    pkg_modname: string;
    pkg_lv: Lv.resolved_unit lazy_t;
    pkg_cpp: Backends.Cpp.cpp_output_t lazy_t;
    pkg_graph: Cuttlebone.Graphs.circuit_graph lazy_t;
  }

exception UnsupportedOutput of string

let output_fname (backend: backend) { cnf_dst_dpath; _ } { pkg_modname; _ } =
  Filename.concat cnf_dst_dpath
    (match backend with
     | `Makefile -> "Makefile"
     | _ -> pkg_modname ^ suffix_of_backend backend)


let run_backend' (backend: backend) cnf pkg =
  match backend with
  | `Coq ->
     let lv = Lazy.force pkg.pkg_lv in
     with_output_to_file (output_fname backend cnf pkg)
       Backends.Coq.main lv
  | `Verilator ->
     Backends.Verilator.main cnf.cnf_dst_dpath pkg.pkg_modname
  | `Makefile ->
     with_output_to_file (output_fname backend cnf pkg)
       Backends.Makefile.main pkg.pkg_modname
  | (`Hpp | `Cpp | `Opt) as kd ->
     let cpp = Lazy.force pkg.pkg_cpp in
     Backends.Cpp.write_output cnf.cnf_dst_dpath kd cpp
  | (`Verilog | `Dot) as backend ->
     let graph = Lazy.force pkg.pkg_graph in
     match backend with
     | `Dot -> Backends.Rtl.Dot.main cnf.cnf_dst_dpath pkg.pkg_modname graph
     | `Verilog -> Backends.Rtl.main cnf.cnf_dst_dpath pkg.pkg_modname graph

let pstderr fmt =
  Printf.kfprintf (fun out -> fprintf out "\n") stderr fmt

let expect_success = ref false
let exit success =
  exit (if success = !expect_success then 0 else 1)

let abort fmt =
  Printf.kfprintf (fun out -> fprintf out "\n"; exit false) stderr fmt

let run_backend backend cnf pkg =
  try Perf.with_timer (sprintf "backend:%s" (name_of_backend backend)) (fun () ->
          run_backend' backend cnf pkg)
  with UnsupportedOutput msg -> abort "%s" msg
     | Common.CompilationError cmd -> abort "Compilation failed: %s" cmd

let run_backends backends cnf pkg =
  List.iter (fun b -> run_backend b cnf pkg) backends

let print_errors_and_warnings errs =
  let errs_with_warnings = List.rev_append (Lv.Errors.fetch_warnings ()) errs in
  List.iter (pstderr "%s" << Lv.Errors.to_string)
    (List.stable_sort Lv.Errors.compare errs_with_warnings)

let dynlink_interop_packages in_fpath : Cuttlebone.Extr.interop_package_t list =
  (try
     Dynlink.loadfile_private in_fpath;
   with Dynlink.Error err ->
     abort "Dynlink error: %s" (Dynlink.error_message err));
  match Registry.reset () with
  | [] -> abort "Package %s does not export Koika modules" in_fpath
  | ips -> ips

(* https://github.com/janestreet/core/issues/136 *)
module RelPath = struct
  let eql = (=)

  open Core

  let split_common_prefix l1 l2 =
    let rec loop acc l1 l2 =
      match l1, l2 with
      | h1 :: t1, h2 :: t2 when h1 = h2 -> loop (h1 :: acc) t1 t2
      | _ -> List.rev acc, l1, l2 in
    loop [] l1 l2

  let abspath (path: string) =
    if Filename.is_relative path then
      let cwd = Core_unix.getcwd () in
      Filename.concat cwd path
    else path

  let rec skip_common_prefix l1 l2 =
    match l1, l2 with
    | h1 :: t1, h2 :: t2 when eql h1 h2 -> skip_common_prefix t1 t2
    | _ -> l1, l2

  let relpath (path: string) (start: string) =
    let open Core.Filename in
    let pparts = parts (abspath path) in
    let sparts = parts (abspath start) in
    let ponly, sonly = skip_common_prefix pparts sparts in
    let go_up = List.map ~f:(fun _ -> parent_dir_name) sonly in
    match go_up @ ponly with
    | [] -> current_dir_name
    | relpath -> of_parts relpath
end

let adjust_pos target_dpath (p: Pos.t) : Pos.t =
  match p with
  | Filename fname -> Filename (RelPath.relpath fname target_dpath)
  | Range (fname, rng) -> Range (RelPath.relpath fname target_dpath, rng)
  | Unknown | StrPos _ -> p

let adjust_positions dst_dpath (cu: Pos.t Cuttlebone.Compilation.compile_unit) =
  { cu with c_pos_of_pos = adjust_pos dst_dpath << cu.c_pos_of_pos }

let run_lv (backends: backend list) (cnf: config) =
  try
    let resolved, c_unit = Lv.load cnf.cnf_src_fpath in
    let c_unit = adjust_positions cnf.cnf_dst_dpath c_unit in
    print_errors_and_warnings [];
    run_backends backends cnf
      { pkg_modname = c_unit.c_modname;
        pkg_lv = lazy resolved;
        pkg_cpp = lazy Backends.Cpp.(compile (input_of_compile_unit c_unit));
        pkg_graph = lazy (Cuttlebone.Graphs.graph_of_compile_unit c_unit) }
  with Lv.Errors.Errors errs ->
    print_errors_and_warnings errs;
    exit false

let run_ip (backends: backend list) cnf (ip: Cuttlebone.Extr.interop_package_t) =
  run_backends backends cnf
    { pkg_modname = Cuttlebone.Util.string_of_coq_string ip.ip_koika.koika_module_name;
      pkg_lv = lazy (raise (UnsupportedOutput "Coq output is only supported from LV input"));
      pkg_cpp = lazy Backends.Cpp.(compile (input_of_sim_package ip.ip_koika ip.ip_sim));
      pkg_graph = lazy (Cuttlebone.Graphs.graph_of_verilog_package ip.ip_koika ip.ip_verilog) }

let run_dynlink (backends: backend list) (cnf: config) =
  List.iter (run_ip backends cnf) (dynlink_interop_packages cnf.cnf_src_fpath)

let run_ocaml (backends: backend list) (cnf: config) =
  let pkg = Frontends.Coq.compile_ml cnf.cnf_src_fpath cnf.cnf_dst_dpath in
  List.iter (run_ip backends cnf) (dynlink_interop_packages pkg)

let run (frontend: frontend) (backends: backend list) (cnf: config) =
  match frontend with
  | LV -> run_lv backends cnf
  | CoqPkg -> run_dynlink backends cnf
  | ExtractedML -> run_ocaml backends cnf

let backends_of_spec frontend spec =
  let found (backend, (spec', _)) =
    if spec' = spec then Some backend else None in
  if spec = "all" then
    all_backends frontend
  else
    match Base.List.find_map backends ~f:found with
    | None -> abort "Unexpected output format: %s" spec
    | Some backend -> [backend]

let parse_output_spec frontend spec =
  Base.List.concat_map
    ~f:(backends_of_spec frontend)
    (String.split_on_char ',' spec)

let run_cli expect_errors src_fpath dst_dpath output_specs =
  expect_success := not expect_errors;
  let _, frontend = frontend_of_path src_fpath in
  let backends = Base.List.concat_map ~f:(parse_output_spec frontend) output_specs in
  let dst_dpath = Base.Option.value dst_dpath ~default:(Filename.dirname src_fpath) in
  (try Unix.mkdir dst_dpath 0o775 with Unix.Unix_error _ -> ());
  run frontend backends { cnf_src_fpath = src_fpath;
                          cnf_dst_dpath = dst_dpath };
  exit true

let cli =
  let open Core in
  let open Command.Let_syntax in
  Command.basic
    ~summary:"Compile Koika programs"
    (let%map_open
        expect_errors = flag "--expect-errors" no_arg ~doc:"flip the exit code (1 for success, 0 for errors)"
     and src_fpath = anon ("input" %: Filename_unix.arg_type)
     and dst_dpath = flag "-o" (optional string) ~doc:"dir output to this directory"
     and output_specs = flag "-T" (listed string) ~doc:"fmt output in this format"
     in fun () -> run_cli expect_errors src_fpath dst_dpath output_specs)

let _: unit =
  Command_unix.run cli
