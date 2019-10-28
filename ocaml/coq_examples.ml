open SGALib

let package_matches filter (p: SGA.demo_package_t) =
  let modname = SGALib.Util.string_of_coq_string p.sga.sga_module_name in
  try ignore (Str.search_forward filter modname 0); true
  with Not_found -> false

let mkdir dirname =
  try Unix.mkdir dirname 0o644
  with Unix.Unix_error(Unix.EEXIST, _, _) -> ()

let coq_main (dp: SGALib.SGA.demo_package_t) =
  CoqInterop.compile_all ~directory:"coq/examples"
    dp.sga dp.sp dp.vp

let _ =
  let open SGALib.SGA in
  mkdir "examples"; mkdir "examples/coq";
  let filter = Str.regexp (try Sys.argv.(1) with Invalid_argument _ -> "") in
  let packages = List.filter (package_matches filter) demo_packages in
  List.iter coq_main packages
