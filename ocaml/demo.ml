let package_matches filter (p: _ Cuttlebone.Extr.demo_package_t) =
  let modname = Cuttlebone.Util.string_of_coq_string p.kp.koika_module_name in
  try ignore (Str.search_forward filter modname 0); true
  with Not_found -> false

let mkdir dirname =
  try Unix.mkdir dirname 0o755
  with Unix.Unix_error(Unix.EEXIST, _, _) -> ()

let coq_main (dp: _ Cuttlebone.Extr.demo_package_t) =
  Backends.Driver.compile_all ~directory:"../examples/demo.v.objects"
    dp.kp dp.sp dp.vp

let _ =
  let open Cuttlebone.Extr in
  mkdir "../examples"; mkdir "../examples/demo.v.objects";
  let filter = Str.regexp (try Sys.argv.(1) with Invalid_argument _ -> "") in
  let packages = List.filter (package_matches filter) demo_packages in
  List.iter coq_main packages
