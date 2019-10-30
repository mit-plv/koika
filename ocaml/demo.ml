let package_matches filter (ip: Cuttlebone.Extr.interop_package_t) =
  let modname = Cuttlebone.Util.string_of_coq_string ip.ip_koika.koika_module_name in
  try ignore (Str.search_forward filter modname 0); true
  with Not_found -> false

let mkdir dirname =
  try Unix.mkdir dirname 0o755
  with Unix.Unix_error(Unix.EEXIST, _, _) -> ()

let coq_main (ip: Cuttlebone.Extr.interop_package_t) =
  Interop.compile_all ~directory:"../examples/demo.v.objects" ip

let _ =
  let open Cuttlebone.Extr in
  mkdir "../examples"; mkdir "../examples/demo.v.objects";
  let filter = Str.regexp (try Sys.argv.(1) with Invalid_argument _ -> "") in
  let packages = List.filter (package_matches filter) demo_packages in
  List.iter coq_main packages
