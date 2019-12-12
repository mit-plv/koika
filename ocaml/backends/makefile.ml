(*! Makefile backend (to make it easier to generate traces, statistics, models, etc.) !*)
let concat flags =
  String.concat " " flags

let main out modname =
  let markers =
    [("__CUTTLEC_MODULE_NAME__", modname);
     ("__CUTTLEC_CXX_STANDARD__", concat Cpp.flags_standard);
     ("__CUTTLEC_CXX_OPT_FLAGS__", concat Cpp.flags_opt);
     ("__CUTTLEC_CXX_WARNINGS__", concat Cpp.flags_warnings)] in
  let rec replace_all s = function
    | [] -> s
    | (src, dst) :: repls ->
       let re = Str.regexp (Str.quote src) in
       replace_all (Str.global_replace re dst s) repls in
  output_string out (replace_all Resources.makefile markers)
