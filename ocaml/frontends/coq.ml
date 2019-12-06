(*! Simple frontend to compile and load OCaml files extracted from Coq !*)
let ensure_koikalib () =
  Common.command "ocamlfind" ["query"; "-qe"; "-qo"; "koika"]

let run_ocamlopt incl mli ml pkg =
  Common.command ~verbose:true "ocamlfind"
    ["ocamlopt"; "-package"; "koika.registry"; "-I"; incl;
     mli; ml; "-shared"; "-o"; pkg]

let compile_ml ml_fpath out_dpath =
  (* Implementing this with compiler-libs would require changes depending on the
     OCaml version, while the command-line interface is simple and stable. *)
  ensure_koikalib ();
  let mli_fpath = ml_fpath ^ "i" in
  let incl_dpath = Filename.dirname ml_fpath in
  let modname = Filename.chop_extension (Filename.basename ml_fpath) in
  let pkg_fpath = Filename.concat out_dpath (modname ^ ".kpkg") in
  run_ocamlopt incl_dpath mli_fpath ml_fpath pkg_fpath;
  pkg_fpath

let compile_coq () = ()
