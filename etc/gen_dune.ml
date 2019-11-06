let format_rule name =
  Printf.printf
    "(library
 (name %s)
 (modules %s)
 (libraries koika.registry))

" name name

let _ =
  let files = Array.to_list (Sys.readdir Sys.argv.(1)) in
  let is_ml fname = Filename.check_suffix fname ".ml" in
  let drop_ext fname = Filename.chop_suffix fname ".ml" in
  let lib_names = List.map drop_ext (List.filter is_ml files) in
  List.iter format_rule lib_names;
  Printf.printf "(include_subdirs no)"
