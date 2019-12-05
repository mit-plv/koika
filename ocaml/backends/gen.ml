(*! Embed resources/* into resources.ml at build time !*)

let read fname =
  let inc = open_in (Filename.concat "resources/" fname) in
  let contents = really_input_string inc (in_channel_length inc) in
  close_in inc;
  contents

let quote str =
  Str.global_replace (Str.regexp "[\"\\]") "\\\\\\0" str

let defvar out varname fname =
  Printf.fprintf out "let %s = \"%s\"" varname (quote (read fname))

let _ =
  let out = open_out "resources.ml" in
  defvar out "cuttlesim_hpp" "cuttlesim.hpp";
  defvar out "verilator_cpp" "verilator.cpp";
  defvar out "verilator_hpp" "verilator.hpp";
  close_out out
