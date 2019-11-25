(*! Embed preamble.hpp into cppPreamble.ml at build time !*)
let cpp_preamble =
  let inc = open_in "preamble.hpp" in
  let preamble = really_input_string inc (in_channel_length inc) in
  close_in inc;
  preamble

let quote str =
  Str.global_replace (Str.regexp "[\"\\]") "\\\\\\0" str

let _ =
  let out = open_out "cppPreamble.ml" in
  Printf.fprintf out "let preamble = \"%s\"" (quote cpp_preamble);
  close_out out
