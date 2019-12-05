let main dpath modname =
  let hpp = Filename.concat dpath "verilator.hpp" in
  let cpp = Filename.concat dpath modname ^ ".verilator.cpp" in
  let markers = [("__CUTTLEC_MODULE_NAME__", modname)] in
  Common.with_output_to_file hpp output_string
    Resources.verilator_hpp;
  Common.with_output_to_file cpp output_string
    (Common.replace_strings Resources.verilator_cpp markers)
