/*! Default driver for Kôika programs compiled to C++ using Verilator !*/
#include "verilator.hpp"
#include "V__CUTTLEC_MODULE_NAME__.h"

// #include "V__CUTTLEC_MODULE_NAME____Dpi.h"
// If you have external functions implemented through DPI, uncomment the line
// above and add your definitions here.

int main(int argc, char** argv) {
  return _main<KoikaToplevel<V__CUTTLEC_MODULE_NAME__>>(argc, argv);
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/share/verilator/include/vltstd/" "Vobj_dir/trace/" "Vobj_dir/opt/")
// End:
