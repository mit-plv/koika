/*! Verilator driver for the UART testbench !*/
#include "verilator.hpp"
#include "Vtop.h"

int main(int argc, char** argv) {
  return _main<KoikaToplevel<Vtop>>(argc, argv);
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/share/verilator/include/vltstd/" "Vobj_dir/trace/" "Vobj_dir/opt/")
// End:
