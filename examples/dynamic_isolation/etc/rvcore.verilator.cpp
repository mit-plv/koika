/*! C++ driver for rv32 simulation with Verilator !*/
#include "verilator.hpp"
#include "Vtop.h"

// Overridden to remove the message
void vl_finish (const char* /*filename*/, int /*linenum*/, const char* /*hier*/) VL_MT_UNSAFE {
  Verilated::gotFinish(true);
}

int main(int argc, char** argv) {
  return _main<KoikaToplevel<Vtop>>(argc, argv);
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/share/verilator/include/vltstd/" "../_objects/rv32i.v/" "../_objects/rv32i.v/obj_dir/" "../_objects/rv32i.v/obj_dir.trace/")
// End:
