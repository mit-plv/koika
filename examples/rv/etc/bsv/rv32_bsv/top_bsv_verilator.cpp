/*! Default driver for Kôika programs compiled to C++ using Verilator !*/
#include "../../verilator.hpp"
#include "Vtop_bsv.h"

void vl_finish (const char* /*filename*/, int /*linenum*/, const char* /*hier*/) VL_MT_UNSAFE {
  Verilated::gotFinish(true);
}

class TB : public KoikaToplevel<Vtop_bsv> {
  using KoikaToplevel<Vtop_bsv>::dut;

public:
  void run(uint64_t ncycles) {
    KoikaToplevel<Vtop_bsv>::run(ncycles);
  }

  TB() : KoikaToplevel<Vtop_bsv>{} {}
};

int main(int argc, char** argv) {
  return _main<TB>(argc, argv);
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/local/share/verilator/include" "/usr/local/share/verilator/include/vltstd/" "bsv.obj_dir.opt/")
// End:
