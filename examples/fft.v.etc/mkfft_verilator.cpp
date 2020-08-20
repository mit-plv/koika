/*! Default driver for Kôika programs compiled to C++ using Verilator !*/
#include "verilator.hpp"
#include "Vmkfft.h"

class TB : public KoikaToplevel<Vmkfft> {
  using KoikaToplevel<Vmkfft>::dut;

public:
  void run(uint64_t ncycles) {
    KoikaToplevel<Vmkfft>::run(ncycles);
    printf("%d", dut.rd);
  }

  TB() : KoikaToplevel<Vmkfft>{} {}
};

int main(int argc, char** argv) {
  return _main<TB>(argc, argv);
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/share/verilator/include/vltstd/" "Vobj_dir/trace/" "Vmkfft.obj_dir.opt/")
// End:
