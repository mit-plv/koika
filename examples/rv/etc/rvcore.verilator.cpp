/*! C++ driver for rv32i simulation with Verilator !*/
#include "verilator.hpp"
#include "Vtop.h"

// Overridden to remove the message
void vl_finish (const char* /*filename*/, int /*linenum*/, const char* /*hier*/) VL_MT_UNSAFE {
  Verilated::gotFinish(true);
}

template<typename Dut>
class RVToplevel : public Toplevel<Dut> {
  using Toplevel<Dut>::dut;
  using Toplevel<Dut>::cycle;

protected:
  void clock(bool up) {
    dut.CLK = up;
  }
public:
  RVToplevel() : Toplevel<Dut>{} {
    dut.RST_N = 0;
    dut.CLK = 0;
    dut.eval();
    cycle();
    dut.RST_N = 1;
  }
};

int main(int argc, char** argv) {
  return _main<RVToplevel<Vtop>>(argc, argv);
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/share/verilator/include/vltstd/" "../_objects/rv32i_core_pipelined.v/" "../_objects/rv32i_core_pipelined.v/obj_dir/" "../_objects/rv32i_core_pipelined.v/obj_dir.trace/")
// End:
