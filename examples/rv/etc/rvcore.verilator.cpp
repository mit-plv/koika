#include "verilator.hpp"
#include "VmkProc.h"

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
  return _main<RVToplevel<VmkProc>>(argc, argv);
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/share/verilator/include/vltstd/" "../_objects/rv32i_core_pipelined.v/" "../_objects/rv32i_core_pipelined.v/Vobj_dir/trace/" "../_objects/rv32i_core_pipelined.v/Vobj_dir/opt/")
// End:
