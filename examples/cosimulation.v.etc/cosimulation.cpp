#include "cosimulation.hpp"
#include "blackbox.obj_dir.opt/Vblackbox.h"
#include <verilated.h>

using Dut = Vblackbox;

class BlackboxWrapper {
public:
  Dut dut;

  void cycle() {
    dut.CLK = 1;
    dut.eval();
    dut.CLK = 0;
    dut.eval();
  }

  BlackboxWrapper() : dut{} {}
};

struct extfuns {
  BlackboxWrapper blackbox_driver;

  bits<32> blackbox(bits<32> input) {
    blackbox_driver.dut.in = input.v;
    blackbox_driver.cycle();
    return  bits<32>{blackbox_driver.dut.out};
  }
};

class simulator final : public module_cosimulation<extfuns> {
  void strobe() const {
    std::cout << "# Cycle: " << meta.cycle_id << std::endl;
    snapshot().report();
  }
};

int main(int argc, char **argv) { return cuttlesim::main<simulator>(argc, argv); }

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/local/share/verilator/include/")
// End:
