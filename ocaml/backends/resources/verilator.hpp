/*! Preamble shared by all Kôika programs compiled to C++ using Verilator !*/
#include "verilated.h"

#ifdef TRACE
#include "verilated_vcd_c.h"
#endif

template<typename Dut>
class Toplevel {
protected:
  Dut dut;

  virtual void clock(bool /*up*/) = 0;

  void cycle() {
    clock(1);
    dut.eval();
    clock(0);
    dut.eval();
  }

public:
#ifdef TRACE
  void trace(uint64_t ncycles, char* vcdpath) {
    Verilated::traceEverOn(true);
    VerilatedVcdC tfp{};

    dut.trace(&tfp, 99);
    tfp.open(vcdpath);

    for (uint64_t cid = 0; !Verilated::gotFinish() && cid < ncycles; cid++) {
      cycle();
      tfp.dump(cid);
    }
  }
#endif

  void run(uint64_t ncycles) {
    for (uint64_t cid = 0; !Verilated::gotFinish() && cid < ncycles; cid++) {
      cycle();
    }
  }

  Toplevel() : dut{} {}
};

template<typename Dut>
class KoikaToplevel : public Toplevel<Dut> {
  using Toplevel<Dut>::dut;
  using Toplevel<Dut>::cycle;

protected:
  void clock(bool up) {
    dut.CLK = up;
  }
public:
  KoikaToplevel() : Toplevel<Dut>{} {
    dut.reset = 0;
    dut.CLK = 0;
    dut.eval();
    cycle();
    dut.reset = 1;
  }
};

struct cli_arguments {
  char* vcd_fpath;
  uint64_t ncycles;

  cli_arguments(int argc, char** argv) : vcd_fpath(nullptr), ncycles(UINT64_MAX) {
    int offset = 1;
    while (offset < argc && argv[offset][0] == '+') {
      offset++;
    }

    if (offset + 1 < argc) {
      vcd_fpath = argv[offset + 1];
    }

    if (offset < argc) {
      ncycles = static_cast<uint64_t>(std::strtoull(argv[offset], nullptr, 10));
    }
  }
};

template<typename Top>
int _main(int argc, char** argv) {
  Verilated::commandArgs(argc, argv);

  cli_arguments args(argc, argv);

#ifdef TRACE
  if (!args.vcd_fpath) {
    printf("Usage: %s ncycles vcd_fname\n", argv[0]);
    return 1;
  }
#endif

  Top toplevel{};

#ifdef TRACE
  toplevel.trace(args.ncycles, args.vcd_fpath);
#else
  toplevel.run(args.ncycles);
#endif

  return 0;
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include")
// End:
