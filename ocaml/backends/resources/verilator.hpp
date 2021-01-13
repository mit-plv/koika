/*! Preamble shared by all Kôika programs compiled to C++ using Verilator !*/
#include <cstdint>
#include "verilated.h"

#ifdef TRACE
#include "verilated_vcd_c.h"
#endif

#define TIMESTEP 5

template<typename Dut>
class Toplevel {
protected:
  Dut dut;
  std::uint64_t time;

#ifdef TRACE
  VerilatedVcdC* tfp{};
#endif

  virtual void clock(bool /*up*/) = 0;
  virtual void reset(bool /*up*/) = 0;

  void dump() {
#ifdef TRACE
    tfp->dump(time);
#endif
  }

  void tick(bool up) {
    time += TIMESTEP;
    clock(up);
    dut.eval();
    dump();
  }

  void cycle() {
    tick(1);
    tick(0);
  }

  void reset() {
    reset(0);
    clock(0);
    dut.eval();
    time = 0;
    cycle();
    reset(1);
  }

public:
  void run(std::uint_fast64_t ncycles) {
    reset();
    for (std::uint_fast64_t cid = 0; !Verilated::gotFinish() && cid < ncycles; cid++) {
      cycle();
    }
  }

#ifdef TRACE
  void trace(std::uint_fast64_t ncycles, char* vcdpath) {
    Verilated::traceEverOn(true);
    tfp = new VerilatedVcdC{};
    dut.trace(tfp, 99);
    tfp->open(vcdpath);
    run(ncycles);
    dump();
    tfp->close();
    delete tfp;
  }
#endif

  Toplevel() : dut{}, time{0} {}
};

template<typename Dut>
class KoikaToplevel : public Toplevel<Dut> {
protected:
  using Toplevel<Dut>::dut;
  using Toplevel<Dut>::cycle;

  // Change CLK to the name of your clock signal
  void clock(bool up) {
    dut.CLK = up;
  }

  // Change RST_N to the name of your clock signal
  void reset(bool up) {
    dut.RST_N = up;
  }

public:
  KoikaToplevel() : Toplevel<Dut>{} {}
};

struct cli_arguments {
  char* vcd_fpath;
  std::uint64_t ncycles;

  cli_arguments(int argc, char** argv) : vcd_fpath(nullptr), ncycles(UINT64_MAX) {
    int offset = 1;
    while (offset < argc && argv[offset][0] == '+') {
      offset++;
    }

    if (offset + 1 < argc) {
      vcd_fpath = argv[offset + 1];
    }

    if (offset < argc) {
      ncycles = static_cast<std::uint64_t>(std::strtoull(argv[offset], nullptr, 10));
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
