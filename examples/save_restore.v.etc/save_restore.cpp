#include "save_restore.hpp"

struct extfuns {};

class simulator final : public module_save_restore<extfuns> {
  void strobe() const {
    std::cout << "# Cycle: " << meta.cycle_id << std::endl;
    snapshot().report();
  }

public:
  void save(std::string fname) {
    std::ofstream vcd(fname);
    state_t::vcd_header(vcd);
    auto latest = Log.snapshot();
    latest.vcd_dumpvars(meta.cycle_id, vcd, latest, true);
  }

  void load(std::string fname) {
    std::ifstream vcd(fname);
    meta.cycle_id = Log.state.vcd_readvars(vcd);
  }
};

int main(int argc, char **argv) {
  auto params = cuttlesim::params::of_cli(argc, argv);
  const std::string save_file = "save_restore.saved_state";

  // A more complex example would also want to save the state in extfuns_t, if
  // any — for example, if extfuns_t contains a Verilator module, it would have
  // to be compiled with --savable and saves separately.

  simulator sim{};
  sim.load(save_file); // Load state from disk
  sim.run(params.ncycles);
  sim.save(save_file); // Dump state to disk

  return 0;
}

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/local/share/verilator/include/")
// End:
