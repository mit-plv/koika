#include "collatz.hpp"
#include <string>

int main(int argc, char** argv) {
  if (argc < 3) {
    std::exit(1);
  }

  auto r0 = (uint32_t)std::stoi(argv[1]);
  auto ncycles = std::stoull(argv[2]);

  Collatz::state_t init = { .r0 = r0 };
  auto sim = Collatz(init);
  sim.run(ncycles);
  sim.dump();
}
