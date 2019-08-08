#include "collatz.generated.hpp"
// #include "collatz.handwritten.hpp"
#include <string>

int main(int argc, char** argv) {
  if (argc < 3) {
    std::exit(1);
  }

  auto r0 = static_cast<uint32_t>(std::strtoul(argv[1], nullptr, 10));
  uint64_t ncycles = std::strtoull(argv[2], nullptr, 10);

  collatz::state_t init = { .r0 = r0 };
  auto sim = collatz(init);
  sim.run(ncycles);
  sim.observe().dump();
}
