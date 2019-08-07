#ifndef collatz_HPP
#define collatz_HPP

//////////////
// PREAMBLE //
//////////////

#include "preamble.hpp"

////////////////////
// IMPLEMENTATION //
////////////////////

class collatz {
public:
  struct state_t {
    std::uint32_t r0 : 32; // FIXME: does this hurt?

    void dump() const {
      std::cout << "r0 = " << r0 << std::endl;
    }
  };

private:
  struct log_t {
    reg_log_t<std::uint32_t, 32> r0;
  };

  log_t Log;
  log_t log;
  state_t state;

  bool rule_divide() {
    log.r0.reset();

    { std::uint32_t v; CHECK_RETURN(log.r0.read0(&v, state.r0, Log.r0.rwset));
      { bool odd = prims::sel<std::uint32_t, std::uint8_t>(v, UINT8_C(0b00000));
        if (prims::lnot<bool, 1>(odd, prims::tt)) {
          CHECK_RETURN(log.r0.write0(prims::lsr<std::uint32_t, bool>(v, bool(0b1)), Log.r0.rwset));
        } else {
          return false;
        }
      }
    }

    Log.r0 = log.r0;
    return true;
  }

  bool rule_multiply() {
    log.r0.reset();

    { std::uint32_t v; CHECK_RETURN(log.r0.read1(&v, Log.r0.rwset));
      { bool odd = prims::sel<std::uint32_t, std::uint8_t>(v, UINT8_C(0b00000));
        if (odd) {
          CHECK_RETURN(log.r0.write1(prims::plus<std::uint32_t, 32>(prims::plus<std::uint32_t, 32>(prims::lsl<std::uint32_t, bool, 32>(v, bool(0b1)), v), UINT32_C(0b00000000000000000000000000000001)), Log.r0.rwset));
        } else {
          return false;
        }
      }
    }

    Log.r0 = log.r0;
    return true;
  }

public:
  explicit collatz(state_t init) : Log(), log(), state(init) {
    // FIXME is this second assignment necessary?
    Log.r0.data0 = log.r0.data0 = state.r0;
  }

  void cycle() {
    rule_divide();
    rule_multiply();
    state.r0 = Log.r0.commit();
  }

  void run(std::uint64_t ncycles) {
    for (std::uint64_t cycle_id = 0; cycle_id < ncycles; cycle_id++) {
      cycle();
    }
  }

  state_t observe() {
    return state;
  }
};

#endif
