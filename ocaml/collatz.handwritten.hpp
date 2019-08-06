#ifndef __COLLATZ_HPP__
#define __COLLATZ_HPP__

//////////////
// PREAMBLE //
//////////////

#include "preamble.hpp"

////////////////////
// AUTO-GENERATED //
////////////////////

class collatz {
public:
  struct state_t {
    uint32_t r0 : 32; // FIXME: does this hurt?

    void dump() const {
      std::cout << "r0 = " << r0 << std::endl;
    }
  };

private:
  struct log_t {
    reg_log_t<uint32_t, 32> r0;
  };

  log_t Log;
  log_t log;
  state_t state;

  bool rule_divide() {
    log.r0.reset(Log.r0);

    { uint32_t v; CHECK_RETURN(log.r0.read0(&v, state.r0, Log.r0));
      { auto odd = prims::sel<uint32_t, uint8_t>(v, 0);
        if (prims::lnot<bool, 1>(odd, prims::tt)) {
          CHECK_RETURN(log.r0.write0(prims::lsr<uint32_t, int>(v, 1), Log.r0));
        } else {
          return false;
        }
      }
    }

    Log.r0 = log.r0;
    return true;
  }

  bool rule_multiply() {
    log.r0.reset(Log.r0);

    { uint32_t v; CHECK_RETURN(log.r0.read1(&v, Log.r0));
      { auto odd = prims::sel<uint32_t, uint8_t>(v, 0);
        if (odd) {
          CHECK_RETURN(log.r0.write1(prims::plus<uint32_t, 32>(prims::plus<uint32_t, 32>(prims::lsl<uint32_t, uint8_t, 32>(v, 1), v), 1), Log.r0));
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
    Log.r0.data0 = state.r0;
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
