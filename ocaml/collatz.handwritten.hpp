#ifndef SIM_collatz_HPP
#define SIM_collatz_HPP

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
    uint_t<32>::t r0 : 32; // FIXME: does this hurt?

    void dump() const {
      std::cout << "r0 = " << r0 << std::endl;
    }
  };

private:
  struct log_t {
    reg_log_t<32> r0;
  };

  log_t Log;
  log_t log;
  state_t state;

  bool rule_divide() {
    log.r0.reset(Log.r0);

    { uint_t<32>::t v; CHECK_RETURN(log.r0.read0(&v, state.r0, Log.r0.rwset));
      { uint_t<1>::t odd = prims::sel<32, 5>(v, UINT8(0b00000));
        if (bool(prims::lnot<1>(odd, prims::tt))) {
          CHECK_RETURN(log.r0.write0(prims::lsr<32, 1>(v, UINT8(0b1)), Log.r0.rwset));
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

    { uint_t<32>::t v; CHECK_RETURN(log.r0.read1(&v, Log.r0.rwset));
      { uint_t<1>::t odd = prims::sel<32, 5>(v, UINT8(0b00000));
        if (bool(odd)) {
          CHECK_RETURN(log.r0.write1(prims::plus<32>(prims::plus<32>(prims::lsl<32, 1>(v, UINT8(0b1)), v), UINT32(0b00000000000000000000000000000001)), Log.r0.rwset));
        } else {
          return false;
        }
      }
    }

    Log.r0 = log.r0;
    return true;
  }

public:
  explicit collatz(state_t init) : state(init) {
    Log.r0.data0 = state.r0;
  }

  void cycle() {
    rule_divide();
    rule_multiply();
    state.r0 = Log.r0.commit();
  }

  template<typename T>
  void run(T ncycles) {
    for (T cycle_id = 0; cycle_id < ncycles; cycle_id++) {
      cycle();
    }
  }

  state_t observe() {
    return state;
  }
};

#endif
