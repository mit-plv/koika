#ifndef __COLLATZ_HPP__
#define __COLLATZ_HPP__

//////////////
// PREAMBLE //
//////////////

#include <cstdint>
#include <iostream>
#include <limits>

#define CHECK_RETURN(can_fire) { if (!can_fire) { return false; } }

namespace prims {
  template<typename T>
  T mask(const size_t size) {
    return ~(T(0)) >> (std::numeric_limits<T>::digits - size);
  }

  template<typename T1, typename T2, size_t size>
  T1 lsr(const T1 data, const T2 shift) {
    return (data >> shift) & mask<T1>(size);
  }

  template<typename T1, typename T2, size_t size>
  T1 lsl(const T1 data, const T2 shift) {
    return (data << shift) & mask<T1>(size);
  }

  template<typename T, size_t size>
  T plus(const T x, const T y) {
    return (x + y) & mask<T>(size);
  }

  template<typename T1, typename T2>
  bool sel(const T1 data, const T2 idx) {
    return (data >> idx) & 1;
  }

  template<typename T, size_t size>
  T lnot(const T data) {
    return (~data) & mask<T>(size);
  }

  template<typename T, size_t size>
  bool lnot(const bool data) {
    return !data;
  }
}

template<typename T, size_t size>
struct reg_log_t {
  bool r1;
  bool w0;
  bool w1;

  // Reset alignment to prevent Clang from packing the fields together
  // This yields a ~25x speedup
  unsigned : 0;
  T data0 : size;
  unsigned : 0;
  T data1 : size;

  bool read0(T* target, T data, const reg_log_t<T, size>& rL) {
    bool failed = w1 || rL.w1 || rL.w0;
    *target = data;
    return failed;
  }

  bool read1(T* target, const reg_log_t<T, size>& rL) {
    bool failed = rL.w1;
    r1 = true;
    *target = data0;
    return failed;
  }

  bool write0(T val, const reg_log_t<T, size>& rL) {
    bool failed = r1 || w0 || w1 || rL.r1 || rL.w0 || rL.w1;
    w0 = true;
    data0 = val;
    return failed;
  }

  bool write1(T val, const reg_log_t<T, size>& rL) {
    bool failed = w1 || rL.w1;
    w1 = true;
    data1 = val;
    return failed;
  }

  void reset(reg_log_t rLog) {
    r1 = w0 = w1 = false;
    data0 = rLog.data0;
    data1 = rLog.data1;
  }

  T commit() {
    if (w1) {
      data0 = data1;
    }
    r1 = w0 = w1 = false;
    return data0;
  }

  reg_log_t() : r1(false), w0(false), w1(false),
                data0(0), data1(0) {}
};

////////////////////
// AUTO-GENERATED //
////////////////////

class Collatz {
public:
  struct state_t {
    uint32_t r0 : 32; // FIXME: does this hurt?

    void dump() {
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
        if (prims::lnot<bool, 1>(odd)) {
          CHECK_RETURN(log.r0.write0(prims::lsr<uint32_t, int, 32>(v, 1), Log.r0));
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
  explicit Collatz(state_t init) : Log(), log(), state(init) {
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
