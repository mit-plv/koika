#include <cstdint>
#include <iostream>
#include <limits>

#define CHECK_RETURN(can_fire) { if (!can_fire) { return false; } }

namespace prims {
  struct unit_t {};
  unit_t tt = {};

  template<typename T>
  T mask(const size_t size) {
    return ~(T(0)) >> (std::numeric_limits<T>::digits - size);
  }

  template<typename T1, typename T2>
  bool sel(const T1 data, const T2 idx) {
    return (data >> idx) & 1;
  }

  template<typename T, size_t size>
  T lnot(const T data, const unit_t _unused) {
    return (~data) & mask<T>(size);
  }

  template<>
  bool lnot<bool, 1>(const bool data, const unit_t _unused) {
    return !data;
  }

  template<typename T, size_t size>
  T land(const T data1, const T data2) {
    return data1 & data2;
  }

  template<>
  bool land<bool, 1>(const bool data1, const bool data2) {
    return data1 && data2;
  }

  template<typename T, size_t size>
  T lor(const T data1, const T data2) {
    return data1 | data2;
  }

  template<>
  bool lor<bool, 1>(const bool data1, const bool data2) {
    return data1 || data2;
  }

  template<typename T1, typename T2>
  T1 lsr(const T1 data, const T2 shift) {
    return data >> shift;
  }

  template<typename T1, typename T2, size_t size>
  T1 lsl(const T1 data, const T2 shift) {
    return (data << shift) & mask<T1>(size);
  }

  template<typename T, size_t size>
  T plus(const T x, const T y) {
    return (x + y) & mask<T>(size);
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
    return !failed;
  }

  bool read1(T* target, const reg_log_t<T, size>& rL) {
    bool failed = rL.w1;
    r1 = true;
    *target = data0;
    return !failed;
  }

  bool write0(T val, const reg_log_t<T, size>& rL) {
    bool failed = r1 || w0 || w1 || rL.r1 || rL.w0 || rL.w1;
    w0 = true;
    data0 = val;
    return !failed;
  }

  bool write1(T val, const reg_log_t<T, size>& rL) {
    bool failed = w1 || rL.w1;
    w1 = true;
    data1 = val;
    return !failed;
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
