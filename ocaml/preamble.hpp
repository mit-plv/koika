#include <cstdint>
#include <iostream>
#include <limits>

#define SIM_DEBUG

void _SIM_ASSERT(const char* repr,
                 bool expr,
                 const char* file,
                 const int line,
                 const char* err_msg) {
  if (!expr) {
    std::cerr << file << ":" << line << ": "
              << err_msg << std::endl
              << "Failed assertion: " << repr;
    abort();
  }
}

#ifdef SIM_DEBUG
#define SIM_ASSERT(expr, msg) \
  _SIM_ASSERT(#expr, expr, __FILE__, __LINE__, msg)
#else
#define SIM_ASSERT(expr, msg) ;
#endif

#define CHECK_RETURN(can_fire) { if (!can_fire) { return false; } }

namespace prims {
  struct unit_t {};
  const unit_t tt = {};

  template<typename T, size_t size>
  T mask(T arg) {
    // GCC and Clang are smart enough to elide this when sz == ::digits
    return arg & (std::numeric_limits<T>::max() >> (std::numeric_limits<T>::digits - sz));
  }

  template<typename T1, typename T2>
  bool sel(const T1 data, const T2 idx) {
    return (data >> idx) & 1;
  }

  template<typename T, size_t size>
  T lnot(const T data, const unit_t) {
    return mask<T, size>(~data);
  }

  template<typename T, size_t size>
  T land(const T data1, const T data2) {
    return data1 & data2;
  }

  template<typename T, size_t size>
  T lor(const T data1, const T data2) {
    return data1 | data2;
  }

  template<typename T1, typename T2>
  T1 lsr(const T1 data, const T2 shift) {
    SIM_ASSERT(shift <= std::numeric_limits<T1>::digits, "lsr: shift > size");
    return data >> shift;
  }

  template<typename T1, typename T2, size_t size>
  T1 lsl(const T1 data, const T2 shift) {
    SIM_ASSERT(shift <= std::numeric_limits<T1>::digits, "lsl: shift > size");
    return mask<T1, size>(data << shift);
  }

  template<typename T, size_t size>
  T plus(const T x, const T y) {
    return mask<T, size>(x + y);
  }

  /// unit specializations

  /// bool specializations

  template<>
  bool lnot<bool, 1>(const bool data, const unit_t) {
    return !data;
  }

  template<>
  bool land<bool, 1>(const bool data1, const bool data2) {
    return data1 && data2;
  }

  template<>
  bool lor<bool, 1>(const bool data1, const bool data2) {
    return data1 || data2;
  }
}

struct rwset_t {
  bool r1;
  bool w0;
  bool w1;

  bool may_read0(rwset_t rL) {
    return !(w1 || rL.w1 || rL.w0);
  }

  bool may_read1(rwset_t rL) {
    return !(rL.w1);
  }

  bool may_write0(rwset_t rL) {
    return !(r1 || w0 || w1 || rL.r1 || rL.w0 || rL.w1);
  }

  bool may_write1(rwset_t rL) {
    return !(w1 || rL.w1);
  }

  void reset() {
    r1 = w0 = w1 = false;
  }

  rwset_t() : r1(false), w0(false), w1(false) {}
};

template<typename T, size_t size>
struct reg_log_t {
  rwset_t rwset;

  // Reset alignment to prevent Clang from packing the fields together
  // This yields a ~25x speedup
  unsigned : 0;
  T data0 : size;
  unsigned : 0;
  T data1 : size;

  bool read0(T* const target, const T data, const rwset_t rLset) {
    bool ok = rwset.may_read0(rLset);
    *target = data;
    return ok;
  }

  bool read1(T* const target, const rwset_t rLset) {
    bool ok = rwset.may_read1(rLset);
    *target = data0;
    rwset.r1 = true;
    return ok;
  }

  bool write0(const T val, const rwset_t rLset) {
    bool ok = rwset.may_write0(rLset);
    data0 = val;
    rwset.w0 = true;
    return ok;
  }

  bool write1(const T val, const rwset_t rLset) {
    bool ok = rwset.may_write1(rLset);
    data1 = val;
    rwset.w1 = true;
    return ok;
  }

  void reset() {
    rwset.reset();
  }

  T commit() {
    if (rwset.w1) {
      data0 = data1;
    }
    rwset.reset();
    return data0;
  }

  reg_log_t() : rwset(), data0(0), data1(0) {}
};
