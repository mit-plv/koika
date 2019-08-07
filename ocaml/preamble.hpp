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

struct unit_t {};

template<size_t size>
struct uint_t {
  using t = std::conditional_t<size ==  0, unit_t,
            std::conditional_t<size <=  8, std::uint8_t,
            std::conditional_t<size <= 16, std::uint16_t,
            std::conditional_t<size <= 32, std::uint32_t,
            std::conditional_t<size <= 64, std::uint64_t, void>>>>>;
};

namespace prims {
  const unit_t tt = {};

  template<typename T, size_t sz>
  T mask(T arg) {
    // GCC and Clang are smart enough to elide this when sz == ::digits
    return arg & (std::numeric_limits<T>::max() >> (std::numeric_limits<T>::digits - sz));
  }

  template<size_t sz1, size_t sz2>
  uint8_t sel(const typename uint_t<sz1>::t data, const typename uint_t<sz2>::t idx) {
    return (data >> idx) & 1;
  }

  template<size_t sz>
  typename uint_t<sz>::t lnot(const typename uint_t<sz>::t data, const unit_t) {
    return mask<typename uint_t<sz>::t, sz>(~data);
  }

  template<size_t sz>
  typename uint_t<sz>::t land(const typename uint_t<sz>::t data1, const typename uint_t<sz>::t data2) {
    return data1 & data2;
  }

  template<size_t sz>
  typename uint_t<sz>::t lor(const typename uint_t<sz>::t data1, const typename uint_t<sz>::t data2) {
    return data1 | data2;
  }

  template<size_t sz1, size_t sz2>
  typename uint_t<sz1>::t lsr(const typename uint_t<sz1>::t data, const typename uint_t<sz2>::t shift) {
    SIM_ASSERT(shift <= std::numeric_limits<typename uint_t<sz1>::t>::digits, "lsr: shift > size");
    return data >> shift;
  }

  template<size_t sz1, size_t sz2>
  typename uint_t<sz1>::t lsl(const typename uint_t<sz1>::t data, const typename uint_t<sz2>::t shift) {
    SIM_ASSERT(shift <= std::numeric_limits<typename uint_t<sz1>::t>::digits, "lsl: shift > size");
    return mask<typename uint_t<sz1>::t, sz1>(data << shift);
  }

  template<size_t sz>
  typename uint_t<sz>::t plus(const typename uint_t<sz>::t x, const typename uint_t<sz>::t y) {
    return mask<typename uint_t<sz>::t, sz>(x + y);
  }

  /// unit specializations
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
  // This yielded a ~25x speedup when rwset was inline
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
    reset();
    return data0;
  }

  reg_log_t() : rwset(), data0(0), data1(0) {}
};
