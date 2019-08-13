#ifndef _PREAMBLE_HPP
#define _PREAMBLE_HPP

#include <cstdint>
#include <string>
#include <sstream>
#include <iostream>
#include <limits>

#ifdef SIM_DEBUG
inline void _SIM_ASSERT(const char* repr,
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

#define SIM_ASSERT(expr, msg) \
  _SIM_ASSERT(#expr, expr, __FILE__, __LINE__, msg)
#else
#define SIM_ASSERT(expr, msg) ;
#endif // #ifdef SIM_DEBUG

struct unit_t {};

#ifdef NEEDS_BOOST_MULTIPRECISION
#include <boost/multiprecision/cpp_int.hpp>
template<size_t size>
struct big_uint_t {
  using t = std::conditional_t<size <= 128, boost::multiprecision::uint128_t,
            std::conditional_t<size <= 256, boost::multiprecision::uint256_t,
            std::conditional_t<size <= 512, boost::multiprecision::uint512_t,
            std::conditional_t<size <= 1024, boost::multiprecision::uint1024_t,
                               void>>>>;
};
#else
template<size_t size>
struct big_uint_t {
  using t = void;
};
#endif // #ifdef NEEDS_BOOST_MULTIPRECISION

template<size_t size>
struct uint_t {
  using t = std::conditional_t<size ==  0, unit_t,
            std::conditional_t<size <=  8, std::uint8_t,
            std::conditional_t<size <= 16, std::uint16_t,
            std::conditional_t<size <= 32, std::uint32_t,
            std::conditional_t<size <= 64, std::uint64_t,
                               typename big_uint_t<size>::t>>>>>;
};

#define UINT_T(sz) typename uint_t<sz>::t
#define CONST_UINT_T(sz) const typename uint_t<sz>::t

// https://stackoverflow.com/questions/57417154/
#define UINT8(c) static_cast<uint8_t>(UINT8_C(c))
#define UINT16(c) static_cast<uint16_t>(UINT16_C(c))
#define UINT32(c) static_cast<uint32_t>(UINT32_C(c))
#define UINT64(c) static_cast<uint64_t>(UINT64_C(c))
#ifdef NEEDS_BOOST_MULTIPRECISION
#define UINT128(c) boost::multiprecision::uint128_t(#c)
#define UINT256(c) boost::multiprecision::uint256_t(#c)
#define UINT512(c) boost::multiprecision::uint512_t(#c)
#define UINT1024(c) boost::multiprecision::uint1024_t(#c)
#endif

#define CHECK_SHIFT(nbits, sz, msg) \
  SIM_ASSERT(idx <= std::numeric_limits<UINT_T(sz)>::digits, msg)

namespace prims {
  const unit_t tt = {};

  template<size_t sz>
  UINT_T(sz) __attribute__((noreturn)) unreachable() {
    __builtin_unreachable();
  }

  template<size_t sz>
  UINT_T(sz) mask(CONST_UINT_T(sz) arg) {
    // GCC and Clang are smart enough to elide this when shift_amount == 0
    constexpr uint8_t shift_amount = std::numeric_limits<UINT_T(sz)>::digits - sz;
    const UINT_T(sz) bitmask = std::numeric_limits<UINT_T(sz)>::max() >> shift_amount;
    return arg & bitmask;
  }

  template<size_t ret_sz, size_t arg_sz>
  UINT_T(ret_sz) truncate(CONST_UINT_T(arg_sz) arg) {
    return mask<ret_sz>(static_cast<UINT_T(ret_sz)>(arg));
  }

  template<size_t sz1, size_t sz2>
  UINT_T(1) sel(CONST_UINT_T(sz1) data, CONST_UINT_T(sz2) idx) {
    CHECK_SHIFT(idx, sz1, "sel: idx > size");
    return truncate<1,sz1>(data >> idx);
  }

  template<size_t sz1, size_t sz2, size_t width>
  UINT_T(width) part(CONST_UINT_T(sz1) data, CONST_UINT_T(sz2) idx) {
    CHECK_SHIFT(idx, sz1, "part: idx > size");
    return truncate<width, sz1>(data >> idx);
  }

  template<size_t sz>
  UINT_T(sz) lnot(CONST_UINT_T(sz) data, const unit_t /*unused*/) {
    return mask<sz>(~data);
  }

  template<size_t sz>
  UINT_T(sz) land(CONST_UINT_T(sz) data1, CONST_UINT_T(sz) data2) {
    return data1 & data2;
  }

  template<size_t sz>
  UINT_T(sz) lor(CONST_UINT_T(sz) data1, CONST_UINT_T(sz) data2) {
    return data1 | data2;
  }

  template<size_t sz1, size_t sz2>
  UINT_T(sz1) lsr(CONST_UINT_T(sz1) data, CONST_UINT_T(sz2) shift) {
    CHECK_SHIFT(shift, sz1, "lsr: shift > size");
    return data >> shift;
  }

  template<size_t sz1, size_t sz2>
  UINT_T(sz1) lsl(CONST_UINT_T(sz1) data, CONST_UINT_T(sz2) shift) {
    CHECK_SHIFT(shift, sz1, "lsl: shift > size");
    return mask<sz1>(data << shift);
  }

  template<size_t sz>
  UINT_T(sz) eq(CONST_UINT_T(sz) x, CONST_UINT_T(sz) y) {
    return x == y;
  }

  template<size_t sz>
  UINT_T(sz) plus(CONST_UINT_T(sz) x, CONST_UINT_T(sz) y) {
    return mask<sz>(x + y);
  }

  template<size_t sz1, size_t sz2>
  UINT_T(sz1 + sz2) concat(CONST_UINT_T(sz1) x, CONST_UINT_T(sz2) y) {
    return static_cast<UINT_T(sz1 + sz2)>(x) << sz2 | y;
  }

  template<size_t sz, size_t nzeroes>
  UINT_T(nzeroes + sz) zextl(CONST_UINT_T(sz) x, const unit_t /*unused*/) {
    return static_cast<UINT_T(nzeroes + sz)>(x);
  }

  template<size_t sz, size_t nzeroes>
  UINT_T(sz + nzeroes) zextr(CONST_UINT_T(sz) x, const unit_t /*unused*/) {
    return static_cast<UINT_T(sz + nzeroes)>(x) << nzeroes;
  }
} // namespace prims

template<size_t sz>
std::string uint_str(CONST_UINT_T(sz) val) {
  std::ostringstream stream;
  stream << sz << "'";
  if (sz <= 64) {
    stream << "b";
    for (int pos = sz - 1; pos >= 0; pos--) {
      bool bit = val >> pos != 0;
      stream << (bit ? "1" : "0");
    }
    stream << " (0x" << std::hex << val << ", " << std::dec << val << ")";
  } else {
    stream << "x" << std::hex << val;
  }
  return stream.str();
};

struct rwset_t {
  bool r1 : 1; // FIXME does adding :1 always help?
  bool w0 : 1;
  bool w1 : 1;

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

template<size_t size>
struct reg_log_t {
  rwset_t rwset;
  using T = typename uint_t<size>::t;

  // Reset alignment to prevent Clang from packing the fields together
  // This yielded a ~25x speedup when rwset was inline
  unsigned : 0;
  T data0;
  unsigned : 0;
  T data1;

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

  void reset(reg_log_t other) {
    rwset.reset();
    data0 = other.data0;
    data1 = other.data1;
  }

  T commit() {
    if (rwset.w1) {
      data0 = data1;
    }
    rwset.reset();
    return data0;
  }

  reg_log_t() : data0(0), data1(0) {}
};

#define CHECK_RETURN(can_fire) { if (!(can_fire)) { return false; } }

#endif // #ifndef _PREAMBLE_HPP
