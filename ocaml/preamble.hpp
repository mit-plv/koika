#ifndef _PREAMBLE_HPP
#define _PREAMBLE_HPP

#include <cstdint>
#include <limits>
#include <type_traits>

#ifndef SIM_MINIMAL
#include <string>
#include <sstream>
#include <iostream>
#endif // #ifndef SIM_MINIMAL

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

#ifdef NEEDS_BOOST_MULTIPRECISION
#include <boost/multiprecision/cpp_int.hpp>
template<std::size_t size>
using big_uint_t = std::conditional_t<size <= 128, boost::multiprecision::uint128_t,
                   std::conditional_t<size <= 256, boost::multiprecision::uint256_t,
                   std::conditional_t<size <= 512, boost::multiprecision::uint512_t,
                   std::conditional_t<size <= 1024, boost::multiprecision::uint1024_t,
                                      void>>>>;
#else
template<std::size_t size>
using big_uint_t = void;
#endif // #ifdef NEEDS_BOOST_MULTIPRECISION

struct unit_t {};

template<std::size_t size>
using uint_t = std::conditional_t<size ==  0, unit_t,
               std::conditional_t<size <=  8, std::uint8_t,
               std::conditional_t<size <= 16, std::uint16_t,
               std::conditional_t<size <= 32, std::uint32_t,
               std::conditional_t<size <= 64, std::uint64_t,
                                  big_uint_t<size>>>>>>;

// https://stackoverflow.com/questions/57417154/
#define UINT8(c) static_cast<uint8_t>(UINT8_C(c))
#define UINT16(c) static_cast<uint16_t>(UINT16_C(c))
#define UINT32(c) static_cast<uint32_t>(UINT32_C(c))
#define UINT64(c) static_cast<uint64_t>(UINT64_C(c))
#ifdef NEEDS_BOOST_MULTIPRECISION
using namespace boost::multiprecision::literals;
#define UINT128(c) c##_cppui128
#define UINT256(c) c##_cppui256
#define UINT512(c) c##_cppui512
#define UINT1024(c) c##_cppui1024
#endif

namespace prims {
  const unit_t __attribute__((unused)) tt = {};

  template<typename T>
  T __attribute__((noreturn)) unreachable() {
    __builtin_unreachable();
  }

  template<std::size_t sz>
  uint_t<sz> ones() {
    // GCC and Clang are smart enough to elide this when shift_amount == 0
    constexpr uint8_t shift_amount = std::numeric_limits<uint_t<sz>>::digits - sz;
    return std::numeric_limits<uint_t<sz>>::max() >> shift_amount;
  }

  template<std::size_t sz>
  uint_t<sz> mask(const uint_t<sz> arg) {
    return arg & ones<sz>();
  }

  template<std::size_t sz, typename T>
  uint_t<sz> widen(const T arg) {
    return static_cast<uint_t<sz>>(arg);
  }

  template<std::size_t ret_sz, std::size_t arg_sz>
  uint_t<ret_sz> truncate(const uint_t<arg_sz> arg) {
    return mask<ret_sz>(widen<ret_sz>(arg));
  }

  template<std::size_t sz1, std::size_t sz2>
  uint_t<1> sel(const uint_t<sz1> data, const uint_t<sz2> idx) {
    return truncate<1,sz1>(data >> idx);
  }

  template<std::size_t sz1, std::size_t idx, std::size_t width>
  uint_t<width> part(const uint_t<sz1> data, const unit_t /*unused*/) {
    return truncate<width, sz1>(data >> idx);
  }

  template<std::size_t sz1, std::size_t idx, std::size_t width>
  uint_t<sz1> part_subst(const uint_t<sz1> data, const uint_t<width> repl) {
    const uint_t<sz1> mask = ~(widen<sz1>(ones<width>()) << idx);
    return (data & mask) | (widen<sz1>(repl) << idx);
  }

  template<std::size_t sz1, std::size_t sz2, std::size_t width>
  uint_t<width> indexed_part(const uint_t<sz1> data, const uint_t<sz2> idx) {
    return truncate<width, sz1>(data >> idx);
  }

  template<std::size_t sz>
  uint_t<sz> lnot(const uint_t<sz> data, const unit_t /*unused*/) {
    return mask<sz>(~data);
  }

  template<std::size_t sz>
  uint_t<sz> land(const uint_t<sz> data1, const uint_t<sz> data2) {
    return data1 & data2;
  }

  template<std::size_t sz>
  uint_t<sz> lor(const uint_t<sz> data1, const uint_t<sz> data2) {
    return data1 | data2;
  }

  template<std::size_t sz1, std::size_t sz2>
  uint_t<sz1> lsr(const uint_t<sz1> data, const uint_t<sz2> shift) {
    return data >> shift;
  }

  template<std::size_t sz1, std::size_t sz2>
  uint_t<sz1> lsl(const uint_t<sz1> data, const uint_t<sz2> shift) {
    return mask<sz1>(data << shift);
  }

  template<std::size_t sz>
  uint_t<sz> eq(const uint_t<sz> x, const uint_t<sz> y) {
    return x == y;
  }

  template<std::size_t sz>
  uint_t<sz> plus(const uint_t<sz> x, const uint_t<sz> y) {
    return mask<sz>(x + y);
  }

  template<std::size_t sz1, std::size_t sz2>
  uint_t<sz1 + sz2> concat(const uint_t<sz1> x, const uint_t<sz2> y) {
    return widen<sz1 + sz2>(x) << sz2 | y;
  }

  template<std::size_t sz, std::size_t nzeroes>
  uint_t<nzeroes + sz> zextl(const uint_t<sz> x, const unit_t /*unused*/) {
    return widen<nzeroes + sz>(x);
  }

  template<std::size_t sz, std::size_t nzeroes>
  uint_t<sz + nzeroes> zextr(const uint_t<sz> x, const unit_t /*unused*/) {
    return widen<sz + nzeroes>(x) << nzeroes;
  }

  // Forward-declared; our compiler defines one instance per structure type
  template<typename T, std::size_t sz> static T unpack(uint_t<sz> /*bits*/);
} // namespace prims

#ifndef SIM_MINIMAL
template<std::size_t sz>
std::string repr(const uint_t<sz> val) {
  std::ostringstream stream;
  stream << sz << "'";
  if (sz <= 64) {
    stream << "b";
    for (size_t pos = sz; pos > 0; pos--) {
      stream << prims::truncate<1, sz>(val >> (pos - 1u));
    }
    stream << " (0x" << std::hex << +val << ", " << std::dec << +val << ")";
  } else {
    stream << "x" << std::hex << +val;
  }
  return stream.str();
}
#endif // #ifndef SIM_MINIMAL

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

template<typename T>
struct reg_log_t {
  rwset_t rwset;

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

  reg_log_t() : data0(T{}), data1(T{}) {}
};

#define CHECK_RETURN(can_fire) { if (!(can_fire)) { return false; } }

#endif // #ifndef _PREAMBLE_HPP
