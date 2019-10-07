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
#include <iostream>
static inline void _sim_assert_fn(const char* repr,
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
#define _sim_assert(expr, msg) _sim_assert_fn(#expr, expr, __FILE__, __LINE__, msg)
#else
#define _sim_assert(expr, msg) ;
#endif // #ifdef SIM_DEBUG

#define _unused __attribute__((unused))

#ifdef NEEDS_BOOST_MULTIPRECISION
#include <boost/multiprecision/cpp_int.hpp>
template<std::size_t size>
using wbits = std::conditional_t<size <= 128, boost::multiprecision::uint128_t,
              std::conditional_t<size <= 256, boost::multiprecision::uint256_t,
              std::conditional_t<size <= 512, boost::multiprecision::uint512_t,
              std::conditional_t<size <= 1024, boost::multiprecision::uint1024_t,
                                 void>>>>;
#else
template<std::size_t size>
using wbits = void;
#endif // #ifdef NEEDS_BOOST_MULTIPRECISION

struct unit {};

template<std::size_t size>
using bits = std::conditional_t<size ==  0, unit,
             std::conditional_t<size <=  8, std::uint8_t,
             std::conditional_t<size <= 16, std::uint16_t,
             std::conditional_t<size <= 32, std::uint32_t,
             std::conditional_t<size <= 64, std::uint64_t,
                                wbits<size>>>>>>;

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
  const unit __attribute__((unused)) tt = {};

  template<typename T>
  T __attribute__((noreturn)) unreachable() {
    __builtin_unreachable();
  }

  template<std::size_t sz>
  bits<sz> ones() {
    // GCC and Clang are smart enough to elide this when shift_amount == 0
    constexpr uint8_t shift_amount = std::numeric_limits<bits<sz>>::digits - sz;
    return std::numeric_limits<bits<sz>>::max() >> shift_amount;
  }

  template<std::size_t sz>
  bits<sz> mask(const bits<sz> arg) {
    return arg & ones<sz>();
  }

  template<std::size_t sz, typename T>
  bits<sz> widen(const T arg) {
    return static_cast<bits<sz>>(arg);
  }

  template<std::size_t ret_sz, std::size_t arg_sz>
  bits<ret_sz> truncate(const bits<arg_sz> arg) {
    return mask<ret_sz>(widen<ret_sz>(arg));
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<1> sel(const bits<sz1> data, const bits<sz2> idx) {
    return truncate<1,sz1>(data >> idx);
  }

  template<std::size_t sz1, std::size_t idx, std::size_t width>
  bits<width> part(const bits<sz1> data, const unit /*unused*/) {
    return truncate<width, sz1>(data >> idx);
  }

  template<std::size_t sz1, std::size_t idx, std::size_t width>
  bits<sz1> part_subst(const bits<sz1> data, const bits<width> repl) {
    const bits<sz1> mask = ~(widen<sz1>(ones<width>()) << idx);
    return (data & mask) | (widen<sz1>(repl) << idx);
  }

  template<std::size_t sz1, std::size_t sz2, std::size_t width>
  bits<width> indexed_part(const bits<sz1> data, const bits<sz2> idx) {
    return truncate<width, sz1>(data >> idx);
  }

  template<std::size_t sz>
  bits<sz> lnot(const bits<sz> data, const unit /*unused*/) {
    return mask<sz>(~data);
  }

  template<std::size_t sz>
  bits<sz> land(const bits<sz> data1, const bits<sz> data2) {
    return data1 & data2;
  }

  template<std::size_t sz>
  bits<sz> lor(const bits<sz> data1, const bits<sz> data2) {
    return data1 | data2;
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<sz1> lsr(const bits<sz1> data, const bits<sz2> shift) {
    return data >> shift;
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<sz1> lsl(const bits<sz1> data, const bits<sz2> shift) {
    return mask<sz1>(data << shift);
  }

  template<std::size_t sz>
  bits<sz> eq(const bits<sz> x, const bits<sz> y) {
    return x == y;
  }

  template<std::size_t sz>
  bits<sz> plus(const bits<sz> x, const bits<sz> y) {
    return mask<sz>(x + y);
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<sz1 + sz2> concat(const bits<sz1> x, const bits<sz2> y) {
    return widen<sz1 + sz2>(x) << sz2 | y;
  }

  template<std::size_t sz, std::size_t width>
  bits<std::max(sz, width)> zextl(const bits<sz> x, const unit /*unused*/) {
    return widen<std::max(sz, width)>(x);
  }

  template<std::size_t sz, std::size_t width>
  bits<std::max(sz, width)> zextr(const bits<sz> x, const unit /*unused*/) {
    return widen<std::max(sz, width)>(x) << (std::max(width, sz) - sz);
  }

  // Forward-declared; our compiler defines one instance per structure type
  template<typename T, std::size_t sz> _unused T unpack(bits<sz> /*bits*/);
} // namespace prims

#ifndef SIM_MINIMAL
enum class repr_style {
  full, hex, dec, bin, utf8
};

template<std::size_t sz>
struct _repr {
  bits<sz> val;
  repr_style style;
  bool include_size;

  _repr(bits<sz> val,
        repr_style style = repr_style::full,
        bool include_size = false)
    : val(val), style(style), include_size(include_size) {}

  friend std::ostream& operator<<(std::ostream& stream, const _repr& r) {
    if (r.include_size && r.style != repr_style::utf8) {
      stream << sz << "'";
    }

    switch (r.style) {
    case repr_style::bin:
      stream << (r.include_size ? "b" : "0b");
      for (size_t pos = sz; pos > 0; pos--) {
        stream << uint(prims::truncate<1, sz>(r.val >> (pos - 1u)));
      }
    break;
    case repr_style::hex:
      stream << (r.include_size ? "x" : "0x") << std::hex << +r.val;
      break;
    case repr_style::dec:
      stream << std::dec << +r.val;
      break;
    case repr_style::utf8:
      stream << '"'; // FIXME: endianness problems: use arrays
      for (size_t printed = 0; printed < sz; printed += 8) {
        stream << static_cast<unsigned char>(prims::truncate<8, sz>(r.val >> printed));
      }
      stream << '"';
      break;
    case repr_style::full:
      if (sz <= 64) {
        stream << _repr<sz>(r.val, repr_style::bin);
        stream << " ("; _repr<sz>(r.val, repr_style::hex);
        stream << ", "; _repr<sz>(r.val, repr_style::dec);
        stream << ")";
      } else {
        stream << _repr<sz>(r.val, repr_style::hex, r.include_size);
      }
      break;
    }

    return stream;
  }
};

template<std::size_t sz>
std::string repr(const bits<sz> val, const repr_style style = repr_style::full) {
  std::ostringstream stream;
  stream << _repr<sz>(val, style, true);
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
