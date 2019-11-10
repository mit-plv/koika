#ifndef _PREAMBLE_HPP
#define _PREAMBLE_HPP

#include <cstddef> // For size_t
#include <cstdint>
#include <cstring> // For memcpy
#include <limits> // For std::numeric_limits used in prims::mask
#include <type_traits> // For std::conditional_t
#include <algorithm> // For std::max
#include <string> // For prims::display

#ifndef SIM_MINIMAL
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
using wbits_t = std::conditional_t<size <= 128, boost::multiprecision::uint128_t,
                std::conditional_t<size <= 256, boost::multiprecision::uint256_t,
                std::conditional_t<size <= 512, boost::multiprecision::uint512_t,
                std::conditional_t<size <= 1024, boost::multiprecision::uint1024_t,
                                   void>>>>;
template<std::size_t size>
using wsbits_t = std::conditional_t<size <= 128, boost::multiprecision::int128_t,
                 std::conditional_t<size <= 256, boost::multiprecision::int256_t,
                 std::conditional_t<size <= 512, boost::multiprecision::int512_t,
                 std::conditional_t<size <= 1024, boost::multiprecision::int1024_t,
                                    void>>>>;
#else
template<std::size_t size>
using wbits_t = void;
template<std::size_t size>
using wsbits_t = void;
#endif // #ifdef NEEDS_BOOST_MULTIPRECISION

struct unit {};

template<std::size_t size>
using bits_t = std::conditional_t<size ==  0, unit,
               std::conditional_t<size <=  8, std::uint8_t,
               std::conditional_t<size <= 16, std::uint16_t,
               std::conditional_t<size <= 32, std::uint32_t,
               std::conditional_t<size <= 64, std::uint64_t,
                                  wbits_t<size>>>>>>;

template<std::size_t size>
using sbits_t = std::conditional_t<size ==  0, unit,
                std::conditional_t<size <=  8, std::int8_t,
                std::conditional_t<size <= 16, std::int16_t,
                std::conditional_t<size <= 32, std::int32_t,
                std::conditional_t<size <= 64, std::int64_t,
                                   wsbits_t<size>>>>>>;

/// Literals

// https://stackoverflow.com/questions/57417154/
#define BITS(sz, c) (bits<sz>{UINT64_C(c)})
#define BITSV(sz, c) (bits_t<sz>{UINT64_C(c)})
#ifdef NEEDS_BOOST_MULTIPRECISION
using namespace boost::multiprecision::literals;
#define BITS_128(sz, c) (bits<sz>{c##_cppui128})
#define BITSV_128(sz, c) (bits_t<sz>{c##_cppui128})
#define BITS_256(sz, c) (bits<sz>{c##_cppui256})
#define BITSV_256(sz, c) (bits_t<sz>{c##_cppui256})
#define BITS_512(sz, c) (bits<sz>{c##_cppui512})
#define BITSV_512(sz, c) (bits_t<sz>{c##_cppui512})
#define BITS_1024(sz, c) (bits<sz>{c##_cppui1024})
#define BITSV_1024(sz, c) (bits_t<sz>{c##_cppui1024})
#endif

namespace prims {
  const unit _unused tt = {};

  template<typename T>
  T __attribute__((noreturn)) unreachable() {
    __builtin_unreachable();
  }

  template<std::size_t sz>
  struct bits {
    bits_t<sz> v;

    /// Casts

    static constexpr int padding_width() {
      return std::numeric_limits<bits_t<sz>>::digits - sz;
    }

    sbits_t<sz> to_sbits() const {
      sbits_t<sz> sx; // FIXME does this work with multiprecision?
      std::memcpy(&sx, &this->v, sizeof sx);
      return sx;
    }

    static bits<sz> of_sbits(sbits_t<sz> sx) {
      bits_t<sz> x; // FIXME does this work with multiprecision?
      std::memcpy(&x, &sx, sizeof x);
      return bits<sz>::mk(x);
    }

    sbits_t<sz> to_shifted_sbits() const {
      return to_sbits() << bits<sz>::padding_width();
    }

    static bits<sz> of_shifted_sbits(sbits_t<sz> sx) {
      // This constructs an int of the same bitsize as x, with the same
      // bitpattern, except that it uses the high bits of the storage type instead
      // of the low ones (e.g. 4'b1101 is represented as 8'b11010000).
      return of_sbits(sx) >> bits<sz>::padding_width();
    }

    /// Constants

    static constexpr bits<sz>
    ones() {
      // GCC and Clang are smart enough to elide the shift when digits == sz
      return bits<sz>::mk(std::numeric_limits<bits_t<sz>>::max() >> bits<sz>::padding_width());
    }

    /// Member functions

    explicit operator bool() const {
      return bool(v);
    }

    explicit operator bits_t<sz>() const {
      return v;
    }

    template<std::size_t idx_sz>
    bits<1> operator[](const bits<idx_sz> idx) const;

    bits<sz>& operator&=(const bits<sz> arg);
    bits<sz>& operator|=(const bits<sz> arg);
    bits<sz>& operator^=(const bits<sz> arg);
    bits<sz>& operator+=(const bits<sz> arg);
    bits<sz>& operator-=(const bits<sz> arg);
    bits<sz>& operator<<=(const std::size_t shift);
    bits<sz>& operator>>=(const std::size_t shift);
    template<std::size_t shift_sz> bits<sz>& operator<<=(const bits<shift_sz> shift);
    template<std::size_t shift_sz> bits<sz>& operator>>=(const bits<shift_sz> shift);

    /// Constructors

    template<typename T>
    static constexpr bits<sz> mk(T arg) {
      return bits{static_cast<bits_t<sz>>(arg)};
    }
  };

  /// Functions on bits

  template<std::size_t sz>
  static bits<sz> mask(bits<sz> arg) {
    return arg & bits<sz>::ones();
  }

  template<std::size_t ret_sz, std::size_t sz>
  static bits<ret_sz> widen(const bits<sz> arg) {
    return bits<ret_sz>::mk(arg.v);
  }

  template<std::size_t ret_sz, std::size_t sz>
  static bits<ret_sz> truncate(const bits<sz> arg) {
    return mask(widen<ret_sz, sz>(arg));
  }

  template<std::size_t sz>
  bits<1> msb(const bits<sz> arg) {
    return sz == 0 ? 0 : truncate<1, sz>(arg >> (sz - 1));
  }

  template<std::size_t sz>
  template<std::size_t idx_sz>
  bits<1> bits<sz>::operator[](const bits<idx_sz> idx) const {
    return truncate<1>((*this) >> idx);
  }

  template<std::size_t sz1, std::size_t idx, std::size_t width>
  bits<sz1> part_subst(const bits<sz1> data, const bits<width> repl) {
    const bits<sz1> mask = ~(widen<sz1, width>(bits<width>::ones()) << idx);
    return (data & mask) | (widen<sz1, width>(repl) << idx);
  }

  template<std::size_t sz1, std::size_t sz2, std::size_t width>
  bits<width> indexed_part(const bits<sz1> data, const bits<sz2> idx) {
    return truncate<width, sz1>(data >> idx);
  }

  template<std::size_t sz>
  bits<sz> operator&(const bits<sz> data1, const bits<sz> data2) {
    return bits<sz>::mk(data1.v & data2.v);
  }

  template<std::size_t sz>
  bits<sz> operator|(const bits<sz> data1, const bits<sz> data2) {
    return bits<sz>::mk(data1.v | data2.v);
  }

  template<std::size_t sz>
  bits<sz> operator^(const bits<sz> data1, const bits<sz> data2) {
    return bits<sz>::mk(data1.v ^ data2.v);
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<sz1> asr(const bits<sz1> data, const bits<sz2> shift) {
    return bits<sz1>::of_shifted_sbits(data.to_shifted_sbits() >> shift.v);
  }

  template<std::size_t sz1>
  bits<sz1> operator>>(const bits<sz1> data, const size_t shift) {
    return bits<sz1>::mk(data.v >> shift);
  }

  template<std::size_t sz1>
  bits<sz1> operator<<(const bits<sz1> data, const size_t shift) {
    return mask(bits<sz1>::mk(data.v << shift));
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<sz1> operator>>(const bits<sz1> data, const bits<sz2> shift) {
    return bits<sz1>::mk(data.v >> shift.v);
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<sz1> operator<<(const bits<sz1> data, const bits<sz2> shift) {
    return mask(bits<sz1>::mk(data.v << shift.v));
  }

  template<std::size_t sz>
  bits<1> operator==(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v == y.v);
  }

  template<std::size_t sz>
  bits<1> operator!=(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v != y.v);;
  }

  template<std::size_t sz>
  bits<sz> operator+(const bits<sz> x, const bits<sz> y) {
    return bits<sz>::mk(x.v + y.v);
  }

  template<std::size_t sz>
  bits<sz> operator-(const bits<sz> x, const bits<sz> y) {
    return mask(bits<sz>::mk(x.v + ~y.v + 1));
  }

  template<std::size_t sz>
  bits<1> operator<(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v < y.v);
  }

  template<std::size_t sz>
  bits<1> operator>(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v > y.v);
  }

  template<std::size_t sz>
  bits<1> operator<=(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v <= y.v);
  }

  template<std::size_t sz>
  bits<1> operator>=(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v >= y.v);
  }

  template<std::size_t sz>
  bits<1> slt(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() < y.to_shifted_sbits());
  }

  template<std::size_t sz>
  bits<1> sgt(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() > y.to_shifted_sbits());
  }

  template<std::size_t sz>
  bits<1> sle(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() <= y.to_shifted_sbits());
  }

  template<std::size_t sz>
  bits<1> sge(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() >= y.to_shifted_sbits());
  }

  template<std::size_t sz1, std::size_t sz2>
  bits<sz1 + sz2> concat(const bits<sz1> x, const bits<sz2> y) {
    return widen<sz1 + sz2, sz1>(x) << sz2 | widen<sz1 + sz2, sz2>(y);
  }

  template<std::size_t sz>
  bits<sz> operator~(const bits<sz> data) {
    return mask(bits<sz>::mk(~data.v));
  }

  template<std::size_t sz, std::size_t width>
  bits<std::max(sz, width)> zextl(const bits<sz> x) {
    return widen<std::max(sz, width), sz>(x);
  }

  template<std::size_t sz, std::size_t width>
  bits<std::max(sz, width)> zextr(const bits<sz> x) {
    return widen<std::max(sz, width), sz>(x) << (std::max(width, sz) - sz);
  }

  template<std::size_t sz1, std::size_t idx, std::size_t width>
  bits<width> part(const bits<sz1> data) {
    return truncate<width, sz1>(data >> idx);
  }

  template<std::size_t sz>
  bits<sz>& bits<sz>::operator&=(const bits<sz> arg) { return (*this = *this & arg); }
  template<std::size_t sz>
  bits<sz>& bits<sz>::operator|=(const bits<sz> arg) { return (*this = *this | arg); }
  template<std::size_t sz>
  bits<sz>& bits<sz>::operator^=(const bits<sz> arg) { return (*this = *this ^ arg); }
  template<std::size_t sz>
  bits<sz>& bits<sz>::operator+=(const bits<sz> arg) { return (*this = *this + arg); }
  template<std::size_t sz>
  bits<sz>& bits<sz>::operator-=(const bits<sz> arg) { return (*this = *this - arg); }
  template<std::size_t sz>
  bits<sz>& bits<sz>::operator<<=(const std::size_t shift) { return (*this = *this << shift); }
  template<std::size_t sz>
  bits<sz>& bits<sz>::operator>>=(const std::size_t shift) { return (*this = *this >> shift); }
  template<std::size_t sz> template<std::size_t shift_sz>
  bits<sz>& bits<sz>::operator<<=(const bits<shift_sz> shift) { return (*this = *this << shift); }
  template<std::size_t sz> template<std::size_t shift_sz>
  bits<sz>& bits<sz>::operator>>=(const bits<shift_sz> shift) { return (*this = *this >> shift); }

  static _unused unit display(_unused const std::string& msg) {
#ifndef SIM_MINIMAL
    std::cout << msg;
#endif
    return tt;
  }

  template<typename T>
  unit ignore(const T /*unused*/) {
    return tt;
  }

  // Forward-declared; our compiler defines one instance per structure type
  template<typename T, std::size_t sz> _unused T unpack(bits<sz> /*bits*/);
} // namespace prims

using prims::bits;

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
        unsigned int bit = prims::truncate<1, sz>(r.val >> (pos - 1u)).v;
        stream << bit;
      }
    break;
    case repr_style::hex:
      stream << (r.include_size ? "x" : "0x") << std::hex << +r.val.v;
      break;
    case repr_style::dec:
      stream << std::dec << +r.val.v;
      break;
    case repr_style::utf8:
      // FIXME: endianness problems: use arrays
      // FIXME: Decode array of bytes before printing
      for (size_t printed = 0; printed < sz; printed += 8) {
        stream << static_cast<unsigned char>(
            prims::truncate<8, sz>(r.val >> printed).v);
      }
      break;
    case repr_style::full:
      if (sz <= 64) {
        stream << _repr<sz>(r.val, repr_style::bin);
        stream << " (" << _repr<sz>(r.val, repr_style::hex);
        stream << ", " << _repr<sz>(r.val, repr_style::dec);
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

  [[nodiscard]] bool read0(T* const target, const T data, const rwset_t rLset) {
    bool ok = rwset.may_read0(rLset);
    *target = data;
    return ok;
  }

  [[nodiscard]] bool read1(T* const target, const rwset_t rLset) {
    bool ok = rwset.may_read1(rLset);
    *target = data0;
    rwset.r1 = true;
    return ok;
  }

  [[nodiscard]] bool write0(const T val, const rwset_t rLset) {
    bool ok = rwset.may_write0(rLset);
    data0 = val;
    rwset.w0 = true;
    return ok;
  }

  [[nodiscard]] bool write1(const T val, const rwset_t rLset) {
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
