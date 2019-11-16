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

#if defined(__clang__)
#define _unoptimized __attribute__((optnone))
#elif defined(__GNUG__)
#define _unoptimized __attribute__((optimize("O0")))
#else
#define _unoptimized
#endif

#if defined(SIM_MINIMAL) && defined(SIM_KEEP_DISPLAY)
#define _display_unoptimized _unoptimized
#else
#define _display_unoptimized
#endif

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

struct unit_t {};

template<std::size_t size>
using bits_t = std::conditional_t<size ==  0, unit_t,
               std::conditional_t<size <=  8, std::uint8_t,
               std::conditional_t<size <= 16, std::uint16_t,
               std::conditional_t<size <= 32, std::uint32_t,
               std::conditional_t<size <= 64, std::uint64_t,
                                  wbits_t<size>>>>>>;

template<std::size_t size>
using sbits_t = std::conditional_t<size ==  0, unit_t,
                std::conditional_t<size <=  8, std::int8_t,
                std::conditional_t<size <= 16, std::int16_t,
                std::conditional_t<size <= 32, std::int32_t,
                std::conditional_t<size <= 64, std::int64_t,
                                   wsbits_t<size>>>>>>;

namespace prims {
  template<typename T>
  T __attribute__((noreturn)) unreachable() {
    __builtin_unreachable();
  }

  static _unused void assume(bool condition) {
    if (!condition) { unreachable<void>(); }
  }

  template<std::size_t sz>
  struct bits {
    bits_t<sz> v;

    /// Representation invariant

    static constexpr int padding_width =
      std::numeric_limits<bits_t<sz>>::digits - sz;

    // Not constexpr because Boost's >> isn't constexpr
    static const bits_t<sz> bitmask() {
      auto pw = bits<sz>::padding_width; // https://stackoverflow.com/questions/8452952/
      return std::numeric_limits<bits_t<sz>>::max() >> pw;
    }

    void invariant() const {
      // Knowing this invariant can sometimes help the compiler; it does in
      // particular in operator bool().
      assume(v <= bitmask());
    }

    /// Casts

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
      return to_sbits() << bits<sz>::padding_width;
    }

    static bits<sz> of_shifted_sbits(sbits_t<sz> sx) {
      // This constructs an int of the same bitsize as x, with the same
      // bitpattern, except that it uses the high bits of the storage type instead
      // of the low ones (e.g. 4'b1101 is represented as 8'b11010000).
      return of_sbits(sx) >> bits<sz>::padding_width;
    }

    /// Constants

    static const bits<sz> ones() {
      return bits<sz>::mk(bits<sz>::bitmask());
    }

    /// Member functions

    explicit operator bool() const {
      invariant(); // Knowing this invariant helps GCC generate better code
      return bool(v); // Writing bool(v & bitmask()) works just as well
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

  using unit = bits<0>;
  const unit _unused tt{};

  namespace literal_parsing {
    using std::size_t;

    template<uint base, char c>
    constexpr bool valid_digit() {
      if (base == 2) {
        return c == '0' || c == '1';
      } else if (base == 10) {
        return '0' <= c && c <= '9';
      } else if (base == 16) {
        return (('0' <= c && c <= '9') ||
                ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F'));
      }
    }

    template <uint base, char c>
    constexpr uint parse_digit() {
      static_assert(base == 2 || base == 10 || base == 16, "Invalid base");
      static_assert(valid_digit<base, c>(), "Invalid digit");
      if ('0' <= c && c <= '9') {
        return c - '0';
      } else if ('a' <= c && c <= 'f') {
        return c - 'a' + 10;
      } else if ('A' <= c && c <= 'F') {
        return c - 'A' + 10;
      }
    }

    template <uint base, uint64_t max, uint64_t num>
    constexpr uint64_t parse_u64() {
      return num;
    }

    template <uint base, uint64_t max, uint64_t num, char c, char... cs>
    constexpr uint64_t parse_u64() {
      const uint64_t digit = parse_digit<base, c>();
      static_assert((max - digit) / base >= num, "Overflow in literal parsing");
      return parse_u64<base, max, base * num + digit, cs...>();
    }

    enum class parser { u64, u128, u256, u512, u1024, unsupported };

    template <parser p, uint base, size_t sz, char... cs>
    struct parse_number {
      static_assert(p != parser::unsupported, "Unsupported bitsize.");
#ifndef NEEDS_BOOST_MULTIPRECISION
      static_assert(p == parser::u64, "Needs boost::multiprecision to parse numbers with > 64 bits.");
#endif
      static_assert(p == parser::u64 || base == 16, "boost::multiprecision only supports base-16 literals.");
    };

    template <uint base, size_t sz, char... cs>
    struct parse_number<parser::u64, base, sz, cs...> {
      static constexpr uint64_t max = std::numeric_limits<bits_t<sz>>::max() >> bits<sz>::padding_width;
      static constexpr bits_t<sz> v = parse_u64<base, max, 0, cs...>();
    };

#ifdef NEEDS_BOOST_MULTIPRECISION
    using namespace boost::multiprecision::literals;

    template <size_t sz, char... cs>
    struct parse_number<parser::u128, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui128<'0', 'x', cs...>();
    };

    template <size_t sz, char... cs>
    struct parse_number<parser::u256, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui256<'0', 'x', cs...>();
    };

    template <size_t sz, char... cs>
    struct parse_number<parser::u512, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui512<'0', 'x', cs...>();
    };

    template <size_t sz, char... cs>
    struct parse_number<parser::u1024, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui1024<'0', 'x', cs...>();
    };
#endif

    constexpr parser get_parser(size_t sz) {
      if (sz <= 64) {
        return parser::u64;
      } else if (sz <= 128) {
        return parser::u128;
      } else if (sz <= 256) {
        return parser::u256;
      } else if (sz <= 512) {
        return parser::u512;
      } else if (sz <= 1024) {
        return parser::u1024;
      } else {
        return parser::unsupported;
      }
    }

    template <bool imm, uint base, size_t sz, char... cs>
    struct parse_literal;

    template <uint base, size_t sz, char... cs>
    struct parse_literal<true, base, sz, '\'', cs...> {
      static_assert(sz <= 64, "Immediates can't have size > 64.");
      static constexpr bits_t<sz> v = parse_number<get_parser(sz), base, sz, cs...>::v;
    };

    template <uint base, size_t sz, char... cs>
    struct parse_literal<false, base, sz, '\'', cs...> {
      static constexpr bits<sz> v = bits<sz>{parse_number<get_parser(sz), base, sz, cs...>::v};
    };

    template <bool imm, uint base, size_t sz, char c, char... cs>
    struct parse_literal<imm, base, sz, c, cs...> {
      static constexpr size_t sz_digit = parse_digit<10, c>();
      static constexpr auto v = parse_literal<imm, base, 10 * sz + sz_digit, cs...>::v;
    };

    template <bool imm, char... cs>
    using parse_bin = parse_literal<imm, 2, 0, cs...>;

    template <bool imm, char... cs>
    using parse_dec = parse_literal<imm, 10, 0, cs...>;

    template <bool imm, char... cs> struct parse_hex;
    template <bool imm, char c0, char c1, char... cs>
    struct parse_hex<imm, c0, c1, cs...> {
      static_assert(c0 == '0' && c1 == 'x', "Hex literal must start with 0x");
      static constexpr auto v = parse_literal<imm, 16, 0, cs...>::v;
    };
  }

  namespace literals {
    // ‘auto v = …; return v’: see
    // * https://stackoverflow.com/questions/8452952/c-linker-error-with-class-static-constexpr
    // * https://stackoverflow.com/questions/45970113/
    // * https://stackoverflow.com/a/18940384/695591
    // … or compile with -std=c++17

    // Binary representation: 4'0010_b
    template <char... cs> constexpr auto operator "" _b() {
      constexpr auto v = literal_parsing::parse_bin<false, cs...>::v; return v;
    }

    // Decimal representation: 11'1234_d
    template <char... cs> constexpr auto operator "" _d() {
      constexpr auto v = literal_parsing::parse_dec<false, cs...>::v; return v;
    }

    // Hex representation: 0x16'abcd_x
    template <char... cs> constexpr auto operator "" _x() {
      constexpr auto v = literal_parsing::parse_hex<false, cs...>::v; return v;
    }

    // Immediate binary representation: 4'0010_bv
    template <char... cs> constexpr auto operator "" _bv() {
      constexpr auto v = literal_parsing::parse_bin<true, cs...>::v; return v;
    }

    // Immediate decimal representation: 11'1234_dv
    template <char... cs> constexpr auto operator "" _dv() {
      constexpr auto v = literal_parsing::parse_dec<true, cs...>::v; return v;
    }

    // Immediate hex representation: 0x16'abcd_xv
    template <char... cs> constexpr auto operator "" _xv() {
      constexpr auto v = literal_parsing::parse_hex<true, cs...>::v; return v;
    }
  }

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
  bits<sz1> slice_subst(const bits<sz1> data, const bits<width> repl) {
    const bits<sz1> mask = ~(widen<sz1, width>(bits<width>::ones()) << idx);
    return (data & mask) | (widen<sz1, width>(repl) << idx);
  }

  template<std::size_t sz1, std::size_t sz2, std::size_t width>
  bits<width> indexed_slice(const bits<sz1> data, const bits<sz2> idx) {
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
  bits<std::max(sz, width)> sext(const bits<sz> x) {
    constexpr std::size_t newsz = std::max(sz, width);
    constexpr std::size_t nbits = width >= sz ? width - sz : std::size_t{0};
    return bits<newsz>::of_shifted_sbits((widen<newsz, sz>(x) << nbits).to_shifted_sbits() >> nbits);
  }

  template<std::size_t sz, std::size_t width>
  bits<std::max(sz, width)> zextl(const bits<sz> x) {
    return widen<std::max(sz, width), sz>(x);
  }

  template<std::size_t sz, std::size_t width>
  bits<std::max(sz, width)> zextr(const bits<sz> x) {
    return widen<std::max(sz, width), sz>(x) << (std::max(width, sz) - sz);
  }

  template<std::size_t sz, std::size_t times> struct repeat_t {
    static const bits<sz * times> v(bits<sz> bs) {
      return concat(repeat_t<sz, times - 1>::v(bs), bs);
    };
  };

  template<std::size_t sz> struct repeat_t<sz, 0> {
    static const bits<0> v(bits<sz>) { return tt; };
  };

  template<std::size_t times> struct repeat_t<1, times> {
    static const bits<times> v(bits<1> bs) { return sext<1, times>(bs); };
  };

  template<std::size_t sz> struct repeat_t<sz, 1> {
    static constexpr auto v(bits<sz> bs) { return bs; }
  };

  template<std::size_t sz, std::size_t times>
  bits<sz * times> repeat(const bits<sz> bs) {
    return repeat_t<sz, times>::v(bs);
  }

  template<std::size_t sz1, std::size_t idx, std::size_t width>
  bits<width> slice(const bits<sz1> data) {
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

#ifdef SIM_MINIMAL
  static _unused _display_unoptimized unit display(_unused const std::string& msg) {
    return tt;
  }
#else
  static _unused unit display(_unused const std::string& msg) {
    std::cout << msg;
    return tt;
  }
#endif

  template<typename T>
  unit ignore(const T /*unused*/) {
    return tt;
  }

  // Forward-declared; our compiler defines one instance per structure type
  template<typename T, std::size_t sz> _unused T unpack(bits<sz> /*bits*/);
} // namespace prims

using prims::unit;
using prims::bits;
using namespace prims::literals;

#ifndef SIM_MINIMAL
enum class repr_style {
  full, hex, dec, bin, utf8
};

template<std::size_t sz>
struct _repr {
  bits<sz> val;
  repr_style style;

  enum class prefixes { sized, plain, minimal };
  prefixes prefix;

  _repr(bits<sz> val, repr_style style, prefixes prefix)
    : val(val), style(style), prefix(prefix) {}

  friend std::ostream& operator<<(std::ostream& stream, const _repr& r) {
    if (r.prefix == prefixes::sized && r.style != repr_style::utf8) {
      stream << sz << "'";
    }

    switch (r.style) {
    case repr_style::bin:
      stream << (r.prefix == prefixes::plain ? "0b" : "b");
      for (size_t pos = sz; pos > 0; pos--) {
        unsigned int bit = prims::truncate<1, sz>(r.val >> (pos - 1u)).v;
        stream << bit;
      }
    break;
    case repr_style::hex:
      stream << (r.prefix == prefixes::plain ? "0x" : "x") << std::hex << +r.val.v;
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
        stream << _repr<sz>(r.val, repr_style::bin, prefixes::minimal);
        stream << " (" << _repr<sz>(r.val, repr_style::hex, prefixes::sized);
        stream << ", " << _repr<sz>(r.val, repr_style::dec, prefixes::sized);
        stream << ")";
      } else {
        stream << _repr<sz>(r.val, repr_style::hex, prefixes::minimal);
      }
      break;
    }

    return stream;
  }
};

template<std::size_t sz>
std::string repr(const bits<sz> val, const repr_style style = repr_style::full) {
  std::ostringstream stream;
  stream << _repr<sz>(val, style, _repr<sz>::prefixes::sized);
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
