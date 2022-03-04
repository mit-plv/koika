/*! Preamble shared by all Kôika programs compiled to C++ !*/
#ifndef _PREAMBLE_HPP
#define _PREAMBLE_HPP

#include <algorithm> // For std::max
#include <array>
#include <cstddef> // For size_t
#include <cstdint> // For uintN_t
#include <cstring> // For memcpy
#include <limits> // For std::numeric_limits used in prims::mask
#include <ostream> // For std::ostream used in operator<<
#include <string> // For prims::display
#include <utility> // for std::forward
#include <type_traits> // For std::conditional_t

#ifndef SIM_MINIMAL
#include <chrono> // For VCD headers
#include <ctime>  // for gmtime
#include <cctype> // For isgraph
#include <cstdlib> // For getenv
#include <initializer_list>
#include <iomanip> // For std::setfill
#include <iostream>
#include <sstream> // For std::ostringstream
#include <fstream> // For VCD files
#include <random> // For executing rules in random order
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

#ifndef SIM_MINIMAL
#define _virtual virtual
#else
#define _virtual
#endif

#if defined(SIM_MINIMAL) && defined(SIM_KEEP_DISPLAY)
#define _display_unoptimized _unoptimized
#else
#define _display_unoptimized
#endif

#ifdef SIM_FLATTEN
#define _flatten __attribute__((flatten))
#else
#define _flatten
#endif

#if defined(SIM_NOINLINE)
#define _inline __attribute__((noinline))
#elif defined(SIM_ALWAYS_INLINE)
#define _inline __attribute__((always_inline))
#else
#define _inline
#endif

#define _noreturn __attribute__((noreturn))
#define _unlikely(b) __builtin_expect((b), 0)

#define MULTIPRECISION_THRESHOLD 64

#ifdef NEEDS_BOOST_MULTIPRECISION
#include <boost/multiprecision/cpp_int.hpp>

#if BOOST_VERSION < 106800
// https://github.com/boostorg/multiprecision/commit/bbe819f8034a3c854deffc6191410b91ac27b3d6
// Before 1.68, static_cast<uint16_t>(uint128_t{1 << 16}) gives 65535 instead of 0
#pragma message("Bignum truncation is broken in Boost < 1.68; if you run into issues, try upgrading.")
#endif

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

namespace cuttlesim {
  static _unused const char* version = "CuttleSim v0.0.1";
}

template<std::size_t size>
using bits_t = std::conditional_t<size <=  8, std::uint8_t,
               std::conditional_t<size <= 16, std::uint16_t,
               std::conditional_t<size <= 32, std::uint32_t,
               std::conditional_t<size <= 64, std::uint64_t,
                                  wbits_t<size>>>>>;

template<std::size_t size>
using sbits_t = std::conditional_t<size <=  8, std::int8_t,
                std::conditional_t<size <= 16, std::int16_t,
                std::conditional_t<size <= 32, std::int32_t,
                std::conditional_t<size <= 64, std::int64_t,
                                   wsbits_t<size>>>>>;

/// # Implementation of Kôika primitives

namespace prims {
  using bitwidth = std::size_t;
  using size_t = std::size_t;

  /// ## Utility functions

  template<typename T>
  T _noreturn unreachable() {
    __builtin_unreachable();
  }

  static _unused void assume(bool condition) {
    if (!condition) { unreachable<void>(); }
  }

  /// ## Array type (array<T, len>)

  template<typename T, size_t len>
  struct array : public std::array<T, len> { // Inherit to be able to overload ‘==’
    // https://stackoverflow.com/questions/24280521/
    // TODO: remove this constructor once we move to C++17
    template <typename... Args>
    // NOLINTNEXTLINE(google-explicit-constructor)
    array(Args&&... args) : std::array<T, len>({std::forward<Args>(args)...}) {}
  };

  /// ## Bitvector type (bits<n>)

  template <bitwidth sz> struct bits;
  // https://stackoverflow.com/questions/4660123/
  template <bitwidth sz> std::ostream& operator<<(std::ostream& /*os*/, const bits<sz>& /*bs*/);

  template<bitwidth sz>
  struct bits {
    bits_t<sz> v;

#ifndef __OPTIMIZE__
    // This makes debugging easier
    static constexpr bitwidth size = sz;
#endif

    /// ### Representation invariant

    static constexpr bitwidth padding_width() noexcept {
      // making this a function avoids polluting GDB's output
      return std::numeric_limits<bits_t<sz>>::digits - sz;
    }

    // Not constexpr because Boost's >> isn't constexpr
    static bits_t<sz> bitmask() noexcept {
      auto pw = bits<sz>::padding_width(); // https://stackoverflow.com/questions/8452952/
      return std::numeric_limits<bits_t<sz>>::max() >> pw;
    }

    void invariant() const noexcept {
      // Knowing this invariant can sometimes help the compiler; it does in
      // particular in ‘operator bool()’ below.
      assume(v <= bitmask());
    }

    /// ### Casts

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
      // This constructs an int of the same bitsize as x, with the same
      // bitpattern, except that it uses the high bits of the storage type instead
      // of the low ones (e.g. 4'b1101 is represented as 8'b11010000).
      return (*this << bits<sz>::padding_width()).to_sbits();
    }

    static bits<sz> of_shifted_sbits(sbits_t<sz> sx) {
      return of_sbits(sx) >> bits<sz>::padding_width();
    }

    /// ### Constants

    // Not constexpr because of ::bitmask
    static bits<sz> ones() {
      return bits<sz>::mk(bits<sz>::bitmask());
    }

    /// ### Member functions

    explicit operator bool() const {
      invariant(); // Knowing this invariant helps GCC generate better code
      return bool(v); // Writing bool(v & bitmask()) works just as well
    }

    // Add an implicit cast to bool for size sz == 1
    // https://github.com/mit-plv/koika/issues/18
    template <int sz_ = sz>
    operator std::enable_if_t<sz_ == 1, bool> () const {
      invariant();
      return bool(v);
    }

    explicit operator bits_t<sz>() const {
      return v;
    }

    template<bitwidth idx_sz>
    bits<1> operator[](bits<idx_sz> idx) const;

    bits<sz>& operator&=(bits<sz> arg);
    bits<sz>& operator|=(bits<sz> arg);
    bits<sz>& operator^=(bits<sz> arg);
    bits<sz>& operator+=(bits<sz> arg);
    bits<sz>& operator-=(bits<sz> arg);
    bits<sz>& operator<<=(size_t shift);
    bits<sz>& operator>>=(size_t shift);
    template<bitwidth shift_sz> bits<sz>& operator<<=(bits<shift_sz> shift);
    template<bitwidth shift_sz> bits<sz>& operator>>=(bits<shift_sz> shift);

    // https://stackoverflow.com/questions/4660123/
    friend std::ostream& operator<<<sz>(std::ostream& os, const bits<sz>& bs);

    /// ### Constructors

    template<typename T>
    static constexpr bits<sz> mk(T arg) {
      return bits{static_cast<bits_t<sz>>(arg)};
    }

    static bits<sz> of_str(const std::string& str) {
      bits<sz> out{};
      std::size_t len = str.length();
      for (std::size_t pos = std::max(len, sz) - sz; pos < len; pos++) {
        if (str[pos] == '1')
          out |= bits<sz>{1} << len - pos - 1;
      }
      return out;
    }
  };

  /// ## Special case for 0-bit bitvectors (bits<0>)

  template<>
  struct bits<0> {
    bits_t<0> v = 0;

    /// ### Representation invariant

    static constexpr bitwidth padding_width() noexcept { return std::numeric_limits<bits_t<0>>::digits; }
    static bits_t<0> bitmask() noexcept { return 0; }
    void invariant() const noexcept { assume(v == 0); }

    /// ### Casts

    sbits_t<0> to_sbits() const { return 0; };
    static bits<0> of_sbits(sbits_t<0>) { return {}; }
    sbits_t<0> to_shifted_sbits() const { return 0; }
    static bits<0> of_shifted_sbits(sbits_t<0>) { return {}; }

    /// ### Constants

    static bits<0> ones() { return {}; }

    /// ### Member functions

    explicit operator bool() const { return false; }
    explicit operator bits_t<0>() const { return 0; }
    template<bitwidth idx_sz> bits<1>
    operator[](bits<idx_sz>) const { return bits<1>{0}; }
    bits<0>& operator&=(bits<0>) { return *this; }
    bits<0>& operator|=(bits<0>) { return *this; }
    bits<0>& operator^=(bits<0>) { return *this; }
    bits<0>& operator+=(bits<0>) { return *this; }
    bits<0>& operator-=(bits<0>) { return *this; }
    bits<0>& operator<<=(size_t) { return *this; }
    bits<0>& operator>>=(size_t) { return *this; }
    template<bitwidth shift_sz> bits<0>& operator<<=(bits<shift_sz>) { return *this; }
    template<bitwidth shift_sz> bits<0>& operator>>=(bits<shift_sz>) { return *this; }
    friend std::ostream& operator<<<0>(std::ostream& os, const bits<0>& bs);

    /// ### Constructors

    template<typename T> static constexpr bits<0> mk(T /*arg*/) { return {}; }
  };

  /// ## Unit type

  using unit = bits<0>;
  static const _unused unit tt{};

  /// ## Bitvector literals

  namespace literal_parsing {
    template<unsigned int base, char c>
    constexpr bool valid_digit() {
      switch (base) {
      case 2:
        return c == '0' || c == '1';
      case 10:
        return '0' <= c && c <= '9';
      case 16:
        return (('0' <= c && c <= '9') ||
                ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F'));
      default:
        return false;
      }
    }

    template <unsigned int base, char c>
    constexpr unsigned int parse_digit() noexcept {
      static_assert(base == 2 || base == 10 || base == 16, "Invalid base");
      static_assert(valid_digit<base, c>(), "Invalid digit");
      if ('0' <= c && c <= '9') {
        return c - '0';
      } else if ('a' <= c && c <= 'f') {
        return c - 'a' + 10;
      } else if ('A' <= c && c <= 'F') {
        return c - 'A' + 10;
      } else {
        unreachable<unsigned int>();
      }
    }

    template <unsigned int base, std::uint64_t max, std::uint64_t num>
    constexpr std::uint64_t parse_u64() noexcept {
      static_assert(max >= num, "Overflow in literal parsing");
      return num;
    }

    template <unsigned int base, std::uint64_t max, std::uint64_t num, char c, char... cs>
    constexpr std::uint64_t parse_u64() noexcept {
      const std::uint64_t digit = parse_digit<base, c>();
      static_assert((max - digit) / base >= num, "Overflow in literal parsing");
      return parse_u64<base, max, base * num + digit, cs...>();
    }

    enum class parser { u64, u128, u256, u512, u1024, unsupported };

    template <parser p, unsigned int base, bitwidth sz, char... cs>
    struct parse_number {
      static_assert(p != parser::unsupported, "Unsupported bitsize.");
#ifndef NEEDS_BOOST_MULTIPRECISION
      static_assert(p == parser::u64, "Needs boost::multiprecision to parse numbers with > 64 bits.");
#endif
      static_assert(p == parser::u64 || base == 16, "boost::multiprecision only supports base-16 literals.");
    };

    template <unsigned int base, bitwidth sz, char... cs>
    struct parse_number<parser::u64, base, sz, cs...> {
      // Not using bits<sz>::bitmask because it isn't constexpr
      static constexpr std::uint64_t max = std::numeric_limits<bits_t<sz>>::max() >> bits<sz>::padding_width();
      static constexpr bits_t<sz> v = parse_u64<base, max, 0, cs...>();
    };

#ifdef NEEDS_BOOST_MULTIPRECISION
    using namespace boost::multiprecision::literals;

    template <bitwidth sz, char... cs>
    struct parse_number<parser::u128, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui128<'0', 'x', cs...>();
    };

    template <bitwidth sz, char... cs>
    struct parse_number<parser::u256, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui256<'0', 'x', cs...>();
    };

    template <bitwidth sz, char... cs>
    struct parse_number<parser::u512, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui512<'0', 'x', cs...>();
    };

    template <bitwidth sz, char... cs>
    struct parse_number<parser::u1024, 16, sz, cs...> {
      static constexpr bits_t<sz> v = operator "" _cppui1024<'0', 'x', cs...>();
    };
#endif

    constexpr parser get_parser(bitwidth sz) noexcept {
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

    template <bool imm, unsigned int base, bitwidth sz, char... cs>
    struct parse_literal;

    template <unsigned int base, bitwidth sz, char... cs>
    struct parse_literal<true, base, sz, '\'', cs...> {
      static_assert(sz <= 64, "Immediates can't have size > 64.");
      static constexpr bits_t<sz> v = parse_number<get_parser(sz), base, sz, cs...>::v;
    };

    template <unsigned int base, bitwidth sz, char... cs>
    struct parse_literal<false, base, sz, '\'', cs...> {
      static constexpr bits<sz> v = bits<sz>{parse_number<get_parser(sz), base, sz, cs...>::v};
    };

    template <bool imm, unsigned int base, bitwidth sz, char c, char... cs>
    struct parse_literal<imm, base, sz, c, cs...> {
      static constexpr bitwidth sz_digit = parse_digit<10, c>();
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
  } // namespace literal_parsing

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
  } // namespace literals

  /// ## Bit- and array-manipulation functions

  template<bitwidth sz>
  static bits<sz> mask(bits<sz> arg) {
    return arg & bits<sz>::ones();
  }

  template<bitwidth ret_sz, bitwidth sz>
  static bits<ret_sz> widen(const bits<sz> arg) {
    static_assert(ret_sz >= sz, "Call to widen has ret_sz < sz");
    return bits<ret_sz>::mk(arg.v);
  }

  template<bitwidth ret_sz, bitwidth sz>
  static bits<ret_sz> truncate(const bits<sz> arg) {
    if (sz > MULTIPRECISION_THRESHOLD && sz > ret_sz) {
      // Truncation is broken in Boost::multiprecision < 1.68.0, so mask before truncating
      // https://github.com/boostorg/multiprecision/commit/bbe819f8034a3c854deffc6191410b91ac27b3d6
      return bits<ret_sz>::mk(arg.v & bits<ret_sz>::bitmask());
    } else {
      return mask(bits<ret_sz>::mk(arg.v));
    }
  }

  template<bitwidth sz>
  bits<1> msb(const bits<sz> arg) {
    return sz == 0 ? 0 : truncate<1>(arg >> (sz - 1));
  }

  template<bitwidth sz>
  template<bitwidth idx_sz>
  bits<1> bits<sz>::operator[](const bits<idx_sz> idx) const {
    return truncate<1>((*this) >> idx);
  }

  template<bitwidth idx, bitwidth sz1, bitwidth width>
  bits<sz1> slice_subst(const bits<sz1> data, const bits<width> repl) {
    const bits<sz1> mask = ~(widen<sz1>(bits<width>::ones()) << idx);
    return (data & mask) | (widen<sz1>(repl) << idx);
  }

  template<bitwidth width, bitwidth sz1, bitwidth sz2>
  bits<width> islice(const bits<sz1> data, const bits<sz2> idx) {
    return truncate<width>(data >> idx);
  }

  template<bitwidth sz>
  bits<sz> operator&(const bits<sz> data1, const bits<sz> data2) {
    return bits<sz>::mk(data1.v & data2.v);
  }

  template<bitwidth sz>
  bits<sz> operator|(const bits<sz> data1, const bits<sz> data2) {
    return bits<sz>::mk(data1.v | data2.v);
  }

  template<bitwidth sz>
  bits<sz> operator^(const bits<sz> data1, const bits<sz> data2) {
    return bits<sz>::mk(data1.v ^ data2.v);
  }

  template<bitwidth sz1, bitwidth sz2>
  bits<sz1> asr(const bits<sz1> data, const bits<sz2> shift) {
    // Implementation-defined, assumes that the compiler does an arithmetic shift
    return bits<sz1>::of_shifted_sbits(data.to_shifted_sbits() >> shift.v);
  }

  template<bitwidth sz1>
  bits<sz1> operator>>(const bits<sz1> data, const size_t shift) {
    return bits<sz1>::mk(data.v >> shift);
  }

  template<bitwidth sz1>
  bits<sz1> operator<<(const bits<sz1> data, const size_t shift) {
    return mask(bits<sz1>::mk(data.v << shift));
  }

  template<bitwidth sz1, bitwidth sz2>
  bits<sz1> operator>>(const bits<sz1> data, const bits<sz2> shift) {
    return bits<sz1>::mk(data.v >> shift.v);
  }

  template<bitwidth sz1, bitwidth sz2>
  bits<sz1> operator<<(const bits<sz1> data, const bits<sz2> shift) {
    return mask(bits<sz1>::mk(data.v << shift.v));
  }

  static _unused bits<1> operator!(const bits<1> x) {
    return bits<1>::mk(!x.v);
  }

  template<bitwidth sz>
  bits<1> operator==(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v == y.v);
  }

  template<typename T, size_t len>
  bits<1> operator==(const array<T, len> x, const array<T, len> y) {
    return bits<1>::mk(static_cast<const std::array<T, len>&>(x) ==
                       static_cast<const std::array<T, len>&>(y));
  }

  template<bitwidth sz>
  bits<1> operator!=(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v != y.v);;
  }

  template<bitwidth sz>
  bits<sz> operator+(const bits<sz> x, const bits<sz> y) {
    return mask(bits<sz>::mk(x.v + y.v));
  }

  template<bitwidth sz>
  bits<sz> operator-(const bits<sz> x, const bits<sz> y) {
    return mask(bits<sz>::mk(x.v + ~y.v + 1));
  }

  template<bitwidth sz_x, bitwidth sz_y>
  bits<sz_x + sz_y> operator*(const bits<sz_x> x, const bits<sz_y> y) {
    return mask(bits<sz_x + sz_y>::mk(widen<sz_x + sz_y>(x).v *
                                      widen<sz_x + sz_y>(y).v));
  }

  template<bitwidth sz>
  bits<1> operator<(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v < y.v);
  }

  template<bitwidth sz>
  bits<1> operator>(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v > y.v);
  }

  template<bitwidth sz>
  bits<1> operator<=(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v <= y.v);
  }

  template<bitwidth sz>
  bits<1> operator>=(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.v >= y.v);
  }

  template<bitwidth sz>
  bits<1> slt(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() < y.to_shifted_sbits());
  }

  template<bitwidth sz>
  bits<1> sgt(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() > y.to_shifted_sbits());
  }

  template<bitwidth sz>
  bits<1> sle(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() <= y.to_shifted_sbits());
  }

  template<bitwidth sz>
  bits<1> sge(const bits<sz> x, const bits<sz> y) {
    return bits<1>::mk(x.to_shifted_sbits() >= y.to_shifted_sbits());
  }

  template<bitwidth sz1, bitwidth sz2>
  bits<sz1 + sz2> concat(const bits<sz1> x, const bits<sz2> y) {
    return widen<sz1 + sz2>(x) << sz2 | widen<sz1 + sz2>(y);
  }

  template<bitwidth sz>
  bits<sz> operator~(const bits<sz> data) {
    return mask(bits<sz>::mk(~data.v));
  }

  template<bitwidth width, bitwidth sz>
  bits<std::max(sz, width)> sext(const bits<sz> x) {
    constexpr bitwidth maxsz = std::max(sz, width);
    constexpr bitwidth nbits = width >= sz ? width - sz : bitwidth{0};
    // Implementation-defined, assumes that the compiler does an arithmetic shift
    return bits<maxsz>::of_shifted_sbits((widen<maxsz>(x) << nbits).to_shifted_sbits() >> nbits);
  }

  template<bitwidth width, bitwidth sz>
  bits<std::max(sz, width)> zextl(const bits<sz> x) {
    return widen<std::max(sz, width)>(x);
  }

  template<bitwidth width, bitwidth sz>
  bits<std::max(sz, width)> zextr(const bits<sz> x) {
    constexpr bitwidth maxsz = std::max(sz, width);
    return widen<maxsz>(x) << (maxsz - sz);
  }

  template<bitwidth times, bitwidth sz> struct repeat_t {
    static bits<sz * times> v(bits<sz> bs) {
      return concat(repeat_t<times - 1, sz>::v(bs), bs);
    };
  };

  template<bitwidth sz> struct repeat_t<0, sz> {
    static bits<0> v(bits<sz> /*unused*/) { return tt; };
  };

  template<bitwidth times> struct repeat_t<times, 1> {
    static bits<times> v(bits<1> bs) { return sext<times>(bs); };
  };

  template<bitwidth sz> struct repeat_t<1, sz> {
    static constexpr auto v(bits<sz> bs) { return bs; }
  };

  template<bitwidth times, bitwidth sz>
  bits<sz * times> repeat(const bits<sz> bs) {
    return repeat_t<times, sz>::v(bs);
  }

  template<bitwidth idx, bitwidth width, bitwidth sz1>
  bits<width> slice(const bits<sz1> data) {
    return truncate<width>(data >> idx);
  }

  template<size_t pos, typename T, size_t len>
  array<T, len> replace(const array<T, len> arr, T val) {
    array<T, len> copy = arr;
    copy[pos] = val;
    return copy;
  }

  template<bitwidth sz>
  bits<sz>& bits<sz>::operator&=(const bits<sz> arg) { return (*this = *this & arg); }
  template<bitwidth sz>
  bits<sz>& bits<sz>::operator|=(const bits<sz> arg) { return (*this = *this | arg); }
  template<bitwidth sz>
  bits<sz>& bits<sz>::operator^=(const bits<sz> arg) { return (*this = *this ^ arg); }
  template<bitwidth sz>
  bits<sz>& bits<sz>::operator+=(const bits<sz> arg) { return (*this = *this + arg); }
  template<bitwidth sz>
  bits<sz>& bits<sz>::operator-=(const bits<sz> arg) { return (*this = *this - arg); }
  template<bitwidth sz>
  bits<sz>& bits<sz>::operator<<=(const size_t shift) { return (*this = *this << shift); }
  template<bitwidth sz>
  bits<sz>& bits<sz>::operator>>=(const size_t shift) { return (*this = *this >> shift); }
  template<bitwidth sz> template<bitwidth shift_sz>
  bits<sz>& bits<sz>::operator<<=(const bits<shift_sz> shift) { return (*this = *this << shift); }
  template<bitwidth sz> template<bitwidth shift_sz>
  bits<sz>& bits<sz>::operator>>=(const bits<shift_sz> shift) { return (*this = *this >> shift); }

  /// ## Display functions

  enum fmtstyle { full, hex, dec, bin };

  struct fmtopts {
    bool strings;
    bool newline;
    fmtstyle style;
  };

  static const _unused fmtopts default_fmtopts{ true, true, fmtstyle::full };

  template<typename T>
  static _unused _display_unoptimized unit display(const _unused T& msg,
                                                   const _unused fmtopts opts = default_fmtopts) {
#ifndef SIM_MINIMAL
    fmt(std::cout, msg, opts);
    std::cout << std::endl;
#endif
    return tt;
  }

#ifndef SIM_MINIMAL
  namespace internal {
    template<typename T, size_t len>
    std::string string_of_bytestring(const array<T, len>& val) {
      std::string s{};
      for (size_t pos = 0; pos < len; pos ++) {
        s.push_back(static_cast<char>(val[pos].v));
      }
      return s;
    }
  } // namespace internal
#endif

  template<size_t len>
  static _unused _display_unoptimized unit putstring(const _unused array<bits<8>, len>& msg) {
#ifndef SIM_MINIMAL
    std::cout << internal::string_of_bytestring(msg);
#endif
    return tt;
  }

  /// ## Other primitives

  template<typename T>
  unit ignore(const T /*unused*/) {
    return tt;
  }

  /// ## Type info

  template<typename T> struct type_info;

  template<bitwidth sz> struct type_info<bits<sz>> {
    static constexpr bitwidth size = sz;
  };

  template<typename T, size_t len> struct type_info<array<T, len>> {
    static constexpr bitwidth size{len * type_info<T>::size};
  };

  /// ## Packing and unpacking

  // Forward-declared; our compiler defines one instance per struct and enum.
  // Unpack needs to be structs to get return-type polymorphism through explicit
  // template instantiation.  Pack is a struct to make overloading it easier.
  template<typename T, bitwidth sz> struct _unpack;
  template<typename T> static bits<type_info<T>::size> pack(const T val);

  template<typename T, bitwidth sz>
  static T unpack(const bits<sz>& bs) {
    return _unpack<T, sz>::unpack(bs);
  }

  /// ### Bits packing and unpacking (no-op, but needed by array packing/unpacking)

  template<bitwidth sz>
  static bits<sz> pack(const bits<sz> val) {
    return val;
  }

  template<bitwidth sz, bitwidth packed_sz>
  struct _unpack<bits<sz>, packed_sz> {
    static_assert(sz == packed_sz, "Inconsistent size parameters in call to unpack");
    static bits<sz> unpack(const bits<packed_sz> bs) {
      return bs;
    }
  };

  /// ### Array packing and unpacking

  template<typename T, size_t len>
  static bits<type_info<array<T, len>>::size> pack(const array<T, len>& val) {
    constexpr bitwidth elem_sz = type_info<T>::size;
    constexpr bitwidth packed_sz = type_info<array<T, len>>::size;
    bits<packed_sz> packed{};
    for (size_t pos = 0; pos < len; pos++) {
      packed <<= elem_sz;
      packed |= prims::widen<packed_sz>(prims::pack(val[pos]));
    }
    return packed;
  }

  template<typename T, size_t len, bitwidth packed_sz>
  struct _unpack<array<T, len>, packed_sz> {
    // We need a struct for return-type polymorphism
    static constexpr bitwidth elem_sz = type_info<T>::size;
    static constexpr bitwidth expected_sz = len * elem_sz;
    static_assert(expected_sz == packed_sz,
                  "Inconsistent size parameters in call to unpack");

    static array<T, len> unpack(bits<packed_sz> bs) { // not const&
      array<T, len> unpacked{};
      for (size_t pos = 0; pos < len; pos++) { // FIXME check the order of elements
        unpacked[len - 1 - pos] = prims::unpack<T>(truncate<elem_sz>(bs));
        bs >>= elem_sz;
      }
      return unpacked;
    }
  };

  /// ## Printing

  /// ### Bitvector-printing functions

#ifndef SIM_MINIMAL
  // This convenience function creates a string from an object
  template<typename T>
  std::string repr(const T& val, const fmtopts opts = default_fmtopts) {
    std::ostringstream stream;
    fmt(stream, val, opts);
    return stream.str();
  }

  // This default overload passes a default set of format options
  template<typename T>
  std::ostream& fmt(std::ostream& os, const T& val) {
    return fmt(os, val, default_fmtopts);
  }

  enum class prefixes { sized, plain, minimal };

  namespace internal {
    template<bitwidth sz>
    static std::ostream& bits_fmt(std::ostream& os, const bits<sz>& val,
                                  const fmtstyle style, const prefixes prefix) {
      if (prefix == prefixes::sized) {
        os << sz << "'";
      }

      switch (style) {
      case fmtstyle::bin:
        os << (prefix == prefixes::plain ? "0b" : "b");
        if (val == bits<sz>{0}) {
          os << "0";
        } else {
          for (bitwidth pos = sz; pos > 0; pos--) {
            unsigned int bit = prims::truncate<1>(val >> (pos - 1u)).v;
            os << bit;
          }
        }
        break;
      case fmtstyle::hex:
        os << (prefix == prefixes::plain ? "0x" : "x");
        os << std::hex << +val.v << std::dec;
        break;
      case fmtstyle::dec:
        os << std::dec << +val.v;
        break;
      case fmtstyle::full:
        if (sz <= 64) {
          bits_fmt(os, val, fmtstyle::bin, prefixes::minimal);
          os << " ("; bits_fmt(os, val, fmtstyle::hex, prefixes::plain);
          os << ", "; bits_fmt(os, val, fmtstyle::dec, prefixes::plain);
          os << ")";
        } else {
          bits_fmt(os, val, fmtstyle::hex, prefixes::minimal);
        }
        break;
      }
      return os;
    }
  } // namespace internal

  template<bitwidth sz>
  static std::ostream& fmt(std::ostream& os, const bits<sz>& val, const fmtopts opts) {
    return internal::bits_fmt(os, val, opts.style, prefixes::sized);
  }

  template<bitwidth sz>
  std::ostream& operator<<(std::ostream& os, const bits<sz>& bs) {
    return fmt(os, bs);
  }

  /// ### Array printing functions

  namespace internal {
    template<typename T>
    static std::ostream& array_fmt(std::ostream& os, const std::size_t len, const T* val, fmtopts opts) {
      if (opts.style == fmtstyle::full) {
        opts.style = fmtstyle::hex;
      }
      os << "[";
      if (len != 0) {
        fmt(os, val[0], opts);
        for (size_t pos = 1; pos < len; pos++) {
          os << "; ";
          fmt(os, val[pos], opts);
        }
      }
      os << "]";
      return os;
    }
  } // namespace internal

  template<typename T, size_t len>
  static std::ostream& fmt(std::ostream& os, const array<T, len>& val, const fmtopts opts) {
    return internal::array_fmt(os, len, val.data(), opts);
  }

  template<size_t len>
  static std::ostream& fmt(std::ostream& os, const array<bits<8>, len>& val, const fmtopts opts) {
    if (opts.strings) {
      os << "\"" << std::hex << std::setfill('0');
      for (size_t pos = 0; pos < len; pos ++) {
        unsigned char chr = static_cast<unsigned char>(val[pos].v);
        if (chr == '\\' || chr == '"') {
          os << "\\" << chr;
        } else if (std::isgraph(chr)) {
          os << chr;
        } else {
          os << "\\x" << std::setw(2) << static_cast<unsigned>(chr);
        }
      }
      os << "\"";
    } else {
      internal::array_fmt(os, len, val.data(), opts);
    }
    return os;
  }

  template<typename T, size_t len>
  std::ostream& operator<<(std::ostream& os, const array<T, len>& val) {
    return fmt(os, val);
  }
#endif // #ifndef SIM_MINIMAL
} // namespace prims

#ifndef SIM_MINIMAL
namespace cuttlesim {
  /// # VCD traces

  namespace vcd {
    using namespace std::chrono;
    using strs = std::initializer_list<std::string>;

    static _unused void begin_header(std::ostream& os, strs scopes) {
      auto now = system_clock::to_time_t(system_clock::now());
      os << "$date " << std::put_time(std::gmtime(&now), "%FT%TZ") << " $end" << std::endl;
      os << "$version " << cuttlesim::version << " $end" << std::endl;
      os << "$timescale 1 ns $end" << std::endl;
      for (auto&& scope : scopes) {
        os << "$scope module "<< scope << " $end" << std::endl;
      }
    }

    static _unused void end_header(std::ostream& os, strs scopes) {
      for (auto&& _ _unused : scopes) {
        os << "$upscope $end" << std::endl;
      }
      os << "$enddefinitions $end" << std::endl;
      os << "$dumpvars" << std::endl;
    }

    static _unused void var(std::ostream& os, const std::string& name, const size_t sz) {
      std::string alias = name;
      os << "$var wire " << sz << " " << alias << " " << name;
      if (sz > 1) {
        os << " [" << sz - 1 << ":0]";
      }
      os << " $end" << std::endl;
    }

    template<typename T>
    static _unused void dumpvar(std::ostream& os, std::string name,
                                const T& val, const T& previous, bool force) {
      if (force || val != previous) {
        using namespace prims;
        internal::bits_fmt(os, pack(val), fmtstyle::bin, prefixes::minimal);
        os << " " << name << '\n';
      }
    }

    static _unused bool read_header(std::istream& is) {
      std::string line{};
      while (std::getline(is, line)) {
        if (line.rfind("$dumpvars", 0) == 0)
          return true;
      }
      return false;
    }

    static _unused bool readvar(std::istream& is, std::uint_fast64_t& cycle_id, std::string& name, std::string& val) {
      std::string line;
      while (std::getline(is, line)) {
        if (line == "")
          continue;

        std::istringstream ls(line);
        if (line[0] == '#') {
          ls.ignore(1, '#');
          ls >> cycle_id;
          continue;
        }

        ls >> val >> name;
        return true;
      }
      return false;
    }
  }

  /// # Randomization

  namespace internal {
    std::size_t gen_seed() {
      if (char* seed = std::getenv("SIM_RANDOMIZED")) {
        return std::hash<std::string>{}(seed);
      }
      auto now = std::chrono::high_resolution_clock::now();
      return now.time_since_epoch().count();
    }
  }

  static _unused std::size_t random_seed = internal::gen_seed();
} // namespace cuttlesim
#endif // #ifndef SIM_MINIMAL

/// # ‘using …’ statements

using prims::array;
using prims::unit;
using prims::bits;
using namespace prims::literals;

/// # Read-write sets

namespace cuttlesim {
  /// ## Registers

  struct reg_rwset {
    bool w0 : 1;

    bool may_read0(reg_rwset rL) {
      return !(rL.w0);
    }

    bool may_write0() {
      return !(w0);
    }

    void reset() {
      w0 = false;
    }

    reg_rwset() : w0{} {}
  };

  /// ## Wires

  struct wire_rwset {
    bool r1 : 1;
    bool w0 : 1;

    static _unused bool may_read1(wire_rwset /*unused*/) {
      return true;
    }

    bool may_write0() {
      return !(r1 || w0);
    }

    void reset() {
      r1 = w0 = false;
    }

    wire_rwset() : r1{}, w0{} {}
  };

  /// ## EHRs

  struct ehr_rwset {
    bool r1 : 1; // FIXME does adding :1 always help?
    bool w0 : 1;
    bool w1 : 1;

    static _unused bool may_read0(ehr_rwset rL) {
      return !(rL.w1 || rL.w0);
    }

    static _unused bool may_read1(ehr_rwset rL) {
      return !(rL.w1);
    }

    bool may_write0() {
      return !(r1 || w0 || w1);
    }

    bool may_write1() {
      return !(w1);
    }

    void reset() {
      r1 = w0 = w1 = false;
    }

    // Removing this constructor causes Collatz's performance to drop 5x with GCC
    ehr_rwset() : r1{}, w0{}, w1{} {}
  };

  /// ## Read and write functions

  template<typename T, typename rwset>
  [[nodiscard]] bool read0(T* target, const T rL, rwset& rwl, const rwset rwL) {
    bool ok = rwl.may_read0(rwL);
    *target = rL;
    return ok;
  }

  template<typename T, typename rwset>
  [[nodiscard]] bool read1(T* target, const T rl, rwset& rwl, const rwset rwL) {
    bool ok = rwl.may_read1(rwL);
    *target = rl;
    rwl.r1 = true;
    return ok;
  }

  template<typename T, typename rwset>
  [[nodiscard]] bool write0(T& rl, const T val, rwset& rwl) {
    bool ok = rwl.may_write0();
    rl = val;
    rwl.w0 = true;
    return ok;
  }

  template<typename T, typename rwset>
  [[nodiscard]] bool write1(T& rl, const T val, rwset& rwl) {
    bool ok = rwl.may_write1();
    rl = val;
    rwl.w1 = true;
    return ok;
  }

  template<typename T>
  void read_fast(T* target, const T rL) {
    *target = rL;
  }

  template<typename T>
  void write_fast(T& rl, const T val) {
    rl = val;
  }
} // namespace cuttlesim

/// # Unused datastructures for fast read-write set tracking

namespace cuttlesim {
  struct offsets {
    std::size_t state_offset;
    std::size_t state_sz;
    std::size_t rwset_offset;
    std::size_t rwset_sz;

    void memcpy(char* dst_state, char* src_state, char* dst_rwset, char* src_rwset) {
      std::memcpy(dst_rwset + rwset_offset, src_rwset + rwset_offset, rwset_sz);
      std::memcpy(dst_state + state_offset, src_state + state_offset, state_sz);
    }
  };

  template<typename T, int capacity>
  struct stack {
    int sz;
    unsigned: 0;
    T data[capacity];

    void push(T value) {
      data[sz++] = value;
    }

    stack() : sz{0} {}
  };
}

/// # API

namespace cuttlesim {
  enum exit_info {
    exit_info_none = 0b00,
    // TODO: exit_info_time  = 0b01,
    exit_info_state = 0b10
  };

  struct sim_metadata {
    bool finished;
    int exit_code;
    int exit_config;
    std::uint_fast64_t cycle_id;

    sim_metadata() :
      finished{false},
      exit_code{0},
      exit_config{exit_info_state}
    {}
  };

  template<typename state_t>
  struct snapshot_t {
    state_t state;
#ifndef SIM_MINIMAL
    sim_metadata meta;

    int report() {
      if (meta.exit_config & exit_info_state)
        state.dump();
      return meta.exit_code;
    }

    snapshot_t(state_t _state, sim_metadata _meta) : state(_state), meta(_meta) {}
#else
    snapshot_t(state_t _state, sim_metadata _meta) : state(_state) {}
#endif
  };
}

/// # Driver

namespace cuttlesim {
  // The particular way the drivers below are written ensures that the compiler
  // can optimize as much as possible.  If these functions returned a copy of
  // the full simulator state instead, the compiler would not be able to
  // optimize read-write sets away.

  using ull = unsigned long long int;
  template <typename simulator, typename... Args>
  _unused _flatten __attribute__((noinline)) typename simulator::snapshot_t
  init_and_run(ull ncycles, Args&&... args) noexcept {
    return simulator(std::forward<Args>(args)...).run(ncycles).snapshot();
  }

#ifndef SIM_MINIMAL
  template <typename simulator, typename... Args>
  _unused _flatten static __attribute__((noinline)) typename simulator::snapshot_t
  init_and_run_randomized(ull ncycles, Args&&... args) noexcept {
    return simulator(std::forward<Args>(args)...).run_randomized(ncycles).snapshot();
  }

  template<typename simulator, typename... Args>
  _unused _flatten static __attribute__((noinline)) typename simulator::snapshot_t
  init_and_trace(std::string fname, ull ncycles, Args&&... args) {
    return simulator(std::forward<Args>(args)...).trace(fname, ncycles).snapshot();
  }

  template<typename simulator, typename... Args>
  _unused _flatten static __attribute__((noinline)) typename simulator::snapshot_t
  init_and_trace_randomized(std::string fname, ull ncycles, Args&&... args) {
    return simulator(std::forward<Args>(args)...).trace_randomized(fname, ncycles).snapshot();
  }

  /// ## Command-line interface

  struct params {
    ull ncycles = 1000;
#ifdef SIM_TRACE
    std::string vcd_fpath = {};
#endif

    static params of_cli(int argc, char **argv) {
      params parsed{};

      if (argc > 1)
        parsed.ncycles = std::stoull(argv[1]);

#ifdef SIM_TRACE
      if (argc > 2)
        parsed.vcd_fpath = argv[2];
      else
        parsed.vcd_fpath = std::string(argv[0]) + ".vcd";
#endif

      return parsed;
    }
  };

  /// ## int main()

  template<typename simulator, typename... Args>
  static _unused int main(int argc, char **argv, Args&&... args) {
    auto params = params::of_cli(argc, argv);

    // The original version of this code used a single ‘simulator’ and called
    // ‘.trace’, ‘.run’, or ‘.run_randomized’ on it based on a runtime
    // parameter.  Changing it to initialize a separate ‘simulator’ in each case
    // made the code 10x faster in both GCC and Clang.  Using a compile-time
    // parameter instead yielded the same speedup, plus an extra 20% speedup in
    // GCC thanks to inlining magic.

#if defined(SIM_TRACE) && defined(SIM_RANDOMIZED)
    auto snapshot = init_and_trace_randomized<simulator>(
      params.vcd_fpath, params.ncycles, std::forward<Args>(args)...);
#elif defined(SIM_TRACE)
    auto snapshot = init_and_trace<simulator>(
      params.vcd_fpath, params.ncycles, std::forward<Args>(args)...);
#elif defined(SIM_RANDOMIZED)
    auto snapshot = init_and_run_randomized<simulator>(
      params.ncycles, std::forward<Args>(args)...);
#else
    auto snapshot = init_and_run<simulator>(
      params.ncycles, std::forward<Args>(args)...);
#endif

    return snapshot.report();
  }
#endif
} // namespace cuttlesim

/// # Macros

/// ## Utilities

#define PASTE_ARGS_2(x0, x1) x0##_##x1
#define PASTE_ARGS_3(x0, x1, x2) x0##_##x1##_##x2
#define PASTE_ARGS_4(x0, x1, x2, x3) x0##_##x1##_##x2##_##x3
#define PASTE_EXPANDED_2(x0, x1) PASTE_ARGS_2(x0, x1)
#define PASTE_EXPANDED_3(x0, x1, x2) PASTE_ARGS_3(x0, x1, x2)
#define PASTE_EXPANDED_4(x0, x1, x2, x3) PASTE_ARGS_4(x0, x1, x2, x3)

// Using __VA_ARGS__ in DECL_FN and WRITE* macros lets us parse things like
// WRITE0(reg, struct_xyz{a, b}) and DECL_FN(xyz, array<int, 4>).
// See https://stackoverflow.com/questions/29578902/.

/// ## Function and rule declarations

#define DECL_FN(fname, ...) \
  using PASTE_EXPANDED_3(ti_fn, RULE_NAME, fname) = __VA_ARGS__;

#define DEF_FN(fname, ...) \
  bool PASTE_EXPANDED_3(fn, RULE_NAME, fname)(__VA_ARGS__) noexcept

#define RULE_DECL(ret_type, name, rl) \
  _inline ret_type PASTE_ARGS_2(name, rl)() noexcept

#define DEF_RULE(rl) RULE_DECL(bool, rule, rl)
#define DEF_RESET(rl) RULE_DECL(void, reset, rl)
#define DEF_COMMIT(rl) RULE_DECL(void, commit, rl)

/// ## Read, write, and fail

#define FAIL() \
  { PASTE_EXPANDED_2(reset, RULE_NAME)(); return false; }
#define FAIL_UNLESS(can_fire) \
  { if (!(can_fire)) { FAIL(); }  }
#define READ(read_fn, reg, source) \
  ({ decltype(source.reg) _tmp; \
     FAIL_UNLESS(read_fn(&_tmp, source.reg, log.rwset.reg, Log.rwset.reg)); \
     _tmp; })
#define WRITE(write_fn, reg, val) \
  FAIL_UNLESS(write_fn(log.state.reg, (val), log.rwset.reg))
#define READ0(reg) \
  READ(read0, reg, Log.state)
#define READ1(reg) \
  READ(read1, reg, log.state)
#define WRITE0(reg, ...) \
  WRITE(write0, reg, (__VA_ARGS__))
#define WRITE1(reg, ...) \
  WRITE(write1, reg, (__VA_ARGS__))
#define FN_RETURN(val) \
  { (*__fn_ret) = val; return true; }
#define CALL_FN(fname, ...) \
  ({ PASTE_EXPANDED_3(ti_fn, RULE_NAME, fname) _tmp; \
     FAIL_UNLESS(PASTE_EXPANDED_3(fn, RULE_NAME, fname)(_tmp,##__VA_ARGS__)); \
     _tmp; })
#define COMMIT() \
  { PASTE_EXPANDED_2(commit, RULE_NAME)(); return true; }

#define FAIL_FAST() \
  { return false; }
#define READ0_FAST(reg) \
  Log.state.reg
#define READ1_FAST(reg) \
  log.state.reg
#define WRITE0_FAST(reg, ...) \
  log.state.reg = (__VA_ARGS__)
#define WRITE1_FAST(reg, ...) \
  log.state.reg = (__VA_ARGS__)

/// ## Alternative implementations of read, write, and fail

#define FAIL_DL() \
  { dlog.apply(log, Log); return false; }
#define FAIL_UNLESS_DL(can_fire) \
  { if (!(can_fire)) { FAIL_DL(); } }
#define READ_DL(read_fn, reg, source) \
  ({ dlog.push(reg_name_t::reg); \
     decltype(source.reg) _tmp; \
     FAIL_UNLESS_DL(read_fn(&_tmp, source.reg, log.rwset.reg, Log.rwset.reg)); \
     _tmp; })
#define WRITE_DL(write_fn, reg) \
  { dlog.push(reg_name_t::reg); \
    FAIL_UNLESS_DL(write_fn(log.state.reg, (val), log.rwset.reg)) }
#define READ0_DL(reg) \
  READ_DL(read0, reg, Log.state)
#define READ1_DL(reg) \
  READ_DL(read1, reg, log.state)
#define WRITE0_DL(reg, ...) \
  WRITE_DL(write0, reg, (__VA_ARGS__))
#define WRITE1_DL(reg, ...) \
  WRITE_DL(write1, reg, (__VA_ARGS__))
#define COMMIT_DL() \
  { dlog.apply(Log, log); return true; }

#define FAIL_DOL() \
  { dlog.apply(log, Log); return false; }
#define FAIL_UNLESS_DOL(can_fire) \
  { if (!(can_fire)) { FAIL_DOL(); } }
#define PUSH_DOL(reg) \
  dlog.push({ \
      offsetof(struct state_t, reg), sizeof(state_t::reg), \
      offsetof(struct rwset_t, reg), sizeof(rwset_t::reg), })
#define READ_DOL(read_fn, reg, source) \
  ({ PUSH_DOL(reg); \
     decltype(source.reg) _tmp; \
     FAIL_UNLESS_DOL(read_fn(&_tmp, source.reg, log.rwset.reg, Log.rwset.reg)); \
     _tmp; })
#define WRITE_DOL(write_fn, reg, val) \
  { PUSH_DOL(reg); \
    FAIL_UNLESS_DOL(write_fn(log.state.reg, (val), log.rwset.reg)) }
#define READ0_DOL(reg) \
  READ_DOL(read0, reg, Log.state)
#define READ1_DOL(reg) \
  READ_DOL(read1, reg, log.state)
#define WRITE0_DOL(reg, ...) \
  WRITE_DOL(write0, reg, (__VA_ARGS__))
#define WRITE1_DOL(reg, ...) \
  WRITE_DOL(write1, reg, (__VA_ARGS__))
#define COMMIT_DOL() \
  { dlog.apply(Log, log); return true; }

#undef _unlikely
#undef _unoptimized
#undef _display_unoptimized
#endif // #ifndef _PREAMBLE_HPP
