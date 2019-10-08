#ifndef _EXTFUNS_HPP
#define _EXTFUNS_HPP

// #include "../preamble.hpp"

static constexpr bits<32> instructions[8] = {
  0b11011000001011000000011111001101,
  0b01101011101010101001010001010101,
  0b10000010111000101110011001100010,
  0b01111010000000100100001000000100,
  0b11101000011110100001011000010011,
  0b10000001001100110010100001110110,
  0b01001000001001101000011001110011,
  0b11000001011111000110001001111001
};

class decoder_extfuns {
public:
  bits<32> fetch_instr(const bits<3> idx, const unit /*unused*/) {
    return instructions[idx];
  }
};

class pipeline_extfuns {
public:
  static bits<32> stream(bits<32> lfsr, unit /*unused*/) {
    return lfsr + 1u;
  }

  static bits<32> f(bits<32> x, unit /*unused*/) {
    return ~(x << 2u) - 1u;
  }

  static bits<32> g(bits<32> x, unit /*unused*/) {
    return 5u * ((x + 1u) >> 1u);
  }
};

class datatypes_lv_extfuns {
public:
  bits<32> getinstr(const bits<32> idx, const unit /*unused*/) {
    return instructions[idx % 8];
  }
};
#endif
