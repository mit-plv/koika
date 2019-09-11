#ifndef _EXTFUNS_HPP
#define _EXTFUNS_HPP

static constexpr uint_t<32> instructions[8] = {
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
  uint_t<32> fetch_instr(const uint_t<3> idx, const unit_t /*unused*/) {
    return instructions[idx];
  }
};

class pipeline_extfuns {
public:
  uint_t<32> fetch_instr(const uint_t<3> idx, const unit_t /*unused*/) {
    return instructions[idx];
  }
};

#endif
