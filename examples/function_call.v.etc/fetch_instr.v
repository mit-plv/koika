// -*- mode: verilog -*-

bit[31:0] instructions[8] = '{
  32'b11011000001011000000011111001101,
  32'b01101011101010101001010001010101,
  32'b10000010111000101110011001100010,
  32'b01111010000000100100001000000100,
  32'b11101000011110100001011000010011,
  32'b10000001001100110010100001110110,
  32'b01001000001001101000011001110011,
  32'b11000001011111000110001001111001
};

module fetch_instr(input wire[2:0] address,
                   output wire[31:0] data);
   assign data = instructions[address];
endmodule

/* An alternative approach would be to use a C function to implement this
   external method; in that case you'd use the following declaration:
     import "DPI-C" function bit[31:0] c_fetch_instr(input bit[2:0] address);
   and then
     assign data = c_fetch_instr(address);

   And on the C side you'd use this:

     static constexpr svBitVecVal instructions[8] = {
       0b11011000001011000000011111001101,
       0b01101011101010101001010001010101,
       0b10000010111000101110011001100010,
       0b01111010000000100100001000000100,
       0b11101000011110100001011000010011,
       0b10000001001100110010100001110110,
       0b01001000001001101000011001110011,
       0b11000001011111000110001001111001
     };

     extern "C" svBitVecVal c_fetch_instr(const svBitVecVal* input) {
       return instructions[*input];
     } */
