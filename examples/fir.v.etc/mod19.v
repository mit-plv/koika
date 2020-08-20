/*! Verilog implementation of external functions for the  fir example -*- mode: verilog -*- !*/

module mod19(input wire CLK, input wire RST_N,
                   input wire[7:0] arg,
                   output wire[7:0] out);
   assign out = arg % 19;
endmodule

