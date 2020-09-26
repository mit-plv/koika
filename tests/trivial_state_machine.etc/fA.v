// -*- mode: verilog -*-
module fA(input wire[31:0] r, input wire[31:0] in, output wire[31:0] out);
   assign out = r & in;
endmodule
