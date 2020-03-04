// -*- verilog -*-
module ext_mem_dmem(input CLK, input RST_N, input[69:0] arg, output[69:0] out);
   ext_mem dmem(.CLK, .RST_N, .arg, .out);
endmodule
