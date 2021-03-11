// -*- mode: verilog -*-
// Returns information about the current host
module ext_host_id(input wire CLK, input wire RST_N, input wire[0:0] arg, output wire[7:0] out);
`ifndef HOST_ID
 `ifdef SIMULATION
  `define HOST_ID 8'b1 // Verilator
 `else
  `define HOST_ID 8'b10000000 // FPGA
 `endif
`endif
   assign out = `HOST_ID;
endmodule // ext_host_id
