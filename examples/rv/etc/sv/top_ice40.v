// -*- verilog -*-
module top_ice40(input CLK, output USBPU, output PIN_1);
   assign USBPU = 0;

   reg [31:0] counter = 0;
   always @(posedge CLK) counter <= counter + 1;

   wire RST_N = counter <= 3;
   top dut(.CLK(CLK), .RST_N(RST_N), .uart_line_out(PIN_1));
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32.v/")
// End:
