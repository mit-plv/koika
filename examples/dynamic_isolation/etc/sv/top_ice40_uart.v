// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in FPGA synthesis, with a UART interface) !*/
// This toplevel is useful if pin 1 of the board is connected to a UART receiver
module top_ice40_uart(input CLK, output USBPU, output LED, input PIN_1, output PIN_2);
   assign USBPU = 1'b0;

   reg [3:0] counter = 0;
   wire RST_N = counter[3];
   always @(posedge CLK)
     counter <= counter + {3'b0, ~RST_N};

   top_uart core(.CLK(CLK), .RST_N(RST_N), .LED(LED), .uart_line_in(PIN_1), .uart_line_out(PIN_2));
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
