// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in FPGA synthesis, with a UART interface) !*/
module top_ulx3s(input clk_25mhz,
                 input [6:0]  btn,
                 output [7:0] led,
                 output ftdi_rxd,
                 output wifi_gpio0);
   // Tye GPIO0 to prevent ULX3S from rebooting
   assign wifi_gpio0 = 1'b1;

   reg [3:0] counter = 0;
   wire RST_N = counter[3];
   always @(posedge clk_25mhz)
     counter <= counter + {3'b0, ~RST_N};

   assign led[2:0] = 3'b0;
   assign led[7:4] = 4'b0;

   wire uart_in = 1'b0;
   top_uart core(.CLK(clk_25mhz), .RST_N(RST_N), .LED(led[3]),
                 .uart_line_in(uart_in), .uart_line_out(ftdi_rxd));
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
