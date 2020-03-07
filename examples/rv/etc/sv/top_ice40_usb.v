// -*- verilog -*-
module top_ice40_usb(input CLK, inout USBP, inout USBN, output USBPU);
   assign USBPU = 1'b1;

   wire clk_48mhz;
   wire clk_locked;
   pll pll48(.clock_in(CLK), .clock_out(clk_48mhz), .locked(clk_locked));

   reg [3:0] counter = 0;
   wire RST_N = counter[3];
   always @(posedge CLK)
     if (clk_locked)
       counter <= counter + {3'b0, ~RST_N};

   wire uart_wr_valid;
   wire[7:0] uart_wr_data;
   wire uart_wr_ready;

   rv32 core(.CLK(CLK), .RST_N(RST_N),
             .ext_uart_write_arg({uart_wr_valid, uart_wr_data}),
             .ext_uart_write_out(uart_wr_ready));

   wire usb_p_tx;
   wire usb_n_tx;
   wire usb_p_rx;
   wire usb_n_rx;
   wire usb_tx_en;

   usb_uart_i40 uart(.clk_48mhz(clk_48mhz),
                     .reset(~RST_N),

                     .pin_usb_p(USBP),
                     .pin_usb_n(USBN),

                     .uart_in_data(uart_wr_data),
                     .uart_in_valid(uart_wr_valid),
                     .uart_in_ready(uart_wr_ready),

                     // .uart_out_data(uart_out_data),
                     // .uart_out_valid(uart_out_valid),
                     .uart_out_ready(1'b0));
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("tinyfpga_bx_usbserial/usb" "../../_objects/rv32.v/")
// End:
