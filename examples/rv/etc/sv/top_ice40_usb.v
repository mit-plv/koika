// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in FPGA synthesis, with a USB interface) !*/
module top_ice40_usb(input CLK, inout USBP, inout USBN, output USBPU, output LED);
   assign USBPU = 1'b1;

   wire clk_48mhz;
   wire clk_locked;
   pll pll48(.clock_in(CLK), .clock_out(clk_48mhz), .locked(clk_locked));

   reg [3:0] reset_counter = 4'b0;
   wire reset = ~reset_counter[3];

   always @(posedge clk_48mhz)
     if (clk_locked)
       reset_counter <= reset_counter + {3'b0, reset};

   wire [69:0] dmem_out;
   wire[69:0] dmem_arg;

   wire[69:0] imem_out;
   wire[69:0] imem_arg;

   wire uart_wr_valid;
   wire[7:0] uart_wr_data;
   wire uart_wr_ready;

   wire uart_rd_valid;
   wire[7:0] uart_rd_data;
   wire uart_rd_ready;

   wire led_wr_valid;
   wire led_wr_data;

   reg led = 1'b0;
   assign LED = led;

   reg RST_N = 1'b0;

   rv32 core(.CLK(CLK), .RST_N(RST_N),

             .ext_mem_dmem_arg(dmem_arg),
             .ext_mem_dmem_out(dmem_out),

             .ext_mem_imem_arg(imem_arg),
             .ext_mem_imem_out(imem_out),

             .ext_uart_write_arg({uart_wr_valid, uart_wr_data}),
             .ext_uart_write_out(uart_wr_ready),

             .ext_uart_read_arg(uart_rd_ready),
             .ext_uart_read_out({uart_rd_valid, uart_rd_data}),

             .ext_led_arg({led_wr_valid, led_wr_data}),
             .ext_led_out(led));

   ext_mem imem(.CLK(CLK), .RST_N(RST_N), .arg(imem_arg), .out(imem_out));
   ext_mem dmem(.CLK(CLK), .RST_N(RST_N), .arg(dmem_arg), .out(dmem_out));

   always @(posedge CLK)
     RST_N <= ~reset;

   always @(posedge CLK)
     if (led_wr_valid)
       led <= led_wr_data;

   usb_uart_i40 uart(.clk_48mhz(clk_48mhz),
                     .reset(reset),

                     .pin_usb_p(USBP),
                     .pin_usb_n(USBN),

                     .uart_in_data(uart_wr_data),
                     .uart_in_valid(uart_wr_valid),
                     .uart_in_ready(uart_wr_ready),

                     .uart_out_data(uart_rd_data),
                     .uart_out_valid(uart_rd_valid),
                     .uart_out_ready(uart_rd_ready));
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("tinyfpga_bx_usbserial/usb" "../../_objects/rv32i.v/")
// End:
