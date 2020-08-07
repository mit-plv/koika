// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in simulation) !*/
// This toplevel is mostly for simulation, since it assumes the UART module
// is always ready to transmit.
module top(input CLK, input RST_N, output uart_wr_valid, output[7:0] uart_wr_data, output LED);
   wire[36:0] ppp_bookkeeping_arg;
   wire[81:0] ppp_bookkeeping_out;

   wire[71:0] cache_imem0_arg;
   wire[53:0] cache_imem0_out;
   wire[71:0] cache_imem1_arg;
   wire[53:0] cache_imem1_out;

   wire[71:0] cache_dmem0_arg;
   wire[53:0] cache_dmem0_out;
   wire[71:0] cache_dmem1_arg;
   wire[53:0] cache_dmem1_out;

   wire[69:0] mainmem_out;
   wire[69:0] mainmem_arg;


   wire uart_wr_ready = 1'b1;

   wire uart_rd_valid = 1'b0;
   wire[7:0] uart_rd_data = 8'b0;
   wire uart_rd_ready;

   wire led_wr_valid;
   wire led_wr_data;

   reg led = 1'b0;
   assign LED = led;

   rv32 core(.CLK(CLK), .RST_N(RST_N),

			 .ext_ppp_bookkeeping_arg(ppp_bookkeeping_arg),
			 .ext_ppp_bookkeeping_out(ppp_bookkeeping_out),

			 .ext_cache_imem0_arg(cache_imem0_arg),
			 .ext_cache_imem0_out(cache_imem0_out),
			 .ext_cache_imem1_arg(cache_imem1_arg),
			 .ext_cache_imem1_out(cache_imem1_out),

			 .ext_cache_dmem0_arg(cache_dmem0_arg),
			 .ext_cache_dmem0_out(cache_dmem0_out),
			 .ext_cache_dmem1_arg(cache_dmem1_arg),
			 .ext_cache_dmem1_out(cache_dmem1_out),

			 .ext_mainmem_arg(mainmem_arg),
			 .ext_mainmem_out(mainmem_out),

             .ext_uart_write_arg({uart_wr_valid, uart_wr_data}),
             .ext_uart_write_out(uart_wr_ready),

             .ext_uart_read_arg(uart_rd_ready),
             .ext_uart_read_out({uart_rd_valid, uart_rd_data}),

             .ext_led_arg({led_wr_valid, led_wr_data}),
             .ext_led_out(led));

   ext_mem mainmem(.CLK(CLK), .RST_N(RST_N), .arg(mainmem_arg), .out(mainmem_out));
   ext_cache imem0(.CLK(CLK), .RST_N(RST_N), .arg(cache_imem0_arg), .out(cache_imem0_out));
   ext_cache dmem0(.CLK(CLK), .RST_N(RST_N), .arg(cache_dmem0_arg), .out(cache_dmem0_out));
   ext_cache imem1(.CLK(CLK), .RST_N(RST_N), .arg(cache_imem1_arg), .out(cache_imem1_out));
   ext_cache dmem1(.CLK(CLK), .RST_N(RST_N), .arg(cache_dmem1_arg), .out(cache_dmem1_out));

   always @(posedge CLK)
     if (led_wr_valid)
       led <= led_wr_data;

`ifdef SIMULATION
   always @(posedge CLK) begin
      if (led_wr_valid) begin
        if (led_wr_data)
          $fwrite(32'h80000002, "☀");
        else
          $fwrite(32'h80000002, "🌣");
      end
      if (uart_wr_ready && uart_wr_valid)
        $fwrite(32'h80000002, "%c", uart_wr_data);
   end
`endif
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
