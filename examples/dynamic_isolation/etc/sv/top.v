// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in simulation) !*/
// This toplevel is mostly for simulation, since it assumes the UART module
// is always ready to transmit.
module top(input CLK, input RST_N, output uart_wr_valid0, output[7:0] uart_wr_data0, output LED0, output uart_wr_valid1, output[7:0] uart_wr_data1, output LED1);
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


   wire uart_wr_ready0 = 1'b1;

   wire uart_rd_valid0 = 1'b0;
   wire[7:0] uart_rd_data0 = 8'b0;
   wire uart_rd_ready0;

   wire led_wr_valid0;
   wire led_wr_data0;

   reg led0 = 1'b0;
   assign LED0 = led0;

   wire uart_wr_ready1 = 1'b1;

   wire uart_rd_valid1 = 1'b0;
   wire[7:0] uart_rd_data1 = 8'b0;
   wire uart_rd_ready1;

   wire led_wr_valid1;
   wire led_wr_data1;

   reg led1 = 1'b0;
   assign LED1 = led1;


   // TODO: for simulation, replace with external call
   reg core0_done = 1'b0;
   reg core1_done = 1'b0;

   wire imem0_finish;
   wire dmem0_finish;
   wire imem1_finish;
   wire dmem1_finish;

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

             .ext_uart_write0_arg({uart_wr_valid0, uart_wr_data0}),
             .ext_uart_write0_out(uart_wr_ready0),

             .ext_uart_read0_arg(uart_rd_ready0),
             .ext_uart_read0_out({uart_rd_valid0, uart_rd_data0}),

             .ext_led0_arg({led_wr_valid0, led_wr_data0}),
             .ext_led0_out(led0),

			 .ext_uart_write1_arg({uart_wr_valid1, uart_wr_data1}),
             .ext_uart_write1_out(uart_wr_ready1),

             .ext_uart_read1_arg(uart_rd_ready1),
             .ext_uart_read1_out({uart_rd_valid1, uart_rd_data1}),

             .ext_led1_arg({led_wr_valid1, led_wr_data1}),
             .ext_led1_out(led1)
			);

   ext_bookkeeping bookkeeping_dir (.CLK(CLK), .RST_N(RST_N), .arg(ppp_bookkeeping_arg), .out(ppp_bookkeeping_out));
   ext_mem mainmem(.CLK(CLK), .RST_N(RST_N), .arg(mainmem_arg), .out(mainmem_out));
   ext_cache #(.CORE_ID(0), .CACHE_TY(0))
             imem0(.CLK(CLK), .RST_N(RST_N), .arg(cache_imem0_arg), .out(cache_imem0_out), .finish(imem0_finish));
   ext_cache #(.CORE_ID(0), .CACHE_TY(1))
	         dmem0(.CLK(CLK), .RST_N(RST_N), .arg(cache_dmem0_arg), .out(cache_dmem0_out), .finish(dmem0_finish));
   ext_cache #(.CORE_ID(1), .CACHE_TY(0))
             imem1(.CLK(CLK), .RST_N(RST_N), .arg(cache_imem1_arg), .out(cache_imem1_out), .finish(imem1_finish));
   ext_cache #(.CORE_ID(1), .CACHE_TY(1))
             dmem1(.CLK(CLK), .RST_N(RST_N), .arg(cache_dmem1_arg), .out(cache_dmem1_out), .finish(dmem1_finish));


   always @(posedge CLK)
     if (led_wr_valid0)
       led0 <= led_wr_data0;

   always @(posedge CLK)
     if (led_wr_valid1)
       led1 <= led_wr_data1;

`ifdef SIMULATION
   always @(posedge CLK) begin
	  core0_done <= core0_done || dmem0_finish || imem0_finish;
	  core1_done <= core1_done || dmem1_finish || imem1_finish;

	  if (core0_done && core1_done) begin
		 $finish(1'b1);
	  end

      if (led_wr_valid0) begin
        if (led_wr_data0)
          $fwrite(32'h80000002, "☀");
        else
          $fwrite(32'h80000002, "🌣");
      end
      if (uart_wr_ready0 && uart_wr_valid0)
        $fwrite(32'h80000002, "%c", uart_wr_data0);

	  if (led_wr_valid1) begin
        if (led_wr_data1)
          $fwrite(32'h80000002, "☀");
        else
          $fwrite(32'h80000002, "🌣");
      end
      if (uart_wr_ready1 && uart_wr_valid1)
        $fwrite(32'h80000002, "%c", uart_wr_data1);

   end
`endif
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
