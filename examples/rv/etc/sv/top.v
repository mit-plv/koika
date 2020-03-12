// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in simulation) !*/
// This toplevel is mostly for simulation, since it assumes the UART module
// is always ready to transmit.
module top(input CLK, input RST_N, output uart_wr_valid, output[7:0] uart_wr_data, output LED);
   wire uart_wr_ready = 1'b1;

   wire uart_rd_valid = 1'b0;
   wire[7:0] uart_rd_data = 8'b0;
   wire uart_rd_ready;

   wire led_wr_valid;
   wire led_wr_data;

   reg led = 1'b0;
   assign LED = led;

   rv32 core(.CLK(CLK), .RST_N(RST_N),
             .ext_uart_write_arg({uart_wr_valid, uart_wr_data}),
             .ext_uart_write_out(uart_wr_ready),

             .ext_uart_read_arg(uart_rd_ready),
             .ext_uart_read_out({uart_rd_valid, uart_rd_data}),

             .ext_led_arg({led_wr_valid, led_wr_data}),
             .ext_led_out(led));

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
