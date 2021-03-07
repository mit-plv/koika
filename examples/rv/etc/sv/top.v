// -*- verilog -*-
/*! Verilog wrapper for the Kôika core (for use in simulation) !*/
// This toplevel is mostly for simulation, since it assumes the UART module
// is always ready to transmit.
module top(input CLK, input RST_N, output uart_wr_valid, output[7:0] uart_wr_data, output LED);
   wire[69:0] dmem_out;
   wire[69:0] dmem_arg;

   wire[69:0] imem_out;
   wire[69:0] imem_arg;

   wire uart_wr_ready = 1'b1;

   wire uart_rd_valid = 1'b0;
   wire[7:0] uart_rd_data = 8'b0;

   wire led_wr_valid;
   wire led_wr_data;

   reg led = 1'b0;
   assign LED = led;

   rv32 core(.CLK(CLK), .RST_N(RST_N),

             .ext_mem_dmem_arg(dmem_arg),
             .ext_mem_dmem_out(dmem_out),

             .ext_mem_imem_arg(imem_arg),
             .ext_mem_imem_out(imem_out),

             .ext_uart_write_arg({uart_wr_valid, uart_wr_data}),
             .ext_uart_write_out(uart_wr_ready),

             .ext_uart_read_arg(),
             .ext_uart_read_out({uart_rd_valid, uart_rd_data}),

             .ext_led_arg({led_wr_valid, led_wr_data}),
             .ext_led_out(led));

   ext_mem imem(.CLK(CLK), .RST_N(RST_N), .arg(imem_arg), .out(imem_out));
   ext_mem dmem(.CLK(CLK), .RST_N(RST_N), .arg(dmem_arg), .out(dmem_out));

   always @(posedge CLK)
     if (led_wr_valid)
       led <= led_wr_data;

`ifndef STDERR
 `define STDERR 32'h80000002
`endif

`ifdef SIMULATION
   always @(posedge CLK) begin
      if (led_wr_valid) begin
         if (led_wr_data)
           $fwrite(`STDERR, "☀");
         else
           $fwrite(`STDERR, "🌣");
      end
      if (uart_wr_ready && uart_wr_valid)
        $fwrite(`STDERR, "%c", uart_wr_data);
   end
`endif
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
