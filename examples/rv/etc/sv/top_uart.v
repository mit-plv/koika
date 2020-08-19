// -*- verilog -*-
/*! Verilog wrapper for the Kôika core with a UART interface !*/
// This toplevel is a good starting point to connect directly to a UART receiver
module top_uart(input CLK, input RST_N, output LED, input uart_line_in, output uart_line_out);
   wire[69:0] dmem_out;
   wire[69:0] dmem_arg;

   wire[69:0] imem_out;
   wire[69:0] imem_arg;

   wire[8:0] uart_wr_opt_byte;
   wire uart_wr_ready;

   wire[8:0] uart_rd_opt_byte = {1'b0, 8'b0};
   wire uart_rd_ready;

   wire led_wr_valid;
   wire led_wr_data;

   reg led = 1'b0;
   assign LED = led;

   uart comms(.CLK(CLK), .RST_N(RST_N),
              .read_byte_arg(uart_wr_ready),
              .read_byte_out(uart_wr_opt_byte),
              .write_bit_arg(uart_line_out),
              .write_bit_out(1'b0));

   // FIXME: Implement a UART emitter

   rv32 core(.CLK(CLK), .RST_N(RST_N),

             .ext_mem_dmem_arg(dmem_arg),
             .ext_mem_dmem_out(dmem_out),

             .ext_mem_imem_arg(imem_arg),
             .ext_mem_imem_out(imem_out),

             .ext_uart_write_arg(uart_wr_opt_byte),
             .ext_uart_write_out(uart_wr_ready),

             .ext_uart_read_arg(uart_rd_ready),
             .ext_uart_read_out(uart_rd_opt_byte),

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
   wire uart_wr_valid = uart_wr_opt_byte[8];
   always @(posedge CLK) begin
      if (uart_wr_ready && uart_wr_valid)
        $fwrite(`STDERR, "%c", uart_wr_opt_byte[7:0]);
   end
`endif
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32i.v/")
// End:
