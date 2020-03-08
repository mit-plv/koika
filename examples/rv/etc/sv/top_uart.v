// -*- verilog -*-
/*! Verilog wrapper for the Kôika core with a UART interface !*/
// This toplevel is a good starting point to connect directly to a UART receiver
module top_uart(input CLK, input RST_N, output uart_line_out);
   wire[8:0] uart_opt_byte;
   wire uart_wr_ready;

   uart comms(.CLK(CLK), .RST_N(RST_N),
              .read_byte_arg(uart_wr_ready),
              .read_byte_out(uart_opt_byte),
              .write_bit_arg(uart_line_out),
              .write_bit_out(1'b0));

   rv32 core(.CLK(CLK), .RST_N(RST_N),
             .ext_uart_write_arg(uart_opt_byte),
             .ext_uart_write_out(uart_wr_ready));

`ifdef SIMULATION
   wire uart_wr_valid = uart_opt_byte[8];
   always @(posedge CLK) begin
      if (uart_wr_ready && uart_wr_valid)
        $fwrite(32'h80000002, "%c", uart_opt_byte[7:0]);
   end
`endif
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32.v/")
// End:
