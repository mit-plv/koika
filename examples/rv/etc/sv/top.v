// -*- verilog -*-
module top(input CLK, input RST_N, output uart_line_out);
   wire uart_wr_valid;
   wire[7:0] uart_wr_data;
   wire uart_wr_ready;

   uart uout(.CLK, .RST_N,
             .wr_valid(uart_wr_valid),
             .wr_data(uart_wr_data),
             .wr_ready(uart_wr_ready),
             .line_out(uart_line_out));
   rv32 core(.CLK, .RST_N,
             .ext_uart_write_arg({uart_wr_valid, uart_wr_data}),
             .ext_uart_write_out(uart_wr_ready));
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32.v/")
// End:
