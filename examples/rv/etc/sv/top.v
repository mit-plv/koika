// -*- verilog -*-
// This toplevel is mostly for simulation, since it assumes the UART module
// is always ready to transmit.
module top(input CLK, input RST_N, output[7:0] uart_wr_data, output uart_wr_valid);
   wire uart_wr_ready = 1'b1;

   rv32 core(.CLK(CLK), .RST_N(RST_N),
             .ext_uart_write_arg({uart_wr_valid, uart_wr_data}),
             .ext_uart_write_out(uart_wr_ready));

`ifdef SIMULATION
   always @(posedge CLK) begin
      if (uart_wr_ready && uart_wr_valid)
        $fwrite(32'h80000002, "%c", uart_wr_data);
   end
`endif
endmodule

// Local Variables:
// flycheck-verilator-include-path: ("../../_objects/rv32.v/")
// End:
