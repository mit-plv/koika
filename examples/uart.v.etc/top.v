// -*- verilog -*-

module top(input CLK, input RST_N, output tx);
`define NINPUTS 5
   reg[7:0] inputs[`NINPUTS - 1:0] = '{"k", "o", "i", "k", "a"};
   reg [2:0] pos = 0;

   wire[7:0] next_input = inputs[pos];
   wire next_input_valid = 1'b1;
   wire uart_ready;

   uart comms(.CLK, .RST_N, .read_byte_out({next_input_valid, next_input}), .read_byte_arg(uart_ready), .write_bit_out(1'b0), .write_bit_arg(tx));

   always @(posedge CLK) begin
      if (pos > `NINPUTS)
        $finish(1'b0);
      if (uart_ready)
        pos <= pos + 1;
   end
endmodule
