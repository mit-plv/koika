// -*- mode: verilog -*-
/*! Testbench used with CVC and Icarus Verilog !*/
`timescale 1 ns / 1 ns
module testbench();
   reg CLK = 1'b0;
   reg RST_N = 1'b0;

   wire uart_wr_valid;
   wire [7:0] uart_wr_data;
   wire LED;

   top m(.CLK(CLK), .RST_N(RST_N),
         .uart_wr_valid(uart_wr_valid), .uart_wr_data(uart_wr_data),
         .LED(LED));

   always begin
      #1 begin
         CLK = ~CLK;
      end
   end
   initial begin
      #1 RST_N = 1'b0;
      #10 RST_N = 1'b1;
   end
endmodule
