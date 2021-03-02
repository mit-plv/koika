
module morse_top(input wire[0:0] clk, output wire[0:0] TOPled_arg);
   reg[5:0] reset_cycle = 0;
   wire rst;
   assign rst_n = reset_cycle == 10;
   morse mymorse(.CLK(clk), .RST_N(rst_n), .led_arg(TOPled_arg), .led_out(0));
	 always @(posedge clk) begin
      if (reset_cycle < 10 ) reset_cycle = reset_cycle + 1;
   end
endmodule
