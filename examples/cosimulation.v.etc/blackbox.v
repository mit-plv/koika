module blackbox(input wire CLK, input wire[31:0] in, output wire[31:0] out);
   reg[31:0] delayed = 42;

   assign out = delayed;
   always @(posedge CLK) delayed <= in;
endmodule
