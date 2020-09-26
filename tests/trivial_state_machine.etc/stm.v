// -*- mode: verilog -*-
/*! Cleaned-up state machine example !*/
`define A 1'b0
`define B 1'b1
module stm(CLK, in, out);
   input wire CLK;
   input wire [31:0] in;
   output wire [31:0] out;

   reg st = 1'b0;
   reg [31:0] r = 32'b0;

   wire [31:0] fB_out, fA_out;
   fA mod_fA(.r(r), .in(in), .out(fA_out));
   fB mod_fB(.r(r), .in(in), .out(fB_out));

   assign out = r;
   always @(posedge CLK) begin
	  st <= st == `A ? `B : `A;
	  r <= st == `A ? fA_out : fB_out;
   end
endmodule
