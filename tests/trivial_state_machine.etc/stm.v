// -*- mode: verilog -*-
/*! Cleaned-up state machine example !*/
`define A 1'b0
`define B 1'b1
module stm(CLK, inputs, outputs);
   input wire CLK;
   input wire [31:0] inputs;
   output wire [31:0] outputs;

   reg st = 1'b0;
   reg [31:0] r = 32'b0;

   wire [31:0] mod_extB_out, mod_extA_out;
   extA mod_extA(.r(r), .in(inputs), .out(mod_extA_out));
   extB mod_extB(.r(r), .in(inputs), .out(mod_extB_out));

   assign outputs = r;
   always @(posedge CLK) begin
	  st <= st == `A ? `B : `A;
	  r <= st == `A ? mod_extA_out : mod_extB_out;
   end
endmodule
