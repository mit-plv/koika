//
// Generated by Bluespec Compiler (build baae2d1)
//
// On Wed Aug 19 23:26:00 EDT 2020
//
//
// Ports:
// Name                         I/O  size props
// rd                             O    64 reg
// RDY_rd                         O     1 const
// CLK                            I     1 clock
// RST_N                          I     1 reset
//
// No combinational paths from inputs to outputs
//
//

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

module mkfir(CLK,
	     RST_N,

	     rd,
	     RDY_rd);
  input  CLK;
  input  RST_N;

  // value method rd
  output [63 : 0] rd;
  output RDY_rd;

  // signals for module outputs
  wire [63 : 0] rd;
  wire RDY_rd;

  // register q
  reg [63 : 0] q;
  wire [63 : 0] q$D_IN;
  wire q$EN;

  // register x
  reg [7 : 0] x;
  wire [7 : 0] x$D_IN;
  wire x$EN;

  // remaining internal signals
  wire [31 : 0] _3_MUL_SEXT_x___d9, _65535_MUL_SEXT_x___d5;
  wire [15 : 0] SEXT_x____d4;
  wire [7 : 0] x__h1649;

  // value method rd
  assign rd = q ;
  assign RDY_rd = 1'd1 ;

  // register q
  assign q$D_IN =
	     { q[47:32] + _65535_MUL_SEXT_x___d5[15:0],
	       q[31:16] + _3_MUL_SEXT_x___d9[15:0],
	       q[15:0] + { SEXT_x____d4[13:0], 2'd0 },
	       16'd0 } ;
  assign q$EN = 1'd1 ;

  // register x
  assign x$D_IN = x__h1649 % 8'd19 ;
  assign x$EN = 1'd1 ;

  // remaining internal signals
  assign SEXT_x____d4 = { {8{x[7]}}, x } ;
  assign _3_MUL_SEXT_x___d9 = 16'd3 * SEXT_x____d4 ;
  assign _65535_MUL_SEXT_x___d5 = 16'd65535 * SEXT_x____d4 ;
  assign x__h1649 = x + 8'd9 ;

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        q <= `BSV_ASSIGNMENT_DELAY 64'hAAAAAAAAAAAAAAAA;
	x <= `BSV_ASSIGNMENT_DELAY 8'd0;
      end
    else
      begin
        if (q$EN) q <= `BSV_ASSIGNMENT_DELAY q$D_IN;
	if (x$EN) x <= `BSV_ASSIGNMENT_DELAY x$D_IN;
      end
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    q = 64'hAAAAAAAAAAAAAAAA;
    x = 8'hAA;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on
endmodule  // mkfir

