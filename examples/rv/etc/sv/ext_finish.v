// -*- mode: verilog -*-
// Detects when the processor wants to exit and call $finish.
// This is done as an internal module as a way to test our support for them.
module ext_finish(input wire CLK, input wire RST_N, input wire[8:0] arg, output wire out);
   wire finish;
   wire[7:0] exitcode;

   assign {finish, exitcode} = arg;
   assign out = 1'b0;

`ifndef STDERR
 `define STDERR 32'h80000002
`endif

`ifdef SIMULATION
   always @(posedge CLK)
     if (finish) begin
        if (exitcode == 0)
    	  $fwrite(`STDERR, "  [0;32mPASS[0m\n");
    	else
    	  $fwrite(`STDERR, "  [0;31mFAIL[0m (%0d)\n", exitcode);
        $finish();
     end
`endif
endmodule // ext_finish
