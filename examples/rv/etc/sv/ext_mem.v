// -*- verilog -*-
/*! Wrapper used to connect the BRAM model with Kôika !*/
module ext_mem(input CLK, input RST_N, input[69:0] arg, output[69:0] out);
   wire get_valid;
   wire put_valid;
   wire[67:0] put_request;
   assign {get_valid, put_valid, put_request} = arg;

   wire get_ready;
   wire put_ready;
   wire [67:0] get_response;
   assign out = {get_ready, put_ready, get_response};

`ifndef STDERR
 `define STDERR 32'h80000002
`endif

`ifndef MEM_ADDRESS_WIDTH
 `define MEM_ADDRESS_WIDTH 16
   initial $fwrite(`STDERR,
                   "MEM_ADDRESS_WIDTH unset, defaulting to %d",
                   `MEM_ADDRESS_WIDTH);
`endif

   memory #(.ADDRESS_WIDTH(`MEM_ADDRESS_WIDTH))
   m(.CLK(CLK), .RST_N(RST_N),
     .get_valid(get_valid), .put_valid(put_valid), .put_request(put_request),
     .get_ready(get_ready), .put_ready(put_ready), .get_response(get_response));
endmodule
