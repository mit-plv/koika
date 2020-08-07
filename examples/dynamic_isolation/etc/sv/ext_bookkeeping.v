// -*- verilog -*-

/*! Wrapper used to connect the cache model with Kôika !*/
module ext_bookkeeping(input CLK, input RST_N, input[36:0] arg, output[81:0] out);

   wire get_valid;
   wire put_valid;
   wire[34:0] put_request;
   assign {get_valid, put_valid, put_request} = arg;

   wire get_ready;
   wire put_ready;
   wire [79:0] get_response;
   assign out = {get_ready, put_ready, get_response};


   bookkeeping_directory m(.CLK(CLK), .RST_N(RST_N),
		   .get_valid(get_valid), .put_valid(put_valid), .put_request(put_request),
		   .get_ready(get_ready), .put_ready(put_ready), .get_response(get_response));
endmodule
