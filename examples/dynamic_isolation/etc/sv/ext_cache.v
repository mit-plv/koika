// -*- verilog -*-

/*! Wrapper used to connect the cache model with Kôika !*/
module ext_cache(input CLK, input RST_N, input[71:0] arg, output[53:0] out);

   wire get_valid;
   wire put_valid;
   wire[69:0] put_request;
   assign {get_valid, put_valid, put_request} = arg;

   wire get_ready;
   wire put_ready;
   wire [51:0] get_response;
   assign out = {get_ready, put_ready, get_response};


   cache m(.CLK(CLK), .RST_N(RST_N),
		   .get_valid(get_valid), .put_valid(put_valid), .put_request(put_request),
		   .get_ready(get_ready), .put_ready(put_ready), .get_response(get_response));
endmodule
