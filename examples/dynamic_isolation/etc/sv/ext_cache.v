// -*- verilog -*-

/*! Wrapper used to connect the cache model with Kôika !*/
module ext_cache(input CLK, input RST_N, input[71:0] arg, output[53:0] out, output finish);
   parameter CORE_ID = 3;
   parameter CACHE_TY = 3;


   wire get_valid;
   wire put_valid;
   wire[69:0] put_request;
   assign {get_valid, put_valid, put_request} = arg;

   wire get_ready;
   wire put_ready;
   wire [51:0] get_response;
   assign out = {get_ready, put_ready, get_response};


   cache #(.CORE_ID(CORE_ID),
		   .CACHE_TY(CACHE_TY))
	 m(.CLK(CLK), .RST_N(RST_N),
		   .get_valid(get_valid), .put_valid(put_valid), .put_request(put_request),
		   .get_ready(get_ready), .put_ready(put_ready), .get_response(get_response),
		   .finish(finish));
endmodule
