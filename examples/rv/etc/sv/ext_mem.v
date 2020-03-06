// -*- verilog -*-
module ext_mem(input CLK, input RST_N, input[69:0] arg, output[69:0] out);
   wire get_valid;
   wire put_valid;
   wire[67:0] put_request;
   assign {get_valid, put_valid, put_request} = arg;

   wire get_ready;
   wire put_ready;
   wire [67:0] get_response;
   assign out = {get_ready, put_ready, get_response};

   memory #(.ADDRESS_WIDTH(14))
   m(.CLK, .RST_N,
     .get_valid, .put_valid, .put_request,
     .get_ready, .put_ready, .get_response);
endmodule
