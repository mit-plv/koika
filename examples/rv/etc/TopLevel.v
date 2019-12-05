/*! Verilog wrapper for the RISC-V processor !*/
module TopLevel(
 input 		   clock,
 input 		   reset,
 input 		   i_or_d,
 input 		   write_en,
 input 		   read_en,
 input [31:0] 	   data_in,
 output reg [31:0] data_out,
 input [31:0] 	   addr);

   reg [31:0] 	   imem [0:1024];
   reg [31:0] 	   dmem [0:1024];

   wire toImem_valid;
   wire [64:0] toImem_req;
   wire toDmem_valid;
   wire [64:0] toDmem_req;
   wire fromDmem_valid;
   wire [64:0] fromDmem_resp;
   wire fromImem_valid;
   wire [64:0] fromImem_resp;

   wire toImem_valid_out;
   wire [64:0] toImem_req_out;
   wire toDmem_valid_out;
   wire [64:0] toDmem_req_out;
   wire fromDmem_valid_out;
   wire [64:0] fromDmem_resp_out;
   wire fromImem_valid_out;
   wire [64:0] fromImem_resp_out;

   wire fromImem_touched;
   wire fromDmem_touched;
   wire toDmem_touched;
   wire toImem_touched;

   rv_core core(.clock(clock),
		.reset(reset),
		.rule_external_output_toIMem_valid0_data0(toImem_valid_out),
		.rule_external_output_toIMem_data0_data0(toImem_req_out),
		.rule_external_output_toDMem_valid0_data0(toDmem_valid_out),
		.rule_external_output_toDMem_data0_data0(toDmem_req_out),
		.rule_external_output_fromIMem_data0_data0(fromImem_resp_out),
		.rule_external_output_fromIMem_valid0_data0(fromImem_valid_out),
		.rule_external_output_fromDMem_data0_data0(fromDmem_resp_out),
		.rule_external_output_fromDMem_valid0_data0(fromDmem_valid_out),

	        .rule_external_input_toIMem_data0_data0(toImem_req),
		.rule_external_input__canfire(1),
		.rule_external_input_fromDMem_data0_data1(0),
		.rule_external_input_fromDMem_data0_data0(fromDmem_resp),
		.rule_external_input_fromDMem_data0_write1(0),
		.rule_external_input_fromDMem_data0_write0(fromDmem_touched),
		.rule_external_input_fromDMem_data0_read1(0),
		.rule_external_input_fromDMem_data0_read0(1),
		.rule_external_input_fromDMem_valid0_data1(0),
		.rule_external_input_fromDMem_valid0_data0(fromDmem_valid),
		.rule_external_input_fromDMem_valid0_write1(0),
		.rule_external_input_fromDMem_valid0_write0(fromDmem_touched),
		.rule_external_input_fromDMem_valid0_read1(0),
		.rule_external_input_fromDMem_valid0_read0(1),
		.rule_external_input_toIMem_data0_write1(0),
		.rule_external_input_toIMem_data0_read1(0),
		.rule_external_input_toIMem_data0_write0(toImem_touched),
		.rule_external_input_toIMem_valid0_write1(0),
		.rule_external_input_toIMem_valid0_read1(0),
		.rule_external_input_toIMem_valid0_write0(toImem_touched),
		.rule_external_input_fromIMem_data0_write1(0),
		.rule_external_input_fromIMem_data0_read1(0),
		.rule_external_input_fromIMem_data0_write0(fromImem_touched),
		.rule_external_input_fromIMem_valid0_write1(0),
		.rule_external_input_fromIMem_valid0_read1(0),
		.rule_external_input_fromIMem_valid0_write0(fromImem_touched),
		.rule_external_input_toDMem_data0_write1(0),
		.rule_external_input_toDMem_data0_read1(0),
		.rule_external_input_toDMem_data0_write0(toDmem_touched),
		.rule_external_input_toDMem_valid0_write1(0),
		.rule_external_input_toDMem_valid0_read1(0),
		.rule_external_input_toDMem_valid0_write0(toDmem_touched),
		.rule_external_input_toDMem_valid0_data1(0),
		.rule_external_input_toDMem_valid0_data0(toDmem_valid),
		.rule_external_input_toDMem_valid0_read0(1),
		.rule_external_input_toDMem_data0_data1(0),
		.rule_external_input_toDMem_data0_data0(toDmem_req),
		.rule_external_input_toDMem_data0_read0(1),
		.rule_external_input_fromIMem_data0_data1(0),
		.rule_external_input_fromIMem_data0_data0(fromImem_resp),
		.rule_external_input_fromIMem_data0_read0(1),
		.rule_external_input_fromIMem_valid0_data1(0),
		.rule_external_input_fromIMem_valid0_data0(fromImem_valid),
		.rule_external_input_fromIMem_valid0_read0(1),
		.rule_external_input_toIMem_valid0_data1(0),
		.rule_external_input_toIMem_valid0_data0(toImem_valid),
		.rule_external_input_toIMem_valid0_read0(1),
		.rule_external_input_toIMem_data0_data1(0),
		.rule_external_input_toIMem_data0_read0(1));
   assign toImem_req = toImem_req_out;
   assign toDmem_req = toDmem_req_out;

   assign fromImem_touched = (write_en | read_en ? 0 :
			      (toImem_valid_out && !fromImem_valid_out)) ;
   assign fromDmem_touched = (write_en | read_en ? 0 :
			      (toDmem_valid_out && !fromDmem_valid_out)) ;
   assign toDmem_touched = (write_en | read_en ? 0 :
			    (toDmem_valid_out && !fromDmem_valid_out)) ;
   assign toImem_touched = (write_en | read_en ? 0 :
			    (toImem_valid_out && !fromImem_valid_out)) ;

   assign toImem_valid = (write_en | read_en ? toImem_valid_out :
			  !toImem_touched & toImem_valid_out) ;
   assign toDmem_valid = (write_en | read_en ? toDmem_valid_out :
			  !toDmem_touched & toDmem_valid_out) ;
   assign fromDmem_valid = (write_en | read_en ? fromDmem_valid_out :
			    toDmem_touched | fromDmem_valid_out) ;
   assign fromImem_valid = (write_en | read_en ? fromImem_valid_out :
			    toImem_touched | fromImem_valid_out) ;

   assign fromImem_resp = (write_en | read_en ? fromImem_resp_out :
			  ((toImem_req_out[64]==1) & toImem_touched
			   ? {1'b0, toImem_req_out[63:32], imem[toImem_req_out[31:0]]}
			   : toImem_req)) ;
   assign fromDmem_resp = (write_en | read_en ? fromDmem_resp_out :
			  ((toDmem_req_out[64]==1) & toDmem_touched
			   ? {1'b0, toDmem_req_out[63:32], dmem[toDmem_req_out[31:0]]}
			   : toDmem_req)) ;


   always @(posedge clock) begin
      if (write_en) begin
	 if (i_or_d) imem[addr] <= data_in;
	 else dmem[addr] <= data_in;
      end else
	if (read_en) begin
	   if(i_or_d) data_out <= imem[addr];
	   else  data_out <= dmem[addr];
	end else begin
	   // imem
	   if (toImem_valid_out && !fromImem_valid_out) begin
	      // there is a question and room for an answer
	      if (toImem_req_out[64]==1) begin
		 // Store
		 imem[toImem_req_out[63:32]] <= imem[toImem_req_out[31:0]];
	      end
	   end
	   // dmem
	   if (toDmem_valid_out && !fromDmem_valid_out) begin
	      if (toDmem_req_out[64]==1) begin
		 dmem[toDmem_req_out[63:32]] <= dmem[toDmem_req_out[31:0]];
	      end
	   end
	end
   end
endmodule
