// -*- verilog -*-

/*! Verilog model of a single-cycle/instantaneous cache !*/
`define BYTE_EN_WIDTH 4
`define CACHE_TAG_WIDTH 18
`define CACHE_INDEX_WIDTH 12 // num sets
`define CACHE_DATA_WIDTH 32
`define ADDR_WIDTH 32
`define CACHE_REQ_SIZE (`BYTE_EN_WIDTH + `CACHE_TAG_WIDTH + `CACHE_INDEX_WIDTH + `CACHE_DATA_WIDTH)

`define MSI_FLAG_SIZE 2
`define MSI_MAYBE_SIZE (`MSI_FLAG_SIZE + 1)
`define CACHE_ROW_SIZE (`CACHE_TAG_WIDTH + `CACHE_DATA_WIDTH + `MSI_MAYBE_SIZE)

module cache(input                          CLK,
			 input 							RST_N,
			 input 							put_valid,
			 input [`CACHE_REQ_SIZE - 1:0] 	put_request,
			 output [`CACHE_ROW_SIZE - 1:0] get_response);

//
//   reg has_request;
//   reg [`CACHE_REQ_SIZE - 1:0] last_request;

`define CACHE_NUM_SETS (1 << `CACHE_INDEX_WIDTH)
   reg [`CACHE_ROW_SIZE - 1:0] mem[`CACHE_NUM_SETS - 1:0];

 // TODO: how to initialize? We should not rely on initialised caches.
`ifdef BRAM_RUNTIME_INIT
   initial
	 begin : init_rom_block
	   for(i = 0; i < DEPTH; i = i+1)
		  mem[i] = {`CACHE_ROW_SIZE{1`b0}};
	 end
`endif

   function[`CACHE_DATA_WIDTH - 1:0] compute_mask(input[3:0] byte_en);
      compute_mask = {{8{byte_en[3]}}, {8{byte_en[2]}}, {8{byte_en[1]}}, {8{byte_en[0]}}};
   endfunction // compute_mask

   function[`CACHE_DATA_WIDTH - 1:0] compute_data_update(input [`CACHE_DATA_WIDTH - 1:0] mask,
														 input [`CACHE_DATA_WIDTH - 1:0] data,
														 input [`CACHE_DATA_WIDTH - 1:0] original);
      begin
         compute_data_update = (original & ~mask) | (data & mask);
      end
   endfunction // compute_update

   wire [`BYTE_EN_WIDTH - 1:0]     put_request_byte_en;
   wire [`CACHE_TAG_WIDTH - 1:0]   put_request_tag;
   wire [`CACHE_INDEX_WIDTH - 1:0] put_request_index;
   wire [`CACHE_DATA_WIDTH - 1:0]  put_request_data;
   wire 						   put_request_msi_valid;
   wire [`MSI_FLAG_SIZE - 1:0] 	   put_request_msi_data;
   assign {put_request_byte_en, put_request_tag, put_request_index,
		   put_request_data, put_request_msi_valid, put_request_msi_data} = put_request;

   wire [`ADDR_WIDTH - 1:0] put_request_addr;
   assign put_request_addr = {put_request_tag, put_request_index, 2'b00};

   wire [`CACHE_ROW_SIZE - 1:0] current_row = mem[put_request_index];

   wire [`CACHE_TAG_WIDTH - 1:0]  current_row_tag;
   wire [`CACHE_DATA_WIDTH - 1:0] current_row_data;
   wire [`MSI_FLAG_SIZE - 1:0] 	  current_row_msi;
   assign {current_row_tag, current_row_data, current_row_msi} = current_row;

   wire [`CACHE_TAG_WIDTH - 1:0]   new_row_tag = put_request_byte_en == 4'b0000 ? current_row_tag : put_request_tag;
   wire [`CACHE_DATA_WIDTH - 1:0]  new_row_data = put_request_byte_en == 4'b0000 ? current_row_data : compute_data_update(compute_mask(put_request_byte_en), put_request_data, current_row_data);
   wire [`MSI_FLAG_SIZE - 1:0] 	 new_row_msi = put_request_msi_valid ? put_request_msi_data : current_row_msi;

   // Always return the current row
   assign get_response = current_row;

   wire put_wf = put_valid;

   always @(posedge CLK) begin
`ifdef SIMULATION
      if (put_wf && put_request_addr == EXIT_ADDRESS) begin
         if (put_request_data == 0)
    	   $fwrite(32'h80000002, "  [0;32mPASS[0m\n");
    	 else
    	   $fwrite(32'h80000002, "  [0;31mFAIL[0m (%0d)\n", last_request_data);

         $finish(1'b1);
      end
`endif

      if (RST_N == 1) begin
		 if (put_wf) begin
			mem[put_request_index] <= {new_row_tag, new_row_data, new_row_msi};
		 end
      end
   end

endmodule
