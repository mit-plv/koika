// -*- verilog -*-

/*! Verilog model of a single-cycle/instantaneous cache !*/
`define BYTE_EN_WIDTH 4
`define CACHE_TAG_WIDTH 18
`define CACHE_INDEX_WIDTH 12 // num sets
`define CACHE_DATA_WIDTH 32
`define MSI_FLAG_SIZE 2
`define ADDR_WIDTH 32
`define CACHE_REQ_SIZE (`BYTE_EN_WIDTH + `CACHE_TAG_WIDTH + `CACHE_INDEX_WIDTH + `CACHE_DATA_WIDTH + `MSI_MAYBE_SIZE + 1)

`define MSI_MAYBE_SIZE (`MSI_FLAG_SIZE + 1)
`define CACHE_ROW_SIZE (`CACHE_TAG_WIDTH + `CACHE_DATA_WIDTH + `MSI_FLAG_SIZE)

module cache(input                          CLK,
			 input 							RST_N,
			 input 							get_valid,
			 input 							put_valid,
			 input [`CACHE_REQ_SIZE - 1:0] 	put_request,
			 output 						get_ready,
			 output 						put_ready,
			 output [`CACHE_ROW_SIZE - 1:0] get_response);
   parameter EXIT_ADDRESS0 = 32'h40001000;
   parameter EXIT_ADDRESS1 = 32'h80001000;
   reg has_request;
   reg [`CACHE_REQ_SIZE - 1:0] last_request;

`define CACHE_NUM_SETS (1 << `CACHE_INDEX_WIDTH)
   reg [`CACHE_ROW_SIZE - 1:0] mem[`CACHE_NUM_SETS - 1:0];

 // TODO: how to initialize? We should not rely on initialised caches.
`ifdef BRAM_RUNTIME_INIT

   integer j;
   initial
	 begin : init_rom_block
	   for(j = 0; j < `CACHE_NUM_SETS; j = j+1)
		  mem[j] = {`CACHE_ROW_SIZE{1'b0}};
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

   // Set up put request: not all of this is needed
   wire [`BYTE_EN_WIDTH - 1:0]     put_request_byte_en;
   wire [`CACHE_TAG_WIDTH - 1:0]   put_request_tag;
   wire [`CACHE_INDEX_WIDTH - 1:0] put_request_index;
   wire [`CACHE_DATA_WIDTH - 1:0]  put_request_data;
   wire 						   put_request_msi_valid;
   wire [`MSI_FLAG_SIZE - 1:0] 	   put_request_msi_data;
   wire                            put_request_ignore_response;
   assign {put_request_byte_en, put_request_tag, put_request_index,
		   put_request_data, put_request_msi_valid, put_request_msi_data,
		   put_request_ignore_response} = put_request;

   wire [`ADDR_WIDTH - 1:0] put_request_addr;
   assign put_request_addr = {put_request_tag, put_request_index, 2'b00};

   // Set up last request
   wire [`BYTE_EN_WIDTH - 1:0]     last_request_byte_en;
   wire [`CACHE_TAG_WIDTH - 1:0]   last_request_tag;
   wire [`CACHE_INDEX_WIDTH - 1:0] last_request_index;
   wire [`CACHE_DATA_WIDTH - 1:0]  last_request_data;
   wire 						   last_request_msi_valid;
   wire [`MSI_FLAG_SIZE - 1:0] 	   last_request_msi_data;
   wire                            last_request_ignore_response;
   assign {last_request_byte_en, last_request_tag, last_request_index,
		   last_request_data, last_request_msi_valid, last_request_msi_data,
		   last_request_ignore_response} = last_request;

   wire [`ADDR_WIDTH - 1:0] last_request_addr;
   assign last_request_addr = {last_request_tag, last_request_index, 2'b00};


   wire [`CACHE_ROW_SIZE - 1:0] current_row = mem[last_request_index];

   wire [`CACHE_TAG_WIDTH - 1:0]  current_row_tag;
   wire [`CACHE_DATA_WIDTH - 1:0] current_row_data;
   wire [`MSI_FLAG_SIZE - 1:0] 	  current_row_msi;
   assign {current_row_tag, current_row_data, current_row_msi} = current_row;

   wire [`CACHE_TAG_WIDTH - 1:0]   new_row_tag = last_request_byte_en == 4'b0000 ? current_row_tag : last_request_tag;
   wire [`CACHE_DATA_WIDTH - 1:0]  new_row_data =
       last_request_byte_en == 4'b0000 ? current_row_data
								       : compute_data_update(compute_mask(last_request_byte_en), last_request_data, current_row_data);
   wire [`MSI_FLAG_SIZE - 1:0] 	 new_row_msi = last_request_msi_valid ? last_request_msi_data : current_row_msi;

   // Always return the current row

   assign get_ready = RST_N && (has_request && !last_request_ignore_response);
   assign put_ready = RST_N && (!has_request || get_valid || last_request_ignore_response);

   assign get_response = current_row;

   wire put_wf = put_valid && put_ready;
   wire get_wf = get_valid && get_ready;

   always @(posedge CLK) begin
`ifdef SIMULATION
      if (put_wf && (put_request_addr == EXIT_ADDRESS0 || put_request_addr == EXIT_ADDRESS1)) begin
         if (put_request_data == 0)
    	   $fwrite(32'h80000002, "  [0;32mPASS[0m\n");
    	 else
    	   $fwrite(32'h80000002, "  [0;31mFAIL[0m (%0d)\n", last_request_data);
		 // TODO
         $finish(1'b1);
      end
`endif

      if (RST_N == 1) begin
		 if (has_request) begin
			mem[last_request_index] <= {new_row_tag, new_row_data, new_row_msi};
		 end

		 if (put_wf) begin
			last_request <= put_request;
		 end

		 has_request <= put_wf || (has_request && (!get_wf || !last_request_ignore_response));
      end else begin // if (RST_N == 1)
		 has_request <= 1'b0;
      end
   end

endmodule
