// -*- verilog -*-

`define INDEX_WIDTH 12
`define TAG_WIDTH 18
`define MSI_STATE_SIZE 2

`define ROW_SIZE (`MSI_STATE_SIZE + `TAG_WIDTH)
`define CACHE_TYPE_SIZE 1
`define CORE_ID_SIZE 1

`define SINGLE_ENTRY_SIZE (`ROW_SIZE + `CORE_ID_SIZE + `CACHE_TYPE_SIZE)
`define INPUT_SIZE (`INDEX_WIDTH + 1 + `SINGLE_ENTRY_SIZE)
`define ENTRY_SIZE (4*`ROW_SIZE)

module bookkeeping_directory (input CLK,
							  input 		   RST_N,
							  input 		   get_valid,
							  input 		   put_valid,
							  input [`INPUT_SIZE - 1:0]  put_request,
							  output 		   get_ready,
							  output 		   put_ready,
							  output [`ENTRY_SIZE - 1:0] get_response);
   reg has_request;
   reg [`INPUT_SIZE - 1:0] last_request;

`define NUM_SETS (1 << `INDEX_WIDTH)
   reg [`ENTRY_SIZE - 1:0] mem[`NUM_SETS - 1:0];

 // TODO: how to initialize? We should not rely on initialisation.
`ifdef BRAM_RUNTIME_INIT

   integer j;
   initial
	 begin : init_rom_block
	   for(j = 0; j < `NUM_SETS; j = j+1)
		  mem[j] = {`ENTRY_SIZE {1'b0}};
	 end
`endif

   wire [`INDEX_WIDTH - 1:0] put_request_idx;
   wire 					 put_request_write_entry_valid;
   wire [`ROW_SIZE - 1:0] 	 put_request_write_entry_row;
   wire 					 put_request_core_id;
   wire 					 put_request_cache_type;

   assign {put_request_idx, put_request_write_entry_valid, put_request_write_entry_row,
		   put_request_core_id, put_request_cache_type} = put_request;

   wire [`INDEX_WIDTH - 1:0] last_request_idx;
   wire 					 last_request_write_entry_valid;
   wire [`ROW_SIZE - 1:0] 	 last_request_write_entry_row;
   wire 					 last_request_core_id;
   wire 					 last_request_cache_type;

   assign {last_request_idx,
		   last_request_write_entry_valid, last_request_write_entry_row,
		   last_request_core_id, last_request_cache_type} = last_request;

   wire [`ENTRY_SIZE - 1:0]  entry = mem[last_request_idx];
   wire [`ROW_SIZE - 1:0] 	 entry_imem0;
   wire [`ROW_SIZE - 1:0] 	 entry_dmem0;
   wire [`ROW_SIZE - 1:0] 	 entry_imem1;
   wire [`ROW_SIZE - 1:0] 	 entry_dmem1;
   assign {entry_imem0, entry_dmem0, entry_imem1, entry_dmem1} = entry;

   wire [`ROW_SIZE - 1:0] 	 new_entry_imem0 = (last_request_core_id == 0 && last_request_cache_type == 0) ? last_request_write_entry_row : entry_imem0;
   wire [`ROW_SIZE - 1:0] 	 new_entry_dmem0 = (last_request_core_id == 0 && last_request_cache_type == 1) ? last_request_write_entry_row : entry_dmem0;
   wire [`ROW_SIZE - 1:0] 	 new_entry_imem1 = (last_request_core_id == 1 && last_request_cache_type == 0) ? last_request_write_entry_row : entry_imem1;
   wire [`ROW_SIZE - 1:0] 	 new_entry_dmem1 = (last_request_core_id == 1 && last_request_cache_type == 1) ? last_request_write_entry_row : entry_dmem1;

   assign get_ready = RST_N && (has_request && !last_request_write_entry_valid);
   assign put_ready = RST_N && (get_valid || !has_request || last_request_write_entry_valid);

   assign get_response = entry;

   wire put_wf = put_valid && put_ready;
   wire get_wf = get_valid && get_ready;

   always @(posedge CLK) begin
      if (RST_N == 1) begin
		 if (has_request && last_request_write_entry_valid) begin
			mem[last_request_idx] <= {new_entry_imem0, new_entry_dmem0, new_entry_imem1, new_entry_dmem1};
		 end

		 if (put_wf) begin
			last_request <= put_request;
		 end

		 has_request <= put_wf || (has_request && (!get_wf || !last_request_write_entry_valid));
      end else begin // if (RST_N == 1)
		 has_request <= 1'b0;
      end
   end

endmodule // bookkeeping_directory
