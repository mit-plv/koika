// -*- verilog -*-
`define REQ_ADDR_WIDTH 32
`define REQ_DATA_WIDTH 32
`define MEM_OP_SIZE (4 + `REQ_ADDR_WIDTH + `REQ_DATA_WIDTH)

module memory(input  CLK,
              input  RST_N,
              input  get_valid,
              input  put_valid,
              input  [`MEM_OP_SIZE - 1:0] put_request,
              output get_ready,
              output put_ready,
              output [`MEM_OP_SIZE - 1:0] get_response);
   parameter ADDRESS_WIDTH = 14;
   parameter IO_ADDRESS = 32'h40000000;
   parameter EXIT_ADDRESS = 32'h40001000;

   reg has_request;
   reg [`MEM_OP_SIZE - 1:0] last_request;

`define MEMSIZE (1 << ADDRESS_WIDTH)
   reg [`REQ_DATA_WIDTH - 1:0] mem[`MEMSIZE - 1:0];

`ifdef BRAM_RUNTIME_INIT
   wire[8 * 256 - 1:0] filename;

   initial
     begin : init_rom_block
      if ($value$plusargs("VMH=%s", filename)) begin
         $readmemh(filename, mem, 0, `MEMSIZE - 1);
      end else begin
         $fwrite(32'h80000002, "ERROR: No memory image loaded. Use +VMH=<path> to load one\n");
         $finish(1'b1);
      end
   end
`else
   initial
     begin : init_rom_block
        $readmemh("mem.vmh", mem, 0, `MEMSIZE - 1);
     end
`endif

   function[ADDRESS_WIDTH - 1:0] translate_address(input[`REQ_ADDR_WIDTH - 1:0] address);
      reg[`REQ_ADDR_WIDTH - 1:0] _untruncated_addr;
      begin
         _untruncated_addr = address >> 2;
         translate_address = _untruncated_addr[ADDRESS_WIDTH - 1:0];
      end
   endfunction

   function[`REQ_DATA_WIDTH - 1:0] compute_mask(input[3:0] byte_en);
      compute_mask = {{8{byte_en[3]}}, {8{byte_en[2]}}, {8{byte_en[1]}}, {8{byte_en[0]}}};
   endfunction

   function[`REQ_DATA_WIDTH - 1:0] compute_update(input [`REQ_DATA_WIDTH - 1:0] mask,
                                             input [`REQ_DATA_WIDTH - 1:0] data,
                                             input [`REQ_DATA_WIDTH - 1:0] original);
      begin
         compute_update = (original & ~mask) | (data & mask);
      end
   endfunction

   wire [3:0] put_request_byte_en;
   wire [`REQ_ADDR_WIDTH - 1:0] put_request_addr;
   wire [`REQ_DATA_WIDTH - 1:0] put_request_data;
   assign {put_request_byte_en, put_request_addr, put_request_data} = put_request;

   wire [3:0] last_request_byte_en;
   wire [`REQ_ADDR_WIDTH - 1:0] last_request_addr;
   wire [`REQ_DATA_WIDTH - 1:0] last_request_data;
   assign {last_request_byte_en, last_request_addr, last_request_data} = last_request;

   wire[13:0] addr = translate_address(last_request_addr);
   wire[`REQ_DATA_WIDTH - 1:0] data = mem[addr];

   assign get_ready = RST_N && has_request;
   assign put_ready = RST_N && (get_valid || !has_request);

   wire[`REQ_DATA_WIDTH - 1:0] get_response_data = last_request_byte_en == 4'b0000 ? data : 0;
   assign get_response = {last_request_byte_en, last_request_addr, get_response_data};

   wire put_wf = put_valid && put_ready;
   wire get_wf = get_valid && get_ready;

   always @(negedge CLK) begin
`ifdef SIMULATION
      if (put_wf && put_request_addr == EXIT_ADDRESS) begin
         if (put_request_data == 0)
    	   $fwrite(32'h80000002, "  [0;32mPASS[0m\n");
    	 else
    	   $fwrite(32'h80000002, "  [0;31mFAIL[0m (%0d)\n", last_request_data);

         $finish(1'b1);
      end

      if (put_wf && put_request_addr == IO_ADDRESS)
        $fwrite(32'h80000002, "%c", put_request_data[7:0]);
`endif

      if (RST_N == 1) begin
         if (has_request) begin
            mem[addr] <= compute_update(compute_mask(last_request_byte_en), last_request_data, data);
         end

         if (put_wf) begin
            last_request <= put_request;
         end

         has_request <= put_wf || (has_request && !get_wf);
      end else begin
         has_request <= 1'b0;
      end
   end
endmodule
