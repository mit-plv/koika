`include "typedefs.sv"

module memory(input  CLK,
              input  RST_N,
              input  get_enable,
              input  put_enable,
              input  mem_op put_request,
              output get_ready,
              output put_ready,
              output mem_op get_response);
   parameter ADDRESS_WIDTH = 14;
   parameter DATA_WIDTH = 32;
   parameter IO_ADDRESS = 32'h40000000;
   parameter EXIT_ADDRESS = 32'h40001000;

   logic has_request;
   mem_op last_request;

`define MEMSIZE (1 << ADDRESS_WIDTH)
   reg [DATA_WIDTH - 1:0] mem[`MEMSIZE - 1:0];

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

   function[ADDRESS_WIDTH - 1:0] translate_address(input[31:0] address);
      logic[31:0] _untruncated_addr = address >> 2;
      translate_address = _untruncated_addr[ADDRESS_WIDTH - 1:0];
   endfunction

   function[DATA_WIDTH - 1:0] compute_mask(input[3:0] byte_en);
      compute_mask = {{8{byte_en[3]}}, {8{byte_en[2]}}, {8{byte_en[1]}}, {8{byte_en[0]}}};
   endfunction

   function mem_op compute_response(input mem_op request, input [DATA_WIDTH - 1:0] data);
      begin
         compute_response.byte_en = request.byte_en;
         compute_response.addr = request.addr;
         compute_response.data = request.byte_en == 4'b0000 ? data : 0;
      end
   endfunction

   function[DATA_WIDTH - 1:0] compute_update(input [DATA_WIDTH - 1:0] mask,
                                             input [DATA_WIDTH - 1:0] data,
                                             input [DATA_WIDTH - 1:0] original);
      begin
         compute_update = (original & ~mask) | (data & mask);
      end
   endfunction

   wire[13:0] addr = translate_address(last_request.addr);
   wire[DATA_WIDTH - 1:0] data = mem[addr];

   reg reset = RST_N; // This realigns RST_N signals on the posedge
   assign get_ready = reset && has_request;
   assign put_ready = reset && (get_enable || !has_request);
   assign get_response = compute_response(last_request, data);

   wire put_wf = put_enable && put_ready;
   wire get_wf = get_enable && get_ready;

   /* Debugging

      `define MEM_OP_POISON { 4'b0000, 32'hdeadbeef, 32'hdeadbeef }
      `define POISON 1'b0

      mem_op getr = (get_ready || !`POISON) ? get_response : `MEM_OP_POISON;
      mem_op putr = (put_enable || !`POISON) ? put_request : `MEM_OP_POISON;
      mem_op lastr = (has_request || !`POISON) ? last_request : `MEM_OP_POISON;

      logic [3:0] last_request_byte_en = lastr.byte_en;
      logic [31:0] last_request_addr = lastr.addr;
      logic [DATA_WIDTH - 1:0] last_request_data = lastr.data;

      logic[3:0] put_request_byte_en = putr.byte_en;
      logic[31:0] put_request_addr = putr.addr;
      logic[DATA_WIDTH - 1:0] put_request_data = putr.data;

      logic[3:0] get_response_byte_en = getr.byte_en;
      logic[31:0] get_response_addr = getr.addr;
      logic[DATA_WIDTH - 1:0] get_response_data = getr.data; */

   always @(negedge CLK) begin
      if (put_wf && put_request.addr == EXIT_ADDRESS) begin
         if (put_request.data == 0)
    	   $fwrite(32'h80000002, "  [0;32mPASS[0m\n");
    	 else
    	   $fwrite(32'h80000002, "  [0;31mFAIL[0m (%0d)\n", last_request.data);

         $finish(1'b1);
      end

      if (put_wf && put_request.addr == IO_ADDRESS)
        $fwrite(32'h80000002, "%c", put_request.data[7:0]);

      if (RST_N == 1) begin
         if (has_request) begin
            mem[addr] <= compute_update(compute_mask(last_request.byte_en), last_request.data, data);
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
