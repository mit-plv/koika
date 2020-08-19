// -*- verilog -*-
/*! Verilog model of a BRAM !*/
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
   parameter EXIT_ADDRESS = `REQ_ADDR_WIDTH'h40001000;

   reg has_request;
   reg [`MEM_OP_SIZE - 1:0] last_request;

`ifndef STDERR
 `define STDERR 32'h80000002
`endif

`ifdef BROKEN_READMEMH
 // The implementation of $readmemh in CVC is broken.  It only loads one entry
 // if both endpoints of the file's range are not specified, and it complains
 // about the final address if it corresponds to the final index.
 `define MEMSIZE (1 << ADDRESS_WIDTH) + 1
`else
 `define MEMSIZE (1 << ADDRESS_WIDTH)
`endif

   reg [`REQ_DATA_WIDTH - 1:0] mem[`MEMSIZE - 1:0];

`ifdef BRAM_RUNTIME_INIT
   wire[8 * 256 - 1:0] filename;
   initial
     begin : init_rom_block
      if ($value$plusargs("VMH=%s", filename)) begin
         // Omitting the last argument to ‘$readmemh’ would prevent complaints
         // when the ‘mem’ array is larger than the image stored in ‘filename’.
         $readmemh(filename, mem, 0, `MEMSIZE - 1);
      end else begin
         $fwrite(`STDERR, "ERROR: No memory image loaded. Use +VMH=<path> to load one\n");
         $finish(1'b1);
      end
   end
`else
 `ifndef MEM_FILENAME
   // We use a macro instead of a parameter because Yosys instantiates the
   // module with its default parameters when it first reads it (See
   // https://www.reddit.com/r/yosys/comments/f92bke/)
  `define MEM_FILENAME "MEM_FILENAME_UNSET"
 `endif
   initial
     begin : init_rom_block
        $readmemh(`MEM_FILENAME, mem, 0, `MEMSIZE - 1);
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

   wire[ADDRESS_WIDTH - 1:0] addr = translate_address(last_request_addr);
   wire[`REQ_DATA_WIDTH - 1:0] data = mem[addr];

   assign get_ready = RST_N && has_request;
   assign put_ready = RST_N && (get_valid || !has_request);

   wire[`REQ_DATA_WIDTH - 1:0] get_response_data = last_request_byte_en == 4'b0000 ? data : 0;
   assign get_response = {last_request_byte_en, last_request_addr, get_response_data};

   wire put_wf = put_valid && put_ready;
   wire get_wf = get_valid && get_ready;

   always @(posedge CLK) begin
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
