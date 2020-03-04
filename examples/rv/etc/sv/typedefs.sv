`ifndef DATATYPES_SV
 `define DATATYPES_SV
typedef struct packed {
   logic       read0;
   logic       read1;
   logic       write0;
   logic       write1;
} rwset;

typedef struct packed {
   rwset rws;
   logic       data0;
   logic       data1;
} bit_ehr;

typedef struct packed {
   logic [3:0] byte_en;
   logic [31:0] addr;
   logic [31:0] data;
} mem_op;

typedef struct packed {
   rwset rws;
   mem_op data0;
   mem_op data1;
} mem_ehr;

typedef struct packed {
   mem_ehr data;
   bit_ehr valid;
} mem_fifo;

typedef struct packed {
   mem_fifo outgoing;
   mem_fifo incoming;
} bidi_mem_fifo;

function mem_ehr mem_ehr_write0(input mem_ehr ehr, input mem_op data0);
   begin
      mem_ehr_write0.rws.read0 = ehr.rws.read0;
      mem_ehr_write0.rws.read1 = ehr.rws.read1;
      mem_ehr_write0.rws.write0 = 1'b1;
      mem_ehr_write0.rws.write1 = 1'b0;
      mem_ehr_write0.data0 = data0;
      mem_ehr_write0.data1 = ehr.data1;
   end
endfunction

function mem_ehr mem_ehr_write1(input mem_ehr ehr, input mem_op data1);
   begin
      mem_ehr_write1.rws.read0 = ehr.rws.read0;
      mem_ehr_write1.rws.read1 = ehr.rws.read1;
      mem_ehr_write1.rws.write0 = 1'b0;
      mem_ehr_write1.rws.write1 = 1'b1;
      mem_ehr_write1.data0 = ehr.data0;
      mem_ehr_write1.data1 = data1;
   end
endfunction

function bit_ehr bit_ehr_write0(input bit_ehr ehr, input data0);
   begin
      bit_ehr_write0.rws.read0 = ehr.rws.read0;
      bit_ehr_write0.rws.read1 = ehr.rws.read1;
      bit_ehr_write0.rws.write0 = 1'b1;
      bit_ehr_write0.rws.write1 = ehr.rws.write1;
      bit_ehr_write0.data0 = data0;
      bit_ehr_write0.data1 = ehr.data1;
   end
endfunction

function bit_ehr bit_ehr_write1(input bit_ehr ehr, input data1);
   begin
      bit_ehr_write1.rws.read0 = ehr.rws.read0;
      bit_ehr_write1.rws.read1 = ehr.rws.read1;
      bit_ehr_write1.rws.write0 = ehr.rws.write0;
      bit_ehr_write1.rws.write1 = 1'b1;
      bit_ehr_write1.data0 = ehr.data0;
      bit_ehr_write1.data1 = data1;
   end
endfunction

function logic mem_fifo_empty(input mem_fifo fifo);
   mem_fifo_empty = !fifo.valid.data0;
endfunction

function logic mem_fifo_full(input mem_fifo fifo);
   mem_fifo_full = fifo.valid.data0;
endfunction

function mem_op mem_fifo_peek(input mem_fifo fifo);
   mem_fifo_peek = fifo.data.data0;
endfunction

function mem_fifo mem_fifo_pop(input mem_fifo fifo);
   mem_fifo_pop.valid = bit_ehr_write1(fifo.valid, 1'b0);
   mem_fifo_pop.data = fifo.data;
endfunction

function mem_fifo mem_fifo_push(input mem_fifo fifo, input mem_op data);
   mem_fifo_push.valid = bit_ehr_write1(fifo.valid, 1'b1);
   mem_fifo_push.data = mem_ehr_write1(fifo.data, data);
endfunction
`endif
