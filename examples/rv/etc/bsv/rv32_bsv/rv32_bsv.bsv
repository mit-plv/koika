import FIFO::*;
import RegFile::*;
import Ehr::*;
import Util::*;
import Scoreboard::*;
import Vector::*;
import ConfigReg::*;
import Glue_types::*;
import SpecialFIFOs::*;
import RF::*;

typedef struct {
   Bit#(32) pc;
   Bit#(32) ppc;
   Bit#(1) epoch;
   } Fetch_bookkeeping deriving (Bits,Eq,FShow);

typedef struct {
   Bit#(32) pc;
   Bit#(32) ppc;
   Bit#(1) epoch;
   DecodedInst dInst;		// Where is it?
   Bit#(32) rval1;
   Bit#(32) rval2;
   } Decode_bookkeeping deriving (Bits,Eq,FShow);

typedef struct {
   Bit#(1) isUnsigned;
   Bit#(2) size;
   Bit#(2) offset;
   Bit#(32) newrd;
   DecodedInst dInst;
   } Execute_bookkeeping deriving (Bits,Eq,FShow);

interface RVIfc;
    method ActionValue#(Mem) getIReq();
    method Action getIResp(Mem a);
    method ActionValue#(Mem) getDReq();
    method Action getDResp(Mem a);
endinterface

module rv32_bsv(RVIfc);
    FIFO#(Mem) toImem <- mkBypassFIFO;
    FIFO#(Mem) fromImem <- mkLFIFO;
    FIFO#(Mem) toDmem <- mkBypassFIFO;
    FIFO#(Mem) fromDmem <- mkLFIFO;
    FIFO#(Fetch_bookkeeping) fromFetch <- mkLFIFO;
    FIFO#(Fetch_bookkeeping) fromFetchprim <- mkLFIFO;
    FIFO#(Decode_bookkeeping) fromDecode <- mkLFIFO;
    FIFO#(Execute_bookkeeping) fromExecute <- mkLFIFO;
    Rf rf <- mkRf;

    Ehr#(2,Bit#(32)) pc <- mkEhr(32'h00000000);
    Ehr#(2,Bit#(1)) epoch <- mkEhr(0);

    Reg#(Bit#(32)) instr_count <- mkReg(0);

    Scoreboard scoreboard <- mkScoreboard;
    Bool debug = False;

    rule fetch;
	    if(debug) $display("Fetch %x", pc[1]);
	    let newpc = pc[1];
        let req = Mem {byte_en : 0,
			   addr : newpc,
			   data : 0};
        let fetch_bookkeeping = Fetch_bookkeeping {pc : newpc,
						   ppc : newpc + 4,
						   epoch : epoch[1]};
        toImem.enq(req);
        pc[1] <= newpc + 4;
        fromFetch.enq(fetch_bookkeeping);
    endrule

    rule fetchDelay;
       let fetch_bookkeeping = fromFetch.first();
       fromFetch.deq();
       fromFetchprim.enq(fetch_bookkeeping);
    endrule


    rule decode;
        let resp = fromImem.first();
        let instr = resp.data;
         let fetched_bookkeeping = fromFetchprim.first();
	//let fetched_bookkeeping = fromFetch.first();
        let decodedInst = decodeInst(instr);
        if (fetched_bookkeeping.epoch == epoch[1]) begin
            let rs1_idx = getInstFields(instr).rs1;
            let rs2_idx = getInstFields(instr).rs2;
            let score1 = scoreboard.search(rs1_idx);
	    let score2 = scoreboard.search(rs2_idx);
	    if (score1 == 0 && score2 == 0) begin
		if(debug) $display("[Decode] Right path: ", fshow(decodedInst));
		//fromFetch.deq();
		fromFetchprim.deq();
		fromImem.deq();
		if (decodedInst.valid_rd) begin
                    let rd_idx = getInstFields(instr).rd;
                    scoreboard.insert(rd_idx);
		end
		let rs1 = rf.read1(rs1_idx);
		let rs2 = rf.read2(rs2_idx);
		let decode_bookkeeping = Decode_bookkeeping {
                                                pc    : fetched_bookkeeping.pc,
                                                ppc   : fetched_bookkeeping.ppc,
                                                epoch : fetched_bookkeeping.epoch,
                                                dInst : decodedInst,
                                                rval1 : rs1,
                                                rval2 : rs2
					      };
		fromDecode.enq(decode_bookkeeping);
	    end
	end
	else begin
	    if(debug) $display("[Decode] Drop Decoded inst ", fshow(decodedInst));
	    // Poisoned, drop
	    //fromFetch.deq();
	    fromFetchprim.deq();
	    fromImem.deq();
	end
    endrule

    rule execute;
        let decoded_bookkeeping = fromDecode.first();
	fromDecode.deq();
        if (decoded_bookkeeping.epoch == epoch[0]) begin
            let dInst = decoded_bookkeeping.dInst;
            if (!dInst.legal) begin
		if(debug) $display("[Execute] Illegal Inst, Drop and fault: ", fshow(dInst));
		epoch[0] <= epoch[0]+1;
		pc[0] <= 0;	// Fault
	    end
            else begin
		if (debug) $display("[Execute] ", fshow(dInst));
		let imm = getImmediate(dInst);
		let ipc = decoded_bookkeeping.pc;
		let fInst = dInst.inst;
		let rs1_val = decoded_bookkeeping.rval1;
		let rs2_val = decoded_bookkeeping.rval2;
		let data = execALU32(fInst, rs1_val, rs2_val, imm, ipc);
		let isUnsigned = 0;
		let funct3 = getInstFields(fInst).funct3;
		let size = funct3[1:0];// |2`d0| :+ 2];
		let addr = rs1_val + imm;
		Bit#(2) offset = addr[1:0];
		if (isMemoryInst(dInst)) begin
		    let shift_amount = {offset, 3'b0};
		    let byte_en = 0;
		    case (size) matches
			2'b00: byte_en = 4'b0001 << offset;
			2'b01: byte_en = 4'b0011 << offset;
			2'b10: byte_en = 4'b1111 << offset;
		    endcase
		    data = rs2_val << shift_amount;
		    addr = {addr[31:2], 2'b0};
		    isUnsigned = funct3[2];
		    let type_mem = (fInst[5] == 1) ? byte_en : 0;
		    let req = Mem {byte_en : type_mem,
				       addr : addr,
				       data : data};
		    toDmem.enq(req);
		end
		else if (isControlInst(dInst)) begin
                    data = ipc + 4;    // (* For jump and link *)
		end
		let controlResult = execControl32(fInst, rs1_val, rs2_val, imm, ipc);
		let nextPc = controlResult.nextPC;
		if (!(nextPc == decoded_bookkeeping.ppc)) begin
		    if(debug) $display("[Execute] Misprediction redirect %x", nextPc);
		    epoch[0] <= epoch[0] + 1;
		    pc[0] <= nextPc;
		end
		let execute_bookkeeping = Execute_bookkeeping {
                                                 isUnsigned : isUnsigned,
                                                 size : size,
                                                 offset : offset,
                                                 newrd : data,
                                                 dInst : decoded_bookkeeping.dInst
					       };
		fromExecute.enq(execute_bookkeeping);
	    end
	end
    endrule

    rule writeback;
	// TODO fromExecute.deq(),fromDMem.deq();
        let execute_bookeeping = fromExecute.first();
	instr_count <= instr_count + 1;
	fromExecute.deq();
        let dInst = execute_bookeeping.dInst;
        let data = execute_bookeeping.newrd;
        let fields = getInstFields(dInst.inst);
        if (isMemoryInst(dInst)) begin // (* // write_val *)
            let resp = fromDmem.first();
	    fromDmem.deq();
            let mem_data = resp.data;
            mem_data = mem_data >> {execute_bookeeping.offset ,3'b0};
             case ({execute_bookeeping.isUnsigned, execute_bookeeping.size}) matches
	     	3'b000 : data = signExtend(mem_data[7:0]);
	     	3'b001 : data = signExtend(mem_data[15:0]);
	     	3'b100 : data = zeroExtend(mem_data[7:0]);
	     	3'b101 : data = zeroExtend(mem_data[15:0]);
	     	3'b010 : data = mem_data;
             endcase
	end

	if(debug) $display("[Writeback]", fshow(dInst));
	if (dInst.valid_rd) begin
            let rd_idx = fields.rd;
            scoreboard.remove(rd_idx);
            if (rd_idx != 0) rf.write(rd_idx,data);
	end
    endrule

    method ActionValue#(Mem) getIReq();
	toImem.deq();
	return toImem.first();
    endmethod
    method Action getIResp(Mem a);
    	fromImem.enq(a);
    endmethod
    method ActionValue#(Mem) getDReq();
	toDmem.deq();
	return toDmem.first();
    endmethod
    method Action getDResp(Mem a);
	fromDmem.enq(a);
    endmethod
endmodule
