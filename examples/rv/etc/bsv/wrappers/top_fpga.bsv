import Glue_types::*;
import BRAM::*;
import RS232::*;
import rv32::*;
typedef Bit#(32) Word;

interface Proc;
    interface RS232 uart_pins;
endinterface

module top_fpga(Proc);
    Bit#(16) div_reg = 54; //100 MHz / (16*54) ~ 115200 bauds
    UART#(16) uart <- mkUART(8, NONE, STOP_1, div_reg);
    // Instantiate the dual ported memory
    BRAM_Configure cfg = defaultValue();
    cfg.loadFormat = tagged Hex "mem.vmh";
    BRAM2PortBE#(Bit#(14), Word, 4) bram <- mkBRAM2ServerBE(cfg);

    Ifcrv32 rv_core <- mkrv32;
    Reg#(Mem) ireq <- mkRegU;
    Reg#(Mem) dreq <- mkRegU;

    RWire#(Bit#(1)) wire_write0_fromIMem_valid0 <- mkRWire();
    RWire#(Bit#(1)) wire_write1_fromIMem_valid0 <- mkRWire();
    RWire#(Mem) wire_write0_fromIMem_data0 <- mkRWire();
    RWire#(Mem) wire_write1_fromIMem_data0 <- mkRWire();
    RWire#(Bit#(1)) wire_write0_toIMem_valid0 <- mkRWire();
    RWire#(Bit#(1)) wire_write1_toIMem_valid0 <- mkRWire();
    RWire#(Mem) wire_write0_toIMem_data0 <- mkRWire();
    RWire#(Mem) wire_write1_toIMem_data0 <- mkRWire();
    RWire#(Bit#(1)) wire_write0_fromDMem_valid0 <- mkRWire();
    RWire#(Bit#(1)) wire_write1_fromDMem_valid0 <- mkRWire();
    RWire#(Mem) wire_write0_fromDMem_data0 <- mkRWire();
    RWire#(Mem) wire_write1_fromDMem_data0 <- mkRWire();
    RWire#(Bit#(1)) wire_write0_toDMem_valid0 <- mkRWire();
    RWire#(Bit#(1)) wire_write1_toDMem_valid0 <- mkRWire();
    RWire#(Mem) wire_write0_toDMem_data0 <- mkRWire();
    RWire#(Mem) wire_write1_toDMem_data0 <- mkRWire();
    Reg#(Bool) debug <- mkReg(False);
    // For this specific example, we don't care about the reads at all,
    // We only care about the writes.

    rule requestI;
	let isValid = rv_core.ifc_ExternalI.read0_toIMem_valid0();
	if (isValid == 'b1) begin
	    let reqB = rv_core.ifc_ExternalI.read0_toIMem_data0();
	    wire_write0_toIMem_valid0.wset(0);
	    Mem req = unpack(reqB);
	    if (debug) $display("Got request from core:", fshow(req));
	    ireq <= req;
            bram.portB.request.put(BRAMRequestBE{
	       writeen: req.byte_en,
	       responseOnWrite: True,
	       address: truncate(req.addr >> 2),
	       datain: req.data});
	end
    endrule

    rule responseI;
	let respB = rv_core.ifc_ExternalI.read0_fromIMem_valid0();
	if (respB == 'b0) begin
	    let x <- bram.portB.response.get();
	    if (debug) $display("Communicating a response:", fshow(ireq), fshow(x));
	    wire_write0_fromIMem_valid0.wset(1);
	    let req = ireq;
	    req.data = x;
	    wire_write0_fromIMem_data0.wset(req);
	end
    endrule

    rule requestD;
	let isValid = rv_core.ifc_ExternalD.read0_toDMem_valid0();
	if (isValid == 'b1) begin
	    let reqA = rv_core.ifc_ExternalD.read0_toDMem_data0();
	    wire_write0_toDMem_valid0.wset(0);
	    Mem req = unpack(reqA);
	    dreq <= req;

    	    if (req.byte_en == 'hf) begin
		if (req.addr ==  'h4000_0000) begin
		    uart.rx.put(req.data[7:0]);
                    // Writing to STDERR
                    $fwrite(stderr, "%c", req.data[7:0]);
                    $fflush(stderr);
	    end
    		else
    		    if (req.addr == 'h4000_0004) begin
    			// Write integer to STDERR
			$fwrite(stderr, "%0d", req.data);
			$fflush(stderr);
    		    end
    		    else
    			if (req.addr == 'h4000_1000) begin
    			    // Exiting Simulation
    			if (req.data == 0) begin
    			    $fdisplay(stderr, "  [0;32mPASS[0m");
    			end
    			else
    			    begin
    				$fdisplay(stderr, "  [0;31mFAIL[0m %0d", req.data);
    			    end
    			$fflush(stderr);
    			$finish;
    		    end
            end
            bram.portA.request.put(BRAMRequestBE{
						 writeen: req.byte_en,
						 responseOnWrite: True,
						 address: truncate(req.addr >> 2),
						 datain: req.data});
	end
    endrule

    rule responseD;
	let respA = rv_core.ifc_ExternalD.read0_fromDMem_valid0();
	if (respA == 'b0) begin
	    let x <- bram.portA.response.get();
	    wire_write0_fromDMem_valid0.wset(1);
	    let req = dreq;
	    req.data = x;
	    wire_write0_fromDMem_data0.wset(req);
	end
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule background;
	let value_write0_fromIMem_valid0 = wire_write0_fromIMem_valid0.wget;
	if (value_write0_fromIMem_valid0 != tagged Invalid)
	    rv_core.ifc_ExternalI.write0_fromIMem_valid0(pack(value_write0_fromIMem_valid0.Valid));
	else
	    rv_core.ifc_ExternalI.write0_fromIMem_valid0(rv_core.ifc_ExternalI.read0_fromIMem_valid0());

	let value_write0_fromIMem_data0 = wire_write0_fromIMem_data0.wget;
	if (value_write0_fromIMem_data0 != tagged Invalid)
	    rv_core.ifc_ExternalI.write0_fromIMem_data0(pack(value_write0_fromIMem_data0.Valid));
	else
	    rv_core.ifc_ExternalI.write0_fromIMem_data0(rv_core.ifc_ExternalI.read0_fromIMem_data0());

 	let value_write0_toIMem_valid0 = wire_write0_toIMem_valid0.wget;
	if (value_write0_toIMem_valid0 != tagged Invalid)
	    rv_core.ifc_ExternalI.write0_toIMem_valid0(pack(value_write0_toIMem_valid0.Valid));
	else
	    rv_core.ifc_ExternalI.write0_toIMem_valid0(rv_core.ifc_ExternalI.read0_toIMem_valid0());

	let value_write0_toIMem_data0 = wire_write0_toIMem_data0.wget;
	if (value_write0_toIMem_data0 != tagged Invalid)
	    rv_core.ifc_ExternalI.write0_toIMem_data0(pack(value_write0_toIMem_data0.Valid));
	else
	    rv_core.ifc_ExternalI.write0_toIMem_data0(rv_core.ifc_ExternalI.read0_toIMem_data0());

	// Never touch the value port 1
	rv_core.ifc_ExternalI.write1_fromIMem_valid0(rv_core.ifc_ExternalI.read1_fromIMem_valid0());
	rv_core.ifc_ExternalI.write1_fromIMem_data0(rv_core.ifc_ExternalI.read1_fromIMem_data0());
	rv_core.ifc_ExternalI.write1_toIMem_valid0(rv_core.ifc_ExternalI.read1_toIMem_valid0());
	rv_core.ifc_ExternalI.write1_toIMem_data0(rv_core.ifc_ExternalI.read1_toIMem_data0());

	let value_write0_fromDMem_valid0 = wire_write0_fromDMem_valid0.wget;
	if (value_write0_fromDMem_valid0 != tagged Invalid)
	    rv_core.ifc_ExternalD.write0_fromDMem_valid0(pack(value_write0_fromDMem_valid0.Valid));
	else
	    rv_core.ifc_ExternalD.write0_fromDMem_valid0(rv_core.ifc_ExternalD.read0_fromDMem_valid0());

	let value_write0_fromDMem_data0 = wire_write0_fromDMem_data0.wget;
	if (value_write0_fromDMem_data0 != tagged Invalid)
	    rv_core.ifc_ExternalD.write0_fromDMem_data0(pack(value_write0_fromDMem_data0.Valid));
	else
	    rv_core.ifc_ExternalD.write0_fromDMem_data0(rv_core.ifc_ExternalD.read0_fromDMem_data0());

 	let value_write0_toDMem_valid0 = wire_write0_toDMem_valid0.wget;
	if (value_write0_toDMem_valid0 != tagged Invalid)
	    rv_core.ifc_ExternalD.write0_toDMem_valid0(pack(value_write0_toDMem_valid0.Valid));
	else
	    rv_core.ifc_ExternalD.write0_toDMem_valid0(rv_core.ifc_ExternalD.read0_toDMem_valid0());

	let value_write0_toDMem_data0 = wire_write0_toDMem_data0.wget;
	if (value_write0_toDMem_data0 != tagged Invalid)
	    rv_core.ifc_ExternalD.write0_toDMem_data0(pack(value_write0_toDMem_data0.Valid));
	else
	    rv_core.ifc_ExternalD.write0_toDMem_data0(rv_core.ifc_ExternalD.read0_toDMem_data0());

	// Never touche the value port 1
	rv_core.ifc_ExternalD.write1_fromDMem_data0(rv_core.ifc_ExternalD.read1_fromDMem_data0());
	rv_core.ifc_ExternalD.write1_toDMem_valid0(rv_core.ifc_ExternalD.read1_toDMem_valid0());
	rv_core.ifc_ExternalD.write1_fromDMem_valid0(rv_core.ifc_ExternalD.read1_fromDMem_valid0());
	rv_core.ifc_ExternalD.write1_toDMem_data0(rv_core.ifc_ExternalD.read1_toDMem_data0());
    endrule
    interface RS232 uart_pins = uart.rs232;
endmodule
