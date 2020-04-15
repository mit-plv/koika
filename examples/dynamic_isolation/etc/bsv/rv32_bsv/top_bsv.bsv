import Glue_types::*;
import BRAM::*;
import rv32_bsv::*;
typedef Bit#(32) Word;

module top_bsv(Empty);
    // Instantiate the dual ported memory
    BRAM_Configure cfg = defaultValue();
    cfg.loadFormat = tagged Hex "mem.vmh";
    BRAM2PortBE#(Bit#(14), Word, 4) bram <- mkBRAM2ServerBE(cfg);

    RVIfc rv_core <- rv32_bsv;
    Reg#(Mem) ireq <- mkRegU;
    Reg#(Mem) dreq <- mkRegU;
    let debug = False;
    Reg#(Bit#(32)) cycle_count <- mkReg(0);

    rule tic;
	    cycle_count <= cycle_count + 1;
    endrule

    rule requestI;
	let req <- rv_core.getIReq;
	if (debug) $display("Get IReq", fshow(req));
	ireq <= req;
        bram.portB.request.put(BRAMRequestBE{
                writeen: req.byte_en,
                responseOnWrite: True,
                address: truncate(req.addr >> 2),
                datain: req.data});
    endrule

    rule responseI;
	let x <- bram.portB.response.get();
	let req = ireq;
	if (debug) $display("Get IResp ", fshow(req), fshow(x));
	req.data = x;
        rv_core.getIResp(req);
    endrule

    rule requestD;
	let req <- rv_core.getDReq;
	dreq <= req;
	if (debug) $display("Get DReq", fshow(req));
	if (req.byte_en == 'hf) begin
            if (req.addr ==  'h4000_0000) begin
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
    				$fdisplay(stderr, "  [0;31mFAIL[0m (%0d)", req.data);
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
    endrule

    rule responseD;
	let x <- bram.portA.response.get();
	let req = dreq;
	if (debug) $display("Get IResp ", fshow(req), fshow(x));
	req.data = x;
        rv_core.getDResp(req);
    endrule
    
endmodule
