import Ehr::*;
import Vector::*;

interface Rf;
    method Bit#(32) read1(Bit#(5) idx);
    method Bit#(32) read2(Bit#(5) idx);
    method Action write(Bit#(5) idx, Bit#(32) data);
endinterface

module mkRf(Rf);
    Vector#(32, Ehr#(2,Bit#(32))) rf <- replicateM(mkEhr(0));

    method Bit#(32) read1(Bit#(5) idx);
	return rf[idx][1];
    endmethod

    method Bit#(32) read2(Bit#(5) idx);
	return rf[idx][1];
    endmethod

    method Action write(Bit#(5) idx, Bit#(32) data);
	rf[idx][0]<= data;
    endmethod
endmodule
