import Vector::*;
import Util::*;
import Ehr::*;



interface Bht#(numeric type indexSize);
    method Bool predBranch(Addr pc);
    method Action update(Addr pc, Addr nextPc);
endinterface

module mkBht(Bht#(indexSize)) provisos(Add#(indexSize,a__,32), NumAlias#(TSub#(TSub#(AddrSz, 2), indexSize), tagSize));
    Vector#(TExp#(indexSize), Ehr#(2,Bit#(2))) entries <- replicateM(mkEhr(0));

    function Bit#(indexSize) getIndex(Addr pc) = truncate(pc >> 2);

    method Bool predBranch(Addr pc);
        let index = getIndex(pc);
        return unpack(entries[index][1][1]);
    endmethod

    method Action update(Addr pc, Addr nextPc);
        let index = getIndex(pc);
        let brTaken = (nextPc != pc + 4);
        if ( brTaken && entries[index][0] != 3) entries[index][0] <= entries[index][0] + 1;
        if (!brTaken && entries[index][0] != 0) entries[index][0] <= entries[index][0] - 1;
    endmethod
endmodule
