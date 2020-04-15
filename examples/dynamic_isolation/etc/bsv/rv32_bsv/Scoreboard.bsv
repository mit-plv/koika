import Vector::*;
import Ehr::*;

interface Scoreboard;
    method Action insert(Bit#(5) idx);
    method Action remove(Bit#(5) idx);
    method Bit#(2) search(Bit#(5) idx);
endinterface

module mkScoreboard(Scoreboard);
    Vector#(32, Ehr#(2,Bit#(2))) scores <- replicateM(mkEhr(0));

    method Action insert(Bit#(5) idx); // if (scores.sub(idx) != 1'b11);
    // Scoreboard NOT safely blocking if more than 3 elements are flying.
        let old_score = scores[idx][1];
        let new_score = old_score + 1;
        scores[idx][1] <= new_score;
    endmethod

    method Action remove(Bit#(5) idx);// if (scores.sub(idx) != 0);
    // scoreboard NOT safely blocking if we are removing an element from an empty scoreboard (bug).
        let old_score = scores[idx][0];
        let new_score = old_score - 1;
        scores[idx][0] <= new_score;
    endmethod

    method Bit#(2) search(Bit#(5) idx);
        return scores[idx][1];
    endmethod
endmodule
