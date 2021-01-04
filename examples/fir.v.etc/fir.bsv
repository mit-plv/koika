/*! A Bluespec implementation of the fir.v example !*/
// Ported from Koika for evaluation purposes
import Vector::*;

typedef  4 T;
Integer t = valueOf(T);
typedef 8 NI ;
typedef TMul#(NI,2) NO;
interface Peak;
	method Vector#(T,Bit#(NO)) rd();
endinterface	


module mkfir(Peak);
  Reg#(Vector#(T, Bit#(NO))) q <- mkReg(?);
  Reg#(Bit#(NI)) x <- mkReg(0);

  Vector#(T, Bit#(NI)) w = replicate(1);
  w[0]=-2;
  w[1]=-1;
  w[2]=3;
  w[3]=4;

  rule doFir;
    function Bit#(NO)  mult(Bit#(NI) data_in) = signExtend(data_in) * signExtend(x);
    let mul_out = map(mult, w);
    Vector#(T,Bit#(NO)) add_out = q;
    for(Integer i=0; i< t ; i = i+1) begin
    	add_out[i] = add_out[i] + mul_out[t-i-1];
    end	
    
    Vector#(T,Bit#(NO)) newq = q;
    newq[0]=0;
    for(Integer i=1; i< t ; i = i+1) begin
    	newq[i] = add_out[i-1];
    end	
    q <= newq;

    Bit#(NO) y = add_out[t-1]; // Reproducing llhd with an unused value

    x<= (x+9)%19;
  endrule
  
  method Vector#(T, Bit#(NO)) rd();
  	return q;
  endmethod
endmodule

 
