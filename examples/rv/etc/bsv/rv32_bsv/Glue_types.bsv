typedef struct {
   Bit#(4) byte_en;
   Bit#(32) addr;
   Bit#(32) data;
   } Mem deriving (Bits,Eq,FShow);
