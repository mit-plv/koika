module uart(input CLK, input RST_N,
            input wr_valid, input[7:0] wr_data, output wr_ready,
            output line_out);
   assign wr_ready = RST_N && 1'b1;
   assign line_out = wr_valid && wr_data[0];

   wire wr_wf = wr_valid && wr_ready;

   always @(negedge CLK) begin
`ifdef SIMULATION
      if (wr_wf)
        $fwrite(32'h80000002, "%c", wr_data);
`endif
   end
endmodule
