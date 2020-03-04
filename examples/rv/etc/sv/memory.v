module memory (
	CLK,
	RST_N,
	get_enable,
	put_enable,
	put_request,
	get_ready,
	put_ready,
	get_response
);
	input CLK;
	input RST_N;
	input get_enable;
	input put_enable;
	input wire [67:0] put_request;
	output get_ready;
	output put_ready;
	output wire [67:0] get_response;
	parameter ADDRESS_WIDTH = 14;
	parameter DATA_WIDTH = 32;
	parameter IO_ADDRESS = 32'h40000000;
	parameter EXIT_ADDRESS = 32'h40001000;
	reg has_request;
	reg [67:0] last_request;
	reg [(DATA_WIDTH - 1):0] mem [((1 << ADDRESS_WIDTH) - 1):0];
	wire [2047:0] vmh_path;
	initial if ($value$plusargs("VMH=%s", vmh_path))
		$readmemh(vmh_path, mem, 0, ((1 << ADDRESS_WIDTH) - 1));
	else begin
		$fwrite(32'h80000002, "ERROR: No memory image loaded. Use +VMH=<path> to load one\n");
		$finish(1'b1);
	end
	function [(ADDRESS_WIDTH - 1):0] translate_address;
		input reg [31:0] address;
		reg [31:0] _untruncated_addr;
		begin
			_untruncated_addr = (address >> 2);
			translate_address = _untruncated_addr[(ADDRESS_WIDTH - 1):0];
		end
	endfunction
	function [(DATA_WIDTH - 1):0] compute_mask;
		input reg [3:0] byte_en;
		compute_mask = {{8 {byte_en[3]}}, {8 {byte_en[2]}}, {8 {byte_en[1]}}, {8 {byte_en[0]}}};
	endfunction
	function [67:0] compute_response;
		input reg [67:0] request;
		input reg [(DATA_WIDTH - 1):0] data;
		begin
			compute_response[67:64] = request[67:64];
			compute_response[63:32] = request[63:32];
			compute_response[31:0] = ((request[67:64] == 4'b0000) ? data : 0);
		end
	endfunction
	function [(DATA_WIDTH - 1):0] compute_update;
		input reg [(DATA_WIDTH - 1):0] mask;
		input reg [(DATA_WIDTH - 1):0] data;
		input reg [(DATA_WIDTH - 1):0] original;
		compute_update = ((original & ~mask) | (data & mask));
	endfunction
	wire [13:0] addr = translate_address(last_request[63:32]);
	wire [(DATA_WIDTH - 1):0] data = mem[addr];
	wire reset = RST_N;
	assign get_ready = (reset && has_request);
	assign put_ready = (reset && (get_enable || !has_request));
	assign get_response = compute_response(last_request, data);
	wire put_wf = (put_enable && put_ready);
	wire get_wf = (get_enable && get_ready);
	always @(negedge CLK) begin
		if ((put_wf && (put_request[63:32] == EXIT_ADDRESS))) begin
			if ((put_request[31:0] == 0))
				$fwrite(32'h80000002, "  [0;32mPASS[0m\n");
			else
				$fwrite(32'h80000002, "  [0;31mFAIL[0m (%0d)\n", last_request[31:0]);
			$finish(1'b1);
		end
		if ((put_wf && (put_request[63:32] == IO_ADDRESS)))
			$fwrite(32'h80000002, "%c", put_request[7:0]);
		if ((RST_N == 1)) begin
			if (has_request)
				mem[addr] <= compute_update(compute_mask(last_request[67:64]), last_request[31:0], data);
			if (put_wf)
				last_request <= put_request;
			has_request <= (put_wf || (has_request && !get_wf));
		end
		else
			has_request <= 1'b0;
	end
endmodule
