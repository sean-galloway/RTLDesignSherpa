module arbiter_round_robin (
	clk,
	rst_n,
	block_arb,
	request,
	grant_ack,
	grant_valid,
	grant,
	grant_id,
	last_grant
);
	reg _sv2v_0;
	parameter signed [31:0] CLIENTS = 4;
	parameter signed [31:0] WAIT_GNT_ACK = 0;
	parameter signed [31:0] N = $clog2(CLIENTS);
	input wire clk;
	input wire rst_n;
	input wire block_arb;
	input wire [CLIENTS - 1:0] request;
	input wire [CLIENTS - 1:0] grant_ack;
	output reg grant_valid;
	output reg [CLIENTS - 1:0] grant;
	output reg [N - 1:0] grant_id;
	output reg [CLIENTS - 1:0] last_grant;
	wire [CLIENTS - 1:0] w_mask_decode [0:CLIENTS - 1];
	wire [CLIENTS - 1:0] w_win_mask_decode [0:CLIENTS - 1];
	genvar _gv_i_1;
	function automatic signed [CLIENTS - 1:0] sv2v_cast_6D6F8_signed;
		input reg signed [CLIENTS - 1:0] inp;
		sv2v_cast_6D6F8_signed = inp;
	endfunction
	generate
		for (_gv_i_1 = 0; _gv_i_1 < CLIENTS; _gv_i_1 = _gv_i_1 + 1) begin : gen_mask_lut
			localparam i = _gv_i_1;
			assign w_mask_decode[i] = (sv2v_cast_6D6F8_signed(1) << i) - sv2v_cast_6D6F8_signed(1);
			assign w_win_mask_decode[i] = ~((sv2v_cast_6D6F8_signed(1) << (i + 1)) - sv2v_cast_6D6F8_signed(1));
		end
	endgenerate
	reg [N - 1:0] r_last_grant_id;
	reg r_last_valid;
	reg r_pending_ack;
	reg [N - 1:0] r_pending_client;
	wire [CLIENTS - 1:0] w_requests_gated;
	wire [CLIENTS - 1:0] w_requests_masked;
	wire [CLIENTS - 1:0] w_requests_unmasked;
	wire w_any_requests;
	wire w_any_masked_requests;
	wire [CLIENTS - 1:0] w_curr_mask_decode;
	assign w_requests_gated = (block_arb ? {CLIENTS {1'sb0}} : request);
	assign w_any_requests = |w_requests_gated;
	assign w_curr_mask_decode = (grant_valid ? w_win_mask_decode[grant_id] : (r_last_valid ? w_win_mask_decode[r_last_grant_id] : sv2v_cast_6D6F8_signed(1)));
	assign w_requests_masked = w_requests_gated & w_curr_mask_decode;
	assign w_requests_unmasked = w_requests_gated;
	assign w_any_masked_requests = |w_requests_masked;
	wire [N - 1:0] w_winner;
	wire w_winner_valid;
	arbiter_priority_encoder #(
		.CLIENTS(CLIENTS),
		.N(N)
	) u_priority_encoder(
		.requests_masked(w_requests_masked),
		.requests_unmasked(w_requests_unmasked),
		.any_masked_requests(w_any_masked_requests),
		.winner(w_winner),
		.winner_valid(w_winner_valid)
	);
	wire w_ack_received;
	wire w_can_grant;
	wire [CLIENTS - 1:0] w_other_requests;
	generate
		if (WAIT_GNT_ACK == 1) begin : gen_ack_optimized
			assign w_ack_received = r_pending_ack && grant_ack[r_pending_client];
			assign w_other_requests = w_requests_gated & ~(sv2v_cast_6D6F8_signed(1) << r_pending_client);
			assign w_can_grant = !r_pending_ack || w_ack_received;
		end
		else begin : gen_no_ack_optimized
			assign w_ack_received = 1'b0;
			assign w_can_grant = 1'b1;
			assign w_other_requests = 1'sb0;
		end
	endgenerate
	wire w_should_grant;
	reg [CLIENTS - 1:0] w_next_grant;
	reg [N - 1:0] w_next_grant_id;
	wire w_next_grant_valid;
	assign w_should_grant = (w_winner_valid && w_any_requests) && w_can_grant;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_grant = 1'sb0;
		w_next_grant_id = 1'sb0;
		if (w_should_grant) begin
			w_next_grant[w_winner] = 1'b1;
			w_next_grant_id = w_winner;
		end
	end
	assign w_next_grant_valid = w_should_grant;
	always @(posedge clk)
		if (!rst_n) begin
			grant <= 1'sb0;
			grant_id <= 1'sb0;
			grant_valid <= 1'b0;
			last_grant <= 1'sb0;
			r_last_grant_id <= 1'sb0;
			r_last_valid <= 1'sb0;
			r_pending_ack <= 1'b0;
			r_pending_client <= 1'sb0;
		end
		else begin
			r_last_valid <= grant_valid;
			if (WAIT_GNT_ACK == 0) begin
				grant <= w_next_grant;
				grant_id <= w_next_grant_id;
				grant_valid <= w_next_grant_valid;
				last_grant <= grant;
				r_last_grant_id <= grant_id;
			end
			else if (grant_valid == 1'b0) begin
				grant <= w_next_grant;
				grant_id <= w_next_grant_id;
				grant_valid <= w_next_grant_valid;
				last_grant <= grant;
				r_last_grant_id <= grant_id;
				if (w_next_grant_valid) begin
					r_pending_ack <= 1'b1;
					r_pending_client <= w_next_grant_id;
				end
			end
			else if ((grant_valid == 1'b1) && !w_ack_received)
				;
			else if (((grant_valid == 1'b1) && w_ack_received) && (w_other_requests == {CLIENTS {1'sb0}})) begin
				grant <= 1'sb0;
				grant_id <= 1'sb0;
				grant_valid <= 1'b0;
				last_grant <= grant;
				r_last_grant_id <= grant_id;
				r_pending_ack <= 1'b0;
				r_pending_client <= 1'sb0;
			end
			else if (((grant_valid == 1'b1) && w_ack_received) && (w_other_requests != {CLIENTS {1'sb0}})) begin
				if (w_next_grant_valid) begin
					grant <= w_next_grant;
					grant_id <= w_next_grant_id;
					grant_valid <= w_next_grant_valid;
					last_grant <= grant;
					r_last_grant_id <= grant_id;
					r_pending_ack <= 1'b1;
					r_pending_client <= w_next_grant_id;
				end
				else begin
					grant <= 1'sb0;
					grant_id <= 1'sb0;
					grant_valid <= 1'b0;
					r_pending_ack <= 1'b0;
					r_pending_client <= 1'sb0;
				end
			end
		end
	initial _sv2v_0 = 0;
endmodule
module arbiter_priority_encoder (
	requests_masked,
	requests_unmasked,
	any_masked_requests,
	winner,
	winner_valid
);
	reg _sv2v_0;
	parameter signed [31:0] CLIENTS = 4;
	parameter signed [31:0] N = $clog2(CLIENTS);
	input wire [CLIENTS - 1:0] requests_masked;
	input wire [CLIENTS - 1:0] requests_unmasked;
	input wire any_masked_requests;
	output reg [N - 1:0] winner;
	output reg winner_valid;
	wire [CLIENTS - 1:0] w_priority_requests;
	assign w_priority_requests = (any_masked_requests ? requests_masked : requests_unmasked);
	generate
		if (CLIENTS == 4) begin : gen_pe_4
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					4'bzzz1: begin
						winner = 2'd0;
						winner_valid = 1'b1;
					end
					4'bzz10: begin
						winner = 2'd1;
						winner_valid = 1'b1;
					end
					4'bz100: begin
						winner = 2'd2;
						winner_valid = 1'b1;
					end
					4'b1000: begin
						winner = 2'd3;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 2'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else if (CLIENTS == 8) begin : gen_pe_8
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					8'bzzzzzzz1: begin
						winner = 3'd0;
						winner_valid = 1'b1;
					end
					8'bzzzzzz10: begin
						winner = 3'd1;
						winner_valid = 1'b1;
					end
					8'bzzzzz100: begin
						winner = 3'd2;
						winner_valid = 1'b1;
					end
					8'bzzzz1000: begin
						winner = 3'd3;
						winner_valid = 1'b1;
					end
					8'bzzz10000: begin
						winner = 3'd4;
						winner_valid = 1'b1;
					end
					8'bzz100000: begin
						winner = 3'd5;
						winner_valid = 1'b1;
					end
					8'bz1000000: begin
						winner = 3'd6;
						winner_valid = 1'b1;
					end
					8'b10000000: begin
						winner = 3'd7;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 3'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else if (CLIENTS == 16) begin : gen_pe_16
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					16'bzzzzzzzzzzzzzzz1: begin
						winner = 4'd0;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzzzzz10: begin
						winner = 4'd1;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzzzz100: begin
						winner = 4'd2;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzzz1000: begin
						winner = 4'd3;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzzz10000: begin
						winner = 4'd4;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzzz100000: begin
						winner = 4'd5;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzzz1000000: begin
						winner = 4'd6;
						winner_valid = 1'b1;
					end
					16'bzzzzzzzz10000000: begin
						winner = 4'd7;
						winner_valid = 1'b1;
					end
					16'bzzzzzzz100000000: begin
						winner = 4'd8;
						winner_valid = 1'b1;
					end
					16'bzzzzzz1000000000: begin
						winner = 4'd9;
						winner_valid = 1'b1;
					end
					16'bzzzzz10000000000: begin
						winner = 4'd10;
						winner_valid = 1'b1;
					end
					16'bzzzz100000000000: begin
						winner = 4'd11;
						winner_valid = 1'b1;
					end
					16'bzzz1000000000000: begin
						winner = 4'd12;
						winner_valid = 1'b1;
					end
					16'bzz10000000000000: begin
						winner = 4'd13;
						winner_valid = 1'b1;
					end
					16'bz100000000000000: begin
						winner = 4'd14;
						winner_valid = 1'b1;
					end
					16'b1000000000000000: begin
						winner = 4'd15;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 4'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else if (CLIENTS == 32) begin : gen_pe_32
			always @(*) begin
				if (_sv2v_0)
					;
				casez (w_priority_requests)
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz1: begin
						winner = 5'd0;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz10: begin
						winner = 5'd1;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzzz100: begin
						winner = 5'd2;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzzz1000: begin
						winner = 5'd3;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzzz10000: begin
						winner = 5'd4;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzzz100000: begin
						winner = 5'd5;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzzz1000000: begin
						winner = 5'd6;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzzz10000000: begin
						winner = 5'd7;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzzz100000000: begin
						winner = 5'd8;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzzz1000000000: begin
						winner = 5'd9;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzzz10000000000: begin
						winner = 5'd10;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzzz100000000000: begin
						winner = 5'd11;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzzz1000000000000: begin
						winner = 5'd12;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzzz10000000000000: begin
						winner = 5'd13;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzzz100000000000000: begin
						winner = 5'd14;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzzz1000000000000000: begin
						winner = 5'd15;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzzz10000000000000000: begin
						winner = 5'd16;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzzz100000000000000000: begin
						winner = 5'd17;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzzz1000000000000000000: begin
						winner = 5'd18;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzzz10000000000000000000: begin
						winner = 5'd19;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzzz100000000000000000000: begin
						winner = 5'd20;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzzz1000000000000000000000: begin
						winner = 5'd21;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzzz10000000000000000000000: begin
						winner = 5'd22;
						winner_valid = 1'b1;
					end
					32'bzzzzzzzz100000000000000000000000: begin
						winner = 5'd23;
						winner_valid = 1'b1;
					end
					32'bzzzzzzz1000000000000000000000000: begin
						winner = 5'd24;
						winner_valid = 1'b1;
					end
					32'bzzzzzz10000000000000000000000000: begin
						winner = 5'd25;
						winner_valid = 1'b1;
					end
					32'bzzzzz100000000000000000000000000: begin
						winner = 5'd26;
						winner_valid = 1'b1;
					end
					32'bzzzz1000000000000000000000000000: begin
						winner = 5'd27;
						winner_valid = 1'b1;
					end
					32'bzzz10000000000000000000000000000: begin
						winner = 5'd28;
						winner_valid = 1'b1;
					end
					32'bzz100000000000000000000000000000: begin
						winner = 5'd29;
						winner_valid = 1'b1;
					end
					32'bz1000000000000000000000000000000: begin
						winner = 5'd30;
						winner_valid = 1'b1;
					end
					32'b10000000000000000000000000000000: begin
						winner = 5'd31;
						winner_valid = 1'b1;
					end
					default: begin
						winner = 5'd0;
						winner_valid = 1'b0;
					end
				endcase
			end
		end
		else begin : gen_pe_generic
			always @(*) begin
				if (_sv2v_0)
					;
				winner = 1'sb0;
				winner_valid = 1'b0;
				begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < CLIENTS; i = i + 1)
						if (w_priority_requests[i] && !winner_valid) begin
							winner = i[N - 1:0];
							winner_valid = 1'b1;
						end
				end
			end
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module counter_bin (
	clk,
	rst_n,
	enable,
	counter_bin_curr,
	counter_bin_next
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 5;
	parameter signed [31:0] MAX = 10;
	input wire clk;
	input wire rst_n;
	input wire enable;
	output reg [WIDTH - 1:0] counter_bin_curr;
	output reg [WIDTH - 1:0] counter_bin_next;
	wire [WIDTH - 2:0] w_max_val;
	function automatic signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] sv2v_cast_00F62_signed;
		input reg signed [((WIDTH - 2) >= 0 ? WIDTH - 1 : 3 - WIDTH) - 1:0] inp;
		sv2v_cast_00F62_signed = inp;
	endfunction
	assign w_max_val = sv2v_cast_00F62_signed(MAX - 1);
	always @(*) begin
		if (_sv2v_0)
			;
		if (enable) begin
			if (counter_bin_curr[WIDTH - 2:0] == w_max_val)
				counter_bin_next = {~counter_bin_curr[WIDTH - 1], {WIDTH - 1 {1'b0}}};
			else
				counter_bin_next = counter_bin_curr + 1;
		end
		else
			counter_bin_next = counter_bin_curr;
	end
	always @(posedge clk)
		if (!rst_n)
			counter_bin_curr <= 'b0;
		else
			counter_bin_curr <= counter_bin_next;
	initial _sv2v_0 = 0;
endmodule
module fifo_control (
	wr_clk,
	wr_rst_n,
	rd_clk,
	rd_rst_n,
	wr_ptr_bin,
	wdom_rd_ptr_bin,
	rd_ptr_bin,
	rdom_wr_ptr_bin,
	count,
	wr_full,
	wr_almost_full,
	rd_empty,
	rd_almost_empty
);
	parameter signed [31:0] ADDR_WIDTH = 3;
	parameter signed [31:0] DEPTH = 16;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] REGISTERED = 0;
	input wire wr_clk;
	input wire wr_rst_n;
	input wire rd_clk;
	input wire rd_rst_n;
	input wire [ADDR_WIDTH:0] wr_ptr_bin;
	input wire [ADDR_WIDTH:0] wdom_rd_ptr_bin;
	input wire [ADDR_WIDTH:0] rd_ptr_bin;
	input wire [ADDR_WIDTH:0] rdom_wr_ptr_bin;
	output wire [ADDR_WIDTH:0] count;
	output reg wr_full;
	output reg wr_almost_full;
	output reg rd_empty;
	output reg rd_almost_empty;
	localparam signed [31:0] D = DEPTH;
	localparam signed [31:0] AW = ADDR_WIDTH;
	localparam signed [31:0] AFULL = ALMOST_WR_MARGIN;
	localparam signed [31:0] AEMPTY = ALMOST_RD_MARGIN;
	localparam signed [31:0] AFT = D - AFULL;
	localparam signed [31:0] AET = AEMPTY;
	wire w_wdom_ptr_xor;
	wire w_rdom_ptr_xor;
	wire w_wr_full_d;
	wire w_wr_almost_full_d;
	wire w_rd_empty_d;
	wire w_rd_almost_empty_d;
	wire [AW:0] w_almost_full_count;
	wire [AW:0] w_almost_empty_count;
	assign w_wdom_ptr_xor = wr_ptr_bin[AW] ^ wdom_rd_ptr_bin[AW];
	assign w_rdom_ptr_xor = rd_ptr_bin[AW] ^ rdom_wr_ptr_bin[AW];
	assign w_wr_full_d = w_wdom_ptr_xor && (wr_ptr_bin[AW - 1:0] == wdom_rd_ptr_bin[AW - 1:0]);
	function automatic signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65_signed;
		input reg signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65_signed = inp;
	endfunction
	assign w_almost_full_count = (w_wdom_ptr_xor ? (sv2v_cast_2BB65_signed(D) - wdom_rd_ptr_bin[AW - 1:0]) + wr_ptr_bin[AW - 1:0] : wr_ptr_bin[AW - 1:0] - wdom_rd_ptr_bin[AW - 1:0]);
	assign w_wr_almost_full_d = w_almost_full_count >= sv2v_cast_2BB65_signed(AFT);
	always @(posedge wr_clk or negedge wr_rst_n)
		if (!wr_rst_n) begin
			wr_full <= 'b0;
			wr_almost_full <= 'b0;
		end
		else begin
			wr_full <= w_wr_full_d;
			wr_almost_full <= w_wr_almost_full_d;
		end
	wire [ADDR_WIDTH:0] w_wr_ptr_for_empty;
	wire w_rdom_ptr_xor_for_empty;
	generate
		if (REGISTERED == 1) begin : gen_flop_mode
			reg [ADDR_WIDTH:0] r_rdom_wr_ptr_bin_delayed;
			always @(posedge rd_clk)
				if (!rd_rst_n)
					r_rdom_wr_ptr_bin_delayed <= 1'sb0;
				else
					r_rdom_wr_ptr_bin_delayed <= rdom_wr_ptr_bin;
			assign w_wr_ptr_for_empty = r_rdom_wr_ptr_bin_delayed;
		end
		else begin : gen_mux_mode
			assign w_wr_ptr_for_empty = rdom_wr_ptr_bin;
		end
	endgenerate
	assign w_rdom_ptr_xor_for_empty = rd_ptr_bin[AW] ^ w_wr_ptr_for_empty[AW];
	assign w_rd_empty_d = !w_rdom_ptr_xor_for_empty && (rd_ptr_bin[AW:0] == w_wr_ptr_for_empty[AW:0]);
	assign w_almost_empty_count = (w_rdom_ptr_xor ? (sv2v_cast_2BB65_signed(D) - rd_ptr_bin[AW - 1:0]) + rdom_wr_ptr_bin[AW - 1:0] : rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]);
	assign w_rd_almost_empty_d = w_almost_empty_count <= sv2v_cast_2BB65_signed(AET);
	wire [ADDR_WIDTH:0] w_count;
	reg [ADDR_WIDTH:0] r_count;
	assign w_count = (w_rdom_ptr_xor ? (rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]) + sv2v_cast_2BB65_signed(D) : rdom_wr_ptr_bin[AW - 1:0] - rd_ptr_bin[AW - 1:0]);
	assign count = (REGISTERED == 1 ? r_count : w_count);
	always @(posedge rd_clk or negedge rd_rst_n)
		if (!rd_rst_n) begin
			rd_empty <= 'b1;
			rd_almost_empty <= 'b0;
			r_count <= 'b0;
		end
		else begin
			rd_empty <= w_rd_empty_d;
			rd_almost_empty <= w_rd_almost_empty_d;
			r_count <= w_count;
		end
endmodule
module gaxi_fifo_sync (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	rd_ready,
	count,
	rd_valid,
	rd_data
);
	reg _sv2v_0;
	parameter signed [31:0] MEM_STYLE = 32'sd0;
	parameter signed [31:0] REGISTERED = 0;
	parameter signed [31:0] DATA_WIDTH = 4;
	parameter signed [31:0] DEPTH = 4;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(DEPTH);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output wire wr_ready;
	input wire [DW - 1:0] wr_data;
	input wire rd_ready;
	output wire [AW:0] count;
	output wire rd_valid;
	output wire [DW - 1:0] rd_data;
	wire [AW - 1:0] r_wr_addr;
	wire [AW - 1:0] r_rd_addr;
	wire [AW:0] r_wr_ptr_bin;
	wire [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	reg [DW - 1:0] w_rd_data;
	wire w_write;
	wire w_read;
	assign w_write = wr_valid && wr_ready;
	assign w_read = rd_valid && rd_ready;
	counter_bin #(
		.WIDTH(AW + 1),
		.MAX(D)
	) write_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_write && !r_wr_full),
		.counter_bin_curr(r_wr_ptr_bin),
		.counter_bin_next(w_wr_ptr_bin_next)
	);
	counter_bin #(
		.WIDTH(AW + 1),
		.MAX(D)
	) read_pointer_inst(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.enable(w_read && !r_rd_empty),
		.counter_bin_curr(r_rd_ptr_bin),
		.counter_bin_next(w_rd_ptr_bin_next)
	);
	fifo_control #(
		.DEPTH(D),
		.ADDR_WIDTH(AW),
		.ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
		.ALMOST_WR_MARGIN(ALMOST_WR_MARGIN),
		.REGISTERED(REGISTERED)
	) fifo_control_inst(
		.wr_clk(axi_aclk),
		.wr_rst_n(axi_aresetn),
		.rd_clk(axi_aclk),
		.rd_rst_n(axi_aresetn),
		.wr_ptr_bin(w_wr_ptr_bin_next),
		.wdom_rd_ptr_bin(w_rd_ptr_bin_next),
		.rd_ptr_bin(w_rd_ptr_bin_next),
		.rdom_wr_ptr_bin(w_wr_ptr_bin_next),
		.count(count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full;
	assign rd_valid = !r_rd_empty;
	assign r_wr_addr = r_wr_ptr_bin[AW - 1:0];
	assign r_rd_addr = r_rd_ptr_bin[AW - 1:0];
	generate
		if (MEM_STYLE == 32'sd1) begin : gen_srl
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				always @(posedge axi_aclk)
					if (!axi_aresetn)
						w_rd_data <= 1'sb0;
					else
						w_rd_data <= mem[r_rd_addr];
			end
			else begin : g_mux
				always @(*) begin
					if (_sv2v_0)
						;
					w_rd_data = mem[r_rd_addr];
				end
			end
		end
		else if (MEM_STYLE == 32'sd2) begin : gen_bram
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			always @(posedge axi_aclk)
				if (!axi_aresetn)
					w_rd_data <= 1'sb0;
				else
					w_rd_data <= mem[r_rd_addr];
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				always @(posedge axi_aclk)
					if (!axi_aresetn)
						w_rd_data <= 1'sb0;
					else
						w_rd_data <= mem[r_rd_addr];
			end
			else begin : g_mux
				always @(*) begin
					if (_sv2v_0)
						;
					w_rd_data = mem[r_rd_addr];
				end
			end
		end
	endgenerate
	assign rd_data = w_rd_data;
	always @(posedge axi_aclk) begin
		if (w_write && r_wr_full)
			;
		if (w_read && r_rd_empty)
			;
	end
	initial _sv2v_0 = 0;
endmodule
module axi_write_engine (
	clk,
	rst_n,
	cfg_axi_wr_xfer_beats,
	sched_wr_valid,
	sched_wr_ready,
	sched_wr_addr,
	sched_wr_beats,
	sched_wr_burst_len,
	sched_wr_done_strobe,
	sched_wr_beats_done,
	axi_wr_drain_req,
	axi_wr_drain_size,
	axi_wr_drain_data_avail,
	axi_wr_sram_valid,
	axi_wr_sram_drain,
	axi_wr_sram_id,
	axi_wr_sram_data,
	m_axi_awid,
	m_axi_awaddr,
	m_axi_awlen,
	m_axi_awsize,
	m_axi_awburst,
	m_axi_awvalid,
	m_axi_awready,
	m_axi_wdata,
	m_axi_wstrb,
	m_axi_wlast,
	m_axi_wuser,
	m_axi_wvalid,
	m_axi_wready,
	m_axi_bid,
	m_axi_bresp,
	m_axi_bvalid,
	m_axi_bready,
	sched_wr_error,
	dbg_wr_all_complete,
	dbg_aw_transactions,
	dbg_w_beats
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] USER_WIDTH = 8;
	parameter signed [31:0] SEG_COUNT_WIDTH = 8;
	parameter signed [31:0] PIPELINE = 0;
	parameter signed [31:0] AW_MAX_OUTSTANDING = 8;
	parameter signed [31:0] W_PHASE_FIFO_DEPTH = 64;
	parameter signed [31:0] B_PHASE_FIFO_DEPTH = 16;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	parameter signed [31:0] UW = USER_WIDTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	parameter signed [31:0] CIW = (NC > 1 ? $clog2(NC) : 1);
	input wire clk;
	input wire rst_n;
	input wire [7:0] cfg_axi_wr_xfer_beats;
	input wire [NC - 1:0] sched_wr_valid;
	output wire [NC - 1:0] sched_wr_ready;
	input wire [(NC * AW) - 1:0] sched_wr_addr;
	input wire [(NC * 32) - 1:0] sched_wr_beats;
	input wire [(NC * 8) - 1:0] sched_wr_burst_len;
	output wire [NC - 1:0] sched_wr_done_strobe;
	output wire [(NC * 32) - 1:0] sched_wr_beats_done;
	output wire [NC - 1:0] axi_wr_drain_req;
	output wire [(NC * 8) - 1:0] axi_wr_drain_size;
	input wire [(NC * SCW) - 1:0] axi_wr_drain_data_avail;
	input wire [NC - 1:0] axi_wr_sram_valid;
	output wire axi_wr_sram_drain;
	output wire [CIW - 1:0] axi_wr_sram_id;
	input wire [DW - 1:0] axi_wr_sram_data;
	output wire [IW - 1:0] m_axi_awid;
	output wire [AW - 1:0] m_axi_awaddr;
	output wire [7:0] m_axi_awlen;
	output wire [2:0] m_axi_awsize;
	output wire [1:0] m_axi_awburst;
	output wire m_axi_awvalid;
	input wire m_axi_awready;
	output wire [DW - 1:0] m_axi_wdata;
	output wire [(DW / 8) - 1:0] m_axi_wstrb;
	output wire m_axi_wlast;
	output wire [UW - 1:0] m_axi_wuser;
	output wire m_axi_wvalid;
	input wire m_axi_wready;
	input wire [IW - 1:0] m_axi_bid;
	input wire [1:0] m_axi_bresp;
	input wire m_axi_bvalid;
	output wire m_axi_bready;
	output wire [NC - 1:0] sched_wr_error;
	output wire [NC - 1:0] dbg_wr_all_complete;
	output wire [31:0] dbg_aw_transactions;
	output wire [31:0] dbg_w_beats;
	localparam signed [31:0] BYTES_PER_BEAT = DW / 8;
	localparam signed [31:0] AXSIZE = $clog2(BYTES_PER_BEAT);
	localparam signed [31:0] MOW = $clog2(AW_MAX_OUTSTANDING + 1);
	reg [NC - 1:0] r_outstanding_limit;
	reg [(NC * MOW) - 1:0] r_outstanding_count;
	reg [CIW - 1:0] r_aw_channel_id;
	function automatic signed [MOW - 1:0] sv2v_cast_04DDF_signed;
		input reg signed [MOW - 1:0] inp;
		sv2v_cast_04DDF_signed = inp;
	endfunction
	generate
		if (PIPELINE == 0) begin : gen_no_pipeline_tracking
			always @(posedge clk)
				if (!rst_n)
					r_outstanding_limit <= 1'sb0;
				else begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						begin
							if ((m_axi_awvalid && m_axi_awready) && (r_aw_channel_id == i[CIW - 1:0]))
								r_outstanding_limit[i] <= 1'b1;
							if ((m_axi_bvalid && m_axi_bready) && (m_axi_bid[CIW - 1:0] == i[CIW - 1:0]))
								r_outstanding_limit[i] <= 1'b0;
						end
				end
			wire [NC * MOW:1] sv2v_tmp_16AB7;
			assign sv2v_tmp_16AB7 = 1'sb0;
			always @(*) r_outstanding_count = sv2v_tmp_16AB7;
		end
		else begin : gen_pipeline_tracking
			reg [NC - 1:0] w_incr;
			reg [NC - 1:0] w_decr;
			always @(*) begin
				if (_sv2v_0)
					;
				begin : sv2v_autoblock_2
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						begin
							w_incr[i] = (m_axi_awvalid && m_axi_awready) && (r_aw_channel_id == i[CIW - 1:0]);
							w_decr[i] = (m_axi_bvalid && m_axi_bready) && (m_axi_bid[CIW - 1:0] == i[CIW - 1:0]);
						end
				end
			end
			always @(posedge clk)
				if (!rst_n)
					r_outstanding_count <= 1'sb0;
				else begin : sv2v_autoblock_3
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						case ({w_incr[i], w_decr[i]})
							2'b10: r_outstanding_count[i * MOW+:MOW] <= r_outstanding_count[i * MOW+:MOW] + 1'b1;
							2'b01: r_outstanding_count[i * MOW+:MOW] <= r_outstanding_count[i * MOW+:MOW] - 1'b1;
							default: r_outstanding_count[i * MOW+:MOW] <= r_outstanding_count[i * MOW+:MOW];
						endcase
				end
			always @(*) begin
				if (_sv2v_0)
					;
				begin : sv2v_autoblock_4
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						r_outstanding_limit[i] = r_outstanding_count[i * MOW+:MOW] >= sv2v_cast_04DDF_signed(AW_MAX_OUTSTANDING);
				end
			end
		end
	endgenerate
	reg [NC - 1:0] r_all_complete;
	reg [(NC * 32) - 1:0] r_beats_written;
	always @(posedge clk)
		if (!rst_n)
			r_all_complete <= 1'sb1;
		else begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					if (r_outstanding_count[i * MOW+:MOW] == {MOW * 1 {1'sb0}})
						r_all_complete[i] <= 1'b1;
					if (sched_wr_valid[i] && (r_beats_written[i * 32+:32] == {32 {1'sb0}}))
						r_all_complete[i] <= 1'b0;
				end
		end
	assign dbg_wr_all_complete = r_all_complete;
	wire [(NC * 9) - 1:0] b_phase_txn_fifo_dout;
	always @(posedge clk)
		if (!rst_n)
			r_beats_written <= {NC {32'd0}};
		else begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				if (!sched_wr_valid[i])
					r_beats_written[i * 32+:32] <= 32'h00000000;
				else if ((m_axi_bvalid && m_axi_bready) && (m_axi_bid[CIW - 1:0] == i[CIW - 1:0]))
					r_beats_written[i * 32+:32] <= r_beats_written[i * 32+:32] + {24'h000000, b_phase_txn_fifo_dout[(i * 9) + 8-:8]};
		end
	reg [NC - 1:0] w_has_data;
	reg [NC - 1:0] w_data_ok;
	reg [NC - 1:0] w_no_outstanding;
	reg [NC - 1:0] w_arb_request;
	reg [(NC * 8) - 1:0] w_transfer_size;
	reg [NC - 1:0] w_final_burst;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic [SCW - 1:0] sv2v_cast_14961;
		input reg [SCW - 1:0] inp;
		sv2v_cast_14961 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					if (sched_wr_valid[i]) begin
						w_transfer_size[i * 8+:8] = sv2v_cast_8((sched_wr_beats[i * 32+:32] <= (sv2v_cast_32(cfg_axi_wr_xfer_beats) + 32'd1) ? sched_wr_beats[i * 32+:32] - 32'd1 : sv2v_cast_32(cfg_axi_wr_xfer_beats)));
						w_has_data[i] = sv2v_cast_14961(axi_wr_drain_data_avail[i * SCW+:SCW]) >= sv2v_cast_14961(w_transfer_size[i * 8+:8] + 8'd1);
						w_final_burst[i] = (sched_wr_beats[i * 32+:32] > 0) && (sched_wr_beats[i * 32+:32] <= (sv2v_cast_32(cfg_axi_wr_xfer_beats) + 32'd1));
						w_data_ok[i] = w_has_data[i] || w_final_burst[i];
					end
					else begin
						w_has_data[i] = 1'b0;
						w_transfer_size[i * 8+:8] = 'b0;
						w_final_burst[i] = 1'b0;
						w_data_ok[i] = 1'b0;
					end
					w_no_outstanding[i] = !r_outstanding_limit[i];
					w_arb_request[i] = (sched_wr_valid[i] && w_data_ok[i]) && w_no_outstanding[i];
				end
		end
	end
	wire w_arb_grant_valid;
	wire [NC - 1:0] w_arb_grant;
	wire [CIW - 1:0] w_arb_grant_id;
	wire [NC - 1:0] w_arb_grant_ack;
	generate
		if (NC == 1) begin : gen_single_channel
			assign w_arb_grant_valid = w_arb_request[0];
			assign w_arb_grant = w_arb_request;
			assign w_arb_grant_id = 1'b0;
		end
		else begin : gen_multi_channel
			arbiter_round_robin #(
				.CLIENTS(NC),
				.WAIT_GNT_ACK(1)
			) u_arbiter(
				.clk(clk),
				.rst_n(rst_n),
				.block_arb(1'b0),
				.request(w_arb_request),
				.grant_ack(w_arb_grant_ack),
				.grant_valid(w_arb_grant_valid),
				.grant(w_arb_grant),
				.grant_id(w_arb_grant_id),
				.last_grant()
			);
		end
	endgenerate
	reg [7:0] r_aw_len;
	reg r_aw_valid;
	assign w_arb_grant_ack = w_arb_grant & {NC {m_axi_awvalid && m_axi_awready}};
	always @(posedge clk)
		if (!rst_n) begin
			r_aw_valid <= 1'b0;
			r_aw_len <= 1'sb0;
			r_aw_channel_id <= 1'sb0;
		end
		else begin
			if (w_arb_grant_valid && !r_aw_valid) begin
				r_aw_valid <= 1'b1;
				r_aw_channel_id <= w_arb_grant_id;
				r_aw_len <= w_transfer_size[w_arb_grant_id * 8+:8];
			end
			if (m_axi_awvalid && m_axi_awready)
				r_aw_valid <= 1'b0;
		end
	assign m_axi_awvalid = r_aw_valid;
	assign m_axi_awid = {{IW - CIW {1'b0}}, r_aw_channel_id};
	assign m_axi_awaddr = sched_wr_addr[r_aw_channel_id * AW+:AW];
	assign m_axi_awlen = r_aw_len;
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign m_axi_awsize = sv2v_cast_3_signed(AXSIZE);
	assign m_axi_awburst = 2'b01;
	reg [NC - 1:0] w_drain_req;
	reg [(NC * 8) - 1:0] w_drain_size;
	always @(*) begin
		if (_sv2v_0)
			;
		w_drain_req = 1'sb0;
		w_drain_size = {NC {8'h00}};
		if (m_axi_awvalid && m_axi_awready) begin
			w_drain_req[r_aw_channel_id] = 1'b1;
			w_drain_size[r_aw_channel_id * 8+:8] = m_axi_awlen + 8'd1;
		end
	end
	assign axi_wr_drain_req = w_drain_req;
	assign axi_wr_drain_size = w_drain_size;
	reg [NC - 1:0] r_sched_ready;
	always @(posedge clk)
		if (!rst_n)
			r_sched_ready <= 1'sb0;
		else begin
			r_sched_ready <= 1'sb0;
			if (m_axi_bvalid && m_axi_bready) begin : sv2v_autoblock_8
				reg [CIW - 1:0] ch_id;
				ch_id = m_axi_bid[CIW - 1:0];
				if (b_phase_txn_fifo_dout[ch_id * 9])
					r_sched_ready[ch_id] <= 1'b1;
			end
		end
	assign sched_wr_ready = r_sched_ready;
	reg [7:0] r_w_beats_remaining;
	reg [CIW - 1:0] r_w_channel_id;
	reg r_w_active;
	wire [(8 + CIW) - 1:0] w_phase_txn_fifo_dout;
	wire w_phase_txn_fifo_empty;
	always @(posedge clk)
		if (!rst_n) begin
			r_w_beats_remaining <= 1'sb0;
			r_w_channel_id <= 1'sb0;
			r_w_active <= 1'b0;
		end
		else if (!r_w_active) begin
			if (!w_phase_txn_fifo_empty) begin
				r_w_active <= 1'b1;
				r_w_channel_id <= w_phase_txn_fifo_dout[CIW - 1-:CIW];
				r_w_beats_remaining <= w_phase_txn_fifo_dout[CIW + 7-:((CIW + 7) >= (CIW + 0) ? ((CIW + 7) - (CIW + 0)) + 1 : ((CIW + 0) - (CIW + 7)) + 1)];
			end
		end
		else if (m_axi_wvalid && m_axi_wready) begin
			r_w_beats_remaining <= r_w_beats_remaining - 8'd1;
			if (m_axi_wlast) begin
				if (!w_phase_txn_fifo_empty) begin
					r_w_channel_id <= w_phase_txn_fifo_dout[CIW - 1-:CIW];
					r_w_beats_remaining <= w_phase_txn_fifo_dout[CIW + 7-:((CIW + 7) >= (CIW + 0) ? ((CIW + 7) - (CIW + 0)) + 1 : ((CIW + 0) - (CIW + 7)) + 1)];
				end
				else
					r_w_active <= 1'b0;
			end
		end
	assign axi_wr_sram_drain = r_w_active && m_axi_wready;
	assign axi_wr_sram_id = r_w_channel_id;
	assign m_axi_wvalid = r_w_active && axi_wr_sram_valid[r_w_channel_id];
	assign m_axi_wdata = axi_wr_sram_data;
	assign m_axi_wstrb = {DW / 8 {1'b1}};
	assign m_axi_wlast = r_w_beats_remaining == 8'd1;
	function automatic [UW - 1:0] sv2v_cast_FDCE5;
		input reg [UW - 1:0] inp;
		sv2v_cast_FDCE5 = inp;
	endfunction
	assign m_axi_wuser = sv2v_cast_FDCE5(r_w_channel_id);
	reg w_phase_txn_fifo_wr;
	wire w_phase_txn_fifo_rd;
	reg [(8 + CIW) - 1:0] w_phase_txn_fifo_din;
	wire w_phase_txn_fifo_full;
	wire w_phase_txn_fifo_wr_ready;
	wire w_phase_txn_fifo_rd_valid;
	gaxi_fifo_sync #(
		.DATA_WIDTH(8 + CIW),
		.DEPTH(W_PHASE_FIFO_DEPTH)
	) u_w_phase_txn_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_data(w_phase_txn_fifo_din),
		.wr_valid(w_phase_txn_fifo_wr),
		.wr_ready(w_phase_txn_fifo_wr_ready),
		.rd_data(w_phase_txn_fifo_dout),
		.rd_valid(w_phase_txn_fifo_rd_valid),
		.rd_ready(w_phase_txn_fifo_rd),
		.count()
	);
	assign w_phase_txn_fifo_full = !w_phase_txn_fifo_wr_ready;
	assign w_phase_txn_fifo_empty = !w_phase_txn_fifo_rd_valid;
	always @(*) begin
		if (_sv2v_0)
			;
		w_phase_txn_fifo_wr = 1'b0;
		w_phase_txn_fifo_din = 1'sb0;
		if (m_axi_awvalid && m_axi_awready) begin
			w_phase_txn_fifo_wr = 1'b1;
			w_phase_txn_fifo_din[CIW + 7-:((CIW + 7) >= (CIW + 0) ? ((CIW + 7) - (CIW + 0)) + 1 : ((CIW + 0) - (CIW + 7)) + 1)] = m_axi_awlen + 8'd1;
			w_phase_txn_fifo_din[CIW - 1-:CIW] = r_aw_channel_id;
		end
	end
	reg w_phase_fifo_pop;
	always @(*) begin
		if (_sv2v_0)
			;
		w_phase_fifo_pop = 1'b0;
		if (!r_w_active && !w_phase_txn_fifo_empty)
			w_phase_fifo_pop = 1'b1;
		else if (((m_axi_wvalid && m_axi_wready) && m_axi_wlast) && !w_phase_txn_fifo_empty)
			w_phase_fifo_pop = 1'b1;
	end
	assign w_phase_txn_fifo_rd = w_phase_fifo_pop;
	reg [NC - 1:0] b_phase_txn_fifo_wr;
	reg [NC - 1:0] b_phase_txn_fifo_rd;
	reg [(NC * 9) - 1:0] b_phase_txn_fifo_din;
	wire [NC - 1:0] b_phase_txn_fifo_empty;
	wire [NC - 1:0] b_phase_txn_fifo_full;
	genvar _gv_g_1;
	generate
		for (_gv_g_1 = 0; _gv_g_1 < NC; _gv_g_1 = _gv_g_1 + 1) begin : gen_b_phase_txn_fifos
			localparam g = _gv_g_1;
			wire b_phase_txn_fifo_wr_ready;
			wire b_phase_txn_fifo_rd_valid;
			gaxi_fifo_sync #(
				.DATA_WIDTH(9),
				.DEPTH(B_PHASE_FIFO_DEPTH)
			) u_b_phase_txn_fifo(
				.axi_aclk(clk),
				.axi_aresetn(rst_n),
				.wr_data(b_phase_txn_fifo_din[g * 9+:9]),
				.wr_valid(b_phase_txn_fifo_wr[g]),
				.wr_ready(b_phase_txn_fifo_wr_ready),
				.rd_data(b_phase_txn_fifo_dout[g * 9+:9]),
				.rd_valid(b_phase_txn_fifo_rd_valid),
				.rd_ready(b_phase_txn_fifo_rd[g]),
				.count()
			);
			assign b_phase_txn_fifo_full[g] = !b_phase_txn_fifo_wr_ready;
			assign b_phase_txn_fifo_empty[g] = !b_phase_txn_fifo_rd_valid;
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		b_phase_txn_fifo_wr = 1'sb0;
		b_phase_txn_fifo_din = {NC {9'b000000000}};
		if (m_axi_awvalid && m_axi_awready) begin
			b_phase_txn_fifo_wr[r_aw_channel_id] = 1'b1;
			b_phase_txn_fifo_din[(r_aw_channel_id * 9) + 8-:8] = m_axi_awlen + 8'd1;
			b_phase_txn_fifo_din[r_aw_channel_id * 9] = sched_wr_beats[r_aw_channel_id * 32+:32] <= ({24'd0, m_axi_awlen} + 32'd1);
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		b_phase_txn_fifo_rd = 1'sb0;
		if (m_axi_bvalid && m_axi_bready)
			b_phase_txn_fifo_rd[m_axi_bid[CIW - 1:0]] = !b_phase_txn_fifo_empty[m_axi_bid[CIW - 1:0]];
	end
	reg [NC - 1:0] r_done_strobe;
	reg [(NC * 32) - 1:0] r_beats_done;
	always @(posedge clk)
		if (!rst_n) begin
			r_done_strobe <= {NC {1'd0}};
			r_beats_done <= {NC {32'd0}};
		end
		else begin
			r_done_strobe <= {NC {1'd0}};
			if (m_axi_awvalid && m_axi_awready) begin
				r_done_strobe[r_aw_channel_id] <= 1'b1;
				r_beats_done[r_aw_channel_id * 32+:32] <= {24'd0, m_axi_awlen} + 32'd1;
			end
		end
	assign sched_wr_done_strobe = r_done_strobe;
	assign sched_wr_beats_done = r_beats_done;
	assign m_axi_bready = 1'b1;
	reg [NC - 1:0] r_wr_error;
	always @(posedge clk)
		if (!rst_n)
			r_wr_error <= 1'sb0;
		else if ((m_axi_bvalid && m_axi_bready) && (m_axi_bresp != 2'b00)) begin : sv2v_autoblock_9
			reg [CIW - 1:0] ch_id;
			ch_id = m_axi_bid[CIW - 1:0];
			r_wr_error[ch_id] <= 1'b1;
		end
	assign sched_wr_error = r_wr_error;
	reg [31:0] r_aw_transactions;
	reg [31:0] r_w_beats;
	always @(posedge clk)
		if (!rst_n) begin
			r_aw_transactions <= 1'sb0;
			r_w_beats <= 1'sb0;
		end
		else begin
			if (m_axi_awvalid && m_axi_awready)
				r_aw_transactions <= r_aw_transactions + 1'b1;
			if (m_axi_wvalid && m_axi_wready)
				r_w_beats <= r_w_beats + 1'b1;
		end
	assign dbg_aw_transactions = r_aw_transactions;
	assign dbg_w_beats = r_w_beats;
	initial _sv2v_0 = 0;
endmodule
