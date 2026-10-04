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
	always @(posedge clk or negedge rst_n)
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
module arbiter_single_client (
	clk,
	rst_n,
	block_arb,
	request,
	grant_ack,
	grant_valid,
	grant,
	grant_id
);
	parameter signed [31:0] WAIT_GNT_ACK = 1;
	input wire clk;
	input wire rst_n;
	input wire block_arb;
	input wire request;
	input wire grant_ack;
	output reg grant_valid;
	output wire grant;
	output wire grant_id;
	reg r_pending_ack;
	wire w_req;
	wire w_ack_received;
	wire w_can_grant;
	wire w_should_grant;
	assign w_req = request && !block_arb;
	assign w_ack_received = (WAIT_GNT_ACK == 1 ? r_pending_ack && grant_ack : 1'b0);
	assign w_can_grant = (WAIT_GNT_ACK == 1 ? !r_pending_ack || w_ack_received : 1'b1);
	assign w_should_grant = w_req && w_can_grant;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			grant_valid <= 1'b0;
			r_pending_ack <= 1'b0;
		end
		else if (WAIT_GNT_ACK == 0) begin
			grant_valid <= w_should_grant;
			r_pending_ack <= 1'b0;
		end
		else if (grant_valid == 1'b0) begin
			grant_valid <= w_should_grant;
			r_pending_ack <= w_should_grant;
		end
		else if (!w_ack_received) begin
			grant_valid <= 1'b1;
			r_pending_ack <= 1'b1;
		end
		else begin
			grant_valid <= 1'b0;
			r_pending_ack <= 1'b0;
		end
	assign grant = grant_valid;
	assign grant_id = 1'b0;
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
	always @(posedge clk or negedge rst_n)
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
	parameter signed [31:0] DEPTH = 8;
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
			always @(posedge rd_clk or negedge rd_rst_n)
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
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
		else if (MEM_STYLE == 32'sd2) begin : gen_bram
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			reg [DATA_WIDTH - 1:0] r_rd_data;
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_rd_data <= 1'sb0;
				else
					r_rd_data <= mem[r_rd_addr];
			assign rd_data = r_rd_data;
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
	endgenerate
	always @(posedge axi_aclk) begin
		if (w_write && r_wr_full)
			;
		if (w_read && r_rd_empty)
			;
	end
endmodule
module stream_alloc_ctrl (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_size,
	wr_ready,
	rd_valid,
	rd_ready,
	space_free,
	wr_full,
	wr_almost_full,
	rd_empty,
	rd_almost_empty
);
	parameter signed [31:0] DEPTH = 512;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] REGISTERED = 1;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(D);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	input wire [7:0] wr_size;
	output wire wr_ready;
	input wire rd_valid;
	output wire rd_ready;
	output wire [AW:0] space_free;
	output wire wr_full;
	output wire wr_almost_full;
	output wire rd_empty;
	output wire rd_almost_empty;
	reg [AW:0] r_wr_ptr_bin;
	wire [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	wire [AW:0] w_count;
	wire w_write;
	wire w_read;
	assign w_write = wr_valid && wr_ready;
	assign w_read = rd_valid && rd_ready;
	function automatic [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65;
		input reg [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn)
			r_wr_ptr_bin <= 1'sb0;
		else if (w_write && !r_wr_full)
			r_wr_ptr_bin <= r_wr_ptr_bin + sv2v_cast_2BB65(wr_size);
	assign w_wr_ptr_bin_next = r_wr_ptr_bin + (w_write && !r_wr_full ? sv2v_cast_2BB65(wr_size) : {(AW >= 0 ? AW + 1 : 1 - AW) {1'sb0}});
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
		.count(w_count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full;
	assign rd_ready = !r_rd_empty;
	function automatic signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65_signed;
		input reg signed [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65_signed = inp;
	endfunction
	assign space_free = sv2v_cast_2BB65_signed(D) - w_count;
	assign wr_full = r_wr_full;
	assign wr_almost_full = r_wr_almost_full;
	assign rd_empty = r_rd_empty;
	assign rd_almost_empty = r_rd_almost_empty;
endmodule
module stream_drain_ctrl (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	rd_valid,
	rd_size,
	rd_ready,
	data_available,
	wr_full,
	wr_almost_full,
	rd_empty,
	rd_almost_empty
);
	parameter signed [31:0] DEPTH = 512;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] REGISTERED = 1;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(D);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output wire wr_ready;
	input wire rd_valid;
	input wire [7:0] rd_size;
	output wire rd_ready;
	output wire [AW:0] data_available;
	output wire wr_full;
	output wire wr_almost_full;
	output wire rd_empty;
	output wire rd_almost_empty;
	wire [AW:0] r_wr_ptr_bin;
	reg [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	wire [AW:0] w_count;
	wire [AW:0] w_available_data;
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
	function automatic [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] sv2v_cast_2BB65;
		input reg [((AW + 0) >= 0 ? AW + 1 : 1 - (AW + 0)) - 1:0] inp;
		sv2v_cast_2BB65 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn)
			r_rd_ptr_bin <= 1'sb0;
		else if (w_read && !r_rd_empty)
			r_rd_ptr_bin <= r_rd_ptr_bin + sv2v_cast_2BB65(rd_size);
	assign w_rd_ptr_bin_next = r_rd_ptr_bin + (w_read && !r_rd_empty ? sv2v_cast_2BB65(rd_size) : {(AW >= 0 ? AW + 1 : 1 - AW) {1'sb0}});
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
		.count(w_count),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty)
	);
	assign wr_ready = !r_wr_full;
	assign rd_ready = !r_rd_empty;
	assign data_available = w_count;
	assign wr_full = r_wr_full;
	assign wr_almost_full = r_wr_almost_full;
	assign rd_empty = r_rd_empty;
	assign rd_almost_empty = r_rd_almost_empty;
	always @(posedge axi_aclk)
		if (((axi_aresetn && rd_valid) && !r_rd_empty) && (sv2v_cast_2BB65(rd_size) > data_available))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dma-ip/stream/rtl/fub/stream_drain_ctrl.sv:177:13 - stream_drain_ctrl.<unnamed_block>.<unnamed_block>\n msg: ", $time, "stream_drain_ctrl: over-drain -- rd_size=%0d exceeds data_available=%0d; rd_ptr will overshoot wr_ptr and permanently corrupt the occupancy count", rd_size, data_available);
endmodule
module stream_latency_bridge (
	clk,
	rst_n,
	s_valid,
	s_ready,
	s_data,
	m_valid,
	m_ready,
	m_data,
	occupancy,
	dbg_r_pending,
	dbg_r_out_valid
);
	parameter signed [31:0] DATA_WIDTH = 64;
	parameter signed [31:0] SKID_DEPTH = 4;
	parameter signed [31:0] DW = DATA_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire s_valid;
	output wire s_ready;
	input wire [DW - 1:0] s_data;
	output wire m_valid;
	input wire m_ready;
	output wire [DW - 1:0] m_data;
	output wire [2:0] occupancy;
	output wire dbg_r_pending;
	output wire dbg_r_out_valid;
	reg r_drain_ip;
	wire skid_wr_valid;
	wire skid_wr_ready;
	wire [DW - 1:0] skid_wr_data;
	wire [$clog2(SKID_DEPTH):0] skid_count;
	wire w_draining_now = m_valid && m_ready;
	wire w_write_stalled = skid_wr_valid && !skid_wr_ready;
	wire [2:0] pending_count = skid_count + {2'b00, w_write_stalled};
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	wire w_room_available = pending_count < sv2v_cast_3_signed(SKID_DEPTH);
	assign s_ready = w_room_available || w_draining_now;
	wire w_drain_fifo = s_valid && s_ready;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_drain_ip <= 1'b0;
		else
			r_drain_ip <= w_drain_fifo;
	assign skid_wr_valid = r_drain_ip;
	assign skid_wr_data = s_data;
	gaxi_fifo_sync #(
		.MEM_STYLE(32'sd0),
		.REGISTERED(0),
		.DATA_WIDTH(DW),
		.DEPTH(SKID_DEPTH)
	) u_skid_buffer(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(skid_wr_valid),
		.wr_ready(skid_wr_ready),
		.wr_data(skid_wr_data),
		.rd_valid(m_valid),
		.rd_ready(m_ready),
		.rd_data(m_data),
		.count(skid_count)
	);
	assign occupancy = skid_count;
	assign dbg_r_pending = r_drain_ip;
	assign dbg_r_out_valid = m_valid;
endmodule
module sram_controller_unit (
	clk,
	rst_n,
	axi_rd_alloc_req,
	axi_rd_alloc_size,
	axi_rd_alloc_space_free,
	axi_rd_sram_valid,
	axi_rd_sram_ready,
	axi_rd_sram_data,
	axi_wr_drain_data_avail,
	axi_wr_drain_req,
	axi_wr_drain_size,
	axi_wr_sram_valid,
	axi_wr_sram_ready,
	axi_wr_sram_data,
	dbg_bridge_pending,
	dbg_bridge_out_valid
);
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] SRAM_DEPTH = 512;
	parameter signed [31:0] SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SD = SRAM_DEPTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire axi_rd_alloc_req;
	input wire [7:0] axi_rd_alloc_size;
	output reg [SCW - 1:0] axi_rd_alloc_space_free;
	input wire axi_rd_sram_valid;
	output wire axi_rd_sram_ready;
	input wire [DW - 1:0] axi_rd_sram_data;
	output wire [SCW - 1:0] axi_wr_drain_data_avail;
	input wire axi_wr_drain_req;
	input wire [7:0] axi_wr_drain_size;
	output wire axi_wr_sram_valid;
	input wire axi_wr_sram_ready;
	output wire [DW - 1:0] axi_wr_sram_data;
	output wire dbg_bridge_pending;
	output wire dbg_bridge_out_valid;
	localparam signed [31:0] ADDR_WIDTH = $clog2(SD);
	wire [ADDR_WIDTH:0] alloc_space_free;
	wire [ADDR_WIDTH:0] drain_data_available;
	wire fifo_rd_valid_internal;
	wire fifo_rd_ready_internal;
	wire [DW - 1:0] fifo_rd_data_internal;
	wire [ADDR_WIDTH:0] fifo_count;
	wire fifo_empty;
	wire fifo_full;
	wire [2:0] bridge_occupancy;
	stream_alloc_ctrl #(
		.DEPTH(SD),
		.REGISTERED(1)
	) u_alloc_ctrl(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(axi_rd_alloc_req),
		.wr_size(axi_rd_alloc_size),
		.wr_ready(),
		.rd_valid(axi_wr_sram_valid && axi_wr_sram_ready),
		.rd_ready(),
		.space_free(alloc_space_free),
		.wr_full(),
		.wr_almost_full(),
		.rd_empty(),
		.rd_almost_empty()
	);
	wire [ADDR_WIDTH + 1:0] w_drain_data_available_acct;
	assign drain_data_available = w_drain_data_available_acct[ADDR_WIDTH:0];
	stream_drain_ctrl #(
		.DEPTH(2 * SD),
		.REGISTERED(1)
	) u_drain_ctrl(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(axi_rd_sram_valid && axi_rd_sram_ready),
		.wr_ready(),
		.rd_valid(axi_wr_drain_req),
		.rd_size(axi_wr_drain_size),
		.rd_ready(),
		.data_available(w_drain_data_available_acct),
		.wr_full(),
		.wr_almost_full(),
		.rd_empty(),
		.rd_almost_empty()
	);
	gaxi_fifo_sync #(
		.MEM_STYLE(32'sd2),
		.REGISTERED(1),
		.DATA_WIDTH(DW),
		.DEPTH(SD)
	) u_channel_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(axi_rd_sram_valid),
		.wr_ready(axi_rd_sram_ready),
		.wr_data(axi_rd_sram_data),
		.rd_valid(fifo_rd_valid_internal),
		.rd_ready(fifo_rd_ready_internal),
		.rd_data(fifo_rd_data_internal),
		.count(fifo_count)
	);
	stream_latency_bridge #(.DATA_WIDTH(DW)) u_latency_bridge(
		.clk(clk),
		.rst_n(rst_n),
		.s_data(fifo_rd_data_internal),
		.s_valid(fifo_rd_valid_internal),
		.s_ready(fifo_rd_ready_internal),
		.m_data(axi_wr_sram_data),
		.m_valid(axi_wr_sram_valid),
		.m_ready(axi_wr_sram_ready),
		.occupancy(bridge_occupancy),
		.dbg_r_pending(dbg_bridge_pending),
		.dbg_r_out_valid(dbg_bridge_out_valid)
	);
	assign axi_wr_drain_data_avail = drain_data_available;
	function automatic signed [SCW - 1:0] sv2v_cast_14961_signed;
		input reg signed [SCW - 1:0] inp;
		sv2v_cast_14961_signed = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			axi_rd_alloc_space_free <= sv2v_cast_14961_signed(SD);
		else
			axi_rd_alloc_space_free <= alloc_space_free;
endmodule
module sram_controller (
	clk,
	rst_n,
	axi_rd_alloc_req,
	axi_rd_alloc_size,
	axi_rd_alloc_id,
	axi_rd_alloc_space_free,
	axi_rd_sram_valid,
	axi_rd_sram_ready,
	axi_rd_sram_id,
	axi_rd_sram_data,
	axi_wr_drain_data_avail,
	axi_wr_drain_req,
	axi_wr_drain_size,
	axi_wr_sram_valid,
	axi_wr_sram_valid_comb,
	axi_wr_sram_drain,
	axi_wr_sram_id,
	axi_wr_sram_data,
	dbg_bridge_pending,
	dbg_bridge_out_valid
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] SRAM_DEPTH = 512;
	parameter signed [31:0] SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SD = SRAM_DEPTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	parameter signed [31:0] CIW = (NC > 1 ? $clog2(NC) : 1);
	input wire clk;
	input wire rst_n;
	input wire axi_rd_alloc_req;
	input wire [7:0] axi_rd_alloc_size;
	input wire [CIW - 1:0] axi_rd_alloc_id;
	output reg [(NC * SCW) - 1:0] axi_rd_alloc_space_free;
	input wire axi_rd_sram_valid;
	output reg axi_rd_sram_ready;
	input wire [CIW - 1:0] axi_rd_sram_id;
	input wire [DW - 1:0] axi_rd_sram_data;
	output reg [(NC * SCW) - 1:0] axi_wr_drain_data_avail;
	input wire [NC - 1:0] axi_wr_drain_req;
	input wire [(NC * 8) - 1:0] axi_wr_drain_size;
	output reg [NC - 1:0] axi_wr_sram_valid;
	output wire [NC - 1:0] axi_wr_sram_valid_comb;
	input wire axi_wr_sram_drain;
	input wire [CIW - 1:0] axi_wr_sram_id;
	output reg [DW - 1:0] axi_wr_sram_data;
	output wire [NC - 1:0] dbg_bridge_pending;
	output wire [NC - 1:0] dbg_bridge_out_valid;
	reg [NC - 1:0] axi_rd_sram_valid_decoded;
	wire [NC - 1:0] axi_rd_sram_ready_per_channel;
	reg [NC - 1:0] axi_wr_sram_drain_decoded;
	wire [(NC * DW) - 1:0] axi_wr_sram_data_per_channel;
	reg [NC - 1:0] axi_rd_alloc_req_decoded;
	wire [(NC * SCW) - 1:0] axi_rd_alloc_space_free_comb;
	wire [(NC * SCW) - 1:0] axi_wr_drain_data_avail_comb;
	always @(*) begin
		if (_sv2v_0)
			;
		axi_rd_sram_valid_decoded = 1'sb0;
		if (axi_rd_sram_valid && (axi_rd_sram_id < NC))
			axi_rd_sram_valid_decoded[axi_rd_sram_id] = 1'b1;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if (axi_rd_sram_id < NC)
			axi_rd_sram_ready = axi_rd_sram_ready_per_channel[axi_rd_sram_id];
		else
			axi_rd_sram_ready = 1'b0;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		axi_wr_sram_drain_decoded = 1'sb0;
		if (axi_wr_sram_drain && (axi_wr_sram_id < NC))
			axi_wr_sram_drain_decoded[axi_wr_sram_id] = 1'b1;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if (axi_wr_sram_id < NC)
			axi_wr_sram_data = axi_wr_sram_data_per_channel[axi_wr_sram_id * DW+:DW];
		else
			axi_wr_sram_data = 1'sb0;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		axi_rd_alloc_req_decoded = 1'sb0;
		if (axi_rd_alloc_req && (axi_rd_alloc_id < NC))
			axi_rd_alloc_req_decoded[axi_rd_alloc_id] = 1'b1;
	end
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < NC; _gv_i_2 = _gv_i_2 + 1) begin : gen_channel_units
			localparam i = _gv_i_2;
			sram_controller_unit #(
				.DATA_WIDTH(DW),
				.SRAM_DEPTH(SRAM_DEPTH),
				.SEG_COUNT_WIDTH(SEG_COUNT_WIDTH)
			) u_channel_unit(
				.clk(clk),
				.rst_n(rst_n),
				.axi_rd_sram_valid(axi_rd_sram_valid_decoded[i]),
				.axi_rd_sram_ready(axi_rd_sram_ready_per_channel[i]),
				.axi_rd_sram_data(axi_rd_sram_data),
				.axi_wr_sram_valid(axi_wr_sram_valid_comb[i]),
				.axi_wr_sram_ready(axi_wr_sram_drain_decoded[i]),
				.axi_wr_sram_data(axi_wr_sram_data_per_channel[i * DW+:DW]),
				.axi_rd_alloc_req(axi_rd_alloc_req_decoded[i]),
				.axi_rd_alloc_size(axi_rd_alloc_size),
				.axi_rd_alloc_space_free(axi_rd_alloc_space_free_comb[i * SCW+:SCW]),
				.axi_wr_drain_req(axi_wr_drain_req[i]),
				.axi_wr_drain_size(axi_wr_drain_size[i * 8+:8]),
				.axi_wr_drain_data_avail(axi_wr_drain_data_avail_comb[i * SCW+:SCW]),
				.dbg_bridge_pending(dbg_bridge_pending[i]),
				.dbg_bridge_out_valid(dbg_bridge_out_valid[i])
			);
		end
	endgenerate
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			axi_rd_alloc_space_free <= 1'sb0;
			axi_wr_drain_data_avail <= 1'sb0;
			axi_wr_sram_valid <= 1'sb0;
		end
		else begin
			axi_rd_alloc_space_free <= axi_rd_alloc_space_free_comb;
			axi_wr_drain_data_avail <= axi_wr_drain_data_avail_comb;
			axi_wr_sram_valid <= axi_wr_sram_valid_comb;
		end
	initial _sv2v_0 = 0;
endmodule
module src_sram_controller (
	clk,
	rst_n,
	cfg_channel_reset,
	fill_alloc_req,
	fill_alloc_size,
	fill_alloc_id,
	fill_space_free,
	fill_valid,
	fill_ready,
	fill_id,
	fill_data,
	drain_data_avail,
	drain_req,
	drain_size,
	drain_valid,
	drain_valid_comb,
	drain_read,
	drain_id,
	drain_data,
	dbg_bridge_pending,
	dbg_bridge_out_valid
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] SRAM_DEPTH = 512;
	parameter signed [31:0] SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SD = SRAM_DEPTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	parameter signed [31:0] CIW = (NC > 1 ? $clog2(NC) : 1);
	input wire clk;
	input wire rst_n;
	input wire [NC - 1:0] cfg_channel_reset;
	input wire fill_alloc_req;
	input wire [7:0] fill_alloc_size;
	input wire [CIW - 1:0] fill_alloc_id;
	output wire [(NC * SCW) - 1:0] fill_space_free;
	input wire fill_valid;
	output reg fill_ready;
	input wire [CIW - 1:0] fill_id;
	input wire [DW - 1:0] fill_data;
	output wire [(NC * SCW) - 1:0] drain_data_avail;
	input wire [NC - 1:0] drain_req;
	input wire [(NC * 8) - 1:0] drain_size;
	output wire [NC - 1:0] drain_valid;
	output wire [NC - 1:0] drain_valid_comb;
	input wire drain_read;
	input wire [CIW - 1:0] drain_id;
	output reg [DW - 1:0] drain_data;
	output wire [NC - 1:0] dbg_bridge_pending;
	output wire [NC - 1:0] dbg_bridge_out_valid;
	initial if (NC > 128) begin
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dma-ip/rapids/rtl/macro/src_sram_controller.sv:121:13 - src_sram_controller.<unnamed_block>.<unnamed_block>\n msg: ", $time, "src_sram_controller: NUM_CHANNELS=%0d exceeds maximum of 128", NC);
		$finish(1);
	end
	reg [NC - 1:0] r_ch_rst_n;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_ch_rst_n <= 1'sb0;
		else
			r_ch_rst_n <= ~cfg_channel_reset;
	wire [NC - 1:0] w_fill_ready_ch;
	wire [(NC * DW) - 1:0] w_drain_data_ch;
	function automatic signed [CIW - 1:0] sv2v_cast_0111B_signed;
		input reg signed [CIW - 1:0] inp;
		sv2v_cast_0111B_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		fill_ready = 1'b0;
		drain_data = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					if (fill_id == sv2v_cast_0111B_signed(i))
						fill_ready = w_fill_ready_ch[i];
					if (drain_id == sv2v_cast_0111B_signed(i))
						drain_data = w_drain_data_ch[i * DW+:DW];
				end
		end
	end
	genvar _gv_i_3;
	generate
		for (_gv_i_3 = 0; _gv_i_3 < NC; _gv_i_3 = _gv_i_3 + 1) begin : gen_channel
			localparam i = _gv_i_3;
			sram_controller #(
				.NUM_CHANNELS(1),
				.DATA_WIDTH(DW),
				.SRAM_DEPTH(SD),
				.SEG_COUNT_WIDTH(SCW)
			) u_sram_controller(
				.clk(clk),
				.rst_n(r_ch_rst_n[i]),
				.axi_rd_alloc_req(fill_alloc_req && (fill_alloc_id == sv2v_cast_0111B_signed(i))),
				.axi_rd_alloc_size(fill_alloc_size),
				.axi_rd_alloc_id(1'b0),
				.axi_rd_alloc_space_free(fill_space_free[i * SCW+:SCW]),
				.axi_rd_sram_valid(fill_valid && (fill_id == sv2v_cast_0111B_signed(i))),
				.axi_rd_sram_ready(w_fill_ready_ch[i]),
				.axi_rd_sram_id(1'b0),
				.axi_rd_sram_data(fill_data),
				.axi_wr_drain_data_avail(drain_data_avail[i * SCW+:SCW]),
				.axi_wr_drain_req(drain_req[i]),
				.axi_wr_drain_size(drain_size[i * 8+:8]),
				.axi_wr_sram_valid(drain_valid[i]),
				.axi_wr_sram_valid_comb(drain_valid_comb[i]),
				.axi_wr_sram_drain(drain_read && (drain_id == sv2v_cast_0111B_signed(i))),
				.axi_wr_sram_id(1'b0),
				.axi_wr_sram_data(w_drain_data_ch[i * DW+:DW]),
				.dbg_bridge_pending(dbg_bridge_pending[i]),
				.dbg_bridge_out_valid(dbg_bridge_out_valid[i])
			);
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module src_data_path (
	clk,
	rst_n,
	cfg_axi_rd_xfer_beats,
	cfg_channel_reset,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	sched_rd_error,
	drain_data_avail,
	drain_req,
	drain_size,
	drain_valid,
	drain_valid_comb,
	drain_read,
	drain_id,
	drain_data,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	m_axi_rvalid,
	m_axi_rready,
	dbg_rd_all_complete,
	dbg_r_beats_rcvd,
	dbg_sram_writes,
	dbg_arb_request,
	dbg_sram_bridge_pending,
	dbg_sram_bridge_out_valid
);
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] SRAM_DEPTH = 512;
	parameter signed [31:0] SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1;
	parameter signed [31:0] PIPELINE = 1;
	parameter signed [31:0] AR_MAX_OUTSTANDING = 8;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SD = SRAM_DEPTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	parameter signed [31:0] CIW = (NC > 1 ? $clog2(NC) : 1);
	input wire clk;
	input wire rst_n;
	input wire [7:0] cfg_axi_rd_xfer_beats;
	input wire [NC - 1:0] cfg_channel_reset;
	input wire [NC - 1:0] sched_rd_valid;
	input wire [(NC * AW) - 1:0] sched_rd_addr;
	input wire [(NC * 32) - 1:0] sched_rd_beats;
	output wire [NC - 1:0] sched_rd_done_strobe;
	output wire [(NC * 32) - 1:0] sched_rd_beats_done;
	output wire [NC - 1:0] sched_rd_error;
	output wire [(NC * SCW) - 1:0] drain_data_avail;
	input wire [NC - 1:0] drain_req;
	input wire [(NC * 8) - 1:0] drain_size;
	output wire [NC - 1:0] drain_valid;
	output wire [NC - 1:0] drain_valid_comb;
	input wire drain_read;
	input wire [CIW - 1:0] drain_id;
	output wire [DW - 1:0] drain_data;
	output wire [IW - 1:0] m_axi_arid;
	output wire [AW - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	input wire [IW - 1:0] m_axi_rid;
	input wire [DW - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	output wire [NC - 1:0] dbg_rd_all_complete;
	output wire [31:0] dbg_r_beats_rcvd;
	output wire [31:0] dbg_sram_writes;
	output wire [NC - 1:0] dbg_arb_request;
	output wire [NC - 1:0] dbg_sram_bridge_pending;
	output wire [NC - 1:0] dbg_sram_bridge_out_valid;
	wire alloc_req;
	wire [7:0] alloc_size;
	wire [IW - 1:0] alloc_id;
	wire [(NC * SCW) - 1:0] alloc_space_free;
	wire sram_valid;
	wire sram_ready;
	wire [IW - 1:0] sram_id;
	wire [DW - 1:0] sram_data;
	axi_read_engine #(
		.NUM_CHANNELS(NC),
		.ADDR_WIDTH(AW),
		.DATA_WIDTH(DW),
		.ID_WIDTH(IW),
		.SEG_COUNT_WIDTH(SCW),
		.PIPELINE(PIPELINE),
		.AR_MAX_OUTSTANDING(AR_MAX_OUTSTANDING),
		.STROBE_EVERY_BEAT(0)
	) u_axi_read_engine(
		.clk(clk),
		.rst_n(rst_n),
		.cfg_axi_rd_xfer_beats(cfg_axi_rd_xfer_beats),
		.cfg_channel_reset(cfg_channel_reset),
		.sched_rd_valid(sched_rd_valid),
		.sched_rd_addr(sched_rd_addr),
		.sched_rd_beats(sched_rd_beats),
		.sched_rd_done_strobe(sched_rd_done_strobe),
		.sched_rd_beats_done(sched_rd_beats_done),
		.axi_rd_alloc_req(alloc_req),
		.axi_rd_alloc_size(alloc_size),
		.axi_rd_alloc_id(alloc_id),
		.axi_rd_alloc_space_free(alloc_space_free),
		.axi_rd_sram_valid(sram_valid),
		.axi_rd_sram_ready(sram_ready),
		.axi_rd_sram_id(sram_id),
		.axi_rd_sram_data(sram_data),
		.m_axi_arvalid(m_axi_arvalid),
		.m_axi_arready(m_axi_arready),
		.m_axi_arid(m_axi_arid),
		.m_axi_araddr(m_axi_araddr),
		.m_axi_arlen(m_axi_arlen),
		.m_axi_arsize(m_axi_arsize),
		.m_axi_arburst(m_axi_arburst),
		.m_axi_rvalid(m_axi_rvalid),
		.m_axi_rready(m_axi_rready),
		.m_axi_rid(m_axi_rid),
		.m_axi_rdata(m_axi_rdata),
		.m_axi_rresp(m_axi_rresp),
		.m_axi_rlast(m_axi_rlast),
		.sched_rd_error(sched_rd_error),
		.dbg_rd_all_complete(dbg_rd_all_complete),
		.dbg_r_beats_rcvd(dbg_r_beats_rcvd),
		.dbg_sram_writes(dbg_sram_writes),
		.dbg_arb_request(dbg_arb_request)
	);
	src_sram_controller #(
		.NUM_CHANNELS(NC),
		.DATA_WIDTH(DW),
		.SRAM_DEPTH(SD),
		.SEG_COUNT_WIDTH(SCW)
	) u_src_sram_controller(
		.clk(clk),
		.rst_n(rst_n),
		.cfg_channel_reset(cfg_channel_reset),
		.fill_alloc_req(alloc_req),
		.fill_alloc_size(alloc_size),
		.fill_alloc_id(alloc_id[CIW - 1:0]),
		.fill_space_free(alloc_space_free),
		.fill_valid(sram_valid),
		.fill_ready(sram_ready),
		.fill_id(sram_id[CIW - 1:0]),
		.fill_data(sram_data),
		.drain_data_avail(drain_data_avail),
		.drain_req(drain_req),
		.drain_size(drain_size),
		.drain_valid(drain_valid),
		.drain_valid_comb(drain_valid_comb),
		.drain_read(drain_read),
		.drain_id(drain_id),
		.drain_data(drain_data),
		.dbg_bridge_pending(dbg_sram_bridge_pending),
		.dbg_bridge_out_valid(dbg_sram_bridge_out_valid)
	);
endmodule
module axi_read_engine (
	clk,
	rst_n,
	cfg_axi_rd_xfer_beats,
	cfg_channel_reset,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	axi_rd_alloc_req,
	axi_rd_alloc_size,
	axi_rd_alloc_id,
	axi_rd_alloc_space_free,
	axi_rd_sram_valid,
	axi_rd_sram_ready,
	axi_rd_sram_id,
	axi_rd_sram_data,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_rvalid,
	m_axi_rready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	sched_rd_error,
	dbg_rd_all_complete,
	dbg_r_beats_rcvd,
	dbg_sram_writes,
	dbg_arb_request
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] SEG_COUNT_WIDTH = 8;
	parameter signed [31:0] PIPELINE = 1;
	parameter signed [31:0] AR_MAX_OUTSTANDING = 8;
	parameter signed [31:0] STROBE_EVERY_BEAT = 0;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	parameter signed [31:0] CIW = (NC > 1 ? $clog2(NC) : 1);
	input wire clk;
	input wire rst_n;
	input wire [7:0] cfg_axi_rd_xfer_beats;
	input wire [NC - 1:0] cfg_channel_reset;
	input wire [NC - 1:0] sched_rd_valid;
	input wire [(NC * AW) - 1:0] sched_rd_addr;
	input wire [(NC * 32) - 1:0] sched_rd_beats;
	output wire [NC - 1:0] sched_rd_done_strobe;
	output wire [(NC * 32) - 1:0] sched_rd_beats_done;
	output wire axi_rd_alloc_req;
	output wire [7:0] axi_rd_alloc_size;
	output wire [IW - 1:0] axi_rd_alloc_id;
	input wire [(NC * SCW) - 1:0] axi_rd_alloc_space_free;
	output wire axi_rd_sram_valid;
	input wire axi_rd_sram_ready;
	output wire [IW - 1:0] axi_rd_sram_id;
	output wire [DW - 1:0] axi_rd_sram_data;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	output wire [IW - 1:0] m_axi_arid;
	output wire [AW - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	input wire [IW - 1:0] m_axi_rid;
	input wire [DW - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	output wire [NC - 1:0] sched_rd_error;
	output wire [NC - 1:0] dbg_rd_all_complete;
	output wire [31:0] dbg_r_beats_rcvd;
	output wire [31:0] dbg_sram_writes;
	output wire [NC - 1:0] dbg_arb_request;
	localparam signed [31:0] CW = (NC > 1 ? $clog2(NC) : 1);
	localparam signed [31:0] BYTES_PER_BEAT = DW / 8;
	localparam signed [31:0] AXSIZE = $clog2(BYTES_PER_BEAT);
	localparam signed [31:0] MOW = $clog2(AR_MAX_OUTSTANDING + 1);
	localparam signed [31:0] SD_BEATS = 1 << (SCW - 1);
	localparam signed [31:0] XFER_MAX = (SD_BEATS < 256 ? SD_BEATS - 1 : 254);
	wire [7:0] w_xfer_cfg;
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	assign w_xfer_cfg = (cfg_axi_rd_xfer_beats > sv2v_cast_8_signed(XFER_MAX) ? sv2v_cast_8_signed(XFER_MAX) : cfg_axi_rd_xfer_beats);
	reg [NC - 1:0] r_outstanding_limit;
	reg [(NC * MOW) - 1:0] r_outstanding_count;
	wire w_arb_grant_valid;
	wire [NC - 1:0] w_arb_grant;
	wire [CW - 1:0] w_arb_grant_id;
	wire [NC - 1:0] w_arb_grant_ack;
	function automatic signed [MOW - 1:0] sv2v_cast_04DDF_signed;
		input reg signed [MOW - 1:0] inp;
		sv2v_cast_04DDF_signed = inp;
	endfunction
	generate
		if (PIPELINE == 0) begin : gen_no_pipeline_tracking
			always @(posedge clk or negedge rst_n)
				if (!rst_n)
					r_outstanding_limit <= 1'sb0;
				else begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < NC; i = i + 1)
						begin
							if ((m_axi_arvalid && m_axi_arready) && (w_arb_grant_id == i[CW - 1:0]))
								r_outstanding_limit[i] <= 1'b1;
							if (((m_axi_rvalid && m_axi_rready) && m_axi_rlast) && (m_axi_rid[CW - 1:0] == i[CW - 1:0]))
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
							w_incr[i] = (m_axi_arvalid && m_axi_arready) && (w_arb_grant_id == i[CW - 1:0]);
							w_decr[i] = ((m_axi_rvalid && m_axi_rready) && m_axi_rlast) && (m_axi_rid[CW - 1:0] == i[CW - 1:0]);
						end
				end
			end
			always @(posedge clk or negedge rst_n)
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
						r_outstanding_limit[i] = r_outstanding_count[i * MOW+:MOW] >= sv2v_cast_04DDF_signed(AR_MAX_OUTSTANDING);
				end
			end
		end
	endgenerate
	reg [NC - 1:0] r_rd_flush;
	reg [NC - 1:0] w_rd_outstanding;
	wire w_rd_discard;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				w_rd_outstanding[i] = (PIPELINE == 0 ? r_outstanding_limit[i] : r_outstanding_count[i * MOW+:MOW] != {MOW * 1 {1'sb0}});
		end
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_rd_flush <= 1'sb0;
		else
			r_rd_flush <= cfg_channel_reset | (r_rd_flush & w_rd_outstanding);
	assign w_rd_discard = r_rd_flush[m_axi_rid[CW - 1:0]] | cfg_channel_reset[m_axi_rid[CW - 1:0]];
	reg [NC - 1:0] r_all_complete;
	reg [NC - 1:0] r_all_complete_prev;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_all_complete <= 1'sb1;
			r_all_complete_prev <= 1'sb1;
		end
		else begin
			r_all_complete_prev <= r_all_complete;
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < NC; i = i + 1)
					if (r_outstanding_count[i * MOW+:MOW] == {MOW * 1 {1'sb0}})
						r_all_complete[i] <= 1'b1;
					else if (r_all_complete_prev[i] && (r_outstanding_count[i * MOW+:MOW] != {MOW * 1 {1'sb0}}))
						r_all_complete[i] <= 1'b0;
			end
		end
	assign dbg_rd_all_complete = r_all_complete;
	reg [NC - 1:0] w_space_ok;
	reg [NC - 1:0] w_below_outstanding_limit;
	reg [NC - 1:0] w_arb_request;
	reg [(NC * 8) - 1:0] w_transfer_size;
	reg [(NC * 16) - 1:0] w_beats_to_4k;
	reg [(NC * 16) - 1:0] w_cap_beats;
	reg [(NC * SCW) - 1:0] w_alloc_t;
	reg [(NC * SCW) - 1:0] r_alloc_tminus1;
	reg [(NC * SCW) - 1:0] r_alloc_tminus2;
	reg [(NC * SCW) - 1:0] w_pending_alloc;
	reg [(NC * SCW) - 1:0] w_effective_space;
	function automatic [SCW - 1:0] sv2v_cast_14961;
		input reg [SCW - 1:0] inp;
		sv2v_cast_14961 = inp;
	endfunction
	function automatic signed [SCW - 1:0] sv2v_cast_14961_signed;
		input reg signed [SCW - 1:0] inp;
		sv2v_cast_14961_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_alloc_t = {NC {sv2v_cast_14961(0)}};
		if (m_axi_arvalid && m_axi_arready)
			w_alloc_t[w_arb_grant_id * SCW+:SCW] = sv2v_cast_14961(m_axi_arlen) + sv2v_cast_14961_signed(1);
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_alloc_tminus1 <= {NC {sv2v_cast_14961(0)}};
			r_alloc_tminus2 <= {NC {sv2v_cast_14961(0)}};
		end
		else begin
			r_alloc_tminus1 <= w_alloc_t;
			r_alloc_tminus2 <= r_alloc_tminus1;
			begin : sv2v_autoblock_7
				reg signed [31:0] i;
				for (i = 0; i < NC; i = i + 1)
					if (cfg_channel_reset[i]) begin
						r_alloc_tminus1[i * SCW+:SCW] <= 1'sb0;
						r_alloc_tminus2[i * SCW+:SCW] <= 1'sb0;
					end
			end
		end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					w_pending_alloc[i * SCW+:SCW] = r_alloc_tminus1[i * SCW+:SCW] + r_alloc_tminus2[i * SCW+:SCW];
					w_effective_space[i * SCW+:SCW] = (sv2v_cast_14961(axi_rd_alloc_space_free[i * SCW+:SCW]) >= w_pending_alloc[i * SCW+:SCW] ? sv2v_cast_14961(axi_rd_alloc_space_free[i * SCW+:SCW]) - w_pending_alloc[i * SCW+:SCW] : {SCW * 1 {1'sb0}});
				end
		end
	end
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_9
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					w_beats_to_4k[i * 16+:16] = sv2v_cast_16((16'd4096 - sv2v_cast_16({4'd0, sched_rd_addr[(i * AW) + (11 >= AXSIZE ? 11 : (11 + (11 >= AXSIZE ? 12 - AXSIZE : AXSIZE - 10)) - 1)-:(11 >= AXSIZE ? 12 - AXSIZE : AXSIZE - 10)], {AXSIZE {1'b0}}})) >> AXSIZE);
					w_cap_beats[i * 16+:16] = ((sv2v_cast_16(w_xfer_cfg) + 16'd1) < w_beats_to_4k[i * 16+:16] ? sv2v_cast_16(w_xfer_cfg) + 16'd1 : w_beats_to_4k[i * 16+:16]);
					w_transfer_size[i * 8+:8] = sv2v_cast_8((sched_rd_beats[i * 32+:32] <= sv2v_cast_32(w_cap_beats[i * 16+:16]) ? sched_rd_beats[i * 32+:32] - 32'd1 : sv2v_cast_32(w_cap_beats[i * 16+:16]) - 32'd1));
					w_space_ok[i] = w_effective_space[i * SCW+:SCW] >= sv2v_cast_14961(w_transfer_size[i * 8+:8] + 8'd1);
					w_below_outstanding_limit[i] = !r_outstanding_limit[i];
					w_arb_request[i] = (((sched_rd_valid[i] && w_space_ok[i]) && w_below_outstanding_limit[i]) && !cfg_channel_reset[i]) && !r_rd_flush[i];
				end
		end
	end
	reg [NC - 1:0] r_arb_request;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_arb_request <= 1'sb0;
		else
			r_arb_request <= w_arb_request;
	generate
		if (NC == 1) begin : gen_single_channel
			arbiter_single_client #(.WAIT_GNT_ACK(1)) u_arbiter_single(
				.clk(clk),
				.rst_n(rst_n),
				.block_arb(1'b0),
				.request(r_arb_request[0]),
				.grant_ack(w_arb_grant_ack[0]),
				.grant_valid(w_arb_grant_valid),
				.grant(w_arb_grant[0]),
				.grant_id(w_arb_grant_id[0])
			);
		end
		else begin : gen_multi_channel
			arbiter_round_robin #(
				.CLIENTS(NC),
				.WAIT_GNT_ACK(1)
			) u_arbiter(
				.clk(clk),
				.rst_n(rst_n),
				.block_arb(1'b0),
				.request(r_arb_request),
				.grant_ack(w_arb_grant_ack),
				.grant_valid(w_arb_grant_valid),
				.grant(w_arb_grant),
				.grant_id(w_arb_grant_id),
				.last_grant()
			);
		end
	endgenerate
	assign m_axi_arvalid = w_arb_grant_valid && w_arb_request[w_arb_grant_id];
	assign m_axi_arid = {{IW - CW {1'b0}}, w_arb_grant_id};
	assign m_axi_araddr = {sched_rd_addr[(w_arb_grant_id * AW) + ((AW - 1) >= AXSIZE ? AW - 1 : ((AW - 1) + ((AW - 1) >= AXSIZE ? ((AW - 1) - AXSIZE) + 1 : (AXSIZE - (AW - 1)) + 1)) - 1)-:((AW - 1) >= AXSIZE ? ((AW - 1) - AXSIZE) + 1 : (AXSIZE - (AW - 1)) + 1)], {AXSIZE {1'b0}}};
	assign m_axi_arlen = w_transfer_size[w_arb_grant_id * 8+:8];
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign m_axi_arsize = sv2v_cast_3_signed(AXSIZE);
	assign m_axi_arburst = 2'b01;
	wire [NC - 1:0] w_stale_grant;
	assign w_stale_grant = w_arb_grant & ~w_arb_request;
	assign w_arb_grant_ack = (w_arb_grant & {NC {m_axi_arvalid && m_axi_arready}}) | w_stale_grant;
	reg r_alloc_req;
	reg [7:0] r_alloc_size;
	reg [IW - 1:0] r_alloc_id;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_alloc_req <= 1'b0;
			r_alloc_size <= 1'sb0;
			r_alloc_id <= 1'sb0;
		end
		else begin
			r_alloc_req <= 1'b0;
			if (m_axi_arvalid && m_axi_arready) begin
				r_alloc_req <= 1'b1;
				r_alloc_size <= w_transfer_size[w_arb_grant_id * 8+:8] + 8'd1;
				r_alloc_id <= {{IW - CW {1'b0}}, w_arb_grant_id};
			end
		end
	assign axi_rd_alloc_req = r_alloc_req;
	assign axi_rd_alloc_size = r_alloc_size;
	assign axi_rd_alloc_id = r_alloc_id;
	assign axi_rd_sram_valid = m_axi_rvalid && !w_rd_discard;
	assign axi_rd_sram_id = m_axi_rid;
	assign axi_rd_sram_data = m_axi_rdata;
	assign m_axi_rready = (w_rd_discard ? 1'b1 : axi_rd_sram_ready);
	reg [NC - 1:0] r_done_strobe;
	reg [(NC * 32) - 1:0] r_beats_done;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_done_strobe <= {NC {1'd0}};
			r_beats_done <= {NC {32'd0}};
		end
		else begin
			r_done_strobe <= {NC {1'd0}};
			if (m_axi_arvalid && m_axi_arready) begin
				r_done_strobe[w_arb_grant_id] <= 1'b1;
				r_beats_done[w_arb_grant_id * 32+:32] <= {24'd0, w_transfer_size[w_arb_grant_id * 8+:8] + 8'd1};
			end
			begin : sv2v_autoblock_10
				reg signed [31:0] i;
				for (i = 0; i < NC; i = i + 1)
					if (cfg_channel_reset[i])
						r_done_strobe[i] <= 1'b0;
			end
		end
	assign sched_rd_done_strobe = r_done_strobe;
	assign sched_rd_beats_done = r_beats_done;
	reg [NC - 1:0] r_rd_error;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_rd_error <= 1'sb0;
		else begin
			if (((m_axi_rvalid && m_axi_rready) && !w_rd_discard) && (m_axi_rresp != 2'b00)) begin : sv2v_autoblock_11
				reg [CW - 1:0] ch_id;
				ch_id = m_axi_rid[CW - 1:0];
				r_rd_error[ch_id] <= 1'b1;
			end
			begin : sv2v_autoblock_12
				reg signed [31:0] i;
				for (i = 0; i < NC; i = i + 1)
					if (cfg_channel_reset[i])
						r_rd_error[i] <= 1'b0;
			end
		end
	assign sched_rd_error = r_rd_error;
	reg [31:0] r_r_beats_rcvd;
	reg [31:0] r_sram_writes;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_r_beats_rcvd <= 1'sb0;
			r_sram_writes <= 1'sb0;
		end
		else begin
			if (m_axi_rvalid && m_axi_rready)
				r_r_beats_rcvd <= r_r_beats_rcvd + 1'b1;
			if (axi_rd_sram_valid && axi_rd_sram_ready)
				r_sram_writes <= r_sram_writes + 1'b1;
		end
	assign dbg_r_beats_rcvd = r_r_beats_rcvd;
	assign dbg_sram_writes = r_sram_writes;
	assign dbg_arb_request = w_arb_request;
	initial _sv2v_0 = 0;
endmodule
module src_data_path_axis (
	clk,
	rst_n,
	cfg_axi_rd_xfer_beats,
	cfg_drain_size,
	cfg_channel_reset,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_rd_pkt_valid,
	sched_rd_pkt_ready,
	sched_rd_pkt_bytes,
	sched_rd_pkt_offset,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	sched_rd_error,
	m_axis_tdata,
	m_axis_tstrb,
	m_axis_tlast,
	m_axis_tid,
	m_axis_tdest,
	m_axis_tuser,
	m_axis_tvalid,
	m_axis_tready,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	m_axi_rvalid,
	m_axi_rready,
	dbg_rd_all_complete,
	dbg_r_beats_rcvd,
	dbg_sram_writes,
	dbg_arb_request,
	dbg_sram_bridge_pending,
	dbg_sram_bridge_out_valid,
	dbg_axis_beats_sent,
	dbg_axis_packets_sent
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] SRAM_DEPTH = 512;
	parameter signed [31:0] SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1;
	parameter signed [31:0] PIPELINE = 1;
	parameter signed [31:0] AR_MAX_OUTSTANDING = 8;
	parameter signed [31:0] AXIS_ID_WIDTH = 8;
	parameter signed [31:0] AXIS_DEST_WIDTH = 4;
	parameter signed [31:0] AXIS_USER_WIDTH = 1;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SD = SRAM_DEPTH;
	parameter signed [31:0] SCW = SEG_COUNT_WIDTH;
	parameter signed [31:0] CIW = (NC > 1 ? $clog2(NC) : 1);
	parameter signed [31:0] SW = DW / 8;
	parameter signed [31:0] OFF_W = (SW > 1 ? $clog2(SW) : 1);
	input wire clk;
	input wire rst_n;
	input wire [7:0] cfg_axi_rd_xfer_beats;
	input wire [7:0] cfg_drain_size;
	input wire [NC - 1:0] cfg_channel_reset;
	input wire [NC - 1:0] sched_rd_valid;
	input wire [(NC * AW) - 1:0] sched_rd_addr;
	input wire [(NC * 32) - 1:0] sched_rd_beats;
	input wire [NC - 1:0] sched_rd_pkt_valid;
	output wire [NC - 1:0] sched_rd_pkt_ready;
	input wire [(NC * 32) - 1:0] sched_rd_pkt_bytes;
	input wire [(NC * OFF_W) - 1:0] sched_rd_pkt_offset;
	output wire [NC - 1:0] sched_rd_done_strobe;
	output wire [(NC * 32) - 1:0] sched_rd_beats_done;
	output wire [NC - 1:0] sched_rd_error;
	output wire [DW - 1:0] m_axis_tdata;
	output wire [SW - 1:0] m_axis_tstrb;
	output wire m_axis_tlast;
	output wire [AXIS_ID_WIDTH - 1:0] m_axis_tid;
	output wire [AXIS_DEST_WIDTH - 1:0] m_axis_tdest;
	output wire [AXIS_USER_WIDTH - 1:0] m_axis_tuser;
	output wire m_axis_tvalid;
	input wire m_axis_tready;
	output wire [IW - 1:0] m_axi_arid;
	output wire [AW - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	input wire [IW - 1:0] m_axi_rid;
	input wire [DW - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	output wire [NC - 1:0] dbg_rd_all_complete;
	output wire [31:0] dbg_r_beats_rcvd;
	output wire [31:0] dbg_sram_writes;
	output wire [NC - 1:0] dbg_arb_request;
	output wire [NC - 1:0] dbg_sram_bridge_pending;
	output wire [NC - 1:0] dbg_sram_bridge_out_valid;
	output wire [31:0] dbg_axis_beats_sent;
	output wire [31:0] dbg_axis_packets_sent;
	wire [(NC * SCW) - 1:0] drain_data_avail;
	reg [NC - 1:0] drain_req;
	reg [(NC * 8) - 1:0] drain_size;
	wire [NC - 1:0] drain_valid;
	wire [NC - 1:0] drain_valid_comb;
	wire drain_read;
	wire [CIW - 1:0] drain_id;
	wire [DW - 1:0] drain_data;
	reg [NC - 1:0] r_arb_request;
	reg [NC - 1:0] w_ch_grantable;
	reg [NC - 1:0] w_no_more_fill;
	reg [7:0] w_grant_size [0:NC - 1];
	wire [7:0] w_eff_drain_size;
	reg [(NC * SCW) - 1:0] w_drain_t;
	reg [(NC * SCW) - 1:0] r_drain_tminus1;
	reg [(NC * SCW) - 1:0] w_pending_drain;
	reg [(NC * SCW) - 1:0] w_effective_avail;
	reg [CIW - 1:0] r_rr_last;
	reg r_res_valid;
	reg [CIW - 1:0] r_res_ch;
	reg [7:0] r_res_size;
	localparam signed [31:0] RQ_DEPTH = 4;
	localparam signed [31:0] RQ_PW = 2;
	reg [(RQ_DEPTH * CIW) - 1:0] r_rq_ch;
	reg [31:0] r_rq_size;
	reg [RQ_PW:0] r_rq_wp;
	reg [RQ_PW:0] r_rq_rp;
	wire [RQ_PW:0] w_rq_count;
	wire w_rq_empty;
	wire w_rq_room;
	reg [CIW - 1:0] r_d_ch;
	reg r_d_active;
	reg [7:0] r_d_remaining;
	wire w_beat_accepted;
	wire w_d_load;
	reg [NC - 1:0] r_rst_d1;
	wire [NC - 1:0] w_rst;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_rst_d1 <= 1'sb0;
		else
			r_rst_d1 <= cfg_channel_reset;
	assign w_rst = cfg_channel_reset | r_rst_d1;
	localparam signed [31:0] PQ_DEPTH = 4;
	localparam signed [31:0] PQ_PW = 2;
	reg [((NC * PQ_DEPTH) * OFF_W) - 1:0] r_pq_off;
	reg [((NC * PQ_DEPTH) * 32) - 1:0] r_pq_bytes;
	reg [(NC * 3) - 1:0] r_pq_wp;
	reg [(NC * 3) - 1:0] r_pq_rp;
	reg [(NC * 3) - 1:0] w_pq_count;
	reg [NC - 1:0] w_pq_empty;
	reg [NC - 1:0] w_pq_full;
	reg [NC - 1:0] w_pq_push;
	reg [NC - 1:0] w_pq_pop;
	reg [(NC * OFF_W) - 1:0] w_head_off;
	reg [(NC * 32) - 1:0] w_head_bytes;
	function automatic signed [2:0] sv2v_cast_3CADD_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3CADD_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] ch;
			for (ch = 0; ch < NC; ch = ch + 1)
				begin
					w_pq_count[0 + (ch * 3)+:3] = r_pq_wp[0 + (ch * 3)+:3] - r_pq_rp[0 + (ch * 3)+:3];
					w_pq_empty[ch] = w_pq_count[0 + (ch * 3)+:3] == {3 {1'sb0}};
					w_pq_full[ch] = w_pq_count[0 + (ch * 3)+:3] == sv2v_cast_3CADD_signed(PQ_DEPTH);
					w_pq_push[ch] = (sched_rd_pkt_valid[ch] && !w_pq_full[ch]) && !w_rst[ch];
					w_head_off[ch * OFF_W+:OFF_W] = r_pq_off[((ch * PQ_DEPTH) + r_pq_rp[(ch * 3) + 1-:PQ_PW]) * OFF_W+:OFF_W];
					w_head_bytes[ch * 32+:32] = r_pq_bytes[((ch * PQ_DEPTH) + r_pq_rp[(ch * 3) + 1-:PQ_PW]) * 32+:32];
				end
		end
	end
	assign sched_rd_pkt_ready = ~w_pq_full;
	reg [(NC * DW) - 1:0] r_hold_data;
	reg [NC - 1:0] r_hold_valid;
	reg [NC - 1:0] r_eg_started;
	reg [(NC * 32) - 1:0] r_eg_bytes_left;
	reg [(NC * 32) - 1:0] r_eg_mem_left;
	reg r_out_valid;
	reg [DW - 1:0] r_out_data;
	reg [SW - 1:0] r_out_strb;
	reg r_out_last;
	reg [CIW - 1:0] r_out_ch;
	wire w_out_free;
	wire [CIW - 1:0] w_c;
	wire [OFF_W - 1:0] w_off;
	wire [31:0] w_bytes_left;
	wire [32:0] w_mem_span;
	wire [31:0] w_mem_total;
	wire [31:0] w_mem_left;
	wire w_pop;
	wire w_emit_on_pop;
	reg [NC - 1:0] w_need_flush;
	reg w_flush_any;
	reg [CIW - 1:0] w_flush_ch;
	wire [DW - 1:0] w_pop_out;
	wire [DW - 1:0] w_pop_hold_next;
	wire [DW - 1:0] w_out_data_n;
	wire [7:0] w_out_bytes_n;
	wire [31:0] w_bytes_left_sel;
	wire [SW - 1:0] w_out_strb_n;
	assign w_c = r_d_ch;
	assign w_off = w_head_off[w_c * OFF_W+:OFF_W];
	assign w_bytes_left = (r_eg_started[w_c] ? r_eg_bytes_left[w_c * 32+:32] : w_head_bytes[w_c * 32+:32]);
	function automatic [32:0] sv2v_cast_33;
		input reg [32:0] inp;
		sv2v_cast_33 = inp;
	endfunction
	function automatic signed [32:0] sv2v_cast_33_signed;
		input reg signed [32:0] inp;
		sv2v_cast_33_signed = inp;
	endfunction
	assign w_mem_span = (sv2v_cast_33(w_off) + sv2v_cast_33(w_head_bytes[w_c * 32+:32])) + sv2v_cast_33_signed(SW - 1);
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	assign w_mem_total = sv2v_cast_32(w_mem_span >> OFF_W);
	assign w_mem_left = (r_eg_started[w_c] ? r_eg_mem_left[w_c * 32+:32] : w_mem_total);
	function automatic signed [CIW - 1:0] sv2v_cast_0111B_signed;
		input reg signed [CIW - 1:0] inp;
		sv2v_cast_0111B_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] ch;
			for (ch = 0; ch < NC; ch = ch + 1)
				w_need_flush[ch] = ((r_eg_started[ch] && (r_eg_mem_left[ch * 32+:32] == 32'd0)) && (r_eg_bytes_left[ch * 32+:32] != 32'd0)) && !w_rst[ch];
		end
		w_flush_any = 1'b0;
		w_flush_ch = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] ch;
			for (ch = 0; ch < NC; ch = ch + 1)
				if (w_need_flush[ch] && !w_flush_any) begin
					w_flush_any = 1'b1;
					w_flush_ch = sv2v_cast_0111B_signed(ch);
				end
		end
	end
	assign w_out_free = !r_out_valid || m_axis_tready;
	assign w_pop = (((((r_d_active && drain_valid[w_c]) && drain_valid_comb[w_c]) && w_out_free) && !w_flush_any) && !w_pq_empty[w_c]) && !w_rst[w_c];
	assign w_emit_on_pop = ((w_off == {OFF_W {1'sb0}}) || r_hold_valid[w_c]) || (w_mem_left == 32'd1);
	assign w_pop_out = (r_hold_valid[w_c] ? r_hold_data[w_c * DW+:DW] | (drain_data << ((SW - sv2v_cast_32(w_off)) * 8)) : drain_data >> (w_off * 8));
	assign w_pop_hold_next = drain_data >> (w_off * 8);
	assign w_out_data_n = (w_flush_any ? r_hold_data[w_flush_ch * DW+:DW] : w_pop_out);
	assign w_bytes_left_sel = (w_flush_any ? r_eg_bytes_left[w_flush_ch * 32+:32] : w_bytes_left);
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign w_out_bytes_n = (w_bytes_left_sel >= SW ? sv2v_cast_8_signed(SW) : sv2v_cast_8(w_bytes_left_sel));
	assign w_out_strb_n = (w_out_bytes_n >= sv2v_cast_8_signed(SW) ? {SW {1'b1}} : ~({SW {1'b1}} << w_out_bytes_n));
	wire w_emit;
	wire [CIW - 1:0] w_emit_ch;
	assign w_emit = (w_flush_any && w_out_free) || (w_pop && w_emit_on_pop);
	assign w_emit_ch = (w_flush_any ? w_flush_ch : w_c);
	always @(*) begin
		if (_sv2v_0)
			;
		w_pq_pop = 1'sb0;
		if (w_emit && (w_bytes_left_sel == sv2v_cast_32(w_out_bytes_n)))
			w_pq_pop[w_emit_ch] = 1'b1;
	end
	function automatic [(PQ_DEPTH * OFF_W) - 1:0] sv2v_cast_B47FD;
		input reg [(PQ_DEPTH * OFF_W) - 1:0] inp;
		sv2v_cast_B47FD = inp;
	endfunction
	function automatic [127:0] sv2v_cast_F3D50;
		input reg [127:0] inp;
		sv2v_cast_F3D50 = inp;
	endfunction
	function automatic [2:0] sv2v_cast_0125D;
		input reg [2:0] inp;
		sv2v_cast_0125D = inp;
	endfunction
	function automatic [DW - 1:0] sv2v_cast_C1F1E;
		input reg [DW - 1:0] inp;
		sv2v_cast_C1F1E = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_pq_off <= {NC {sv2v_cast_B47FD(1'sb0)}};
			r_pq_bytes <= {NC {sv2v_cast_F3D50(1'sb0)}};
			r_pq_wp <= {NC {sv2v_cast_0125D(1'sb0)}};
			r_pq_rp <= {NC {sv2v_cast_0125D(1'sb0)}};
			r_hold_data <= {NC {sv2v_cast_C1F1E(1'sb0)}};
			r_hold_valid <= 1'sb0;
			r_eg_started <= 1'sb0;
			r_eg_bytes_left <= {NC {32'b00000000000000000000000000000000}};
			r_eg_mem_left <= {NC {32'b00000000000000000000000000000000}};
			r_out_valid <= 1'b0;
			r_out_data <= 1'sb0;
			r_out_strb <= 1'sb0;
			r_out_last <= 1'b0;
			r_out_ch <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_4
				reg signed [31:0] ch;
				for (ch = 0; ch < NC; ch = ch + 1)
					if (w_pq_push[ch]) begin
						r_pq_off[((ch * PQ_DEPTH) + r_pq_wp[(ch * 3) + 1-:PQ_PW]) * OFF_W+:OFF_W] <= sched_rd_pkt_offset[ch * OFF_W+:OFF_W];
						r_pq_bytes[((ch * PQ_DEPTH) + r_pq_wp[(ch * 3) + 1-:PQ_PW]) * 32+:32] <= sched_rd_pkt_bytes[ch * 32+:32];
						r_pq_wp[0 + (ch * 3)+:3] <= r_pq_wp[0 + (ch * 3)+:3] + 1'b1;
					end
			end
			if (m_axis_tvalid && m_axis_tready)
				r_out_valid <= 1'b0;
			if (w_emit) begin
				r_out_valid <= 1'b1;
				r_out_data <= w_out_data_n;
				r_out_strb <= w_out_strb_n;
				r_out_last <= w_bytes_left_sel == sv2v_cast_32(w_out_bytes_n);
				r_out_ch <= w_emit_ch;
			end
			if (w_pop) begin
				r_eg_started[w_c] <= 1'b1;
				r_eg_mem_left[w_c * 32+:32] <= w_mem_left - 32'd1;
				if (w_off != {OFF_W {1'sb0}}) begin
					r_hold_data[w_c * DW+:DW] <= w_pop_hold_next;
					r_hold_valid[w_c] <= 1'b1;
				end
				r_eg_bytes_left[w_c * 32+:32] <= (w_emit_on_pop ? w_bytes_left - sv2v_cast_32(w_out_bytes_n) : w_bytes_left);
			end
			else if (w_flush_any && w_out_free)
				r_eg_bytes_left[w_flush_ch * 32+:32] <= r_eg_bytes_left[w_flush_ch * 32+:32] - sv2v_cast_32(w_out_bytes_n);
			begin : sv2v_autoblock_5
				reg signed [31:0] ch;
				for (ch = 0; ch < NC; ch = ch + 1)
					if (w_pq_pop[ch]) begin
						r_pq_rp[0 + (ch * 3)+:3] <= r_pq_rp[0 + (ch * 3)+:3] + 1'b1;
						r_eg_started[ch] <= 1'b0;
						r_hold_valid[ch] <= 1'b0;
						r_hold_data[ch * DW+:DW] <= 1'sb0;
						r_eg_bytes_left[ch * 32+:32] <= 1'sb0;
						r_eg_mem_left[ch * 32+:32] <= 1'sb0;
					end
			end
			begin : sv2v_autoblock_6
				reg signed [31:0] ch;
				for (ch = 0; ch < NC; ch = ch + 1)
					if (w_rst[ch]) begin
						r_pq_wp[0 + (ch * 3)+:3] <= 1'sb0;
						r_pq_rp[0 + (ch * 3)+:3] <= 1'sb0;
						r_eg_started[ch] <= 1'b0;
						r_hold_valid[ch] <= 1'b0;
						r_hold_data[ch * DW+:DW] <= 1'sb0;
						r_eg_bytes_left[ch * 32+:32] <= 1'sb0;
						r_eg_mem_left[ch * 32+:32] <= 1'sb0;
					end
			end
		end
	function automatic [SCW - 1:0] sv2v_cast_79219;
		input reg [SCW - 1:0] inp;
		sv2v_cast_79219 = inp;
	endfunction
	function automatic [SCW - 1:0] sv2v_cast_14961;
		input reg [SCW - 1:0] inp;
		sv2v_cast_14961 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_drain_t = {NC {sv2v_cast_79219(1'sb0)}};
		if (r_res_valid)
			w_drain_t[r_res_ch * SCW+:SCW] = sv2v_cast_14961(r_res_size);
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_drain_tminus1 <= {NC {sv2v_cast_79219(1'sb0)}};
		else begin
			r_drain_tminus1 <= w_drain_t;
			begin : sv2v_autoblock_7
				reg signed [31:0] ch;
				for (ch = 0; ch < NC; ch = ch + 1)
					if (w_rst[ch])
						r_drain_tminus1[ch * SCW+:SCW] <= 1'sb0;
			end
		end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_8
			reg signed [31:0] ch;
			for (ch = 0; ch < NC; ch = ch + 1)
				begin
					w_pending_drain[ch * SCW+:SCW] = r_drain_tminus1[ch * SCW+:SCW] + w_drain_t[ch * SCW+:SCW];
					w_effective_avail[ch * SCW+:SCW] = (drain_data_avail[ch * SCW+:SCW] >= w_pending_drain[ch * SCW+:SCW] ? drain_data_avail[ch * SCW+:SCW] - w_pending_drain[ch * SCW+:SCW] : {SCW * 1 {1'sb0}});
				end
		end
	end
	assign w_eff_drain_size = (cfg_drain_size == 8'd0 ? 8'd1 : cfg_drain_size);
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_9
			reg signed [31:0] ch;
			for (ch = 0; ch < NC; ch = ch + 1)
				begin
					w_no_more_fill[ch] = (sched_rd_beats[ch * 32+:32] == 32'd0) && dbg_rd_all_complete[ch];
					w_ch_grantable[ch] = !w_rst[ch] && ((w_effective_avail[ch * SCW+:SCW] >= sv2v_cast_14961(w_eff_drain_size)) || ((w_effective_avail[ch * SCW+:SCW] != {SCW * 1 {1'sb0}}) && w_no_more_fill[ch]));
					w_grant_size[ch] = (w_effective_avail[ch * SCW+:SCW] >= sv2v_cast_14961(w_eff_drain_size) ? w_eff_drain_size : sv2v_cast_8(w_effective_avail[ch * SCW+:SCW]));
					r_arb_request[ch] = w_ch_grantable[ch];
				end
		end
	end
	assign w_rq_count = r_rq_wp - r_rq_rp;
	assign w_rq_empty = w_rq_count == {3 {1'sb0}};
	function automatic [2:0] sv2v_cast_1D27F;
		input reg [2:0] inp;
		sv2v_cast_1D27F = inp;
	endfunction
	function automatic signed [2:0] sv2v_cast_1D27F_signed;
		input reg signed [2:0] inp;
		sv2v_cast_1D27F_signed = inp;
	endfunction
	assign w_rq_room = (w_rq_count + sv2v_cast_1D27F(r_res_valid)) < sv2v_cast_1D27F_signed(RQ_DEPTH);
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	always @(posedge clk or negedge rst_n) begin : sv2v_autoblock_10
		reg [0:1] _sv2v_jump;
		_sv2v_jump = 2'b00;
		if (!rst_n) begin
			r_rr_last <= 1'sb0;
			r_res_valid <= 1'b0;
			r_res_ch <= 1'sb0;
			r_res_size <= 1'sb0;
		end
		else begin
			r_res_valid <= 1'b0;
			if (w_rq_room) begin : sv2v_autoblock_11
				reg signed [31:0] ch;
				begin : sv2v_autoblock_12
					reg signed [31:0] _sv2v_value_on_break;
					for (ch = 0; ch < NC; ch = ch + 1)
						if (_sv2v_jump < 2'b10) begin
							_sv2v_jump = 2'b00;
							begin : sv2v_autoblock_13
								reg [CIW - 1:0] check_ch;
								check_ch = sv2v_cast_0111B_signed(((sv2v_cast_32_signed(r_rr_last) + 1) + ch) % NC);
								if (w_ch_grantable[check_ch]) begin
									r_res_valid <= 1'b1;
									r_res_ch <= check_ch;
									r_res_size <= w_grant_size[check_ch];
									r_rr_last <= check_ch;
									_sv2v_jump = 2'b10;
								end
							end
							_sv2v_value_on_break = ch;
						end
					if (!(_sv2v_jump < 2'b10))
						ch = _sv2v_value_on_break;
					if (_sv2v_jump != 2'b11)
						_sv2v_jump = 2'b00;
				end
			end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		drain_req = 1'sb0;
		drain_size = {NC {8'b00000000}};
		if (r_res_valid) begin
			drain_req[r_res_ch] = 1'b1;
			drain_size[r_res_ch * 8+:8] = r_res_size;
		end
	end
	assign w_beat_accepted = w_pop;
	assign w_d_load = !w_rq_empty && (!r_d_active || (w_beat_accepted && (r_d_remaining <= 8'd1)));
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_rq_wp <= 1'sb0;
			r_rq_rp <= 1'sb0;
			r_rq_ch <= 1'sb0;
			r_rq_size <= 1'sb0;
			r_d_ch <= 1'sb0;
			r_d_active <= 1'b0;
			r_d_remaining <= 1'sb0;
		end
		else begin
			if (r_res_valid && !w_rst[r_res_ch]) begin
				r_rq_ch[r_rq_wp[1:0] * CIW+:CIW] <= r_res_ch;
				r_rq_size[r_rq_wp[1:0] * 8+:8] <= r_res_size;
				r_rq_wp <= r_rq_wp + 1'b1;
			end
			if (w_d_load) begin
				r_d_active <= r_rq_size[r_rq_rp[1:0] * 8+:8] != 8'd0;
				r_d_ch <= r_rq_ch[r_rq_rp[1:0] * CIW+:CIW];
				r_d_remaining <= r_rq_size[r_rq_rp[1:0] * 8+:8];
				r_rq_rp <= r_rq_rp + 1'b1;
			end
			else if (r_d_active && w_beat_accepted) begin
				if (r_d_remaining <= 8'd1) begin
					r_d_active <= 1'b0;
					r_d_remaining <= 1'sb0;
				end
				else
					r_d_remaining <= r_d_remaining - 8'd1;
			end
			begin : sv2v_autoblock_14
				reg signed [31:0] k;
				for (k = 0; k < RQ_DEPTH; k = k + 1)
					if (w_rst[r_rq_ch[k * CIW+:CIW]] && !((r_res_valid && !w_rst[r_res_ch]) && (k == sv2v_cast_32_signed(r_rq_wp[1:0]))))
						r_rq_size[k * 8+:8] <= 1'sb0;
			end
			begin : sv2v_autoblock_15
				reg signed [31:0] ch;
				for (ch = 0; ch < NC; ch = ch + 1)
					if ((w_rst[ch] && r_d_active) && (r_d_ch == ch[CIW - 1:0])) begin
						r_d_active <= 1'b0;
						r_d_remaining <= 1'sb0;
					end
			end
		end
	assign drain_id = r_d_ch;
	assign drain_read = w_pop;
	reg [31:0] r_axis_beats_sent;
	reg [31:0] r_axis_packets_sent;
	assign m_axis_tdata = r_out_data;
	assign m_axis_tstrb = r_out_strb;
	assign m_axis_tid = {{AXIS_ID_WIDTH - CIW {1'b0}}, r_out_ch};
	assign m_axis_tdest = {{AXIS_DEST_WIDTH - CIW {1'b0}}, r_out_ch};
	assign m_axis_tuser = 1'sb0;
	assign m_axis_tvalid = r_out_valid;
	assign m_axis_tlast = r_out_last;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_axis_beats_sent <= 1'sb0;
			r_axis_packets_sent <= 1'sb0;
		end
		else if (m_axis_tvalid && m_axis_tready) begin
			r_axis_beats_sent <= r_axis_beats_sent + 1'b1;
			if (m_axis_tlast)
				r_axis_packets_sent <= r_axis_packets_sent + 1'b1;
		end
	assign dbg_axis_beats_sent = r_axis_beats_sent;
	assign dbg_axis_packets_sent = r_axis_packets_sent;
	src_data_path #(
		.NUM_CHANNELS(NC),
		.ADDR_WIDTH(AW),
		.DATA_WIDTH(DW),
		.AXI_ID_WIDTH(IW),
		.SRAM_DEPTH(SD),
		.SEG_COUNT_WIDTH(SCW),
		.PIPELINE(PIPELINE),
		.AR_MAX_OUTSTANDING(AR_MAX_OUTSTANDING)
	) u_source_data_path(
		.clk(clk),
		.rst_n(rst_n),
		.cfg_axi_rd_xfer_beats(cfg_axi_rd_xfer_beats),
		.cfg_channel_reset(cfg_channel_reset),
		.sched_rd_valid(sched_rd_valid),
		.sched_rd_addr(sched_rd_addr),
		.sched_rd_beats(sched_rd_beats),
		.sched_rd_done_strobe(sched_rd_done_strobe),
		.sched_rd_beats_done(sched_rd_beats_done),
		.sched_rd_error(sched_rd_error),
		.drain_data_avail(drain_data_avail),
		.drain_req(drain_req),
		.drain_size(drain_size),
		.drain_valid(drain_valid),
		.drain_valid_comb(drain_valid_comb),
		.drain_read(drain_read),
		.drain_id(drain_id),
		.drain_data(drain_data),
		.m_axi_arid(m_axi_arid),
		.m_axi_araddr(m_axi_araddr),
		.m_axi_arlen(m_axi_arlen),
		.m_axi_arsize(m_axi_arsize),
		.m_axi_arburst(m_axi_arburst),
		.m_axi_arvalid(m_axi_arvalid),
		.m_axi_arready(m_axi_arready),
		.m_axi_rid(m_axi_rid),
		.m_axi_rdata(m_axi_rdata),
		.m_axi_rresp(m_axi_rresp),
		.m_axi_rlast(m_axi_rlast),
		.m_axi_rvalid(m_axi_rvalid),
		.m_axi_rready(m_axi_rready),
		.dbg_rd_all_complete(dbg_rd_all_complete),
		.dbg_r_beats_rcvd(dbg_r_beats_rcvd),
		.dbg_sram_writes(dbg_sram_writes),
		.dbg_arb_request(dbg_arb_request),
		.dbg_sram_bridge_pending(dbg_sram_bridge_pending),
		.dbg_sram_bridge_out_valid(dbg_sram_bridge_out_valid)
	);
	initial _sv2v_0 = 0;
endmodule
