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
module gaxi_skid_buffer (
	axi_aclk,
	axi_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	count,
	rd_valid,
	rd_ready,
	rd_count,
	rd_data
);
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] DEPTH = 2;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] BUF_WIDTH = DATA_WIDTH * DEPTH;
	parameter signed [31:0] BW = BUF_WIDTH;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire wr_valid;
	output reg wr_ready;
	input wire [DW - 1:0] wr_data;
	output wire [3:0] count;
	output reg rd_valid;
	input wire rd_ready;
	output wire [3:0] rd_count;
	output wire [DW - 1:0] rd_data;
	reg [BW - 1:0] r_data;
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	wire [DW - 1:0] zeros;
	assign zeros = 'b0;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk)
		if (!axi_aresetn) begin
			r_data <= 'b0;
			r_data_count <= 'b0;
		end
		else
			case ({w_wr_xfer, w_rd_xfer})
				2'b10: begin
					r_data[DW * r_data_count+:DW] <= wr_data;
					r_data_count <= r_data_count + 1;
				end
				2'b01: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data_count <= r_data_count - 1;
				end
				2'b11: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data[DW * (sv2v_cast_32(r_data_count) - 1)+:DW] <= wr_data;
				end
				default:
					;
			endcase
	always @(posedge axi_aclk)
		if (!axi_aresetn) begin
			wr_ready <= 1'b0;
			rd_valid <= 1'b0;
		end
		else begin
			wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && (~w_wr_xfer || w_rd_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && w_rd_xfer);
			rd_valid <= ((r_data_count >= 2) || ((r_data_count == 4'b0001) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'b0000) && w_wr_xfer);
		end
	assign rd_data = r_data[DW - 1:0];
	assign rd_count = r_data_count;
	assign count = r_data_count;
endmodule
module monbus_arbiter (
	axi_aclk,
	axi_aresetn,
	block_arb,
	monbus_valid_in,
	monbus_ready_in,
	monbus_packet_in,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	grant_valid,
	grant,
	grant_id,
	last_grant
);
	reg _sv2v_0;
	parameter signed [31:0] CLIENTS = 4;
	parameter signed [31:0] INPUT_SKID_ENABLE = 1;
	parameter signed [31:0] OUTPUT_SKID_ENABLE = 1;
	parameter signed [31:0] INPUT_SKID_DEPTH = 2;
	parameter signed [31:0] OUTPUT_SKID_DEPTH = 2;
	parameter signed [31:0] N = $clog2(CLIENTS);
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire block_arb;
	input wire [0:CLIENTS - 1] monbus_valid_in;
	output wire [0:CLIENTS - 1] monbus_ready_in;
	input wire [(CLIENTS * 64) - 1:0] monbus_packet_in;
	output wire monbus_valid;
	input wire monbus_ready;
	output wire [63:0] monbus_packet;
	output wire grant_valid;
	output wire [CLIENTS - 1:0] grant;
	output wire [N - 1:0] grant_id;
	output wire [CLIENTS - 1:0] last_grant;
	localparam [0:0] INPUT_SKID_EN = INPUT_SKID_ENABLE != 0;
	localparam [0:0] OUTPUT_SKID_EN = OUTPUT_SKID_ENABLE != 0;
	wire int_monbus_valid_in [0:CLIENTS - 1];
	reg int_monbus_ready_in [0:CLIENTS - 1];
	wire [63:0] int_monbus_packet_in [0:CLIENTS - 1];
	reg int_monbus_valid;
	wire int_monbus_ready;
	reg [63:0] int_monbus_packet;
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < CLIENTS; _gv_i_2 = _gv_i_2 + 1) begin : gen_input_skid
			localparam i = _gv_i_2;
			if (INPUT_SKID_EN == 1'b1) begin : gen_input_skid_enabled
				gaxi_skid_buffer #(
					.DATA_WIDTH(64),
					.DEPTH(INPUT_SKID_DEPTH)
				) u_input_skid(
					.axi_aclk(axi_aclk),
					.axi_aresetn(axi_aresetn),
					.wr_valid(monbus_valid_in[i]),
					.wr_ready(monbus_ready_in[i]),
					.wr_data(monbus_packet_in[((CLIENTS - 1) - i) * 64+:64]),
					.rd_valid(int_monbus_valid_in[i]),
					.rd_ready(int_monbus_ready_in[i]),
					.rd_data(int_monbus_packet_in[i]),
					.count(),
					.rd_count()
				);
			end
			else begin : gen_input_skid_disabled
				assign int_monbus_valid_in[i] = monbus_valid_in[i];
				assign monbus_ready_in[i] = int_monbus_ready_in[i];
				assign int_monbus_packet_in[i] = monbus_packet_in[((CLIENTS - 1) - i) * 64+:64];
			end
		end
	endgenerate
	reg [CLIENTS - 1:0] request;
	reg [CLIENTS - 1:0] grant_ack;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < CLIENTS; i = i + 1)
				request[i] = int_monbus_valid_in[i];
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < CLIENTS; i = i + 1)
				grant_ack[i] = grant[i] && int_monbus_valid_in[i];
		end
	end
	arbiter_round_robin #(
		.CLIENTS(CLIENTS),
		.WAIT_GNT_ACK(1)
	) u_arbiter(
		.clk(axi_aclk),
		.rst_n(axi_aresetn),
		.block_arb(block_arb),
		.request(request),
		.grant_ack(grant_ack),
		.grant_valid(grant_valid),
		.grant(grant),
		.grant_id(grant_id),
		.last_grant(last_grant)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < CLIENTS; i = i + 1)
				int_monbus_ready_in[i] = grant[i] && int_monbus_ready;
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		int_monbus_valid = grant_valid;
		int_monbus_packet = 1'sb0;
		if (grant_valid)
			int_monbus_packet = int_monbus_packet_in[grant_id];
	end
	generate
		if (OUTPUT_SKID_EN == 1'b1) begin : gen_output_skid_enabled
			gaxi_skid_buffer #(
				.DATA_WIDTH(64),
				.DEPTH(OUTPUT_SKID_DEPTH)
			) u_output_skid(
				.axi_aclk(axi_aclk),
				.axi_aresetn(axi_aresetn),
				.wr_valid(int_monbus_valid),
				.wr_ready(int_monbus_ready),
				.wr_data(int_monbus_packet),
				.rd_valid(monbus_valid),
				.rd_ready(monbus_ready),
				.rd_data(monbus_packet),
				.count(),
				.rd_count()
			);
		end
		else begin : gen_output_skid_disabled
			assign monbus_valid = int_monbus_valid;
			assign int_monbus_ready = monbus_ready;
			assign monbus_packet = int_monbus_packet;
		end
	endgenerate
	always @(posedge axi_aclk)
		if (axi_aresetn && grant_valid)
			;
	always @(posedge axi_aclk)
		if (axi_aresetn && grant_valid)
			;
	always @(posedge axi_aclk)
		if (axi_aresetn) begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < CLIENTS; i = i + 1)
				if (!grant[i])
					;
		end
	initial _sv2v_0 = 0;
endmodule
module descriptor_engine (
	clk,
	rst_n,
	apb_valid,
	apb_ready,
	apb_addr,
	channel_idle,
	descriptor_valid,
	descriptor_ready,
	descriptor_packet,
	descriptor_error,
	descriptor_eos,
	descriptor_eol,
	descriptor_eod,
	descriptor_type,
	ar_valid,
	ar_ready,
	ar_addr,
	ar_len,
	ar_size,
	ar_burst,
	ar_id,
	ar_lock,
	ar_cache,
	ar_prot,
	ar_qos,
	ar_region,
	r_valid,
	r_ready,
	r_data,
	r_resp,
	r_last,
	r_id,
	cfg_prefetch_enable,
	cfg_fifo_threshold,
	cfg_addr0_base,
	cfg_addr0_limit,
	cfg_addr1_base,
	cfg_addr1_limit,
	cfg_channel_reset,
	descriptor_engine_idle,
	mon_valid,
	mon_ready,
	mon_packet
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter signed [31:0] NUM_CHANNELS = 32;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] FIFO_DEPTH = 8;
	parameter signed [31:0] DESC_ADDR_FIFO_DEPTH = 2;
	parameter signed [31:0] TIMEOUT_CYCLES = 1000;
	parameter [7:0] MON_AGENT_ID = 8'h10;
	parameter [3:0] MON_UNIT_ID = 4'h1;
	parameter [5:0] MON_CHANNEL_ID = 6'h00;
	input wire clk;
	input wire rst_n;
	input wire apb_valid;
	output wire apb_ready;
	input wire [ADDR_WIDTH - 1:0] apb_addr;
	input wire channel_idle;
	output wire descriptor_valid;
	input wire descriptor_ready;
	output wire [255:0] descriptor_packet;
	output wire descriptor_error;
	output wire descriptor_eos;
	output wire descriptor_eol;
	output wire descriptor_eod;
	output wire [1:0] descriptor_type;
	output wire ar_valid;
	input wire ar_ready;
	output wire [ADDR_WIDTH - 1:0] ar_addr;
	output wire [7:0] ar_len;
	output wire [2:0] ar_size;
	output wire [1:0] ar_burst;
	output wire [AXI_ID_WIDTH - 1:0] ar_id;
	output wire ar_lock;
	output wire [3:0] ar_cache;
	output wire [2:0] ar_prot;
	output wire [3:0] ar_qos;
	output wire [3:0] ar_region;
	input wire r_valid;
	output wire r_ready;
	input wire [255:0] r_data;
	input wire [1:0] r_resp;
	input wire r_last;
	input wire [AXI_ID_WIDTH - 1:0] r_id;
	input wire cfg_prefetch_enable;
	input wire [3:0] cfg_fifo_threshold;
	input wire [ADDR_WIDTH - 1:0] cfg_addr0_base;
	input wire [ADDR_WIDTH - 1:0] cfg_addr0_limit;
	input wire [ADDR_WIDTH - 1:0] cfg_addr1_base;
	input wire [ADDR_WIDTH - 1:0] cfg_addr1_limit;
	input wire cfg_channel_reset;
	output wire descriptor_engine_idle;
	output wire mon_valid;
	input wire mon_ready;
	output wire [63:0] mon_packet;
	initial if (AXI_ID_WIDTH < CHAN_WIDTH) begin
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/stream/rtl/fub/descriptor_engine.sv:137:13 - descriptor_engine.<unnamed_block>.<unnamed_block>\n msg: ", $time, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
		$finish(1);
	end
	reg [2:0] r_current_state;
	reg [2:0] w_next_state;
	reg r_channel_reset_active;
	wire w_safe_to_reset;
	wire w_fifos_empty;
	wire w_no_active_operations;
	wire w_apb_skid_valid_in;
	wire w_apb_skid_ready_in;
	wire w_apb_skid_valid_out;
	wire w_apb_skid_ready_out;
	wire [ADDR_WIDTH - 1:0] w_apb_skid_dout;
	reg w_desc_addr_fifo_wr_valid;
	wire w_desc_addr_fifo_wr_ready;
	wire w_desc_addr_fifo_rd_valid;
	wire w_desc_addr_fifo_rd_ready;
	reg [ADDR_WIDTH - 1:0] w_desc_addr_fifo_wr_data;
	wire [ADDR_WIDTH - 1:0] w_desc_addr_fifo_rd_data;
	wire w_desc_addr_fifo_empty;
	wire w_desc_fifo_wr_valid;
	wire w_desc_fifo_wr_ready;
	wire w_desc_fifo_rd_valid;
	wire w_desc_fifo_rd_ready;
	reg [260:0] w_desc_fifo_wr_data;
	wire [260:0] w_desc_fifo_rd_data;
	reg r_apb_operation_active;
	reg r_axi_read_active;
	reg [ADDR_WIDTH - 1:0] r_axi_read_addr;
	reg [1:0] r_axi_read_resp;
	reg [255:0] r_descriptor_data;
	reg [ADDR_WIDTH - 1:0] r_saved_next_addr;
	wire w_chain_condition;
	wire w_next_addr_valid;
	wire w_should_chain;
	reg w_desc_eos;
	reg w_desc_eol;
	reg w_desc_eod;
	reg w_desc_last;
	reg w_desc_valid;
	reg [1:0] w_desc_type;
	reg [31:0] w_next_addr;
	wire w_addr_range_valid;
	wire w_our_axi_response;
	wire w_axi_response_ok;
	reg r_descriptor_error;
	reg r_apb_ip;
	reg r_channel_idle_prev;
	reg r_mon_valid;
	reg [63:0] r_mon_packet;
	always @(posedge clk)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	assign w_fifos_empty = (!w_apb_skid_valid_out && !w_desc_addr_fifo_rd_valid) && !w_desc_fifo_rd_valid;
	assign w_no_active_operations = !r_apb_operation_active && !r_axi_read_active;
	assign w_safe_to_reset = (w_fifos_empty && w_no_active_operations) && (r_current_state == 3'b000);
	assign descriptor_engine_idle = ((r_current_state == 3'b000) && !r_channel_reset_active) && w_fifos_empty;
	wire w_apb_addr_valid;
	assign w_apb_addr_valid = apb_addr != {ADDR_WIDTH {1'sb0}};
	assign w_apb_skid_valid_in = (((apb_valid && !r_channel_reset_active) && w_desc_addr_fifo_empty) && channel_idle) && !r_apb_ip;
	assign apb_ready = (((w_apb_skid_ready_in && !r_channel_reset_active) && w_desc_addr_fifo_empty) && channel_idle) && !r_apb_ip;
	gaxi_skid_buffer #(
		.DATA_WIDTH(ADDR_WIDTH),
		.DEPTH(2)
	) i_apb_skid_buffer(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_apb_skid_valid_in),
		.wr_ready(w_apb_skid_ready_in),
		.wr_data(apb_addr),
		.rd_valid(w_apb_skid_valid_out),
		.rd_ready(w_apb_skid_ready_out),
		.rd_data(w_apb_skid_dout),
		.count(),
		.rd_count()
	);
	assign w_apb_skid_ready_out = ((r_current_state == 3'b000) && w_desc_addr_fifo_wr_ready) && !r_channel_reset_active;
	gaxi_fifo_sync #(
		.DATA_WIDTH(ADDR_WIDTH),
		.DEPTH(DESC_ADDR_FIFO_DEPTH)
	) i_desc_addr_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_desc_addr_fifo_wr_valid),
		.wr_ready(w_desc_addr_fifo_wr_ready),
		.wr_data(w_desc_addr_fifo_wr_data),
		.rd_valid(w_desc_addr_fifo_rd_valid),
		.rd_ready(w_desc_addr_fifo_rd_ready),
		.rd_data(w_desc_addr_fifo_rd_data),
		.count()
	);
	assign w_desc_addr_fifo_empty = !w_desc_addr_fifo_rd_valid;
	assign w_desc_addr_fifo_rd_ready = (r_current_state == 3'b000) && !r_channel_reset_active;
	always @(*) begin
		if (_sv2v_0)
			;
		w_desc_addr_fifo_wr_valid = 1'b0;
		w_desc_addr_fifo_wr_data = 1'sb0;
		if (w_apb_skid_valid_out && w_apb_skid_ready_out) begin
			w_desc_addr_fifo_wr_valid = 1'b1;
			w_desc_addr_fifo_wr_data = w_apb_skid_dout;
		end
		else if (w_should_chain && (r_current_state == 3'b011)) begin
			w_desc_addr_fifo_wr_valid = 1'b1;
			w_desc_addr_fifo_wr_data = {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
		end
	end
	wire [ADDR_WIDTH - 1:0] w_next_addr_extended;
	assign w_next_addr_extended = {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
	assign w_next_addr_valid = ((w_next_addr_extended >= cfg_addr0_base) && (w_next_addr_extended <= cfg_addr0_limit)) || ((w_next_addr_extended >= cfg_addr1_base) && (w_next_addr_extended <= cfg_addr1_limit));
	assign w_chain_condition = ((w_next_addr != {32 {1'sb0}}) && !w_desc_last) && w_desc_valid;
	assign w_should_chain = ((w_chain_condition && w_next_addr_valid) && !r_descriptor_error) && w_desc_fifo_wr_ready;
	assign w_desc_fifo_wr_valid = (r_current_state == 3'b011) && !r_channel_reset_active;
	assign w_desc_fifo_rd_ready = descriptor_ready && !r_channel_reset_active;
	gaxi_fifo_sync #(
		.DATA_WIDTH(261),
		.DEPTH(FIFO_DEPTH)
	) i_descriptor_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_desc_fifo_wr_valid),
		.wr_ready(w_desc_fifo_wr_ready),
		.wr_data(w_desc_fifo_wr_data),
		.rd_valid(w_desc_fifo_rd_valid),
		.rd_ready(w_desc_fifo_rd_ready),
		.rd_data(w_desc_fifo_rd_data),
		.count()
	);
	always @(*) begin
		if (_sv2v_0)
			;
		w_desc_eos = 1'b0;
		w_desc_eol = 1'b0;
		w_desc_eod = 1'b0;
		w_desc_last = 1'b0;
		w_desc_type = 2'b00;
		w_next_addr = 32'h00000000;
		w_next_addr = r_descriptor_data[191:160];
		w_desc_last = r_descriptor_data[194];
		w_desc_valid = r_descriptor_data[192];
		w_desc_eos = 1'b0;
		w_desc_eol = 1'b0;
		w_desc_eod = 1'b0;
		w_desc_type = 2'b00;
	end
	assign w_addr_range_valid = ((r_axi_read_addr >= cfg_addr0_base) && (r_axi_read_addr <= cfg_addr0_limit)) || ((r_axi_read_addr >= cfg_addr1_base) && (r_axi_read_addr <= cfg_addr1_limit));
	assign w_our_axi_response = r_valid && (r_id[CHAN_WIDTH - 1:0] == CHANNEL_ID[CHAN_WIDTH - 1:0]);
	assign w_axi_response_ok = r_resp == 2'b00;
	assign r_ready = (r_current_state == 3'b010) && w_our_axi_response;
	always @(posedge clk)
		if (!rst_n)
			r_current_state <= 3'b000;
		else
			r_current_state <= w_next_state;
	reg w_pkt_error;
	reg w_pkt_last;
	reg w_pkt_gen_irq;
	reg w_pkt_valid;
	reg [31:0] w_pkt_next_descriptor_ptr;
	reg [31:0] w_pkt_length;
	reg [63:0] w_pkt_dst_addr;
	reg [63:0] w_pkt_src_addr;
	always @(*) begin
		if (_sv2v_0)
			;
		w_pkt_error = r_data[195];
		w_pkt_last = r_data[194];
		w_pkt_gen_irq = r_data[193];
		w_pkt_valid = r_data[192];
		w_pkt_next_descriptor_ptr = r_data[191:160];
		w_pkt_length = r_data[159:128];
		w_pkt_dst_addr = r_data[127:64];
		w_pkt_src_addr = r_data[63:0];
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_current_state;
		case (r_current_state)
			3'b000:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_desc_addr_fifo_rd_valid && w_desc_addr_fifo_rd_ready)
					w_next_state = 3'b001;
			3'b001:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (ar_ready)
					w_next_state = 3'b010;
			3'b010:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_our_axi_response && r_valid) begin
					if (w_axi_response_ok)
						w_next_state = 3'b011;
					else
						w_next_state = 3'b100;
				end
			3'b011:
				if (w_desc_fifo_wr_ready)
					w_next_state = 3'b000;
			3'b100: w_next_state = 3'b000;
			default: w_next_state = 3'b000;
		endcase
	end
	always @(posedge clk)
		if (!rst_n) begin
			r_apb_operation_active <= 1'b0;
			r_axi_read_active <= 1'b0;
			r_axi_read_addr <= 64'h0000000000000000;
			r_axi_read_resp <= 2'b00;
			r_descriptor_data <= 1'sb0;
			r_saved_next_addr <= 64'h0000000000000000;
			r_descriptor_error <= 1'b0;
		end
		else begin
			case (r_current_state)
				3'b000: begin
					if (w_desc_addr_fifo_rd_valid && w_desc_addr_fifo_rd_ready) begin
						r_apb_operation_active <= 1'b1;
						r_axi_read_addr <= w_desc_addr_fifo_rd_data;
					end
					r_descriptor_error <= 1'b0;
				end
				3'b001:
					if (ar_ready)
						r_axi_read_active <= 1'b1;
				3'b010:
					if (w_our_axi_response && r_valid) begin
						r_descriptor_data <= r_data;
						r_axi_read_resp <= r_resp;
						r_saved_next_addr <= {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
						if (!r_data[192])
							r_descriptor_error <= 1'b1;
					end
				3'b011:
					if (w_desc_fifo_wr_ready) begin
						r_apb_operation_active <= 1'b0;
						r_axi_read_active <= 1'b0;
					end
				3'b100: begin
					r_descriptor_error <= 1'b1;
					r_apb_operation_active <= 1'b0;
					r_axi_read_active <= 1'b0;
				end
				default:
					;
			endcase
			// APB address-0 error detection (merged from separate always block)
			if (apb_valid && !w_apb_addr_valid)
				r_descriptor_error <= 1'b1;
			if (r_channel_reset_active) begin
				r_apb_operation_active <= 1'b0;
				r_axi_read_active <= 1'b0;
				r_descriptor_error <= 1'b0;
			end
		end
	always @(*) begin
		if (_sv2v_0)
			;
		w_desc_fifo_wr_data = 1'sb0;
		if (r_current_state == 3'b011) begin
			w_desc_fifo_wr_data[260-:256] = r_descriptor_data;
			w_desc_fifo_wr_data[4] = w_desc_eos;
			w_desc_fifo_wr_data[3] = w_desc_eol;
			w_desc_fifo_wr_data[2] = w_desc_eod;
			w_desc_fifo_wr_data[1-:2] = w_desc_type;
		end
	end
	assign ar_valid = (r_current_state == 3'b001) && !r_axi_read_active;
	assign ar_addr = r_axi_read_addr;
	assign ar_len = 8'h00;
	assign ar_size = 3'b110;
	assign ar_burst = 2'b01;
	assign ar_id = {{AXI_ID_WIDTH - CHAN_WIDTH {1'b0}}, CHANNEL_ID[CHAN_WIDTH - 1:0]};
	assign ar_lock = 1'b0;
	assign ar_cache = 4'b0010;
	assign ar_prot = 3'b000;
	assign ar_qos = 4'h0;
	assign ar_region = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	function automatic [63:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [2:0] protocol;
		input reg [3:0] event_code;
		input reg [5:0] channel_id;
		input reg [3:0] unit_id;
		input reg [7:0] agent_id;
		input reg [34:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
	endfunction
	always @(posedge clk)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
			case (r_current_state)
				3'b011: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, 4'h0, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, r_axi_read_addr[34:0]);
				end
				3'b100: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 3'b100, 4'h6, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {16'h0000, r_axi_read_resp, 17'h00000});
				end
				default:
					;
			endcase
		end
	wire w_channel_idle_falling = r_channel_idle_prev && !channel_idle;
	always @(posedge clk)
		if (!rst_n) begin
			r_apb_ip <= 1'b0;
			r_channel_idle_prev <= 1'b1;
		end
		else begin
			r_channel_idle_prev <= channel_idle;
			if (w_apb_skid_valid_in && w_apb_skid_ready_in)
				r_apb_ip <= 1'b1;
			else if (w_channel_idle_falling && r_apb_ip)
				r_apb_ip <= 1'b0;
		end
	assign descriptor_valid = w_desc_fifo_rd_valid && !r_descriptor_error;
	assign descriptor_packet = w_desc_fifo_rd_data[260-:256];
	assign descriptor_error = r_descriptor_error;
	assign descriptor_eos = w_desc_fifo_rd_data[4];
	assign descriptor_eol = w_desc_fifo_rd_data[3];
	assign descriptor_eod = w_desc_fifo_rd_data[2];
	assign descriptor_type = w_desc_fifo_rd_data[1-:2];
	assign mon_valid = r_mon_valid;
	assign mon_packet = r_mon_packet;
	initial _sv2v_0 = 0;
endmodule
module scheduler (
	clk,
	rst_n,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_enable,
	scheduler_idle,
	scheduler_state,
	descriptor_valid,
	descriptor_ready,
	descriptor_packet,
	descriptor_error,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_wr_valid,
	sched_wr_ready,
	sched_wr_addr,
	sched_wr_beats,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	sched_wr_done_strobe,
	sched_wr_beats_done,
	sched_rd_error,
	sched_wr_error,
	sched_error,
	mon_valid,
	mon_ready,
	mon_packet
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter [7:0] MON_AGENT_ID = 8'h40;
	parameter [3:0] MON_UNIT_ID = 4'h1;
	parameter [5:0] MON_CHANNEL_ID = 6'h00;
	parameter signed [31:0] DESC_WIDTH = 256;
	input wire clk;
	input wire rst_n;
	input wire cfg_channel_enable;
	input wire cfg_channel_reset;
	input wire [15:0] cfg_sched_timeout_cycles;
	input wire cfg_sched_timeout_enable;
	output wire scheduler_idle;
	output wire [6:0] scheduler_state;
	input wire descriptor_valid;
	output wire descriptor_ready;
	input wire [DESC_WIDTH - 1:0] descriptor_packet;
	input wire descriptor_error;
	output wire sched_rd_valid;
	output wire [ADDR_WIDTH - 1:0] sched_rd_addr;
	output wire [31:0] sched_rd_beats;
	output wire sched_wr_valid;
	input wire sched_wr_ready;
	output wire [ADDR_WIDTH - 1:0] sched_wr_addr;
	output wire [31:0] sched_wr_beats;
	input wire sched_rd_done_strobe;
	input wire [31:0] sched_rd_beats_done;
	input wire sched_wr_done_strobe;
	input wire [31:0] sched_wr_beats_done;
	input wire sched_rd_error;
	input wire sched_wr_error;
	output wire sched_error;
	output wire mon_valid;
	input wire mon_ready;
	output wire [63:0] mon_packet;
	initial if (DESC_WIDTH != 256) begin
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/stream/rtl/fub/scheduler.sv:137:13 - scheduler.<unnamed_block>.<unnamed_block>\n msg: ", $time, "scheduler (STREAM): DESC_WIDTH must be 256, got %0d. For RAPIDS, use rapids_scheduler.", DESC_WIDTH);
		$finish(1);
	end
	localparam signed [31:0] DESC_SRC_ADDR_LO = 0;
	localparam signed [31:0] DESC_SRC_ADDR_HI = 63;
	localparam signed [31:0] DESC_DST_ADDR_LO = 64;
	localparam signed [31:0] DESC_DST_ADDR_HI = 127;
	localparam signed [31:0] DESC_LENGTH_LO = 128;
	localparam signed [31:0] DESC_LENGTH_HI = 159;
	localparam signed [31:0] DESC_NEXT_PTR_LO = 160;
	localparam signed [31:0] DESC_NEXT_PTR_HI = 191;
	localparam signed [31:0] DESC_VALID_BIT = 192;
	localparam signed [31:0] DESC_GEN_IRQ = 193;
	localparam signed [31:0] DESC_LAST = 194;
	wire w_pkt_error;
	reg w_pkt_last;
	reg w_pkt_gen_irq;
	reg w_pkt_valid;
	reg [31:0] w_pkt_next_descriptor_ptr;
	reg [31:0] w_pkt_length;
	reg [63:0] w_pkt_dst_addr;
	reg [63:0] w_pkt_src_addr;
	reg [6:0] r_current_state;
	reg [6:0] w_next_state;
	wire w_state_idle = r_current_state == 7'b0000001;
	wire w_state_fetch_desc = r_current_state == 7'b0000010;
	wire w_state_xfer_data = r_current_state == 7'b0000100;
	wire w_state_complete = r_current_state == 7'b0001000;
	wire w_state_next_desc = r_current_state == 7'b0010000;
	wire w_state_error = r_current_state == 7'b0100000;
	reg r_channel_reset_active;
	reg [271:0] r_descriptor;
	reg r_descriptor_loaded;
	reg [ADDR_WIDTH - 1:0] r_src_addr;
	reg [ADDR_WIDTH - 1:0] r_dst_addr;
	reg [31:0] r_beats_remaining;
	reg [31:0] r_read_beats_remaining;
	reg [31:0] r_write_beats_remaining;
	reg [31:0] r_timeout_counter;
	wire w_timeout_expired;
	reg r_read_error_sticky;
	reg r_write_error_sticky;
	reg r_descriptor_error;
	reg r_mon_valid;
	reg [63:0] r_mon_packet;
	wire w_read_complete;
	wire w_write_complete;
	wire w_transfer_complete;
	always @(posedge clk)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	always @(posedge clk)
		if (!rst_n)
			r_current_state <= 7'b0000001;
		else
			r_current_state <= w_next_state;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_current_state;
		if (r_channel_reset_active)
			w_next_state = 7'b0000001;
		else if (((((descriptor_error || sched_rd_error) || sched_wr_error) || r_read_error_sticky) || r_write_error_sticky) || w_timeout_expired)
			w_next_state = 7'b0100000;
		else
			case (r_current_state)
				7'b0000001:
					if (descriptor_valid && cfg_channel_enable)
						w_next_state = 7'b0000010;
				7'b0000010:
					if (r_descriptor[192])
						w_next_state = 7'b0000100;
					else
						w_next_state = 7'b0100000;
				7'b0000100:
					if (w_transfer_complete && sched_wr_ready)
						w_next_state = 7'b0001000;
				7'b0001000:
					if ((r_descriptor[191-:32] != 32'h00000000) && !r_descriptor[194])
						w_next_state = 7'b0010000;
					else
						w_next_state = 7'b0000001;
				7'b0010000:
					if (descriptor_valid)
						w_next_state = 7'b0000010;
				7'b0100000: w_next_state = 7'b0100000;
				default: w_next_state = 7'b0100000;
			endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_pkt_last = r_descriptor[194];
		w_pkt_gen_irq = r_descriptor[193];
		w_pkt_valid = r_descriptor[192];
		w_pkt_next_descriptor_ptr = r_descriptor[191-:32];
		w_pkt_length = r_descriptor[159-:32];
		w_pkt_dst_addr = r_descriptor[127-:64];
		w_pkt_src_addr = r_descriptor[63-:64];
	end
	function automatic [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5;
		input reg [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5 = inp;
	endfunction
	always @(posedge clk)
		if (!rst_n) begin
			r_descriptor <= 1'sb0;
			r_descriptor_loaded <= 1'b0;
			r_src_addr <= 64'h0000000000000000;
			r_dst_addr <= 64'h0000000000000000;
			r_beats_remaining <= 32'h00000000;
			r_read_beats_remaining <= 32'h00000000;
			r_write_beats_remaining <= 32'h00000000;
		end
		else begin
			if ((((r_current_state == 7'b0000001) || (r_current_state == 7'b0010000)) && descriptor_valid) && descriptor_ready) begin
				r_descriptor[63-:64] <= descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
				r_descriptor[127-:64] <= descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
				r_descriptor[159-:32] <= descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
				r_descriptor[191-:32] <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
				r_descriptor[192] <= descriptor_packet[DESC_VALID_BIT];
				r_descriptor[193] <= descriptor_packet[DESC_GEN_IRQ];
				r_descriptor[194] <= descriptor_packet[DESC_LAST];
				r_descriptor_loaded <= 1'b1;
			end
			case (r_current_state)
				7'b0000010: begin
					r_src_addr <= r_descriptor[63-:64];
					r_dst_addr <= r_descriptor[127-:64];
					r_beats_remaining <= r_descriptor[159-:32];
					r_read_beats_remaining <= r_descriptor[159-:32];
					r_write_beats_remaining <= r_descriptor[159-:32];
				end
				7'b0000100: begin
					if (sched_rd_done_strobe) begin
						r_read_beats_remaining <= (r_read_beats_remaining >= sched_rd_beats_done ? r_read_beats_remaining - sched_rd_beats_done : 32'h00000000);
						r_src_addr <= r_src_addr + (sv2v_cast_A5DC5(sched_rd_beats_done) << $clog2(DATA_WIDTH / 8));
					end
					if (sched_wr_done_strobe) begin
						r_write_beats_remaining <= (r_write_beats_remaining >= sched_wr_beats_done ? r_write_beats_remaining - sched_wr_beats_done : 32'h00000000);
						r_dst_addr <= r_dst_addr + (sv2v_cast_A5DC5(sched_wr_beats_done) << $clog2(DATA_WIDTH / 8));
					end
				end
				7'b0001000: r_descriptor_loaded <= 1'b0;
				default:
					;
			endcase
			if (r_channel_reset_active) begin
				r_descriptor_loaded <= 1'b0;
				r_read_beats_remaining <= 32'h00000000;
				r_write_beats_remaining <= 32'h00000000;
			end
		end
	assign w_read_complete = r_read_beats_remaining == 32'h00000000;
	assign w_write_complete = r_write_beats_remaining == 32'h00000000;
	assign w_transfer_complete = w_read_complete && w_write_complete;
	wire w_sched_rd_completing_this_cycle;
	wire w_sched_wr_completing_this_cycle;
	assign w_sched_rd_completing_this_cycle = sched_rd_done_strobe && (r_read_beats_remaining <= sched_rd_beats_done);
	assign w_sched_wr_completing_this_cycle = sched_wr_done_strobe && (r_write_beats_remaining <= sched_wr_beats_done);
	assign sched_rd_valid = ((r_current_state == 7'b0000100) && !w_read_complete) && !w_sched_rd_completing_this_cycle;
	assign sched_rd_addr = r_src_addr;
	assign sched_rd_beats = r_read_beats_remaining;
	assign sched_wr_valid = ((r_current_state == 7'b0000100) && !w_write_complete) && !w_sched_wr_completing_this_cycle;
	assign sched_wr_addr = r_dst_addr;
	assign sched_wr_beats = r_write_beats_remaining;
	assign descriptor_ready = (r_current_state == 7'b0000001) || (r_current_state == 7'b0010000);
	always @(posedge clk)
		if (!rst_n) begin
			r_timeout_counter <= 32'h00000000;
			r_read_error_sticky <= 1'b0;
			r_write_error_sticky <= 1'b0;
			r_descriptor_error <= 1'b0;
		end
		else begin
			if (sched_wr_valid && !sched_wr_ready)
				r_timeout_counter <= r_timeout_counter + 1;
			else
				r_timeout_counter <= 32'h00000000;
			if (descriptor_error)
				r_descriptor_error <= 1'b1;
			if (sched_rd_error)
				r_read_error_sticky <= 1'b1;
			if (sched_wr_error)
				r_write_error_sticky <= 1'b1;
			if ((sched_rd_error || sched_wr_error) || w_timeout_expired)
				r_descriptor_error <= 1'b1;
			if (r_current_state == 7'b0000001) begin
				r_read_error_sticky <= 1'b0;
				r_write_error_sticky <= 1'b0;
				r_descriptor_error <= 1'b0;
			end
		end
	assign w_timeout_expired = cfg_sched_timeout_enable && (r_timeout_counter >= {16'h0000, cfg_sched_timeout_cycles});
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	function automatic [63:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [2:0] protocol;
		input reg [3:0] event_code;
		input reg [5:0] channel_id;
		input reg [3:0] unit_id;
		input reg [7:0] agent_id;
		input reg [34:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
	endfunction
	localparam [3:0] stream_pkg_STREAM_EVENT_DESC_COMPLETE = 4'h1;
	localparam [3:0] stream_pkg_STREAM_EVENT_DESC_START = 4'h0;
	localparam [3:0] stream_pkg_STREAM_EVENT_ERROR = 4'hf;
	localparam [3:0] stream_pkg_STREAM_EVENT_IRQ = 4'h7;
	always @(posedge clk)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 64'h0000000000000000;
			case (r_current_state)
				7'b0000010: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, stream_pkg_STREAM_EVENT_DESC_START, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {3'h0, r_descriptor[159-:32]});
				end
				7'b0000100:
					;
				7'b0001000: begin
					r_mon_valid <= 1'b1;
					if (r_descriptor[193])
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, stream_pkg_STREAM_EVENT_IRQ, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {3'h0, r_descriptor[159-:32]});
					else
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 3'b100, stream_pkg_STREAM_EVENT_DESC_COMPLETE, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {3'h0, r_descriptor[159-:32]});
				end
				7'b0100000: begin
					r_mon_valid <= 1'b1;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 3'b100, stream_pkg_STREAM_EVENT_ERROR, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {r_write_error_sticky, r_read_error_sticky, 33'h000000000});
				end
				default:
					;
			endcase
		end
	assign scheduler_idle = ((r_current_state == 7'b0000001) || (r_current_state == 7'b0100000)) && !r_channel_reset_active;
	assign scheduler_state = r_current_state;
	assign sched_error = w_state_error;
	assign mon_valid = r_mon_valid;
	assign mon_packet = r_mon_packet;
	initial _sv2v_0 = 0;
endmodule
module scheduler_group (
	clk,
	rst_n,
	apb_valid,
	apb_ready,
	apb_addr,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_enable,
	cfg_sched_err_enable,
	cfg_sched_compl_enable,
	cfg_sched_perf_enable,
	cfg_desceng_prefetch,
	cfg_desceng_fifo_thresh,
	cfg_desceng_addr0_base,
	cfg_desceng_addr0_limit,
	cfg_desceng_addr1_base,
	cfg_desceng_addr1_limit,
	descriptor_engine_idle,
	scheduler_idle,
	scheduler_state,
	sched_error,
	desc_ar_valid,
	desc_ar_ready,
	desc_ar_addr,
	desc_ar_len,
	desc_ar_size,
	desc_ar_burst,
	desc_ar_id,
	desc_ar_lock,
	desc_ar_cache,
	desc_ar_prot,
	desc_ar_qos,
	desc_ar_region,
	desc_r_valid,
	desc_r_ready,
	desc_r_data,
	desc_r_resp,
	desc_r_last,
	desc_r_id,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_wr_valid,
	sched_wr_ready,
	sched_wr_addr,
	sched_wr_beats,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	sched_wr_done_strobe,
	sched_wr_beats_done,
	sched_rd_error,
	sched_wr_error,
	mon_valid,
	mon_ready,
	mon_packet
);
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter DESC_MON_AGENT_ID = 16;
	parameter SCHED_MON_AGENT_ID = 48;
	parameter MON_UNIT_ID = 1;
	parameter MON_CHANNEL_ID = 0;
	input wire clk;
	input wire rst_n;
	input wire apb_valid;
	output wire apb_ready;
	input wire [ADDR_WIDTH - 1:0] apb_addr;
	input wire cfg_channel_enable;
	input wire cfg_channel_reset;
	input wire [15:0] cfg_sched_timeout_cycles;
	input wire cfg_sched_timeout_enable;
	input wire cfg_sched_err_enable;
	input wire cfg_sched_compl_enable;
	input wire cfg_sched_perf_enable;
	input wire cfg_desceng_prefetch;
	input wire [3:0] cfg_desceng_fifo_thresh;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_limit;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_limit;
	output wire descriptor_engine_idle;
	output wire scheduler_idle;
	output wire [6:0] scheduler_state;
	output wire sched_error;
	output wire desc_ar_valid;
	input wire desc_ar_ready;
	output wire [ADDR_WIDTH - 1:0] desc_ar_addr;
	output wire [7:0] desc_ar_len;
	output wire [2:0] desc_ar_size;
	output wire [1:0] desc_ar_burst;
	output wire [AXI_ID_WIDTH - 1:0] desc_ar_id;
	output wire desc_ar_lock;
	output wire [3:0] desc_ar_cache;
	output wire [2:0] desc_ar_prot;
	output wire [3:0] desc_ar_qos;
	output wire [3:0] desc_ar_region;
	input wire desc_r_valid;
	output wire desc_r_ready;
	input wire [255:0] desc_r_data;
	input wire [1:0] desc_r_resp;
	input wire desc_r_last;
	input wire [AXI_ID_WIDTH - 1:0] desc_r_id;
	output wire sched_rd_valid;
	output wire [ADDR_WIDTH - 1:0] sched_rd_addr;
	output wire [31:0] sched_rd_beats;
	output wire sched_wr_valid;
	input wire sched_wr_ready;
	output wire [ADDR_WIDTH - 1:0] sched_wr_addr;
	output wire [31:0] sched_wr_beats;
	input wire sched_rd_done_strobe;
	input wire [31:0] sched_rd_beats_done;
	input wire sched_wr_done_strobe;
	input wire [31:0] sched_wr_beats_done;
	input wire sched_rd_error;
	input wire sched_wr_error;
	output wire mon_valid;
	input wire mon_ready;
	output wire [63:0] mon_packet;
	wire desceng_to_sched_valid;
	wire desceng_to_sched_ready;
	wire [255:0] desceng_to_sched_packet;
	wire desceng_to_sched_error;
	wire desceng_to_sched_eos;
	wire desceng_to_sched_eol;
	wire desceng_to_sched_eod;
	wire [1:0] desceng_to_sched_type;
	wire sched_channel_idle;
	wire desceng_mon_valid;
	wire desceng_mon_ready;
	wire [63:0] desceng_mon_packet;
	wire sched_mon_valid;
	wire sched_mon_ready;
	wire [63:0] sched_mon_packet;
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	function automatic signed [3:0] sv2v_cast_4_signed;
		input reg signed [3:0] inp;
		sv2v_cast_4_signed = inp;
	endfunction
	function automatic signed [5:0] sv2v_cast_6_signed;
		input reg signed [5:0] inp;
		sv2v_cast_6_signed = inp;
	endfunction
	descriptor_engine #(
		.CHANNEL_ID(CHANNEL_ID),
		.NUM_CHANNELS(NUM_CHANNELS),
		.CHAN_WIDTH(CHAN_WIDTH),
		.ADDR_WIDTH(ADDR_WIDTH),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.MON_AGENT_ID(sv2v_cast_8_signed(DESC_MON_AGENT_ID)),
		.MON_UNIT_ID(sv2v_cast_4_signed(MON_UNIT_ID)),
		.MON_CHANNEL_ID(sv2v_cast_6_signed(MON_CHANNEL_ID))
	) u_descriptor_engine(
		.clk(clk),
		.rst_n(rst_n),
		.apb_valid(apb_valid),
		.apb_ready(apb_ready),
		.apb_addr(apb_addr),
		.channel_idle(sched_channel_idle),
		.descriptor_valid(desceng_to_sched_valid),
		.descriptor_ready(desceng_to_sched_ready),
		.descriptor_packet(desceng_to_sched_packet),
		.descriptor_error(desceng_to_sched_error),
		.descriptor_eos(desceng_to_sched_eos),
		.descriptor_eol(desceng_to_sched_eol),
		.descriptor_eod(desceng_to_sched_eod),
		.descriptor_type(desceng_to_sched_type),
		.ar_valid(desc_ar_valid),
		.ar_ready(desc_ar_ready),
		.ar_addr(desc_ar_addr),
		.ar_len(desc_ar_len),
		.ar_size(desc_ar_size),
		.ar_burst(desc_ar_burst),
		.ar_id(desc_ar_id),
		.ar_lock(desc_ar_lock),
		.ar_cache(desc_ar_cache),
		.ar_prot(desc_ar_prot),
		.ar_qos(desc_ar_qos),
		.ar_region(desc_ar_region),
		.r_valid(desc_r_valid),
		.r_ready(desc_r_ready),
		.r_data(desc_r_data),
		.r_resp(desc_r_resp),
		.r_last(desc_r_last),
		.r_id(desc_r_id),
		.cfg_prefetch_enable(cfg_desceng_prefetch),
		.cfg_fifo_threshold(cfg_desceng_fifo_thresh),
		.cfg_addr0_base(cfg_desceng_addr0_base),
		.cfg_addr0_limit(cfg_desceng_addr0_limit),
		.cfg_addr1_base(cfg_desceng_addr1_base),
		.cfg_addr1_limit(cfg_desceng_addr1_limit),
		.cfg_channel_reset(cfg_channel_reset),
		.descriptor_engine_idle(descriptor_engine_idle),
		.mon_valid(desceng_mon_valid),
		.mon_ready(desceng_mon_ready),
		.mon_packet(desceng_mon_packet)
	);
	scheduler #(
		.CHANNEL_ID(CHANNEL_ID),
		.NUM_CHANNELS(NUM_CHANNELS),
		.CHAN_WIDTH(CHAN_WIDTH),
		.ADDR_WIDTH(ADDR_WIDTH),
		.DATA_WIDTH(DATA_WIDTH),
		.MON_AGENT_ID(sv2v_cast_8_signed(SCHED_MON_AGENT_ID)),
		.MON_UNIT_ID(sv2v_cast_4_signed(MON_UNIT_ID)),
		.MON_CHANNEL_ID(sv2v_cast_6_signed(MON_CHANNEL_ID))
	) u_scheduler(
		.clk(clk),
		.rst_n(rst_n),
		.cfg_channel_enable(cfg_channel_enable),
		.cfg_channel_reset(cfg_channel_reset),
		.cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
		.cfg_sched_timeout_enable(cfg_sched_timeout_enable),
		.scheduler_idle(scheduler_idle),
		.scheduler_state(scheduler_state),
		.sched_error(sched_error),
		.descriptor_valid(desceng_to_sched_valid),
		.descriptor_ready(desceng_to_sched_ready),
		.descriptor_packet(desceng_to_sched_packet),
		.descriptor_error(desceng_to_sched_error),
		.sched_rd_valid(sched_rd_valid),
		.sched_rd_addr(sched_rd_addr),
		.sched_rd_beats(sched_rd_beats),
		.sched_wr_valid(sched_wr_valid),
		.sched_wr_ready(sched_wr_ready),
		.sched_wr_addr(sched_wr_addr),
		.sched_wr_beats(sched_wr_beats),
		.sched_rd_done_strobe(sched_rd_done_strobe),
		.sched_rd_beats_done(sched_rd_beats_done),
		.sched_wr_done_strobe(sched_wr_done_strobe),
		.sched_wr_beats_done(sched_wr_beats_done),
		.sched_rd_error(sched_rd_error),
		.sched_wr_error(sched_wr_error),
		.mon_valid(sched_mon_valid),
		.mon_ready(sched_mon_ready),
		.mon_packet(sched_mon_packet)
	);
	assign sched_channel_idle = scheduler_idle;
	monbus_arbiter #(
		.CLIENTS(2),
		.INPUT_SKID_ENABLE(1),
		.OUTPUT_SKID_ENABLE(1),
		.INPUT_SKID_DEPTH(2),
		.OUTPUT_SKID_DEPTH(2)
	) u_monbus_aggregator(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.block_arb(1'b0),
		.monbus_valid_in({desceng_mon_valid, sched_mon_valid}),
		.monbus_ready_in({desceng_mon_ready, sched_mon_ready}),
		.monbus_packet_in({desceng_mon_packet, sched_mon_packet}),
		.monbus_valid(mon_valid),
		.monbus_ready(mon_ready),
		.monbus_packet(mon_packet),
		.grant_valid(),
		.grant(),
		.grant_id(),
		.last_grant()
	);
endmodule
