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
module pwm (
	clk,
	rst_n,
	sync_rst_n,
	start,
	duty,
	period,
	repeat_count,
	done,
	pwm_out
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 8;
	parameter signed [31:0] CHANNELS = 4;
	input wire clk;
	input wire rst_n;
	input wire sync_rst_n;
	input wire [CHANNELS - 1:0] start;
	input wire [(CHANNELS * WIDTH) - 1:0] duty;
	input wire [(CHANNELS * WIDTH) - 1:0] period;
	input wire [(CHANNELS * WIDTH) - 1:0] repeat_count;
	output wire [CHANNELS - 1:0] done;
	output reg [CHANNELS - 1:0] pwm_out;
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < CHANNELS; _gv_i_2 = _gv_i_2 + 1) begin : gen_channel
			localparam i = _gv_i_2;
			localparam signed [31:0] EndIdx = ((i + 1) * WIDTH) - 1;
			reg [1:0] r_state;
			reg [WIDTH - 1:0] r_count;
			reg [WIDTH - 1:0] r_repeat_value;
			wire [WIDTH - 1:0] w_local_duty;
			wire [WIDTH - 1:0] w_local_period;
			wire [WIDTH - 1:0] w_local_repeat;
			assign w_local_duty = duty[EndIdx-:WIDTH];
			assign w_local_period = period[EndIdx-:WIDTH];
			assign w_local_repeat = repeat_count[EndIdx-:WIDTH];
			wire w_period_complete;
			wire w_all_repeats_done;
			wire w_start_edge;
			reg r_start_prev;
			always @(posedge clk or negedge rst_n)
				if (!rst_n)
					r_start_prev <= 1'b0;
				else if (!sync_rst_n)
					r_start_prev <= 1'b0;
				else
					r_start_prev <= start[i];
			assign w_start_edge = start[i] && !r_start_prev;
			assign w_period_complete = (r_count == (w_local_period - 1)) && (r_state == 2'b01);
			assign w_all_repeats_done = (w_local_repeat == 0 ? 1'b0 : r_repeat_value >= (w_local_repeat - 1'b1));
			always @(posedge clk or negedge rst_n)
				if (!rst_n)
					r_state <= 2'b00;
				else if (!sync_rst_n)
					r_state <= 2'b00;
				else
					case (r_state)
						2'b00:
							if (w_start_edge && (w_local_period > 0))
								r_state <= 2'b01;
						2'b01:
							if (w_period_complete && w_all_repeats_done)
								r_state <= 2'b10;
						2'b10:
							if (w_start_edge)
								r_state <= 2'b01;
						default: r_state <= 2'b00;
					endcase
			always @(posedge clk or negedge rst_n)
				if (!rst_n)
					r_count <= 1'sb0;
				else if (!sync_rst_n)
					r_count <= 1'sb0;
				else
					case (r_state)
						2'b00: r_count <= 1'sb0;
						2'b01:
							if (w_period_complete)
								r_count <= 1'sb0;
							else
								r_count <= r_count + 1;
						2'b10:
							if (w_start_edge)
								r_count <= 1'sb0;
						default: r_count <= 1'sb0;
					endcase
			always @(posedge clk or negedge rst_n)
				if (!rst_n)
					r_repeat_value <= 1'sb0;
				else if (!sync_rst_n)
					r_repeat_value <= 1'sb0;
				else
					case (r_state)
						2'b00: r_repeat_value <= 1'sb0;
						2'b01:
							if (w_period_complete)
								r_repeat_value <= r_repeat_value + 1;
						2'b10:
							if (w_start_edge)
								r_repeat_value <= 1'sb0;
						default: r_repeat_value <= 1'sb0;
					endcase
			always @(*) begin
				if (_sv2v_0)
					;
				case (r_state)
					2'b01:
						if (w_local_duty == 0)
							pwm_out[i] = 1'b0;
						else if (w_local_duty >= w_local_period)
							pwm_out[i] = 1'b1;
						else
							pwm_out[i] = r_count < w_local_duty;
					default: pwm_out[i] = 1'b0;
				endcase
			end
			assign done[i] = r_state == 2'b10;
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
module arbiter_monbus_common (
	clk,
	rst_n,
	cfg_max_thresh,
	request,
	grant_valid,
	grant,
	grant_id,
	grant_ack,
	block_arb,
	cfg_mon_enable,
	cfg_mon_pkt_type_enable,
	cfg_mon_latency_thresh,
	cfg_mon_starvation_thresh,
	cfg_mon_fairness_thresh,
	cfg_mon_active_thresh,
	cfg_mon_ack_timeout_thresh,
	cfg_mon_efficiency_thresh,
	cfg_mon_sample_period,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	debug_fifo_count,
	debug_packet_count,
	debug_ack_timeout,
	debug_protocol_violations,
	debug_grant_efficiency,
	debug_client_starvation,
	debug_fairness_deviation,
	debug_monitor_state
);
	reg _sv2v_0;
	parameter signed [31:0] CLIENTS = 4;
	parameter signed [31:0] WAIT_GNT_ACK = 0;
	parameter signed [31:0] WEIGHTED_MODE = 0;
	parameter [15:0] MON_AGENT_ID = 16'h0010;
	parameter [7:0] MON_UNIT_ID = 8'h00;
	parameter signed [31:0] MON_FIFO_DEPTH = 8;
	parameter signed [31:0] MON_FIFO_ALMOST_MARGIN = 1;
	parameter signed [31:0] FAIRNESS_REPORT_CYCLES = 256;
	parameter signed [31:0] MIN_GRANTS_FOR_FAIRNESS = 100;
	parameter signed [31:0] DEFAULT_ACK_TIMEOUT = 64;
	parameter signed [31:0] MON_FIFO_COUNT_WIDTH = $clog2(MON_FIFO_DEPTH + 1);
	parameter signed [31:0] N = $clog2(CLIENTS);
	parameter signed [31:0] MFCW = MON_FIFO_COUNT_WIDTH;
	parameter signed [31:0] MAX_LEVELS = 16;
	parameter signed [31:0] MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS);
	parameter signed [31:0] MTW = MAX_LEVELS_WIDTH;
	parameter signed [31:0] CXMTW = CLIENTS * MAX_LEVELS_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire [CXMTW - 1:0] cfg_max_thresh;
	input wire [CLIENTS - 1:0] request;
	input wire grant_valid;
	input wire [CLIENTS - 1:0] grant;
	input wire [N - 1:0] grant_id;
	input wire [CLIENTS - 1:0] grant_ack;
	input wire block_arb;
	input wire cfg_mon_enable;
	input wire [15:0] cfg_mon_pkt_type_enable;
	input wire [15:0] cfg_mon_latency_thresh;
	input wire [15:0] cfg_mon_starvation_thresh;
	input wire [15:0] cfg_mon_fairness_thresh;
	input wire [15:0] cfg_mon_active_thresh;
	input wire [15:0] cfg_mon_ack_timeout_thresh;
	input wire [15:0] cfg_mon_efficiency_thresh;
	input wire [7:0] cfg_mon_sample_period;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire [$clog2(MON_FIFO_DEPTH):0] debug_fifo_count;
	output wire [15:0] debug_packet_count;
	output wire [CLIENTS - 1:0] debug_ack_timeout;
	output wire [15:0] debug_protocol_violations;
	output wire [15:0] debug_grant_efficiency;
	output wire [CLIENTS - 1:0] debug_client_starvation;
	output wire [15:0] debug_fairness_deviation;
	output wire [2:0] debug_monitor_state;
	localparam signed [31:0] ACTIVE_COUNT_WIDTH = $clog2(CLIENTS + 1);
	wire w_starvation_detected;
	reg [N - 1:0] w_starvation_client;
	reg w_latency_threshold_detected;
	reg [N - 1:0] w_latency_threshold_client;
	wire w_active_threshold_detected;
	wire [$clog2(CLIENTS + 1) - 1:0] w_active_request_count;
	wire w_grant_event_detected;
	wire [N - 1:0] w_grant_client_id;
	wire w_ack_timeout_event_detected;
	reg [N - 1:0] w_ack_timeout_client;
	wire w_protocol_violation_detected;
	wire w_fairness_violation_detected;
	wire w_efficiency_threshold_detected;
	wire [15:0] w_current_efficiency;
	wire w_completion_event_detected;
	reg [N - 1:0] w_completion_client;
	wire [63 - ACTIVE_COUNT_WIDTH:0] w_evt_pad0;
	wire w_sample_event;
	wire [127:0] w_event_packet;
	wire w_event_valid;
	wire w_fifo_wr_valid;
	wire w_fifo_wr_ready;
	wire w_fifo_rd_ready;
	wire w_fifo_rd_valid;
	wire w_fifo_write_transfer;
	wire w_fifo_read_transfer;
	wire [$clog2(MON_FIFO_DEPTH):0] w_fifo_count;
	wire [127:0] w_fifo_data_out;
	reg [3:0] w_packet_pkt_type;
	reg [3:0] w_packet_protocol;
	reg [7:0] w_packet_event_code;
	reg [8:0] w_packet_channel_id;
	reg [7:0] w_packet_unit_id;
	reg [15:0] w_packet_agent_id;
	reg [63:0] w_packet_data;
	wire [3:0] w_packet_enum_protocol;
	reg [7:0] w_packet_enum_arb_error;
	reg [7:0] w_packet_enum_arb_timeout;
	reg [7:0] w_packet_enum_arb_completion;
	reg [7:0] w_packet_enum_arb_threshold;
	reg [7:0] w_packet_enum_arb_performance;
	wire w_packet_starvation_pkt_en;
	wire w_packet_ack_timeout_pkt_en;
	wire w_packet_latency_thresh_pkt_en;
	wire w_packet_fairness_violation_pkt_en;
	wire w_packet_efficiency_thresh_pkt_en;
	wire w_packet_active_thresh_pkt_en;
	wire w_packet_completion_pkt_en;
	wire w_packet_grant_perf_pkt_en;
	wire [7:0] w_packet_enable_mask;
	wire [127:0] w_packet_debug_fields;
	wire [MTW - 1:0] client_weight [0:CLIENTS - 1];
	genvar _gv_j_1;
	generate
		for (_gv_j_1 = 0; _gv_j_1 < CLIENTS; _gv_j_1 = _gv_j_1 + 1) begin : gen_weights
			localparam j = _gv_j_1;
			assign client_weight[j] = cfg_max_thresh[((j + 1) * MTW) - 1-:MTW];
		end
	endgenerate
	reg [15:0] r_total_grants;
	reg [15:0] r_total_completed_grants;
	reg [15:0] r_grant_counters [0:CLIENTS - 1];
	reg [15:0] r_completed_grants [0:CLIENTS - 1];
	reg [15:0] r_latency_counters [0:CLIENTS - 1];
	reg [15:0] r_starvation_counters [0:CLIENTS - 1];
	reg [CLIENTS - 1:0] r_starvation_detected;
	reg [15:0] r_protocol_violation_count;
	reg [15:0] r_debug_packet_count;
	reg [7:0] r_sample_timer;
	reg [15:0] r_fairness_timer;
	reg [15:0] r_max_fairness_deviation;
	reg [15:0] r_ack_timers [0:CLIENTS - 1];
	reg [CLIENTS - 1:0] r_ack_pending;
	reg [CLIENTS - 1:0] r_ack_timeout_detected;
	reg [2:0] r_monitor_state;
	reg r_starvation_event;
	reg [N - 1:0] r_starvation_client;
	reg r_latency_threshold_event;
	reg [N - 1:0] r_latency_client;
	reg r_active_threshold_event;
	reg r_grant_event;
	reg [N - 1:0] r_grant_client_id;
	reg r_ack_timeout_event;
	reg [N - 1:0] r_ack_timeout_client;
	reg r_protocol_violation_event;
	reg r_fairness_violation_event;
	reg r_efficiency_threshold_event;
	reg r_completion_event;
	reg [N - 1:0] r_completion_client;
	assign w_evt_pad0 = 1'sb0;
	assign w_starvation_detected = cfg_mon_enable && |r_starvation_detected;
	function automatic signed [N - 1:0] sv2v_cast_D80EA_signed;
		input reg signed [N - 1:0] inp;
		sv2v_cast_D80EA_signed = inp;
	endfunction
	always @(*) begin : sv2v_autoblock_1
		reg [0:1] _sv2v_jump;
		_sv2v_jump = 2'b00;
		if (_sv2v_0)
			;
		w_starvation_client = {N {1'b0}};
		if (cfg_mon_enable) begin : sv2v_autoblock_2
			reg signed [31:0] i;
			begin : sv2v_autoblock_3
				reg signed [31:0] _sv2v_value_on_break;
				for (i = 0; i < CLIENTS; i = i + 1)
					if (_sv2v_jump < 2'b10) begin
						_sv2v_jump = 2'b00;
						if (r_starvation_detected[i]) begin
							w_starvation_client = sv2v_cast_D80EA_signed(i);
							_sv2v_jump = 2'b10;
						end
						_sv2v_value_on_break = i;
					end
				if (!(_sv2v_jump < 2'b10))
					i = _sv2v_value_on_break;
				if (_sv2v_jump != 2'b11)
					_sv2v_jump = 2'b00;
			end
		end
	end
	always @(*) begin : sv2v_autoblock_4
		reg [0:1] _sv2v_jump;
		_sv2v_jump = 2'b00;
		if (_sv2v_0)
			;
		w_latency_threshold_detected = 1'b0;
		w_latency_threshold_client = {N {1'b0}};
		if (cfg_mon_enable) begin : sv2v_autoblock_5
			reg signed [31:0] i;
			begin : sv2v_autoblock_6
				reg signed [31:0] _sv2v_value_on_break;
				for (i = 0; i < CLIENTS; i = i + 1)
					if (_sv2v_jump < 2'b10) begin
						_sv2v_jump = 2'b00;
						if (r_latency_counters[i] >= cfg_mon_latency_thresh) begin
							w_latency_threshold_detected = 1'b1;
							w_latency_threshold_client = sv2v_cast_D80EA_signed(i);
							_sv2v_jump = 2'b10;
						end
						_sv2v_value_on_break = i;
					end
				if (!(_sv2v_jump < 2'b10))
					i = _sv2v_value_on_break;
				if (_sv2v_jump != 2'b11)
					_sv2v_jump = 2'b00;
			end
		end
	end
	assign w_active_request_count = $countones(request);
	assign w_active_threshold_detected = cfg_mon_enable && (w_active_request_count >= cfg_mon_active_thresh[$clog2(CLIENTS + 1) - 1:0]);
	assign w_grant_event_detected = (cfg_mon_enable && grant_valid) && |grant;
	assign w_grant_client_id = grant_id;
	assign w_ack_timeout_event_detected = cfg_mon_enable && |r_ack_timeout_detected;
	always @(*) begin : sv2v_autoblock_7
		reg [0:1] _sv2v_jump;
		_sv2v_jump = 2'b00;
		if (_sv2v_0)
			;
		w_ack_timeout_client = {N {1'b0}};
		if (cfg_mon_enable) begin : sv2v_autoblock_8
			reg signed [31:0] i;
			begin : sv2v_autoblock_9
				reg signed [31:0] _sv2v_value_on_break;
				for (i = 0; i < CLIENTS; i = i + 1)
					if (_sv2v_jump < 2'b10) begin
						_sv2v_jump = 2'b00;
						if (r_ack_timeout_detected[i]) begin
							w_ack_timeout_client = sv2v_cast_D80EA_signed(i);
							_sv2v_jump = 2'b10;
						end
						_sv2v_value_on_break = i;
					end
				if (!(_sv2v_jump < 2'b10))
					i = _sv2v_value_on_break;
				if (_sv2v_jump != 2'b11)
					_sv2v_jump = 2'b00;
			end
		end
	end
	wire w_multiple_grants;
	wire w_spurious_ack;
	wire w_grant_without_request;
	assign w_multiple_grants = grant_valid && ($countones(grant) > 1);
	assign w_spurious_ack = (WAIT_GNT_ACK == 1 ? |grant_ack && ((grant_ack & r_ack_pending) != grant_ack) : 1'b0);
	assign w_grant_without_request = grant_valid && ((grant & request) != grant);
	assign w_protocol_violation_detected = cfg_mon_enable && ((w_multiple_grants || w_spurious_ack) || w_grant_without_request);
	assign w_fairness_violation_detected = cfg_mon_enable && (r_max_fairness_deviation >= cfg_mon_fairness_thresh);
	wire [31:0] w_efficiency_raw_calc;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	assign w_efficiency_raw_calc = (r_total_grants > 0 ? (sv2v_cast_32(r_total_completed_grants) * 32'd100) / sv2v_cast_32(r_total_grants) : 32'd100);
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	assign w_current_efficiency = (w_efficiency_raw_calc > 32'd100 ? 16'd100 : sv2v_cast_16(w_efficiency_raw_calc));
	assign w_efficiency_threshold_detected = cfg_mon_enable && (w_current_efficiency < cfg_mon_efficiency_thresh);
	assign w_completion_event_detected = cfg_mon_enable && (WAIT_GNT_ACK == 0 ? grant_valid && |grant : |grant_ack);
	always @(*) begin : sv2v_autoblock_10
		reg [0:1] _sv2v_jump;
		_sv2v_jump = 2'b00;
		if (_sv2v_0)
			;
		w_completion_client = {N {1'b0}};
		if (cfg_mon_enable) begin
			if (WAIT_GNT_ACK == 0)
				w_completion_client = grant_id;
			else begin : sv2v_autoblock_11
				reg signed [31:0] i;
				begin : sv2v_autoblock_12
					reg signed [31:0] _sv2v_value_on_break;
					for (i = 0; i < CLIENTS; i = i + 1)
						if (_sv2v_jump < 2'b10) begin
							_sv2v_jump = 2'b00;
							if (grant_ack[i]) begin
								w_completion_client = sv2v_cast_D80EA_signed(i);
								_sv2v_jump = 2'b10;
							end
							_sv2v_value_on_break = i;
						end
					if (!(_sv2v_jump < 2'b10))
						i = _sv2v_value_on_break;
					if (_sv2v_jump != 2'b11)
						_sv2v_jump = 2'b00;
				end
			end
		end
	end
	generate
		if (WAIT_GNT_ACK == 1) begin : gen_ack_monitoring
			always @(posedge clk or negedge rst_n)
				if (!rst_n) begin : sv2v_autoblock_13
					reg signed [31:0] i;
					for (i = 0; i < CLIENTS; i = i + 1)
						begin
							r_ack_timers[i] <= 16'h0000;
							r_ack_pending[i] <= 1'b0;
							r_ack_timeout_detected[i] <= 1'b0;
						end
				end
				else begin : sv2v_autoblock_14
					reg signed [31:0] i;
					for (i = 0; i < CLIENTS; i = i + 1)
						if (grant_valid && grant[i]) begin
							r_ack_pending[i] <= 1'b1;
							r_ack_timers[i] <= 16'h0000;
							r_ack_timeout_detected[i] <= 1'b0;
						end
						else if (r_ack_pending[i] && grant_ack[i]) begin
							r_ack_pending[i] <= 1'b0;
							r_ack_timers[i] <= 16'h0000;
							r_ack_timeout_detected[i] <= 1'b0;
						end
						else if (r_ack_pending[i]) begin
							r_ack_timers[i] <= r_ack_timers[i] + 16'h0001;
							if (r_ack_timers[i] >= cfg_mon_ack_timeout_thresh) begin
								r_ack_timeout_detected[i] <= 1'b1;
								r_ack_pending[i] <= 1'b0;
							end
						end
				end
		end
		else begin : gen_no_ack_monitoring
			always @(*) begin
				if (_sv2v_0)
					;
				begin : sv2v_autoblock_15
					reg signed [31:0] i;
					for (i = 0; i < CLIENTS; i = i + 1)
						begin
							r_ack_timers[i] = 16'h0000;
							r_ack_pending[i] = 1'b0;
							r_ack_timeout_detected[i] = 1'b0;
						end
				end
			end
		end
	endgenerate
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_monitor_state <= 3'b000;
		else
			case (r_monitor_state)
				3'b000:
					if (cfg_mon_enable)
						r_monitor_state <= 3'b001;
				3'b001:
					if (!cfg_mon_enable)
						r_monitor_state <= 3'b000;
					else if (w_sample_event)
						r_monitor_state <= 3'b010;
				3'b010: r_monitor_state <= 3'b011;
				3'b011: r_monitor_state <= 3'b100;
				3'b100: r_monitor_state <= 3'b001;
				3'b101:
					if (cfg_mon_enable)
						r_monitor_state <= 3'b001;
					else
						r_monitor_state <= 3'b000;
				default: r_monitor_state <= 3'b000;
			endcase
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_total_grants <= 16'h0000;
			r_total_completed_grants <= 16'h0000;
			begin : sv2v_autoblock_16
				reg signed [31:0] i;
				for (i = 0; i < CLIENTS; i = i + 1)
					begin
						r_grant_counters[i] <= 16'h0000;
						r_completed_grants[i] <= 16'h0000;
					end
			end
		end
		else begin
			if (grant_valid && |grant) begin
				r_total_grants <= r_total_grants + 16'h0001;
				begin : sv2v_autoblock_17
					reg signed [31:0] i;
					for (i = 0; i < CLIENTS; i = i + 1)
						if (grant[i])
							r_grant_counters[i] <= r_grant_counters[i] + 16'h0001;
				end
			end
			if (WAIT_GNT_ACK == 0) begin
				if (grant_valid && |grant) begin
					r_total_completed_grants <= r_total_completed_grants + 16'h0001;
					begin : sv2v_autoblock_18
						reg signed [31:0] i;
						for (i = 0; i < CLIENTS; i = i + 1)
							if (grant[i])
								r_completed_grants[i] <= r_completed_grants[i] + 16'h0001;
					end
				end
			end
			else if (|grant_ack) begin
				r_total_completed_grants <= r_total_completed_grants + 16'h0001;
				begin : sv2v_autoblock_19
					reg signed [31:0] i;
					for (i = 0; i < CLIENTS; i = i + 1)
						if (grant_ack[i])
							r_completed_grants[i] <= r_completed_grants[i] + 16'h0001;
				end
			end
		end
	reg [15:0] max_deviation_temp;
	reg [15:0] total_weight;
	function automatic signed [15:0] sv2v_cast_16_signed;
		input reg signed [15:0] inp;
		sv2v_cast_16_signed = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_fairness_timer <= 16'h0000;
			r_max_fairness_deviation <= 16'h0000;
		end
		else begin
			r_fairness_timer <= r_fairness_timer + 16'h0001;
			if (r_fairness_timer >= sv2v_cast_16_signed(FAIRNESS_REPORT_CYCLES)) begin
				r_fairness_timer <= 16'h0000;
				if (r_total_grants >= sv2v_cast_16_signed(MIN_GRANTS_FOR_FAIRNESS)) begin
					max_deviation_temp = 16'h0000;
					total_weight = 16'h0000;
					begin : sv2v_autoblock_20
						reg signed [31:0] j;
						for (j = 0; j < CLIENTS; j = j + 1)
							if (client_weight[j] > 0)
								total_weight = total_weight + sv2v_cast_16(client_weight[j]);
					end
					begin : sv2v_autoblock_21
						reg signed [31:0] i;
						for (i = 0; i < CLIENTS; i = i + 1)
							if ((total_weight > 0) && (client_weight[i] > 0)) begin : sv2v_autoblock_22
								reg [15:0] expected_percentage;
								reg [15:0] actual_percentage;
								reg [15:0] deviation;
								expected_percentage = (sv2v_cast_16(client_weight[i]) * 100) / total_weight;
								actual_percentage = (r_grant_counters[i] * 100) / r_total_grants;
								if (actual_percentage >= expected_percentage)
									deviation = actual_percentage - expected_percentage;
								else
									deviation = expected_percentage - actual_percentage;
								if (deviation > max_deviation_temp)
									max_deviation_temp = deviation;
							end
					end
					r_max_fairness_deviation <= max_deviation_temp;
				end
			end
		end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			begin : sv2v_autoblock_23
				reg signed [31:0] i;
				for (i = 0; i < CLIENTS; i = i + 1)
					begin
						r_latency_counters[i] <= 16'h0000;
						r_starvation_counters[i] <= 16'h0000;
					end
			end
			r_starvation_detected <= {CLIENTS {1'b0}};
		end
		else begin : sv2v_autoblock_24
			reg signed [31:0] i;
			for (i = 0; i < CLIENTS; i = i + 1)
				if (request[i] && !grant[i]) begin
					r_latency_counters[i] <= r_latency_counters[i] + 16'h0001;
					r_starvation_counters[i] <= r_starvation_counters[i] + 16'h0001;
					if (r_starvation_counters[i] >= cfg_mon_starvation_thresh)
						r_starvation_detected[i] <= 1'b1;
				end
				else if (grant[i]) begin
					r_latency_counters[i] <= 16'h0000;
					r_starvation_counters[i] <= 16'h0000;
					r_starvation_detected[i] <= 1'b0;
				end
		end
	assign w_sample_event = r_sample_timer == cfg_mon_sample_period;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_sample_timer <= 8'h00;
		else if (w_sample_event)
			r_sample_timer <= 8'h00;
		else
			r_sample_timer <= r_sample_timer + 8'h01;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_starvation_event <= 1'b0;
			r_starvation_client <= {N {1'b0}};
			r_latency_threshold_event <= 1'b0;
			r_latency_client <= {N {1'b0}};
			r_active_threshold_event <= 1'b0;
			r_grant_event <= 1'b0;
			r_grant_client_id <= {N {1'b0}};
			r_ack_timeout_event <= 1'b0;
			r_ack_timeout_client <= {N {1'b0}};
			r_protocol_violation_event <= 1'b0;
			r_fairness_violation_event <= 1'b0;
			r_efficiency_threshold_event <= 1'b0;
			r_completion_event <= 1'b0;
			r_completion_client <= {N {1'b0}};
		end
		else begin
			r_starvation_event <= w_starvation_detected;
			r_starvation_client <= w_starvation_client;
			r_latency_threshold_event <= w_latency_threshold_detected;
			r_latency_client <= w_latency_threshold_client;
			r_active_threshold_event <= w_active_threshold_detected;
			r_grant_event <= w_grant_event_detected;
			r_grant_client_id <= w_grant_client_id;
			r_ack_timeout_event <= w_ack_timeout_event_detected;
			r_ack_timeout_client <= w_ack_timeout_client;
			r_protocol_violation_event <= w_protocol_violation_detected;
			r_fairness_violation_event <= w_fairness_violation_detected;
			r_efficiency_threshold_event <= w_efficiency_threshold_detected;
			r_completion_event <= w_completion_event_detected;
			r_completion_client <= w_completion_client;
		end
	assign w_packet_enum_protocol = w_packet_protocol;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	always @(*) begin
		if (_sv2v_0)
			;
		w_packet_enum_arb_error = 8'h00;
		w_packet_enum_arb_timeout = 8'h00;
		w_packet_enum_arb_completion = 8'h00;
		w_packet_enum_arb_threshold = 8'h00;
		w_packet_enum_arb_performance = 8'h00;
		case (w_packet_pkt_type)
			monitor_common_pkg_PktTypeError: w_packet_enum_arb_error = w_packet_event_code;
			monitor_common_pkg_PktTypeTimeout: w_packet_enum_arb_timeout = w_packet_event_code;
			monitor_common_pkg_PktTypeCompletion: w_packet_enum_arb_completion = w_packet_event_code;
			monitor_common_pkg_PktTypeThreshold: w_packet_enum_arb_threshold = w_packet_event_code;
			monitor_common_pkg_PktTypePerf: w_packet_enum_arb_performance = w_packet_event_code;
			default:
				;
		endcase
	end
	assign w_packet_starvation_pkt_en = r_starvation_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypeError];
	assign w_packet_ack_timeout_pkt_en = r_ack_timeout_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypeTimeout];
	assign w_packet_latency_thresh_pkt_en = r_latency_threshold_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypeThreshold];
	assign w_packet_fairness_violation_pkt_en = r_fairness_violation_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypeThreshold];
	assign w_packet_efficiency_thresh_pkt_en = r_efficiency_threshold_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypeThreshold];
	assign w_packet_active_thresh_pkt_en = r_active_threshold_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypeThreshold];
	assign w_packet_completion_pkt_en = r_completion_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypeCompletion];
	assign w_packet_grant_perf_pkt_en = r_grant_event && cfg_mon_pkt_type_enable[monitor_common_pkg_PktTypePerf];
	assign w_event_valid = ((((((w_packet_starvation_pkt_en || w_packet_ack_timeout_pkt_en) || w_packet_latency_thresh_pkt_en) || w_packet_fairness_violation_pkt_en) || w_packet_efficiency_thresh_pkt_en) || w_packet_active_thresh_pkt_en) || w_packet_completion_pkt_en) || w_packet_grant_perf_pkt_en;
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_packet_pkt_type = 4'h0;
		w_packet_protocol = 4'h3;
		w_packet_event_code = 8'h00;
		w_packet_channel_id = 9'h000;
		w_packet_unit_id = MON_UNIT_ID;
		w_packet_agent_id = MON_AGENT_ID;
		w_packet_data = 64'h0000000000000000;
		if (w_packet_starvation_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypeError;
			w_packet_event_code = 8'h00;
			w_packet_channel_id = sv2v_cast_9(r_starvation_client);
			w_packet_data = sv2v_cast_64(r_starvation_counters[r_starvation_client]);
		end
		else if (w_packet_ack_timeout_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypeTimeout;
			w_packet_event_code = 8'h00;
			w_packet_channel_id = sv2v_cast_9(r_ack_timeout_client);
			w_packet_data = sv2v_cast_64(r_ack_timers[r_ack_timeout_client]);
		end
		else if (w_packet_latency_thresh_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypeThreshold;
			w_packet_event_code = 8'h00;
			w_packet_channel_id = sv2v_cast_9(r_latency_client);
			w_packet_data = sv2v_cast_64(r_latency_counters[r_latency_client]);
		end
		else if (w_packet_fairness_violation_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypeThreshold;
			w_packet_event_code = 8'h02;
			w_packet_channel_id = 9'h000;
			w_packet_data = sv2v_cast_64(r_max_fairness_deviation);
		end
		else if (w_packet_efficiency_thresh_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypeThreshold;
			w_packet_event_code = 8'h05;
			w_packet_channel_id = 9'h000;
			w_packet_data = sv2v_cast_64(w_current_efficiency);
		end
		else if (w_packet_active_thresh_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypeThreshold;
			w_packet_event_code = 8'h03;
			w_packet_channel_id = 9'h000;
			w_packet_data = sv2v_cast_64(w_active_request_count);
		end
		else if (w_packet_completion_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypeCompletion;
			w_packet_event_code = 8'h02;
			w_packet_channel_id = sv2v_cast_9(r_completion_client);
			w_packet_data = sv2v_cast_64(r_completed_grants[r_completion_client]);
		end
		else if (w_packet_grant_perf_pkt_en) begin
			w_packet_pkt_type = monitor_common_pkg_PktTypePerf;
			w_packet_event_code = 8'h00;
			w_packet_channel_id = sv2v_cast_9(r_grant_client_id);
			w_packet_data = sv2v_cast_64(r_grant_counters[r_grant_client_id]);
		end
	end
	function automatic [127:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [3:0] protocol;
		input reg [7:0] event_code;
		input reg [8:0] channel_id;
		input reg [7:0] unit_id;
		input reg [15:0] agent_id;
		input reg [63:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, 15'h0000, protocol, event_code, channel_id, agent_id, unit_id, event_data};
	endfunction
	assign w_event_packet = monitor_common_pkg_create_monitor_packet(w_packet_pkt_type, w_packet_protocol, w_packet_event_code, w_packet_channel_id, w_packet_unit_id, w_packet_agent_id, w_packet_data);
	assign w_packet_debug_fields = {w_packet_pkt_type, 15'h0000, w_packet_protocol, w_packet_event_code, w_packet_channel_id, w_packet_agent_id, w_packet_unit_id, w_packet_data};
	assign w_packet_enable_mask = {w_packet_grant_perf_pkt_en, w_packet_completion_pkt_en, w_packet_active_thresh_pkt_en, w_packet_efficiency_thresh_pkt_en, w_packet_fairness_violation_pkt_en, w_packet_latency_thresh_pkt_en, w_packet_ack_timeout_pkt_en, w_packet_starvation_pkt_en};
	assign w_fifo_wr_valid = w_event_valid;
	assign w_fifo_rd_ready = monbus_ready;
	assign w_fifo_write_transfer = w_fifo_wr_valid & w_fifo_wr_ready;
	assign w_fifo_read_transfer = w_fifo_rd_valid & w_fifo_rd_ready;
	gaxi_fifo_sync #(
		.REGISTERED(0),
		.DATA_WIDTH(monitor_common_pkg_MONBUS_PKT_WIDTH),
		.DEPTH(MON_FIFO_DEPTH),
		.ALMOST_WR_MARGIN(MON_FIFO_ALMOST_MARGIN),
		.ALMOST_RD_MARGIN(MON_FIFO_ALMOST_MARGIN)
	) u_event_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_fifo_wr_valid),
		.wr_ready(w_fifo_wr_ready),
		.wr_data(w_event_packet),
		.rd_ready(w_fifo_rd_ready),
		.rd_valid(w_fifo_rd_valid),
		.rd_data(w_fifo_data_out),
		.count(w_fifo_count)
	);
	assign monbus_valid = w_fifo_rd_valid;
	assign monbus_packet = w_fifo_data_out;
	assign monbus_timestamp = i_mon_time;
	assign debug_fifo_count = w_fifo_count;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_debug_packet_count <= 16'h0000;
		else if (w_fifo_write_transfer)
			r_debug_packet_count <= r_debug_packet_count + 16'h0001;
	assign debug_packet_count = r_debug_packet_count;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_protocol_violation_count <= 16'h0000;
		else if ((w_protocol_violation_detected && !r_protocol_violation_event) && (r_protocol_violation_count != 16'hffff))
			r_protocol_violation_count <= r_protocol_violation_count + 16'h0001;
	assign debug_ack_timeout = r_ack_timeout_detected;
	assign debug_protocol_violations = r_protocol_violation_count;
	assign debug_grant_efficiency = w_current_efficiency;
	assign debug_client_starvation = r_starvation_detected;
	assign debug_fairness_deviation = r_max_fairness_deviation;
	assign debug_monitor_state = r_monitor_state;
	reg [15:0] w_debug_total_weight;
	reg [15:0] w_debug_expected_percentage [0:CLIENTS - 1];
	reg [15:0] w_debug_actual_percentage [0:CLIENTS - 1];
	always @(*) begin
		if (_sv2v_0)
			;
		w_debug_total_weight = 16'h0000;
		begin : sv2v_autoblock_25
			reg signed [31:0] i;
			for (i = 0; i < CLIENTS; i = i + 1)
				if (client_weight[i] > 0)
					w_debug_total_weight = w_debug_total_weight + sv2v_cast_16(client_weight[i]);
		end
	end
	genvar _gv_i_3;
	generate
		for (_gv_i_3 = 0; _gv_i_3 < CLIENTS; _gv_i_3 = _gv_i_3 + 1) begin : gen_debug_percentages
			localparam i = _gv_i_3;
			always @(*) begin
				if (_sv2v_0)
					;
				if ((w_debug_total_weight > 0) && (client_weight[i] > 0))
					w_debug_expected_percentage[i] = (sv2v_cast_16(client_weight[i]) * 100) / w_debug_total_weight;
				else
					w_debug_expected_percentage[i] = 16'h0000;
				if (r_total_grants > 0)
					w_debug_actual_percentage[i] = (r_grant_counters[i] * 100) / r_total_grants;
				else
					w_debug_actual_percentage[i] = 16'h0000;
			end
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module arbiter_rr_pwm_monbus (
	clk,
	rst_n,
	request,
	grant_valid,
	grant,
	grant_id,
	grant_ack,
	cfg_pwm_sync_rst_n,
	cfg_pwm_start,
	cfg_pwm_duty,
	cfg_pwm_period,
	cfg_pwm_repeat_count,
	cfg_pwm_sts_done,
	pwm_out,
	cfg_mon_enable,
	cfg_mon_pkt_type_enable,
	cfg_mon_latency,
	cfg_mon_starvation,
	cfg_mon_fairness,
	cfg_mon_active,
	cfg_mon_period,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	debug_fifo_count,
	debug_packet_count
);
	parameter [0:0] USE_MONITOR = 1'b1;
	parameter signed [31:0] CLIENTS = 4;
	parameter signed [31:0] WAIT_GNT_ACK = 0;
	parameter [15:0] MON_AGENT_ID = 16'h0010;
	parameter [7:0] MON_UNIT_ID = 8'h00;
	localparam signed [31:0] MAX_LEVELS = 16;
	localparam signed [31:0] MAX_LEVELS_WIDTH = 4;
	localparam signed [31:0] CXMTW = CLIENTS * MAX_LEVELS_WIDTH;
	localparam signed [31:0] PWM_WIDTH = 16;
	localparam signed [31:0] MON_FIFO_DEPTH = 16;
	localparam signed [31:0] MON_FIFO_ALMOST_MARGIN = 2;
	localparam signed [31:0] FAIRNESS_REPORT_CYCLES = 256;
	localparam signed [31:0] MIN_GRANTS_FOR_FAIRNESS = 64;
	parameter signed [31:0] N = $clog2(CLIENTS);
	input wire clk;
	input wire rst_n;
	input wire [CLIENTS - 1:0] request;
	output wire grant_valid;
	output wire [CLIENTS - 1:0] grant;
	output wire [N - 1:0] grant_id;
	input wire [CLIENTS - 1:0] grant_ack;
	input wire cfg_pwm_sync_rst_n;
	input wire cfg_pwm_start;
	input wire [15:0] cfg_pwm_duty;
	input wire [15:0] cfg_pwm_period;
	input wire [15:0] cfg_pwm_repeat_count;
	output wire cfg_pwm_sts_done;
	output wire pwm_out;
	input wire cfg_mon_enable;
	input wire [15:0] cfg_mon_pkt_type_enable;
	input wire [15:0] cfg_mon_latency;
	input wire [15:0] cfg_mon_starvation;
	input wire [15:0] cfg_mon_fairness;
	input wire [15:0] cfg_mon_active;
	input wire [7:0] cfg_mon_period;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire [4:0] debug_fifo_count;
	output wire [15:0] debug_packet_count;
	wire block_arb_internal;
	assign block_arb_internal = pwm_out;
	arbiter_round_robin #(
		.CLIENTS(CLIENTS),
		.WAIT_GNT_ACK(WAIT_GNT_ACK)
	) u_arbiter(
		.clk(clk),
		.rst_n(rst_n),
		.block_arb(block_arb_internal),
		.request(request),
		.grant_ack(grant_ack),
		.grant_valid(grant_valid),
		.grant(grant),
		.grant_id(grant_id),
		.last_grant()
	);
	pwm #(
		.WIDTH(PWM_WIDTH),
		.CHANNELS(1)
	) u_pwm(
		.clk(clk),
		.rst_n(rst_n),
		.sync_rst_n(cfg_pwm_sync_rst_n),
		.start(cfg_pwm_start),
		.duty(cfg_pwm_duty),
		.period(cfg_pwm_period),
		.repeat_count(cfg_pwm_repeat_count),
		.done(cfg_pwm_sts_done),
		.pwm_out(pwm_out)
	);
	function automatic signed [3:0] sv2v_cast_FD2F2_signed;
		input reg signed [3:0] inp;
		sv2v_cast_FD2F2_signed = inp;
	endfunction
	generate
		if (USE_MONITOR) begin : gen_monitor
			arbiter_monbus_common #(
				.CLIENTS(CLIENTS),
				.WAIT_GNT_ACK(WAIT_GNT_ACK),
				.MON_AGENT_ID(MON_AGENT_ID),
				.MON_UNIT_ID(MON_UNIT_ID),
				.MON_FIFO_DEPTH(MON_FIFO_DEPTH),
				.MON_FIFO_ALMOST_MARGIN(MON_FIFO_ALMOST_MARGIN),
				.FAIRNESS_REPORT_CYCLES(FAIRNESS_REPORT_CYCLES),
				.MIN_GRANTS_FOR_FAIRNESS(MIN_GRANTS_FOR_FAIRNESS)
			) u_monitor(
				.clk(clk),
				.rst_n(rst_n),
				.cfg_max_thresh({CLIENTS {sv2v_cast_FD2F2_signed(1)}}),
				.request(request),
				.grant_valid(grant_valid),
				.grant(grant),
				.grant_id(grant_id),
				.grant_ack(grant_ack),
				.block_arb(block_arb_internal),
				.cfg_mon_enable(cfg_mon_enable),
				.cfg_mon_pkt_type_enable(cfg_mon_pkt_type_enable),
				.cfg_mon_latency_thresh(cfg_mon_latency),
				.cfg_mon_starvation_thresh(cfg_mon_starvation),
				.cfg_mon_fairness_thresh(cfg_mon_fairness),
				.cfg_mon_active_thresh(cfg_mon_active),
				.cfg_mon_ack_timeout_thresh(16'h0040),
				.cfg_mon_efficiency_thresh(16'h0050),
				.cfg_mon_sample_period(cfg_mon_period),
				.i_mon_time(i_mon_time),
				.monbus_valid(monbus_valid),
				.monbus_ready(monbus_ready),
				.monbus_packet(monbus_packet),
				.monbus_timestamp(monbus_timestamp),
				.debug_fifo_count(debug_fifo_count),
				.debug_packet_count(debug_packet_count),
				.debug_ack_timeout(),
				.debug_protocol_violations(),
				.debug_grant_efficiency(),
				.debug_client_starvation(),
				.debug_fairness_deviation(),
				.debug_monitor_state()
			);
		end
		else begin : gen_no_monitor
			assign monbus_valid = 1'b0;
			assign monbus_packet = 1'sb0;
			assign monbus_timestamp = 1'sb0;
			assign debug_fifo_count = 1'sb0;
			assign debug_packet_count = 16'h0000;
		end
	endgenerate
endmodule
