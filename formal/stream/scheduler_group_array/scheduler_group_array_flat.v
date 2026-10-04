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
module counter_load_clear (
	clk,
	rst_n,
	clear,
	increment,
	load,
	loadval,
	count,
	done
);
	parameter signed [31:0] MAX = 32'd32;
	input wire clk;
	input wire rst_n;
	input wire clear;
	input wire increment;
	input wire load;
	input wire [$clog2(MAX) - 1:0] loadval;
	output reg [$clog2(MAX) - 1:0] count;
	output wire done;
	reg [$clog2(MAX) - 1:0] r_match_val;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			count <= 'b0;
			r_match_val <= 'b0;
		end
		else begin
			if (load)
				r_match_val <= loadval;
			if (clear)
				count <= 'b0;
			else if (increment)
				count <= (count == r_match_val ? 'b0 : count + 'b1);
		end
	assign done = count == r_match_val;
endmodule
module counter_freq_invariant (
	clk,
	rst_n,
	sync_reset_n,
	freq_sel,
	o_counter,
	tick
);
	parameter signed [31:0] COUNTER_WIDTH = 16;
	parameter signed [31:0] MIN_FREQ_MHZ = 5;
	parameter signed [31:0] MAX_FREQ_MHZ = 220;
	parameter signed [31:0] NUM_FREQ_ENTRIES = 16;
	parameter signed [31:0] FREQ_STRATEGY = 0;
	parameter [0:0] DEBUG_LUT = 1'b0;
	parameter signed [31:0] SEL_WIDTH = (NUM_FREQ_ENTRIES > 1 ? $clog2(NUM_FREQ_ENTRIES) : 1);
	parameter signed [31:0] DIV_WIDTH = $clog2(MAX_FREQ_MHZ + 1);
	parameter signed [31:0] PRESCALER_MAX = 2 ** DIV_WIDTH;
	input wire clk;
	input wire rst_n;
	input wire sync_reset_n;
	input wire [SEL_WIDTH - 1:0] freq_sel;
	output reg [COUNTER_WIDTH - 1:0] o_counter;
	output reg tick;
	initial begin : param_check
		if (MIN_FREQ_MHZ < 1)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/rtl/common/counter_freq_invariant.sv:128:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MIN_FREQ_MHZ must be >= 1 (got %0d)", MIN_FREQ_MHZ);
		if (MAX_FREQ_MHZ < MIN_FREQ_MHZ)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/rtl/common/counter_freq_invariant.sv:130:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MAX_FREQ_MHZ (%0d) < MIN_FREQ_MHZ (%0d)", MAX_FREQ_MHZ, MIN_FREQ_MHZ);
		if (NUM_FREQ_ENTRIES < 1)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/rtl/common/counter_freq_invariant.sv:133:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: NUM_FREQ_ENTRIES must be >= 1 (got %0d)", NUM_FREQ_ENTRIES);
	end
	function automatic signed [31:0] linear_freq;
		input reg signed [31:0] idx;
		input reg signed [31:0] n;
		input reg signed [31:0] lo;
		input reg signed [31:0] hi;
		reg [0:1] _sv2v_jump;
		begin
			_sv2v_jump = 2'b00;
			if (n <= 1) begin
				linear_freq = lo;
				_sv2v_jump = 2'b11;
			end
			if (_sv2v_jump == 2'b00) begin
				linear_freq = lo + (((hi - lo) * idx) / (n - 1));
				_sv2v_jump = 2'b11;
			end
		end
	endfunction
	function automatic signed [31:0] pow2_freq;
		input reg signed [31:0] idx;
		input reg signed [31:0] n;
		input reg signed [31:0] lo;
		input reg signed [31:0] hi;
		reg signed [31:0] v;
		reg [0:1] _sv2v_jump;
		begin
			_sv2v_jump = 2'b00;
			v = lo;
			begin : sv2v_autoblock_1
				reg signed [31:0] k;
				begin : sv2v_autoblock_2
					reg signed [31:0] _sv2v_value_on_break;
					for (k = 0; k < idx; k = k + 1)
						if (_sv2v_jump < 2'b10) begin
							_sv2v_jump = 2'b00;
							if (v >= hi) begin
								pow2_freq = hi;
								_sv2v_jump = 2'b11;
							end
							if (_sv2v_jump == 2'b00)
								v = v * 2;
							_sv2v_value_on_break = k;
						end
					if (!(_sv2v_jump < 2'b10))
						k = _sv2v_value_on_break;
					if (_sv2v_jump != 2'b11)
						_sv2v_jump = 2'b00;
				end
			end
			if (_sv2v_jump == 2'b00) begin
				if (v > hi)
					v = hi;
				pow2_freq = v;
				_sv2v_jump = 2'b11;
			end
		end
	endfunction
	function automatic signed [31:0] freq_mhz_at_idx;
		input reg signed [31:0] idx;
		case (FREQ_STRATEGY)
			1: freq_mhz_at_idx = pow2_freq(idx, NUM_FREQ_ENTRIES, MIN_FREQ_MHZ, MAX_FREQ_MHZ);
			default: freq_mhz_at_idx = linear_freq(idx, NUM_FREQ_ENTRIES, MIN_FREQ_MHZ, MAX_FREQ_MHZ);
		endcase
	endfunction
	wire [DIV_WIDTH - 1:0] w_div_table [0:NUM_FREQ_ENTRIES - 1];
	genvar _gv_gi_1;
	function automatic signed [DIV_WIDTH - 1:0] sv2v_cast_DC41E_signed;
		input reg signed [DIV_WIDTH - 1:0] inp;
		sv2v_cast_DC41E_signed = inp;
	endfunction
	generate
		for (_gv_gi_1 = 0; _gv_gi_1 < NUM_FREQ_ENTRIES; _gv_gi_1 = _gv_gi_1 + 1) begin : gen_div_entry
			localparam gi = _gv_gi_1;
			assign w_div_table[gi] = sv2v_cast_DC41E_signed(freq_mhz_at_idx(gi));
		end
	endgenerate
	wire [DIV_WIDTH - 1:0] w_division_factor;
	assign w_division_factor = w_div_table[freq_sel];
	reg [SEL_WIDTH - 1:0] r_prev_freq_sel;
	reg r_clear_pulse;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_prev_freq_sel <= 1'sb0;
			r_clear_pulse <= 1'b1;
		end
		else begin
			r_prev_freq_sel <= freq_sel;
			r_clear_pulse <= (freq_sel != r_prev_freq_sel) || !sync_reset_n;
		end
	wire w_prescaler_done;
	counter_load_clear #(.MAX(PRESCALER_MAX)) prescaler_counter(
		.clk(clk),
		.rst_n(rst_n),
		.clear(r_clear_pulse),
		.increment(1'b1),
		.load(1'b1),
		.loadval(w_division_factor - sv2v_cast_DC41E_signed(1)),
		.done(w_prescaler_done),
		.count()
	);
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			o_counter <= 1'sb0;
			tick <= 1'b0;
		end
		else if (r_clear_pulse) begin
			o_counter <= 1'sb0;
			tick <= 1'b0;
		end
		else if (w_prescaler_done && sync_reset_n) begin
			o_counter <= o_counter + 1'b1;
			tick <= 1'b1;
		end
		else
			tick <= 1'b0;
	initial begin : debug_print
		if (DEBUG_LUT) begin
			$display("counter_freq_invariant LUT (strategy=%0d, %0d entries, %0d-%0d MHz, DIV_WIDTH=%0d):", FREQ_STRATEGY, NUM_FREQ_ENTRIES, MIN_FREQ_MHZ, MAX_FREQ_MHZ, DIV_WIDTH);
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < NUM_FREQ_ENTRIES; i = i + 1)
					$display("  freq_sel[%2d] = %4d MHz  (%0d cycles/us)", i, freq_mhz_at_idx(i), freq_mhz_at_idx(i));
			end
		end
	end
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
	reg [DW - 1:0] r_data [0:DEPTH - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH < 2) || (DEPTH > 8)) begin : gen_depth_guard
			initial $display("Error [elaboration] /tmp/rds-canonical-repo-root/rtl/amba/gaxi/gaxi_skid_buffer.sv:101:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
		end
	endgenerate
	genvar _gv_gi_2;
	generate
		for (_gv_gi_2 = 0; _gv_gi_2 < DEPTH; _gv_gi_2 = _gv_gi_2 + 1) begin : g_slot
			localparam gi = _gv_gi_2;
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_data[gi] <= 1'sb0;
				else
					(* full_case, parallel_case *)
					case ({w_wr_xfer, w_rd_xfer})
						2'b10:
							if (r_data_count == gi[3:0])
								r_data[gi] <= wr_data;
						2'b01:
							if (gi < (DEPTH - 1))
								r_data[gi] <= r_data[gi + 1];
							else
								r_data[gi] <= 1'sb0;
						2'b11:
							if ((r_data_count >= 1) && (gi[3:0] == (r_data_count - 4'd1)))
								r_data[gi] <= wr_data;
							else if (gi < (DEPTH - 1))
								r_data[gi] <= r_data[gi + 1];
							else
								r_data[gi] <= 1'sb0;
						default:
							;
					endcase
		end
	endgenerate
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn)
			r_data_count <= 1'sb0;
		else
			(* full_case, parallel_case *)
			case ({w_wr_xfer, w_rd_xfer})
				2'b10: r_data_count <= r_data_count + 4'd1;
				2'b01: r_data_count <= r_data_count - 4'd1;
				default:
					;
			endcase
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			wr_ready <= 1'b0;
			rd_valid <= 1'b0;
		end
		else begin
			wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && (~w_wr_xfer || w_rd_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && w_rd_xfer);
			rd_valid <= ((r_data_count >= 2) || ((r_data_count == 4'b0001) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'b0000) && w_wr_xfer);
		end
	assign rd_data = r_data[0];
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
	monbus_timestamp_in,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
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
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	parameter signed [31:0] SKID_DATA_WIDTH = monitor_common_pkg_MONBUS_PKT_WIDTH + monitor_common_pkg_MONBUS_TS_WIDTH;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire block_arb;
	input wire [0:CLIENTS - 1] monbus_valid_in;
	output wire [0:CLIENTS - 1] monbus_ready_in;
	input wire [(CLIENTS * monitor_common_pkg_MONBUS_PKT_WIDTH) - 1:0] monbus_packet_in;
	input wire [(CLIENTS * monitor_common_pkg_MONBUS_TS_WIDTH) - 1:0] monbus_timestamp_in;
	output wire monbus_valid;
	input wire monbus_ready;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire grant_valid;
	output wire [CLIENTS - 1:0] grant;
	output wire [N - 1:0] grant_id;
	output wire [CLIENTS - 1:0] last_grant;
	localparam [0:0] INPUT_SKID_EN = INPUT_SKID_ENABLE != 0;
	localparam [0:0] OUTPUT_SKID_EN = OUTPUT_SKID_ENABLE != 0;
	wire int_monbus_valid_in [0:CLIENTS - 1];
	reg int_monbus_ready_in [0:CLIENTS - 1];
	wire [127:0] int_monbus_packet_in [0:CLIENTS - 1];
	wire [63:0] int_monbus_timestamp_in [0:CLIENTS - 1];
	reg int_monbus_valid;
	wire int_monbus_ready;
	reg [127:0] int_monbus_packet;
	reg [63:0] int_monbus_timestamp;
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < CLIENTS; _gv_i_2 = _gv_i_2 + 1) begin : gen_input_skid
			localparam i = _gv_i_2;
			if (INPUT_SKID_EN == 1'b1) begin : gen_input_skid_enabled
				wire [SKID_DATA_WIDTH - 1:0] skid_wr_data;
				wire [SKID_DATA_WIDTH - 1:0] skid_rd_data;
				assign skid_wr_data = {monbus_timestamp_in[((CLIENTS - 1) - i) * monitor_common_pkg_MONBUS_TS_WIDTH+:monitor_common_pkg_MONBUS_TS_WIDTH], monbus_packet_in[((CLIENTS - 1) - i) * monitor_common_pkg_MONBUS_PKT_WIDTH+:monitor_common_pkg_MONBUS_PKT_WIDTH]};
				assign int_monbus_packet_in[i] = skid_rd_data[127:0];
				assign int_monbus_timestamp_in[i] = skid_rd_data[SKID_DATA_WIDTH - 1:monitor_common_pkg_MONBUS_PKT_WIDTH];
				gaxi_skid_buffer #(
					.DATA_WIDTH(SKID_DATA_WIDTH),
					.DEPTH(INPUT_SKID_DEPTH)
				) u_input_skid(
					.axi_aclk(axi_aclk),
					.axi_aresetn(axi_aresetn),
					.wr_valid(monbus_valid_in[i]),
					.wr_ready(monbus_ready_in[i]),
					.wr_data(skid_wr_data),
					.rd_valid(int_monbus_valid_in[i]),
					.rd_ready(int_monbus_ready_in[i]),
					.rd_data(skid_rd_data),
					.count(),
					.rd_count()
				);
			end
			else begin : gen_input_skid_disabled
				assign int_monbus_valid_in[i] = monbus_valid_in[i];
				assign monbus_ready_in[i] = int_monbus_ready_in[i];
				assign int_monbus_packet_in[i] = monbus_packet_in[((CLIENTS - 1) - i) * monitor_common_pkg_MONBUS_PKT_WIDTH+:monitor_common_pkg_MONBUS_PKT_WIDTH];
				assign int_monbus_timestamp_in[i] = monbus_timestamp_in[((CLIENTS - 1) - i) * monitor_common_pkg_MONBUS_TS_WIDTH+:monitor_common_pkg_MONBUS_TS_WIDTH];
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
				grant_ack[i] = (grant[i] && int_monbus_valid_in[i]) && int_monbus_ready;
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
		int_monbus_timestamp = 1'sb0;
		if (grant_valid) begin
			int_monbus_packet = int_monbus_packet_in[grant_id];
			int_monbus_timestamp = int_monbus_timestamp_in[grant_id];
		end
	end
	generate
		if (OUTPUT_SKID_EN == 1'b1) begin : gen_output_skid_enabled
			wire [SKID_DATA_WIDTH - 1:0] out_skid_wr_data;
			wire [SKID_DATA_WIDTH - 1:0] out_skid_rd_data;
			assign out_skid_wr_data = {int_monbus_timestamp, int_monbus_packet};
			assign monbus_packet = out_skid_rd_data[127:0];
			assign monbus_timestamp = out_skid_rd_data[SKID_DATA_WIDTH - 1:monitor_common_pkg_MONBUS_PKT_WIDTH];
			gaxi_skid_buffer #(
				.DATA_WIDTH(SKID_DATA_WIDTH),
				.DEPTH(OUTPUT_SKID_DEPTH)
			) u_output_skid(
				.axi_aclk(axi_aclk),
				.axi_aresetn(axi_aresetn),
				.wr_valid(int_monbus_valid),
				.wr_ready(int_monbus_ready),
				.wr_data(out_skid_wr_data),
				.rd_valid(monbus_valid),
				.rd_ready(monbus_ready),
				.rd_data(out_skid_rd_data),
				.count(),
				.rd_count()
			);
		end
		else begin : gen_output_skid_disabled
			assign monbus_valid = int_monbus_valid;
			assign int_monbus_ready = monbus_ready;
			assign monbus_packet = int_monbus_packet;
			assign monbus_timestamp = int_monbus_timestamp;
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
module dma_address_gen (
	i_clk,
	i_rst_n,
	i_cfg_base_addr,
	i_cfg_stride_0,
	i_cfg_stride_1,
	i_cfg_wrap_mask_0,
	i_cfg_wrap_mask_1,
	i_req_valid,
	o_req_ready,
	i_req_index_0,
	i_req_index_1,
	i_req_tag,
	o_result_valid,
	i_result_ready,
	o_result_addr,
	o_result_tag
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 40;
	parameter signed [31:0] INDEX_WIDTH = 16;
	parameter signed [31:0] STRIDE_WIDTH = 24;
	parameter signed [31:0] TAG_WIDTH = 8;
	input wire i_clk;
	input wire i_rst_n;
	input wire [ADDR_WIDTH - 1:0] i_cfg_base_addr;
	input wire signed [STRIDE_WIDTH - 1:0] i_cfg_stride_0;
	input wire signed [STRIDE_WIDTH - 1:0] i_cfg_stride_1;
	input wire [ADDR_WIDTH - 1:0] i_cfg_wrap_mask_0;
	input wire [ADDR_WIDTH - 1:0] i_cfg_wrap_mask_1;
	input wire i_req_valid;
	output wire o_req_ready;
	input wire [INDEX_WIDTH - 1:0] i_req_index_0;
	input wire [INDEX_WIDTH - 1:0] i_req_index_1;
	input wire [TAG_WIDTH - 1:0] i_req_tag;
	output wire o_result_valid;
	input wire i_result_ready;
	output wire [ADDR_WIDTH - 1:0] o_result_addr;
	output wire [TAG_WIDTH - 1:0] o_result_tag;
	localparam signed [31:0] PRODUCT_WIDTH = INDEX_WIDTH + STRIDE_WIDTH;
	wire signed [PRODUCT_WIDTH:0] w_s1_raw_offset_0;
	wire signed [PRODUCT_WIDTH:0] w_s1_raw_offset_1;
	assign w_s1_raw_offset_0 = $signed({1'b0, i_req_index_0}) * i_cfg_stride_0;
	assign w_s1_raw_offset_1 = $signed({1'b0, i_req_index_1}) * i_cfg_stride_1;
	reg [ADDR_WIDTH - 1:0] w_s1_offset_0;
	reg [ADDR_WIDTH - 1:0] w_s1_offset_1;
	function automatic signed [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5_signed;
		input reg signed [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		if (i_cfg_wrap_mask_0 != {ADDR_WIDTH {1'sb0}})
			w_s1_offset_0 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_0) & i_cfg_wrap_mask_0;
		else
			w_s1_offset_0 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_0);
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if (i_cfg_wrap_mask_1 != {ADDR_WIDTH {1'sb0}})
			w_s1_offset_1 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_1) & i_cfg_wrap_mask_1;
		else
			w_s1_offset_1 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_1);
	end
	reg r_s1_valid;
	reg [ADDR_WIDTH - 1:0] r_s1_offset_0;
	reg [ADDR_WIDTH - 1:0] r_s1_offset_1;
	reg [ADDR_WIDTH - 1:0] r_s1_base_addr;
	reg [TAG_WIDTH - 1:0] r_s1_tag;
	wire w_s1_ready;
	wire w_s2_ready;
	assign w_s1_ready = !r_s1_valid || w_s2_ready;
	assign o_req_ready = w_s1_ready;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_s1_valid <= 1'b0;
			r_s1_offset_0 <= 1'sb0;
			r_s1_offset_1 <= 1'sb0;
			r_s1_base_addr <= 1'sb0;
			r_s1_tag <= 1'sb0;
		end
		else if (i_req_valid && w_s1_ready) begin
			r_s1_valid <= 1'b1;
			r_s1_offset_0 <= w_s1_offset_0;
			r_s1_offset_1 <= w_s1_offset_1;
			r_s1_base_addr <= i_cfg_base_addr;
			r_s1_tag <= i_req_tag;
		end
		else if (w_s2_ready)
			r_s1_valid <= 1'b0;
	wire [ADDR_WIDTH - 1:0] w_s2_addr;
	assign w_s2_addr = (r_s1_base_addr + r_s1_offset_0) + r_s1_offset_1;
	reg r_s2_valid;
	reg [ADDR_WIDTH - 1:0] r_s2_addr;
	reg [TAG_WIDTH - 1:0] r_s2_tag;
	assign w_s2_ready = !r_s2_valid || i_result_ready;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_s2_valid <= 1'b0;
			r_s2_addr <= 1'sb0;
			r_s2_tag <= 1'sb0;
		end
		else if (r_s1_valid && w_s2_ready) begin
			r_s2_valid <= 1'b1;
			r_s2_addr <= w_s2_addr;
			r_s2_tag <= r_s1_tag;
		end
		else if (i_result_ready)
			r_s2_valid <= 1'b0;
	assign o_result_valid = r_s2_valid;
	assign o_result_addr = r_s2_addr;
	assign o_result_tag = r_s2_tag;
	initial _sv2v_0 = 0;
endmodule
module stream_run_addr_gen (
	clk,
	rst_n,
	start,
	cfg_per_beat,
	cfg_base_addr,
	cfg_stride_0,
	cfg_stride_1,
	cfg_wrap_mask_0,
	cfg_wrap_mask_1,
	cfg_inner_count,
	cfg_total_beats,
	o_base_valid,
	i_base_ready,
	o_base_addr
);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] STRIDE_WIDTH = 32;
	parameter signed [31:0] INDEX_WIDTH = 16;
	parameter signed [31:0] FIFO_DEPTH = 4;
	parameter signed [31:0] BEATS_WIDTH = 32;
	input wire clk;
	input wire rst_n;
	input wire start;
	input wire cfg_per_beat;
	input wire [ADDR_WIDTH - 1:0] cfg_base_addr;
	input wire signed [STRIDE_WIDTH - 1:0] cfg_stride_0;
	input wire signed [STRIDE_WIDTH - 1:0] cfg_stride_1;
	input wire [ADDR_WIDTH - 1:0] cfg_wrap_mask_0;
	input wire [ADDR_WIDTH - 1:0] cfg_wrap_mask_1;
	input wire [INDEX_WIDTH - 1:0] cfg_inner_count;
	input wire [BEATS_WIDTH - 1:0] cfg_total_beats;
	output wire o_base_valid;
	input wire i_base_ready;
	output wire [ADDR_WIDTH - 1:0] o_base_addr;
	reg r_per_beat;
	reg [ADDR_WIDTH - 1:0] r_base_addr;
	reg signed [STRIDE_WIDTH - 1:0] r_stride_0;
	reg signed [STRIDE_WIDTH - 1:0] r_stride_1;
	reg [ADDR_WIDTH - 1:0] r_wrap_mask_0;
	reg [ADDR_WIDTH - 1:0] r_wrap_mask_1;
	reg [BEATS_WIDTH - 1:0] r_total_beats;
	reg [INDEX_WIDTH - 1:0] r_inner_count;
	reg [INDEX_WIDTH - 1:0] r_i0;
	reg [INDEX_WIDTH - 1:0] r_i1;
	reg [BEATS_WIDTH - 1:0] r_gen_beats;
	reg r_gen_active;
	wire [INDEX_WIDTH - 1:0] w_start_inner;
	function automatic signed [INDEX_WIDTH - 1:0] sv2v_cast_5F989_signed;
		input reg signed [INDEX_WIDTH - 1:0] inp;
		sv2v_cast_5F989_signed = inp;
	endfunction
	assign w_start_inner = (cfg_inner_count == {INDEX_WIDTH {1'sb0}} ? sv2v_cast_5F989_signed(1) : cfg_inner_count);
	wire [BEATS_WIDTH - 1:0] w_step;
	function automatic signed [BEATS_WIDTH - 1:0] sv2v_cast_DF906_signed;
		input reg signed [BEATS_WIDTH - 1:0] inp;
		sv2v_cast_DF906_signed = inp;
	endfunction
	function automatic [BEATS_WIDTH - 1:0] sv2v_cast_DF906;
		input reg [BEATS_WIDTH - 1:0] inp;
		sv2v_cast_DF906 = inp;
	endfunction
	assign w_step = (r_per_beat ? sv2v_cast_DF906_signed(1) : sv2v_cast_DF906(r_inner_count));
	wire w_more;
	assign w_more = r_gen_active && (r_gen_beats < r_total_beats);
	wire w_req_valid;
	wire w_req_ready;
	wire w_res_valid;
	wire w_res_ready;
	wire [ADDR_WIDTH - 1:0] w_res_addr;
	assign w_req_valid = w_more;
	dma_address_gen #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.INDEX_WIDTH(INDEX_WIDTH),
		.STRIDE_WIDTH(STRIDE_WIDTH),
		.TAG_WIDTH(1)
	) u_addr_gen(
		.i_clk(clk),
		.i_rst_n(rst_n),
		.i_cfg_base_addr(r_base_addr),
		.i_cfg_stride_0(r_stride_0),
		.i_cfg_stride_1(r_stride_1),
		.i_cfg_wrap_mask_0(r_wrap_mask_0),
		.i_cfg_wrap_mask_1(r_wrap_mask_1),
		.i_req_valid(w_req_valid),
		.o_req_ready(w_req_ready),
		.i_req_index_0(r_i0),
		.i_req_index_1(r_i1),
		.i_req_tag(1'b0),
		.o_result_valid(w_res_valid),
		.i_result_ready(w_res_ready),
		.o_result_addr(w_res_addr),
		.o_result_tag()
	);
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_per_beat <= 1'b0;
			r_base_addr <= 1'sb0;
			r_stride_0 <= 1'sb0;
			r_stride_1 <= 1'sb0;
			r_wrap_mask_0 <= 1'sb0;
			r_wrap_mask_1 <= 1'sb0;
			r_total_beats <= 1'sb0;
			r_inner_count <= sv2v_cast_5F989_signed(1);
			r_i0 <= 1'sb0;
			r_i1 <= 1'sb0;
			r_gen_beats <= 1'sb0;
			r_gen_active <= 1'b0;
		end
		else if (start) begin
			r_per_beat <= cfg_per_beat;
			r_base_addr <= cfg_base_addr;
			r_stride_0 <= cfg_stride_0;
			r_stride_1 <= cfg_stride_1;
			r_wrap_mask_0 <= cfg_wrap_mask_0;
			r_wrap_mask_1 <= cfg_wrap_mask_1;
			r_total_beats <= cfg_total_beats;
			r_inner_count <= w_start_inner;
			r_gen_active <= 1'b1;
			if (cfg_per_beat) begin
				r_gen_beats <= sv2v_cast_DF906_signed(1);
				if (w_start_inner > sv2v_cast_5F989_signed(1)) begin
					r_i0 <= sv2v_cast_5F989_signed(1);
					r_i1 <= 1'sb0;
				end
				else begin
					r_i0 <= 1'sb0;
					r_i1 <= sv2v_cast_5F989_signed(1);
				end
			end
			else begin
				r_gen_beats <= sv2v_cast_DF906(w_start_inner);
				r_i0 <= 1'sb0;
				r_i1 <= sv2v_cast_5F989_signed(1);
			end
		end
		else if (w_req_valid && w_req_ready) begin
			r_gen_beats <= r_gen_beats + w_step;
			if (r_per_beat) begin
				if (r_i0 == (r_inner_count - sv2v_cast_5F989_signed(1))) begin
					r_i0 <= 1'sb0;
					r_i1 <= r_i1 + sv2v_cast_5F989_signed(1);
				end
				else
					r_i0 <= r_i0 + sv2v_cast_5F989_signed(1);
			end
			else
				r_i1 <= r_i1 + sv2v_cast_5F989_signed(1);
		end
	wire w_fifo_wr_ready;
	assign w_res_ready = w_fifo_wr_ready;
	gaxi_fifo_sync #(
		.DATA_WIDTH(ADDR_WIDTH),
		.DEPTH(FIFO_DEPTH)
	) i_addr_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_res_valid),
		.wr_ready(w_fifo_wr_ready),
		.wr_data(w_res_addr),
		.rd_valid(o_base_valid),
		.rd_ready(i_base_ready),
		.rd_data(o_base_addr),
		.count()
	);
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
	descriptor_ext_packet,
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
	i_mon_time,
	mon_valid,
	mon_ready,
	mon_packet,
	mon_timestamp
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter [0:0] GEN_MON = 1'b1;
	parameter signed [31:0] NUM_CHANNELS = 32;
	parameter signed [31:0] CHAN_WIDTH = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] FIFO_DEPTH = 8;
	parameter signed [31:0] DESC_ADDR_FIFO_DEPTH = 2;
	parameter signed [31:0] USE_ROW_COL_MAJOR_ADDRESSING = 1;
	parameter signed [31:0] TIMEOUT_CYCLES = 1000;
	parameter [15:0] MON_AGENT_ID = 16'h0010;
	parameter [7:0] MON_UNIT_ID = 8'h01;
	parameter [8:0] MON_CHANNEL_ID = 9'h000;
	input wire clk;
	input wire rst_n;
	input wire apb_valid;
	output wire apb_ready;
	input wire [ADDR_WIDTH - 1:0] apb_addr;
	input wire channel_idle;
	output wire descriptor_valid;
	input wire descriptor_ready;
	output wire [255:0] descriptor_packet;
	output wire [255:0] descriptor_ext_packet;
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
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	initial if (AXI_ID_WIDTH < CHAN_WIDTH) begin
		$display("Fatal [%0t] /tmp/rds-canonical-repo-root/projects/components/dma-ip/stream/rtl/fub/descriptor_engine.sv:153:13 - descriptor_engine.<unnamed_block>.<unnamed_block>\n msg: ", $time, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
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
	reg [255:0] r_descriptor_ext_data;
	reg r_is_ext;
	wire w_want_ext;
	reg [ADDR_WIDTH - 1:0] r_saved_next_addr;
	wire w_chain_condition;
	wire w_next_addr_valid;
	wire w_chain_eligible;
	wire w_should_chain;
	wire w_desc_committed;
	localparam signed [31:0] DFC_W = $clog2(FIFO_DEPTH) + 1;
	wire [DFC_W - 1:0] w_desc_fifo_count;
	reg [DFC_W - 1:0] w_prefetch_limit;
	wire w_prefetch_allows;
	reg r_chain_pending;
	reg [ADDR_WIDTH - 1:0] r_pending_chain_addr;
	wire w_pending_push_fire;
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
	reg [127:0] r_mon_packet;
	reg [63:0] r_mon_timestamp;
	always @(posedge clk or negedge rst_n)
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
		else if (w_should_chain) begin
			w_desc_addr_fifo_wr_valid = 1'b1;
			w_desc_addr_fifo_wr_data = {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
		end
		else if (w_pending_push_fire) begin
			w_desc_addr_fifo_wr_valid = 1'b1;
			w_desc_addr_fifo_wr_data = r_pending_chain_addr;
		end
	end
	wire [ADDR_WIDTH - 1:0] w_next_addr_extended;
	assign w_next_addr_extended = {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
	assign w_next_addr_valid = ((w_next_addr_extended >= cfg_addr0_base) && (w_next_addr_extended <= cfg_addr0_limit)) || ((w_next_addr_extended >= cfg_addr1_base) && (w_next_addr_extended <= cfg_addr1_limit));
	assign w_chain_condition = ((w_next_addr != {32 {1'sb0}}) && !w_desc_last) && w_desc_valid;
	assign w_chain_eligible = (w_chain_condition && w_next_addr_valid) && !r_descriptor_error;
	assign w_desc_committed = (r_current_state == 3'b011) && w_desc_fifo_wr_ready;
	function automatic [DFC_W - 1:0] sv2v_cast_E6249;
		input reg [DFC_W - 1:0] inp;
		sv2v_cast_E6249 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		if (!cfg_prefetch_enable)
			w_prefetch_limit = {{DFC_W - 1 {1'b0}}, 1'b1};
		else if (cfg_fifo_threshold == 4'h0)
			w_prefetch_limit = {{DFC_W - 1 {1'b0}}, 1'b1};
		else
			w_prefetch_limit = sv2v_cast_E6249(cfg_fifo_threshold);
	end
	assign w_prefetch_allows = w_desc_fifo_count < w_prefetch_limit;
	assign w_should_chain = ((w_chain_eligible && w_desc_committed) && w_prefetch_allows) && w_desc_addr_fifo_wr_ready;
	assign w_pending_push_fire = ((r_chain_pending && w_prefetch_allows) && w_desc_addr_fifo_wr_ready) && !w_desc_committed;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_chain_pending <= 1'b0;
			r_pending_chain_addr <= 1'sb0;
		end
		else if (r_channel_reset_active)
			r_chain_pending <= 1'b0;
		else if (((w_desc_committed && w_chain_eligible) && !w_should_chain) && !r_chain_pending) begin
			r_chain_pending <= 1'b1;
			r_pending_chain_addr <= {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
		end
		else if (w_pending_push_fire)
			r_chain_pending <= 1'b0;
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
		.count(w_desc_fifo_count)
	);
	generate
		if (USE_ROW_COL_MAJOR_ADDRESSING != 0) begin : g_ext_fifo
			wire [255:0] w_desc_ext_fifo_rd_data;
			gaxi_fifo_sync #(
				.DATA_WIDTH(256),
				.DEPTH(FIFO_DEPTH)
			) i_descriptor_ext_fifo(
				.axi_aclk(clk),
				.axi_aresetn(rst_n),
				.wr_valid(w_desc_fifo_wr_valid),
				.wr_ready(),
				.wr_data(r_descriptor_ext_data),
				.rd_valid(),
				.rd_ready(w_desc_fifo_rd_ready),
				.rd_data(w_desc_ext_fifo_rd_data),
				.count()
			);
			assign descriptor_ext_packet = w_desc_ext_fifo_rd_data;
		end
		else begin : g_no_ext
			assign descriptor_ext_packet = 1'sb0;
		end
	endgenerate
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
	assign w_want_ext = (USE_ROW_COL_MAJOR_ADDRESSING != 0) && (r_data[210:208] == 3'd1);
	assign r_ready = ((r_current_state == 3'b010) || (r_current_state == 3'b110)) && w_our_axi_response;
	always @(posedge clk or negedge rst_n)
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
				else if (!w_addr_range_valid)
					w_next_state = 3'b100;
				else if (ar_valid && ar_ready)
					w_next_state = 3'b010;
			3'b010:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_our_axi_response && r_valid) begin
					if (!w_axi_response_ok)
						w_next_state = 3'b100;
					else if (w_want_ext)
						w_next_state = 3'b101;
					else
						w_next_state = 3'b011;
				end
			3'b101:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (ar_ready)
					w_next_state = 3'b110;
			3'b110:
				if (r_channel_reset_active)
					w_next_state = 3'b000;
				else if (w_our_axi_response && r_valid)
					w_next_state = (w_axi_response_ok ? 3'b011 : 3'b100);
			3'b011:
				if (w_desc_fifo_wr_ready)
					w_next_state = 3'b000;
			3'b100: w_next_state = 3'b000;
			default: w_next_state = 3'b000;
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_apb_operation_active <= 1'b0;
			r_axi_read_active <= 1'b0;
			r_axi_read_addr <= 1'sb0;
			r_axi_read_resp <= 2'b00;
			r_descriptor_data <= 1'sb0;
			r_descriptor_ext_data <= 1'sb0;
			r_is_ext <= 1'b0;
			r_saved_next_addr <= 1'sb0;
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
					if (ar_valid && ar_ready)
						r_axi_read_active <= 1'b1;
				3'b010:
					if (w_our_axi_response && r_valid) begin
						r_descriptor_data <= r_data;
						r_axi_read_resp <= r_resp;
						r_saved_next_addr <= {{ADDR_WIDTH - 32 {1'b0}}, w_next_addr};
						r_is_ext <= w_want_ext;
						if (w_want_ext && w_axi_response_ok)
							r_axi_read_active <= 1'b0;
						if (!r_data[192])
							r_descriptor_error <= 1'b1;
					end
				3'b101:
					if (ar_ready)
						r_axi_read_active <= 1'b1;
				3'b110:
					if (w_our_axi_response && r_valid) begin
						r_descriptor_ext_data <= r_data;
						r_axi_read_resp <= r_resp;
					end
				3'b011:
					if (w_desc_fifo_wr_ready) begin
						r_apb_operation_active <= 1'b0;
						r_axi_read_active <= 1'b0;
						r_is_ext <= 1'b0;
					end
				3'b100: begin
					r_descriptor_error <= 1'b1;
					r_apb_operation_active <= 1'b0;
					r_axi_read_active <= 1'b0;
				end
				default:
					;
			endcase
			if (r_channel_reset_active) begin
				r_apb_operation_active <= 1'b0;
				r_axi_read_active <= 1'b0;
				r_descriptor_error <= 1'b0;
			end
			if (apb_valid && !w_apb_addr_valid)
				r_descriptor_error <= 1'b1;
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
	assign ar_valid = (((r_current_state == 3'b001) && w_addr_range_valid) || (r_current_state == 3'b101)) && !r_axi_read_active;
	function automatic signed [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5_signed;
		input reg signed [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5_signed = inp;
	endfunction
	assign ar_addr = (r_current_state == 3'b101 ? r_axi_read_addr + sv2v_cast_A5DC5_signed(32) : r_axi_read_addr);
	assign ar_len = 8'h00;
	assign ar_size = 3'b101;
	assign ar_burst = 2'b01;
	assign ar_id = {{AXI_ID_WIDTH - CHAN_WIDTH {1'b0}}, CHANNEL_ID[CHAN_WIDTH - 1:0]};
	assign ar_lock = 1'b0;
	assign ar_cache = 4'b0010;
	assign ar_prot = 3'b000;
	assign ar_qos = 4'h0;
	assign ar_region = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
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
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			r_mon_timestamp <= 1'sb0;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			case (r_current_state)
				3'b011: begin
					r_mon_valid <= 1'b1;
					r_mon_timestamp <= i_mon_time;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, 8'h00, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, sv2v_cast_64(r_axi_read_addr));
				end
				3'b100: begin
					r_mon_valid <= 1'b1;
					r_mon_timestamp <= i_mon_time;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 4'h4, 8'h06, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {46'h000000000000, r_axi_read_resp, 16'h0000});
				end
				default:
					;
			endcase
		end
	wire w_channel_idle_falling = r_channel_idle_prev && !channel_idle;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_apb_ip <= 1'b0;
			r_channel_idle_prev <= 1'b1;
		end
		else begin
			r_channel_idle_prev <= channel_idle;
			if (r_channel_reset_active)
				r_apb_ip <= 1'b0;
			else if (w_apb_skid_valid_in && w_apb_skid_ready_in)
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
	assign mon_valid = (GEN_MON ? r_mon_valid : 1'b0);
	assign mon_packet = (GEN_MON ? r_mon_packet : {128 {1'sb0}});
	assign mon_timestamp = (GEN_MON ? r_mon_timestamp : {64 {1'sb0}});
	initial _sv2v_0 = 0;
endmodule
module scheduler (
	clk,
	rst_n,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_limit,
	cfg_sched_timeout_enable,
	cfg_rd_prefetch_enable,
	scheduler_idle,
	scheduler_state,
	descriptor_valid,
	descriptor_ready,
	descriptor_packet,
	descriptor_ext_packet,
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
	sched_wr_commit_strobe,
	sched_wr_commit_beats,
	sched_rd_error,
	sched_wr_error,
	sched_error,
	dbg_descriptor_error,
	dbg_read_error_sticky,
	dbg_write_error_sticky,
	dbg_timeout_expired,
	i_mon_time,
	mon_valid,
	mon_ready,
	mon_packet,
	mon_timestamp
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter [0:0] GEN_MON = 1'b1;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter [15:0] MON_AGENT_ID = 16'h0040;
	parameter [7:0] MON_UNIT_ID = 8'h01;
	parameter [8:0] MON_CHANNEL_ID = 9'h000;
	parameter signed [31:0] DESC_WIDTH = 256;
	parameter signed [31:0] USE_ROW_COL_MAJOR_ADDRESSING = 1;
	input wire clk;
	input wire rst_n;
	input wire cfg_channel_enable;
	input wire cfg_channel_reset;
	input wire [31:0] cfg_sched_timeout_cycles;
	input wire [7:0] cfg_sched_timeout_limit;
	input wire cfg_sched_timeout_enable;
	input wire cfg_rd_prefetch_enable;
	output wire scheduler_idle;
	output wire [6:0] scheduler_state;
	input wire descriptor_valid;
	output wire descriptor_ready;
	input wire [DESC_WIDTH - 1:0] descriptor_packet;
	input wire [255:0] descriptor_ext_packet;
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
	input wire sched_wr_commit_strobe;
	input wire [31:0] sched_wr_commit_beats;
	input wire sched_rd_error;
	input wire sched_wr_error;
	output wire sched_error;
	output wire dbg_descriptor_error;
	output wire dbg_read_error_sticky;
	output wire dbg_write_error_sticky;
	output wire dbg_timeout_expired;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	initial if (DESC_WIDTH != 256) begin
		$display("Fatal [%0t] /tmp/rds-canonical-repo-root/projects/components/dma-ip/stream/rtl/fub/scheduler.sv:175:13 - scheduler.<unnamed_block>.<unnamed_block>\n msg: ", $time, "scheduler (STREAM): DESC_WIDTH must be 256, got %0d. For RAPIDS, use rapids_scheduler.", DESC_WIDTH);
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
	reg [31:0] r_write_beats_to_commit;
	reg [255:0] r_descriptor_ext;
	reg r_is_ext;
	wire w_is_ext;
	assign w_is_ext = r_is_ext;
	wire [255:0] w_descriptor_ext_in;
	wire w_is_ext_in;
	assign w_descriptor_ext_in = descriptor_ext_packet;
	assign w_is_ext_in = (USE_ROW_COL_MAJOR_ADDRESSING != 0) && (descriptor_packet[210:208] == 3'd1);
	reg [31:0] r_rd_run_remaining;
	reg [31:0] r_wr_run_remaining;
	wire w_rd_base_valid;
	wire w_rd_base_ready;
	wire [ADDR_WIDTH - 1:0] w_rd_base_addr;
	wire w_wr_base_valid;
	wire w_wr_base_ready;
	wire [ADDR_WIDTH - 1:0] w_wr_base_addr;
	wire w_rd_need_base;
	wire w_wr_need_base;
	assign w_rd_need_base = (w_is_ext && (r_rd_run_remaining == 32'h00000000)) && (r_read_beats_remaining != 32'h00000000);
	assign w_wr_need_base = (w_is_ext && (r_wr_run_remaining == 32'h00000000)) && (r_write_beats_remaining != 32'h00000000);
	assign w_rd_base_ready = w_rd_need_base;
	assign w_wr_base_ready = w_wr_need_base;
	reg r_fetch_desc_d;
	wire w_addrgen_start;
	assign w_addrgen_start = (w_state_fetch_desc && !r_fetch_desc_d) && w_is_ext;
	localparam signed [31:0] stream_pkg_STREAM_ADDRGEN_STRIDE_WIDTH = 32;
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	localparam signed [31:0] BEAT_BYTES = sv2v_cast_32_signed(DATA_WIDTH / 8);
	reg r_rd_per_beat;
	reg r_wr_per_beat;
	wire w_rd_per_beat;
	wire w_wr_per_beat;
	assign w_rd_per_beat = r_rd_per_beat;
	assign w_wr_per_beat = r_wr_per_beat;
	wire [31:0] w_rd_inner_beats;
	wire [31:0] w_wr_inner_beats;
	assign w_rd_inner_beats = (r_descriptor_ext[79-:16] == {16 {1'sb0}} ? 32'd1 : {16'h0000, r_descriptor_ext[79-:16]});
	assign w_wr_inner_beats = (r_descriptor_ext[175-:16] == {16 {1'sb0}} ? 32'd1 : {16'h0000, r_descriptor_ext[175-:16]});
	wire [31:0] w_rd_run_size;
	wire [31:0] w_wr_run_size;
	assign w_rd_run_size = (w_rd_per_beat ? 32'd1 : w_rd_inner_beats);
	assign w_wr_run_size = (w_wr_per_beat ? 32'd1 : w_wr_inner_beats);
	wire [31:0] w_rd_run_init;
	wire [31:0] w_wr_run_init;
	assign w_rd_run_init = (!w_is_ext ? r_descriptor[159-:32] : (w_rd_run_size < r_descriptor[159-:32] ? w_rd_run_size : r_descriptor[159-:32]));
	assign w_wr_run_init = (!w_is_ext ? r_descriptor[159-:32] : (w_wr_run_size < r_descriptor[159-:32] ? w_wr_run_size : r_descriptor[159-:32]));
	reg [31:0] r_timeout_counter;
	wire w_timeout_expired;
	reg [7:0] r_timeout_strikes;
	wire w_hard_error;
	wire w_timeout_escalate;
	reg r_read_error_sticky;
	reg r_write_error_sticky;
	reg r_descriptor_error;
	reg r_mon_valid;
	reg [127:0] r_mon_packet;
	reg [63:0] r_mon_timestamp;
	reg r_error_pkt_sent;
	wire w_read_complete;
	wire w_write_issued;
	wire w_write_complete;
	wire w_transfer_complete;
	wire w_desc_launch;
	reg [31:0] w_ctc_next;
	wire w_ctc_add_en;
	wire [31:0] w_ctc_add_len;
	reg [31:0] r_ctc_pending_add;
	reg r_rd_ahead;
	wire w_desc_chained;
	reg r_desc_chained;
	wire w_rd_prefetch_en;
	wire w_rd_peek;
	wire w_wr_advance;
	wire [63:0] w_next_src_addr;
	wire [63:0] w_next_dst_addr;
	wire [31:0] w_next_length;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	always @(posedge clk or negedge rst_n)
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
		else if (w_hard_error || w_timeout_escalate)
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
					if (w_wr_advance)
						w_next_state = 7'b0000100;
					else if (w_transfer_complete && !r_rd_ahead)
						w_next_state = 7'b0001000;
				7'b0001000:
					if ((r_descriptor[191-:32] != 32'h00000000) && !r_descriptor[194])
						w_next_state = 7'b0010000;
					else if (w_write_complete)
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
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_descriptor <= 1'sb0;
			r_descriptor_ext <= 1'sb0;
			r_descriptor_loaded <= 1'b0;
			r_src_addr <= 1'sb0;
			r_dst_addr <= 1'sb0;
			r_beats_remaining <= 32'h00000000;
			r_read_beats_remaining <= 32'h00000000;
			r_write_beats_remaining <= 32'h00000000;
			r_rd_run_remaining <= 32'h00000000;
			r_wr_run_remaining <= 32'h00000000;
			r_is_ext <= 1'b0;
			r_rd_per_beat <= 1'b0;
			r_wr_per_beat <= 1'b0;
			r_fetch_desc_d <= 1'b0;
			r_rd_ahead <= 1'b0;
			r_desc_chained <= 1'b0;
		end
		else begin
			r_fetch_desc_d <= w_state_fetch_desc;
			if ((((r_current_state == 7'b0000001) || (r_current_state == 7'b0010000)) && descriptor_valid) && descriptor_ready) begin
				r_descriptor[63-:64] <= descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
				r_descriptor[127-:64] <= descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
				r_descriptor[159-:32] <= descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
				r_descriptor[191-:32] <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
				r_descriptor[192] <= descriptor_packet[DESC_VALID_BIT];
				r_descriptor[193] <= descriptor_packet[DESC_GEN_IRQ];
				r_descriptor[194] <= descriptor_packet[DESC_LAST];
				r_descriptor[210-:3] <= descriptor_packet[210:208];
				r_descriptor_ext <= descriptor_ext_packet;
				r_is_ext <= w_is_ext_in;
				r_desc_chained <= (descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO] != 32'h00000000) && !descriptor_packet[DESC_LAST];
				r_rd_per_beat <= w_is_ext_in && ($signed(w_descriptor_ext_in[31-:32]) != BEAT_BYTES);
				r_wr_per_beat <= w_is_ext_in && ($signed(w_descriptor_ext_in[127-:32]) != BEAT_BYTES);
				r_descriptor_loaded <= 1'b1;
			end
			case (r_current_state)
				7'b0000010: begin
					r_src_addr <= r_descriptor[ADDR_WIDTH - 1:0];
					r_dst_addr <= r_descriptor[63 + ADDR_WIDTH:64];
					r_beats_remaining <= r_descriptor[159-:32];
					r_read_beats_remaining <= r_descriptor[159-:32];
					r_write_beats_remaining <= r_descriptor[159-:32];
					r_rd_run_remaining <= w_rd_run_init;
					r_wr_run_remaining <= w_wr_run_init;
				end
				7'b0000100: begin
					if (sched_rd_done_strobe) begin
						r_read_beats_remaining <= (r_read_beats_remaining >= sched_rd_beats_done ? r_read_beats_remaining - sched_rd_beats_done : 32'h00000000);
						r_src_addr <= r_src_addr + (sv2v_cast_A5DC5(sched_rd_beats_done) << $clog2(DATA_WIDTH / 8));
						if (w_is_ext)
							r_rd_run_remaining <= (r_rd_run_remaining >= sched_rd_beats_done ? r_rd_run_remaining - sched_rd_beats_done : 32'h00000000);
					end
					if (w_rd_need_base && w_rd_base_valid) begin
						r_src_addr <= w_rd_base_addr;
						r_rd_run_remaining <= (r_read_beats_remaining >= w_rd_run_size ? w_rd_run_size : r_read_beats_remaining);
					end
					if (sched_wr_done_strobe) begin
						r_write_beats_remaining <= (r_write_beats_remaining >= sched_wr_beats_done ? r_write_beats_remaining - sched_wr_beats_done : 32'h00000000);
						r_dst_addr <= r_dst_addr + (sv2v_cast_A5DC5(sched_wr_beats_done) << $clog2(DATA_WIDTH / 8));
						if (w_is_ext)
							r_wr_run_remaining <= (r_wr_run_remaining >= sched_wr_beats_done ? r_wr_run_remaining - sched_wr_beats_done : 32'h00000000);
					end
					if (w_wr_need_base && w_wr_base_valid) begin
						r_dst_addr <= w_wr_base_addr;
						r_wr_run_remaining <= (r_write_beats_remaining >= w_wr_run_size ? w_wr_run_size : r_write_beats_remaining);
					end
				end
				7'b0001000: r_descriptor_loaded <= 1'b0;
				default:
					;
			endcase
			if (w_rd_peek) begin
				r_src_addr <= w_next_src_addr[ADDR_WIDTH - 1:0];
				r_read_beats_remaining <= w_next_length;
				r_rd_run_remaining <= w_next_length;
				r_rd_ahead <= 1'b1;
			end
			if (w_wr_advance) begin
				r_dst_addr <= w_next_dst_addr[ADDR_WIDTH - 1:0];
				r_write_beats_remaining <= w_next_length;
				r_wr_run_remaining <= w_next_length;
				r_descriptor[63-:64] <= w_next_src_addr;
				r_descriptor[127-:64] <= w_next_dst_addr;
				r_descriptor[159-:32] <= w_next_length;
				r_descriptor[191-:32] <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
				r_descriptor[192] <= descriptor_packet[DESC_VALID_BIT];
				r_descriptor[193] <= descriptor_packet[DESC_GEN_IRQ];
				r_descriptor[194] <= descriptor_packet[DESC_LAST];
				r_descriptor[210-:3] <= descriptor_packet[210:208];
				r_is_ext <= w_is_ext_in;
				r_desc_chained <= (descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO] != 32'h00000000) && !descriptor_packet[DESC_LAST];
				if (!r_rd_ahead) begin
					r_src_addr <= w_next_src_addr[ADDR_WIDTH - 1:0];
					r_read_beats_remaining <= w_next_length;
					r_rd_run_remaining <= w_next_length;
				end
				r_rd_ahead <= 1'b0;
			end
			if (r_channel_reset_active) begin
				r_descriptor_loaded <= 1'b0;
				r_read_beats_remaining <= 32'h00000000;
				r_write_beats_remaining <= 32'h00000000;
				r_rd_ahead <= 1'b0;
			end
		end
	assign w_read_complete = r_read_beats_remaining == 32'h00000000;
	assign w_desc_launch = w_state_fetch_desc && (w_next_state == 7'b0000100);
	assign w_ctc_add_en = w_desc_launch || w_wr_advance;
	assign w_ctc_add_len = (w_desc_launch ? r_descriptor[159-:32] : w_next_length);
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_ctc_pending_add <= 32'h00000000;
		else if (r_channel_reset_active)
			r_ctc_pending_add <= 32'h00000000;
		else
			r_ctc_pending_add <= (w_ctc_add_en ? w_ctc_add_len : 32'h00000000);
	always @(*) begin
		if (_sv2v_0)
			;
		w_ctc_next = r_write_beats_to_commit + r_ctc_pending_add;
		if (sched_wr_commit_strobe)
			w_ctc_next = (w_ctc_next >= sched_wr_commit_beats ? w_ctc_next - sched_wr_commit_beats : 32'h00000000);
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_write_beats_to_commit <= 32'h00000000;
		else if (r_channel_reset_active)
			r_write_beats_to_commit <= 32'h00000000;
		else
			r_write_beats_to_commit <= w_ctc_next;
	assign w_write_issued = r_write_beats_remaining == 32'h00000000;
	assign w_write_complete = r_write_beats_to_commit == 32'h00000000;
	assign w_transfer_complete = w_read_complete && w_write_issued;
	assign w_next_src_addr = descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
	assign w_next_dst_addr = descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
	assign w_next_length = descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
	assign w_desc_chained = r_desc_chained;
	assign w_rd_prefetch_en = (cfg_rd_prefetch_enable && !w_is_ext) && !w_is_ext_in;
	assign w_rd_peek = (((((w_rd_prefetch_en && w_state_xfer_data) && !r_rd_ahead) && (r_read_beats_remaining == 32'h00000000)) && !w_write_issued) && w_desc_chained) && descriptor_valid;
	assign w_wr_advance = (((w_rd_prefetch_en && w_state_xfer_data) && w_write_issued) && w_desc_chained) && descriptor_valid;
	wire w_sched_rd_completing_this_cycle;
	wire w_sched_wr_completing_this_cycle;
	assign w_sched_rd_completing_this_cycle = sched_rd_done_strobe && (r_read_beats_remaining <= sched_rd_beats_done);
	assign w_sched_wr_completing_this_cycle = sched_wr_done_strobe && (r_write_beats_remaining <= sched_wr_beats_done);
	assign sched_rd_valid = (((r_current_state == 7'b0000100) && !w_read_complete) && !w_sched_rd_completing_this_cycle) && !w_rd_need_base;
	assign sched_rd_addr = r_src_addr;
	assign sched_rd_beats = (w_is_ext ? r_rd_run_remaining : r_read_beats_remaining);
	assign sched_wr_valid = ((((r_current_state == 7'b0000100) && (r_write_beats_remaining != 32'h00000000)) && !w_write_complete) && !w_sched_wr_completing_this_cycle) && !w_wr_need_base;
	assign sched_wr_addr = r_dst_addr;
	assign sched_wr_beats = (w_is_ext ? r_wr_run_remaining : r_write_beats_remaining);
	localparam signed [31:0] stream_pkg_STREAM_ADDRGEN_INDEX_WIDTH = 16;
	localparam signed [31:0] stream_pkg_STREAM_ADDR_WIDTH = 64;
	function automatic [63:0] stream_pkg_wrap_log2_to_mask;
		input reg [5:0] wrap_log2;
		stream_pkg_wrap_log2_to_mask = (wrap_log2 == 6'd0 ? {64 {1'sb0}} : (64'h0000000000000001 << wrap_log2) - 64'h0000000000000001);
	endfunction
	generate
		if (USE_ROW_COL_MAJOR_ADDRESSING != 0) begin : g_addrgen
			stream_run_addr_gen #(
				.ADDR_WIDTH(ADDR_WIDTH),
				.STRIDE_WIDTH(stream_pkg_STREAM_ADDRGEN_STRIDE_WIDTH),
				.INDEX_WIDTH(stream_pkg_STREAM_ADDRGEN_INDEX_WIDTH),
				.FIFO_DEPTH(4),
				.BEATS_WIDTH(32)
			) u_rd_addr_gen(
				.clk(clk),
				.rst_n(rst_n),
				.start(w_addrgen_start),
				.cfg_per_beat(w_rd_per_beat),
				.cfg_base_addr(r_descriptor[ADDR_WIDTH - 1:0]),
				.cfg_stride_0($signed(r_descriptor_ext[31-:32])),
				.cfg_stride_1($signed(r_descriptor_ext[63-:32])),
				.cfg_wrap_mask_0(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[85-:6]))),
				.cfg_wrap_mask_1(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[91-:6]))),
				.cfg_inner_count(r_descriptor_ext[79-:16]),
				.cfg_total_beats(r_descriptor[159-:32]),
				.o_base_valid(w_rd_base_valid),
				.i_base_ready(w_rd_base_ready),
				.o_base_addr(w_rd_base_addr)
			);
			stream_run_addr_gen #(
				.ADDR_WIDTH(ADDR_WIDTH),
				.STRIDE_WIDTH(stream_pkg_STREAM_ADDRGEN_STRIDE_WIDTH),
				.INDEX_WIDTH(stream_pkg_STREAM_ADDRGEN_INDEX_WIDTH),
				.FIFO_DEPTH(4),
				.BEATS_WIDTH(32)
			) u_wr_addr_gen(
				.clk(clk),
				.rst_n(rst_n),
				.start(w_addrgen_start),
				.cfg_per_beat(w_wr_per_beat),
				.cfg_base_addr(r_descriptor[63 + ADDR_WIDTH:64]),
				.cfg_stride_0($signed(r_descriptor_ext[127-:32])),
				.cfg_stride_1($signed(r_descriptor_ext[159-:32])),
				.cfg_wrap_mask_0(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[181-:6]))),
				.cfg_wrap_mask_1(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[187-:6]))),
				.cfg_inner_count(r_descriptor_ext[175-:16]),
				.cfg_total_beats(r_descriptor[159-:32]),
				.o_base_valid(w_wr_base_valid),
				.i_base_ready(w_wr_base_ready),
				.o_base_addr(w_wr_base_addr)
			);
		end
		else begin : g_no_addrgen
			assign w_rd_base_valid = 1'b0;
			assign w_rd_base_addr = 1'sb0;
			assign w_wr_base_valid = 1'b0;
			assign w_wr_base_addr = 1'sb0;
		end
	endgenerate
	assign descriptor_ready = ((r_current_state == 7'b0000001) || (r_current_state == 7'b0010000)) || w_wr_advance;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_timeout_counter <= 32'h00000000;
			r_timeout_strikes <= 8'h00;
			r_read_error_sticky <= 1'b0;
			r_write_error_sticky <= 1'b0;
			r_descriptor_error <= 1'b0;
		end
		else begin
			if (sched_wr_done_strobe || sched_wr_commit_strobe)
				r_timeout_counter <= 32'h00000000;
			else if (w_timeout_expired)
				r_timeout_counter <= 32'h00000000;
			else if (sched_wr_valid && !sched_wr_ready)
				r_timeout_counter <= r_timeout_counter + 1;
			else
				r_timeout_counter <= 32'h00000000;
			if (r_channel_reset_active || (r_current_state == 7'b0000001))
				r_timeout_strikes <= 8'h00;
			else if (sched_wr_done_strobe || sched_wr_commit_strobe)
				r_timeout_strikes <= 8'h00;
			else if (w_timeout_expired && !(&r_timeout_strikes))
				r_timeout_strikes <= r_timeout_strikes + 8'h01;
			if (descriptor_error)
				r_descriptor_error <= 1'b1;
			if (sched_rd_error)
				r_read_error_sticky <= 1'b1;
			if (sched_wr_error)
				r_write_error_sticky <= 1'b1;
			if ((sched_rd_error || sched_wr_error) || w_timeout_escalate)
				r_descriptor_error <= 1'b1;
			if (r_current_state == 7'b0000001) begin
				r_read_error_sticky <= 1'b0;
				r_write_error_sticky <= 1'b0;
				r_descriptor_error <= 1'b0;
			end
		end
	assign w_timeout_expired = cfg_sched_timeout_enable && (r_timeout_counter >= cfg_sched_timeout_cycles);
	assign w_timeout_escalate = (cfg_sched_timeout_limit != 8'd0) && (r_timeout_strikes >= cfg_sched_timeout_limit);
	assign w_hard_error = (((descriptor_error || sched_rd_error) || sched_wr_error) || r_read_error_sticky) || r_write_error_sticky;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
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
	localparam [7:0] stream_pkg_STREAM_EVENT_DESC_COMPLETE = 8'h01;
	localparam [7:0] stream_pkg_STREAM_EVENT_DESC_START = 8'h00;
	localparam [7:0] stream_pkg_STREAM_EVENT_ERROR = 8'h0f;
	localparam [7:0] stream_pkg_STREAM_EVENT_IRQ = 8'h07;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			r_mon_timestamp <= 1'sb0;
			r_error_pkt_sent <= 1'b0;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			if (r_current_state == 7'b0000001)
				r_error_pkt_sent <= 1'b0;
			case (r_current_state)
				7'b0000010: begin
					r_mon_valid <= 1'b1;
					r_mon_timestamp <= i_mon_time;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_DESC_START, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
				end
				7'b0000100:
					if (w_wr_advance) begin
						r_mon_valid <= 1'b1;
						r_mon_timestamp <= i_mon_time;
						if (r_descriptor[193])
							r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_IRQ, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
						else
							r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_DESC_COMPLETE, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
					end
				7'b0001000: begin
					r_mon_valid <= 1'b1;
					r_mon_timestamp <= i_mon_time;
					if (r_descriptor[193])
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_IRQ, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
					else
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_DESC_COMPLETE, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
				end
				7'b0100000:
					if (!r_error_pkt_sent) begin
						r_mon_valid <= 1'b1;
						r_mon_timestamp <= i_mon_time;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 4'h4, stream_pkg_STREAM_EVENT_ERROR, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {29'h00000000, r_write_error_sticky, r_read_error_sticky, 33'h000000000});
						r_error_pkt_sent <= 1'b1;
					end
				default:
					;
			endcase
		end
	assign scheduler_idle = (r_current_state == 7'b0000001) && !r_channel_reset_active;
	assign scheduler_state = r_current_state;
	assign sched_error = w_state_error;
	assign dbg_descriptor_error = r_descriptor_error;
	assign dbg_read_error_sticky = r_read_error_sticky;
	assign dbg_write_error_sticky = r_write_error_sticky;
	assign dbg_timeout_expired = w_timeout_expired;
	assign mon_valid = (GEN_MON ? r_mon_valid : 1'b0);
	assign mon_packet = (GEN_MON ? r_mon_packet : {128 {1'sb0}});
	assign mon_timestamp = (GEN_MON ? r_mon_timestamp : {64 {1'sb0}});
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
	cfg_sched_timeout_limit,
	cfg_sched_timeout_enable,
	cfg_sched_err_enable,
	cfg_sched_compl_enable,
	cfg_sched_perf_enable,
	cfg_desceng_prefetch,
	cfg_rd_prefetch_enable,
	cfg_desceng_fifo_thresh,
	cfg_desceng_addr0_base,
	cfg_desceng_addr0_limit,
	cfg_desceng_addr1_base,
	cfg_desceng_addr1_limit,
	descriptor_engine_idle,
	scheduler_idle,
	scheduler_state,
	sched_error,
	dbg_descriptor_error,
	dbg_read_error_sticky,
	dbg_write_error_sticky,
	dbg_timeout_expired,
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
	sched_wr_commit_strobe,
	sched_wr_commit_beats,
	sched_rd_error,
	sched_wr_error,
	i_mon_time,
	mon_valid,
	mon_ready,
	mon_packet,
	mon_timestamp
);
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter [0:0] GEN_MON = 1'b1;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] USE_ROW_COL_MAJOR_ADDRESSING = 1;
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
	input wire [31:0] cfg_sched_timeout_cycles;
	input wire [7:0] cfg_sched_timeout_limit;
	input wire cfg_sched_timeout_enable;
	input wire cfg_sched_err_enable;
	input wire cfg_sched_compl_enable;
	input wire cfg_sched_perf_enable;
	input wire cfg_desceng_prefetch;
	input wire cfg_rd_prefetch_enable;
	input wire [3:0] cfg_desceng_fifo_thresh;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_limit;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_limit;
	output wire descriptor_engine_idle;
	output wire scheduler_idle;
	output wire [6:0] scheduler_state;
	output wire sched_error;
	output wire dbg_descriptor_error;
	output wire dbg_read_error_sticky;
	output wire dbg_write_error_sticky;
	output wire dbg_timeout_expired;
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
	input wire sched_wr_commit_strobe;
	input wire [31:0] sched_wr_commit_beats;
	input wire sched_rd_error;
	input wire sched_wr_error;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	wire desceng_to_sched_valid;
	wire desceng_to_sched_ready;
	wire [255:0] desceng_to_sched_packet;
	wire [255:0] desceng_to_sched_ext_packet;
	wire desceng_to_sched_error;
	wire desceng_to_sched_eos;
	wire desceng_to_sched_eol;
	wire desceng_to_sched_eod;
	wire [1:0] desceng_to_sched_type;
	wire sched_channel_idle;
	wire desceng_mon_valid;
	wire desceng_mon_ready;
	wire [127:0] desceng_mon_packet;
	wire [63:0] desceng_mon_timestamp;
	wire sched_mon_valid;
	wire sched_mon_ready;
	wire [127:0] sched_mon_packet;
	wire [63:0] sched_mon_timestamp;
	function automatic signed [15:0] sv2v_cast_16_signed;
		input reg signed [15:0] inp;
		sv2v_cast_16_signed = inp;
	endfunction
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	function automatic signed [8:0] sv2v_cast_9_signed;
		input reg signed [8:0] inp;
		sv2v_cast_9_signed = inp;
	endfunction
	descriptor_engine #(
		.CHANNEL_ID(CHANNEL_ID),
		.GEN_MON(GEN_MON),
		.NUM_CHANNELS(NUM_CHANNELS),
		.CHAN_WIDTH(CHAN_WIDTH),
		.ADDR_WIDTH(ADDR_WIDTH),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING),
		.MON_AGENT_ID(sv2v_cast_16_signed(DESC_MON_AGENT_ID)),
		.MON_UNIT_ID(sv2v_cast_8_signed(MON_UNIT_ID)),
		.MON_CHANNEL_ID(sv2v_cast_9_signed(MON_CHANNEL_ID))
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
		.descriptor_ext_packet(desceng_to_sched_ext_packet),
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
		.i_mon_time(i_mon_time),
		.mon_valid(desceng_mon_valid),
		.mon_ready(desceng_mon_ready),
		.mon_packet(desceng_mon_packet),
		.mon_timestamp(desceng_mon_timestamp)
	);
	scheduler #(
		.CHANNEL_ID(CHANNEL_ID),
		.GEN_MON(GEN_MON),
		.NUM_CHANNELS(NUM_CHANNELS),
		.CHAN_WIDTH(CHAN_WIDTH),
		.ADDR_WIDTH(ADDR_WIDTH),
		.DATA_WIDTH(DATA_WIDTH),
		.USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING),
		.MON_AGENT_ID(sv2v_cast_16_signed(SCHED_MON_AGENT_ID)),
		.MON_UNIT_ID(sv2v_cast_8_signed(MON_UNIT_ID)),
		.MON_CHANNEL_ID(sv2v_cast_9_signed(MON_CHANNEL_ID))
	) u_scheduler(
		.clk(clk),
		.rst_n(rst_n),
		.cfg_channel_enable(cfg_channel_enable),
		.cfg_channel_reset(cfg_channel_reset),
		.cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
		.cfg_sched_timeout_limit(cfg_sched_timeout_limit),
		.cfg_sched_timeout_enable(cfg_sched_timeout_enable),
		.cfg_rd_prefetch_enable(cfg_rd_prefetch_enable),
		.scheduler_idle(scheduler_idle),
		.scheduler_state(scheduler_state),
		.sched_error(sched_error),
		.dbg_descriptor_error(dbg_descriptor_error),
		.dbg_read_error_sticky(dbg_read_error_sticky),
		.dbg_write_error_sticky(dbg_write_error_sticky),
		.dbg_timeout_expired(dbg_timeout_expired),
		.descriptor_valid(desceng_to_sched_valid),
		.descriptor_ready(desceng_to_sched_ready),
		.descriptor_packet(desceng_to_sched_packet),
		.descriptor_ext_packet(desceng_to_sched_ext_packet),
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
		.sched_wr_commit_strobe(sched_wr_commit_strobe),
		.sched_wr_commit_beats(sched_wr_commit_beats),
		.sched_rd_error(sched_rd_error),
		.sched_wr_error(sched_wr_error),
		.i_mon_time(i_mon_time),
		.mon_valid(sched_mon_valid),
		.mon_ready(sched_mon_ready),
		.mon_packet(sched_mon_packet),
		.mon_timestamp(sched_mon_timestamp)
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
		.monbus_timestamp_in({desceng_mon_timestamp, sched_mon_timestamp}),
		.monbus_valid(mon_valid),
		.monbus_ready(mon_ready),
		.monbus_packet(mon_packet),
		.monbus_timestamp(mon_timestamp),
		.grant_valid(),
		.grant(),
		.grant_id(),
		.last_grant()
	);
endmodule
module axi_monitor_addr_check (
	clk,
	aresetn,
	i_mon_time,
	cmd_addr,
	cmd_id,
	cmd_valid,
	cmd_ready,
	cfg_addr_check_enable,
	cfg_debug_enable,
	cfg_error_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	addr_pkt_valid,
	addr_pkt_ready,
	addr_pkt_data,
	addr_pkt_timestamp
);
	reg _sv2v_0;
	parameter signed [31:0] N_ADDR_RANGES = 4;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 6;
	parameter [7:0] UNIT_ID = 8'h00;
	parameter [15:0] AGENT_ID = 16'h0000;
	parameter [0:0] IS_READ = 1'b1;
	parameter [N_ADDR_RANGES - 1:0] ADDR_RANGE_IS_ERROR = 1'sb0;
	parameter signed [31:0] M = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	input wire clk;
	input wire aresetn;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	input wire [M - 1:0] cmd_addr;
	input wire [IW - 1:0] cmd_id;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire cfg_addr_check_enable;
	input wire cfg_debug_enable;
	input wire cfg_error_enable;
	input wire [N_ADDR_RANGES - 1:0] cfg_addr_range_enable;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_low;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_high;
	output wire addr_pkt_valid;
	input wire addr_pkt_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] addr_pkt_data;
	output wire [63:0] addr_pkt_timestamp;
	wire cmd_fire;
	reg [N_ADDR_RANGES - 1:0] raw_hit;
	assign cmd_fire = (cmd_valid && cmd_ready) && cfg_addr_check_enable;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				raw_hit[i] = (cfg_addr_range_enable[i] && (cmd_addr >= cfg_addr_range_low[i * M+:M])) && (cmd_addr <= cfg_addr_range_high[i * M+:M]);
		end
	end
	reg [N_ADDR_RANGES - 1:0] debug_hit;
	reg [N_ADDR_RANGES - 1:0] err_range_en;
	wire err_hit;
	wire err_ranges_exist;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				begin
					debug_hit[i] = raw_hit[i] && !ADDR_RANGE_IS_ERROR[i];
					err_range_en[i] = cfg_addr_range_enable[i] && ADDR_RANGE_IS_ERROR[i];
				end
		end
	end
	assign err_hit = |(raw_hit & ADDR_RANGE_IS_ERROR);
	assign err_ranges_exist = |err_range_en;
	reg [N_ADDR_RANGES - 1:0] match_set;
	wire miss_set;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				match_set[i] = (cmd_fire && cfg_debug_enable) && debug_hit[i];
		end
	end
	assign miss_set = ((cmd_fire && cfg_error_enable) && err_ranges_exist) && !err_hit;
	reg [N_ADDR_RANGES - 1:0] r_match_pending;
	reg [(N_ADDR_RANGES * M) - 1:0] r_match_addr;
	reg [(N_ADDR_RANGES * IW) - 1:0] r_match_id;
	reg r_miss_pending;
	reg [M - 1:0] r_miss_addr;
	reg [IW - 1:0] r_miss_id;
	wire [N_ADDR_RANGES - 1:0] match_emit_oh;
	wire match_emit_any;
	reg [3:0] match_emit_idx;
	assign match_emit_any = |r_match_pending;
	reg [N_ADDR_RANGES - 1:0] w_match_pick;
	always @(*) begin
		if (_sv2v_0)
			;
		w_match_pick = 1'sb0;
		begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (r_match_pending[i] && (w_match_pick == {N_ADDR_RANGES {1'sb0}}))
					w_match_pick[i] = 1'b1;
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_emit_hold;
	reg r_emit_hold_miss;
	reg r_emit_held;
	assign match_emit_oh = (r_emit_held ? r_emit_hold : w_match_pick);
	function automatic signed [3:0] sv2v_cast_4_signed;
		input reg signed [3:0] inp;
		sv2v_cast_4_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		match_emit_idx = 4'h0;
		begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (match_emit_oh[i])
					match_emit_idx = sv2v_cast_4_signed(i);
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_shadow_valid;
	reg [(N_ADDR_RANGES * M) - 1:0] r_shadow_addr;
	reg [(N_ADDR_RANGES * IW) - 1:0] r_shadow_id;
	reg r_miss_shadow_valid;
	reg [M - 1:0] r_miss_shadow_addr;
	reg [IW - 1:0] r_miss_shadow_id;
	wire emit_is_miss;
	assign emit_is_miss = (r_emit_held ? r_emit_hold_miss : r_miss_pending);
	assign addr_pkt_valid = (r_miss_pending || match_emit_any) && cfg_addr_check_enable;
	wire accept;
	assign accept = addr_pkt_valid && addr_pkt_ready;
	wire w_miss_presented;
	wire w_miss_accept;
	assign w_miss_presented = addr_pkt_valid && emit_is_miss;
	assign w_miss_accept = accept && emit_is_miss;
	reg [N_ADDR_RANGES - 1:0] w_presented;
	reg [N_ADDR_RANGES - 1:0] w_range_accept;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				begin
					w_presented[i] = (addr_pkt_valid && !emit_is_miss) && match_emit_oh[i];
					w_range_accept[i] = (accept && !emit_is_miss) && match_emit_oh[i];
				end
		end
	end
	always @(posedge clk or negedge aresetn)
		if (!aresetn) begin
			r_match_pending <= 1'sb0;
			r_emit_hold <= 1'sb0;
			r_emit_hold_miss <= 1'b0;
			r_emit_held <= 1'b0;
			r_shadow_valid <= 1'sb0;
			r_shadow_addr <= 1'sb0;
			r_shadow_id <= 1'sb0;
			r_match_addr <= 1'sb0;
			r_match_id <= 1'sb0;
			r_miss_pending <= 1'b0;
			r_miss_addr <= 1'sb0;
			r_miss_id <= 1'sb0;
			r_miss_shadow_valid <= 1'b0;
			r_miss_shadow_addr <= 1'sb0;
			r_miss_shadow_id <= 1'sb0;
		end
		else begin
			if (accept)
				r_emit_held <= 1'b0;
			else if (addr_pkt_valid && !addr_pkt_ready) begin
				r_emit_held <= 1'b1;
				r_emit_hold <= match_emit_oh;
				r_emit_hold_miss <= emit_is_miss;
			end
			begin : sv2v_autoblock_7
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (w_range_accept[i]) begin
						if (match_set[i]) begin
							r_match_addr[i * M+:M] <= cmd_addr;
							r_match_id[i * IW+:IW] <= cmd_id;
						end
						else if (r_shadow_valid[i]) begin
							r_match_addr[i * M+:M] <= r_shadow_addr[i * M+:M];
							r_match_id[i * IW+:IW] <= r_shadow_id[i * IW+:IW];
						end
					end
					else if (match_set[i] && !w_presented[i]) begin
						r_match_addr[i * M+:M] <= cmd_addr;
						r_match_id[i * IW+:IW] <= cmd_id;
					end
			end
			begin : sv2v_autoblock_8
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (w_range_accept[i])
						r_shadow_valid[i] <= 1'b0;
					else if (match_set[i] && w_presented[i]) begin
						r_shadow_valid[i] <= 1'b1;
						r_shadow_addr[i * M+:M] <= cmd_addr;
						r_shadow_id[i * IW+:IW] <= cmd_id;
					end
			end
			begin : sv2v_autoblock_9
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (match_set[i])
						r_match_pending[i] <= 1'b1;
					else if (w_range_accept[i])
						r_match_pending[i] <= r_shadow_valid[i];
			end
			if (w_miss_accept) begin
				if (miss_set) begin
					r_miss_addr <= cmd_addr;
					r_miss_id <= cmd_id;
				end
				else if (r_miss_shadow_valid) begin
					r_miss_addr <= r_miss_shadow_addr;
					r_miss_id <= r_miss_shadow_id;
				end
			end
			else if (miss_set && !w_miss_presented) begin
				r_miss_addr <= cmd_addr;
				r_miss_id <= cmd_id;
			end
			if (w_miss_accept)
				r_miss_shadow_valid <= 1'b0;
			else if (miss_set && w_miss_presented) begin
				r_miss_shadow_valid <= 1'b1;
				r_miss_shadow_addr <= cmd_addr;
				r_miss_shadow_id <= cmd_id;
			end
			if (miss_set)
				r_miss_pending <= 1'b1;
			else if (w_miss_accept && !r_miss_shadow_valid)
				r_miss_pending <= 1'b0;
		end
	localparam [3:0] MISS_RANGE_SENTINEL = 4'hf;
	reg [3:0] pkt_type_field;
	reg [7:0] event_code_field;
	reg [3:0] emit_idx;
	reg [M - 1:0] emit_addr;
	reg [IW - 1:0] emit_id;
	wire [8:0] channel_id_field;
	wire [63:0] event_data_field;
	wire [59:0] addr_payload;
	localparam [3:0] monitor_common_pkg_PktTypeAddrMatch = 4'h8;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	always @(*) begin
		if (_sv2v_0)
			;
		if (emit_is_miss) begin
			pkt_type_field = monitor_common_pkg_PktTypeError;
			event_code_field = 8'h0d;
			emit_idx = MISS_RANGE_SENTINEL;
			emit_addr = r_miss_addr;
			emit_id = r_miss_id;
		end
		else begin
			pkt_type_field = monitor_common_pkg_PktTypeAddrMatch;
			event_code_field = 8'h01;
			emit_idx = match_emit_idx;
			emit_addr = 1'sb0;
			emit_id = 1'sb0;
			begin : sv2v_autoblock_10
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (match_emit_oh[i]) begin
						emit_addr = r_match_addr[i * M+:M];
						emit_id = r_match_id[i * IW+:IW];
					end
			end
		end
	end
	generate
		if (IW >= 9) begin : g_chan_id_wide
			assign channel_id_field = emit_id[8:0];
		end
		else begin : g_chan_id_narrow
			assign channel_id_field = {{9 - IW {1'b0}}, emit_id};
		end
		if (M >= 60) begin : g_addr_wide
			assign addr_payload = emit_addr[59:0];
		end
		else begin : g_addr_narrow
			assign addr_payload = {{60 - M {1'b0}}, emit_addr};
		end
	endgenerate
	assign event_data_field = {emit_idx[3:0], addr_payload};
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
	assign addr_pkt_data = monitor_common_pkg_create_monitor_packet(pkt_type_field, 4'h0, event_code_field, channel_id_field, UNIT_ID, AGENT_ID, event_data_field);
	assign addr_pkt_timestamp = i_mon_time;
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_lite (
	aclk,
	aresetn,
	clear,
	i_mon_time,
	cmd_addr,
	cmd_id,
	cmd_len,
	cmd_valid,
	cmd_ready,
	data_id,
	data_last,
	data_resp,
	data_valid,
	data_ready,
	resp_id,
	resp_code,
	resp_valid,
	resp_ready,
	cfg_freq_sel,
	cfg_timeout_cnt,
	cfg_error_enable,
	cfg_compl_enable,
	cfg_timeout_enable,
	cfg_threshold_enable,
	cfg_active_trans_threshold,
	cfg_latency_threshold,
	cfg_axi_pkt_mask,
	cfg_addr_check_enable,
	cfg_addr_match_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	active_count,
	busy,
	perf_completed_count,
	perf_error_count,
	dropped_count,
	refused_count
);
	reg _sv2v_0;
	parameter [7:0] UNIT_ID = 8'h09;
	parameter [15:0] AGENT_ID = 16'h0063;
	parameter signed [31:0] MAX_TRANSACTIONS = 8;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter signed [31:0] TS_WIDTH = 16;
	parameter signed [31:0] AGE_WIDTH = 16;
	parameter signed [31:0] OUT_DEPTH = 4;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] ADDR_RANGE_IS_ERROR = 1'sb0;
	parameter signed [31:0] CFI_MIN_FREQ_MHZ = 5;
	parameter signed [31:0] CFI_MAX_FREQ_MHZ = 220;
	parameter signed [31:0] CFI_NUM_FREQ_ENTRIES = 16;
	parameter signed [31:0] CFI_FREQ_STRATEGY = 0;
	parameter signed [31:0] N = MAX_TRANSACTIONS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = (ID_WIDTH > 0 ? ID_WIDTH : 1);
	parameter signed [31:0] SW = (N > 1 ? $clog2(N) : 1);
	parameter signed [31:0] CW = $clog2(N + 1);
	parameter signed [31:0] SELW = (CFI_NUM_FREQ_ENTRIES > 1 ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1);
	parameter signed [31:0] NAR = (N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1);
	input wire aclk;
	input wire aresetn;
	input wire clear;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	input wire [AW - 1:0] cmd_addr;
	input wire [IW - 1:0] cmd_id;
	input wire [7:0] cmd_len;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire [IW - 1:0] data_id;
	input wire data_last;
	input wire [1:0] data_resp;
	input wire data_valid;
	input wire data_ready;
	input wire [IW - 1:0] resp_id;
	input wire [1:0] resp_code;
	input wire resp_valid;
	input wire resp_ready;
	input wire [SELW - 1:0] cfg_freq_sel;
	input wire [15:0] cfg_timeout_cnt;
	input wire cfg_error_enable;
	input wire cfg_compl_enable;
	input wire cfg_timeout_enable;
	input wire cfg_threshold_enable;
	input wire [15:0] cfg_active_trans_threshold;
	input wire [31:0] cfg_latency_threshold;
	input wire [15:0] cfg_axi_pkt_mask;
	input wire cfg_addr_check_enable;
	input wire cfg_addr_match_enable;
	input wire [NAR - 1:0] cfg_addr_range_enable;
	input wire [(NAR * AW) - 1:0] cfg_addr_range_low;
	input wire [(NAR * AW) - 1:0] cfg_addr_range_high;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire [7:0] active_count;
	output wire busy;
	output wire [15:0] perf_completed_count;
	output wire [15:0] perf_error_count;
	output wire [15:0] dropped_count;
	output wire [15:0] refused_count;
	wire cmd_hs = cmd_valid && cmd_ready;
	wire data_hs = data_valid && data_ready;
	wire resp_hs = (resp_valid && resp_ready) && !IS_READ;
	reg [TS_WIDTH - 1:0] r_now;
	reg [AGE_WIDTH - 1:0] r_us;
	wire w_tick;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_now <= 1'sb0;
			r_us <= 1'sb0;
		end
		else begin
			r_now <= r_now + 1'b1;
			if (w_tick)
				r_us <= r_us + 1'b1;
		end
	counter_freq_invariant #(
		.COUNTER_WIDTH(1),
		.MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
		.MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
		.NUM_FREQ_ENTRIES(CFI_NUM_FREQ_ENTRIES),
		.FREQ_STRATEGY(CFI_FREQ_STRATEGY)
	) u_tick(
		.clk(aclk),
		.rst_n(aresetn),
		.sync_reset_n(1'b1),
		.freq_sel(cfg_freq_sel),
		.tick(w_tick),
		.o_counter()
	);
	reg [N - 1:0] r_valid;
	reg [(N * IW) - 1:0] r_id;
	reg [(N * AW) - 1:0] r_addr;
	reg [(N * 8) - 1:0] r_beats;
	reg [N - 1:0] r_phase;
	reg [N - 1:0] r_err;
	reg [N - 1:0] r_tmo;
	reg [(N * TS_WIDTH) - 1:0] r_ts0;
	reg [(N * AGE_WIDTH) - 1:0] r_us0;
	reg [N - 1:0] r_head;
	reg [N - 1:0] r_tail;
	reg [N - 1:0] r_has_next;
	reg [(N * SW) - 1:0] r_next;
	reg w_have_free;
	reg [SW - 1:0] w_free_idx;
	function automatic signed [SW - 1:0] sv2v_cast_6C2E3_signed;
		input reg signed [SW - 1:0] inp;
		sv2v_cast_6C2E3_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_have_free = 1'b0;
		w_free_idx = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = N - 1; i >= 0; i = i - 1)
				if (!r_valid[i]) begin
					w_have_free = 1'b1;
					w_free_idx = sv2v_cast_6C2E3_signed(i);
				end
		end
	end
	reg [N - 1:0] w_dmatch;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_dmatch[i] = ((r_valid[i] && r_head[i]) && !r_phase[i]) && (!IS_AXI || (r_id[i * IW+:IW] == data_id));
		end
	end
	function automatic [SW - 1:0] onehot_idx;
		input reg [N - 1:0] oh;
		reg [SW - 1:0] r;
		begin
			r = 1'sb0;
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r = r | (oh[i] ? sv2v_cast_6C2E3_signed(i) : {SW {1'sb0}});
			end
			onehot_idx = r;
		end
	endfunction
	wire w_dhit;
	wire [SW - 1:0] w_dslot;
	reg [(N * SW) - 1:0] r_wq;
	reg [SW - 1:0] r_wq_wp;
	reg [SW - 1:0] r_wq_rp;
	reg [CW - 1:0] r_wq_cnt;
	wire w_wq_empty = r_wq_cnt == {CW {1'sb0}};
	wire [SW - 1:0] w_wq_head = r_wq[r_wq_rp * SW+:SW];
	reg [7:0] r_early_beats;
	reg r_early_last;
	reg r_early_any;
	generate
		if (IS_READ) begin : g_rd_attr
			assign w_dhit = |w_dmatch;
			assign w_dslot = onehot_idx(w_dmatch);
		end
		else begin : g_wr_attr
			assign w_dhit = !w_wq_empty && r_valid[w_wq_head];
			assign w_dslot = w_wq_head;
		end
	endgenerate
	reg [N - 1:0] w_bmatch;
	wire w_bhit;
	wire [SW - 1:0] w_bslot;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_bmatch[i] = ((r_valid[i] && r_head[i]) && r_phase[i]) && (!IS_AXI || (r_id[i * IW+:IW] == resp_id));
		end
	end
	assign w_bhit = |w_bmatch;
	assign w_bslot = onehot_idx(w_bmatch);
	reg [N - 1:0] w_beats_zero;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_beats_zero[i] = r_beats[i * 8+:8] == 8'd0;
		end
	end
	wire w_dbeats_zero = w_beats_zero[w_dslot];
	wire w_data_err = (((data_hs && w_dhit) && IS_READ) && data_resp[1]) && !r_err[w_dslot];
	wire w_data_orph = (data_hs && !w_dhit) && IS_READ;
	wire w_same_w = ((((cmd_hs && w_have_free) && data_hs) && !w_dhit) && !IS_READ) && !r_early_any;
	wire w_last_early = data_hs && (((w_dhit && data_last) && !w_dbeats_zero) || ((w_same_w && data_last) && (cmd_len != 8'd0)));
	wire w_last_late = ((data_hs && w_dhit) && !data_last) && w_dbeats_zero;
	wire w_data_done = (data_hs && w_dhit) && data_last;
	wire w_early_w = ((data_hs && !w_dhit) && !IS_READ) && !w_same_w;
	wire w_early_ovf = (w_early_w && r_early_last) && !(cmd_hs && w_have_free);
	wire w_resp_err = ((resp_hs && w_bhit) && resp_code[1]) && !r_err[w_bslot];
	wire w_resp_orph = resp_hs && !w_bhit;
	wire w_resp_done = resp_hs && w_bhit;
	wire w_refused = cmd_hs && !w_have_free;
	wire w_compl = (IS_READ ? w_data_done : w_resp_done);
	wire [SW - 1:0] w_compl_slot = (IS_READ ? w_dslot : w_bslot);
	wire w_compl_clean = (w_compl && !r_err[w_compl_slot]) && !(IS_READ ? data_resp[1] || w_last_early : resp_code[1]);
	wire [TS_WIDTH - 1:0] w_latency = r_now - r_ts0[w_compl_slot * TS_WIDTH+:TS_WIDTH];
	wire w_free_has_next = r_has_next[w_compl_slot];
	wire [SW - 1:0] w_free_next = r_next[w_compl_slot * SW+:SW];
	reg [SW - 1:0] r_scan;
	wire [AGE_WIDTH - 1:0] w_scan_age = r_us - r_us0[r_scan * AGE_WIDTH+:AGE_WIDTH];
	wire w_never = cfg_timeout_cnt == 16'hffff;
	wire w_scan_hit = (((cfg_timeout_enable && !w_never) && r_valid[r_scan]) && !r_tmo[r_scan]) && (w_scan_age >= cfg_timeout_cnt[AGE_WIDTH - 1:0]);
	reg [AGE_WIDTH - 1:0] r_cmd_stall_us0;
	reg r_cmd_stalling;
	reg r_cmd_stall_rpt;
	wire [AGE_WIDTH - 1:0] w_cmd_stall_age = r_us - r_cmd_stall_us0;
	wire w_cmd_tmo = (((((cfg_timeout_enable && !w_never) && cmd_valid) && !cmd_ready) && r_cmd_stalling) && !r_cmd_stall_rpt) && (w_cmd_stall_age >= cfg_timeout_cnt[AGE_WIDTH - 1:0]);
	reg [CW - 1:0] w_occupancy;
	function automatic [CW - 1:0] sv2v_cast_3D2D3;
		input reg [CW - 1:0] inp;
		sv2v_cast_3D2D3 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_occupancy = 1'sb0;
		begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_occupancy = w_occupancy + sv2v_cast_3D2D3(r_valid[i]);
		end
	end
	reg r_over_thresh;
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	wire w_over_thresh = (sv2v_cast_16(w_occupancy) >= cfg_active_trans_threshold) && (cfg_active_trans_threshold != 16'd0);
	wire w_thresh_evt = (cfg_threshold_enable && w_over_thresh) && !r_over_thresh;
	wire w_alloc = cmd_hs && w_have_free;
	wire [7:0] w_alloc_beats = (!IS_READ && r_early_any ? cmd_len - r_early_beats : (w_same_w && (cmd_len != 8'd0) ? cmd_len - 8'd1 : cmd_len));
	wire w_alloc_done = ((!IS_READ && r_early_any) && r_early_last) || (w_same_w && data_last);
	wire w_dprogress = data_hs && w_dhit;
	reg [N - 1:0] w_same_tail;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_same_tail[i] = (r_valid[i] && r_tail[i]) && (!IS_AXI || (r_id[i * IW+:IW] == cmd_id));
		end
	end
	wire w_tail_freeing = w_compl && w_same_tail[w_compl_slot];
	wire w_link = |w_same_tail && !w_tail_freeing;
	wire [SW - 1:0] w_tail_slot = onehot_idx(w_same_tail);
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_valid <= 1'sb0;
			r_phase <= 1'sb0;
			r_err <= 1'sb0;
			r_tmo <= 1'sb0;
			r_id <= 1'sb0;
			r_addr <= 1'sb0;
			r_beats <= 1'sb0;
			r_ts0 <= 1'sb0;
			r_us0 <= 1'sb0;
			r_head <= 1'sb0;
			r_tail <= 1'sb0;
			r_has_next <= 1'sb0;
			r_next <= 1'sb0;
			r_wq <= 1'sb0;
			r_wq_wp <= 1'sb0;
			r_wq_rp <= 1'sb0;
			r_wq_cnt <= 1'sb0;
			r_early_beats <= 1'sb0;
			r_early_last <= 1'b0;
			r_early_any <= 1'b0;
			r_scan <= 1'sb0;
			r_cmd_stall_us0 <= 1'sb0;
			r_cmd_stalling <= 1'b0;
			r_cmd_stall_rpt <= 1'b0;
			r_over_thresh <= 1'b0;
		end
		else if (clear) begin
			r_valid <= 1'sb0;
			r_err <= 1'sb0;
			r_tmo <= 1'sb0;
			r_wq_wp <= 1'sb0;
			r_wq_rp <= 1'sb0;
			r_wq_cnt <= 1'sb0;
			r_early_beats <= 1'sb0;
			r_early_last <= 1'b0;
			r_early_any <= 1'b0;
			r_scan <= 1'sb0;
			r_cmd_stalling <= 1'b0;
			r_cmd_stall_rpt <= 1'b0;
			r_over_thresh <= 1'b0;
		end
		else begin
			if (w_alloc) begin
				r_valid[w_free_idx] <= 1'b1;
				r_id[w_free_idx * IW+:IW] <= cmd_id;
				r_addr[w_free_idx * AW+:AW] <= cmd_addr;
				r_beats[w_free_idx * 8+:8] <= w_alloc_beats;
				r_phase[w_free_idx] <= w_alloc_done;
				r_err[w_free_idx] <= w_same_w && w_last_early;
				r_tmo[w_free_idx] <= 1'b0;
				r_ts0[w_free_idx * TS_WIDTH+:TS_WIDTH] <= r_now;
				r_us0[w_free_idx * AGE_WIDTH+:AGE_WIDTH] <= r_us;
				r_head[w_free_idx] <= !w_link;
				r_tail[w_free_idx] <= 1'b1;
				r_has_next[w_free_idx] <= 1'b0;
				if (w_link) begin
					r_tail[w_tail_slot] <= 1'b0;
					r_has_next[w_tail_slot] <= 1'b1;
					r_next[w_tail_slot * SW+:SW] <= w_free_idx;
				end
				if (!IS_READ) begin
					if (!w_alloc_done) begin
						r_wq[r_wq_wp * SW+:SW] <= w_free_idx;
						r_wq_wp <= r_wq_wp + 1'b1;
					end
					r_early_beats <= 1'sb0;
					r_early_last <= 1'b0;
					r_early_any <= 1'b0;
				end
			end
			if (w_dprogress) begin
				r_us0[w_dslot * AGE_WIDTH+:AGE_WIDTH] <= r_us;
				if (!w_dbeats_zero)
					r_beats[w_dslot * 8+:8] <= r_beats[w_dslot * 8+:8] - 8'd1;
				if ((w_data_err || w_last_early) || w_last_late)
					r_err[w_dslot] <= 1'b1;
				if (data_last) begin
					if (IS_READ)
						r_valid[w_dslot] <= 1'b0;
					else begin
						r_phase[w_dslot] <= 1'b1;
						r_wq_rp <= r_wq_rp + 1'b1;
					end
				end
			end
			if (w_early_w && !w_early_ovf) begin
				r_early_any <= 1'b1;
				r_early_beats <= (w_alloc ? 8'd0 : r_early_beats) + 8'd1;
				r_early_last <= data_last || (r_early_last && !w_alloc);
			end
			if (resp_hs && w_bhit)
				r_valid[w_bslot] <= 1'b0;
			if (w_compl && w_free_has_next)
				r_head[w_free_next] <= 1'b1;
			case ({(w_alloc && !IS_READ) && !w_alloc_done, (w_dprogress && data_last) && !IS_READ})
				2'b10: r_wq_cnt <= r_wq_cnt + 1'b1;
				2'b01: r_wq_cnt <= r_wq_cnt - 1'b1;
				default:
					;
			endcase
			r_scan <= (r_scan == sv2v_cast_6C2E3_signed(N - 1) ? {SW {1'sb0}} : r_scan + 1'b1);
			if (w_scan_hit)
				r_tmo[r_scan] <= 1'b1;
			if (cmd_valid && !cmd_ready) begin
				if (!r_cmd_stalling) begin
					r_cmd_stalling <= 1'b1;
					r_cmd_stall_us0 <= r_us;
				end
				if (w_cmd_tmo)
					r_cmd_stall_rpt <= 1'b1;
			end
			else begin
				r_cmd_stalling <= 1'b0;
				r_cmd_stall_rpt <= 1'b0;
			end
			r_over_thresh <= w_over_thresh;
		end
	reg r_e_resp_err;
	reg r_e_data_err;
	reg r_e_last_early;
	reg r_e_last_late;
	reg r_e_resp_orph;
	reg r_e_data_orph;
	reg r_e_early_ovf;
	reg r_e_scan_hit;
	reg r_e_cmd_tmo;
	reg r_e_compl;
	reg r_e_thresh;
	reg r_lat_pend;
	reg [IW - 1:0] r_lat_id;
	reg [AW - 1:0] r_lat_addr;
	reg [15:0] r_lat_latency;
	wire w_lat_take;
	wire w_lat_hit;
	reg r_tmo_pend;
	reg [7:0] r_tmo_code;
	reg [IW - 1:0] r_tmo_id;
	reg [AW - 1:0] r_tmo_addr;
	wire w_tmo_held_take;
	wire w_tmo_saved;
	wire w_tmo_save_scan;
	reg r_e_scan_phase;
	reg r_e_data_decerr;
	reg r_e_resp_decerr;
	reg [SW - 1:0] r_e_dslot;
	reg [SW - 1:0] r_e_bslot;
	reg [SW - 1:0] r_e_tslot;
	reg [SW - 1:0] r_e_cslot;
	reg [IW - 1:0] r_e_data_id;
	reg [IW - 1:0] r_e_resp_id;
	reg [IW - 1:0] r_e_cmd_id;
	reg [AW - 1:0] r_e_cmd_addr;
	reg [15:0] r_e_latency;
	reg [CW - 1:0] r_e_occupancy;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_e_resp_err <= 1'b0;
			r_e_data_err <= 1'b0;
			r_e_last_early <= 1'b0;
			r_e_last_late <= 1'b0;
			r_e_resp_orph <= 1'b0;
			r_e_data_orph <= 1'b0;
			r_e_early_ovf <= 1'b0;
			r_e_scan_hit <= 1'b0;
			r_e_cmd_tmo <= 1'b0;
			r_e_compl <= 1'b0;
			r_e_thresh <= 1'b0;
			r_lat_pend <= 1'b0;
			r_lat_id <= 1'sb0;
			r_lat_addr <= 1'sb0;
			r_lat_latency <= 1'sb0;
			r_tmo_pend <= 1'b0;
			r_tmo_code <= 1'sb0;
			r_tmo_id <= 1'sb0;
			r_tmo_addr <= 1'sb0;
			r_e_scan_phase <= 1'b0;
			r_e_data_decerr <= 1'b0;
			r_e_resp_decerr <= 1'b0;
			r_e_dslot <= 1'sb0;
			r_e_bslot <= 1'sb0;
			r_e_tslot <= 1'sb0;
			r_e_cslot <= 1'sb0;
			r_e_data_id <= 1'sb0;
			r_e_resp_id <= 1'sb0;
			r_e_cmd_id <= 1'sb0;
			r_e_cmd_addr <= 1'sb0;
			r_e_latency <= 1'sb0;
			r_e_occupancy <= 1'sb0;
		end
		else begin
			r_e_resp_err <= w_resp_err && !clear;
			r_e_data_err <= w_data_err && !clear;
			r_e_last_early <= w_last_early && !clear;
			r_e_last_late <= w_last_late && !clear;
			r_e_resp_orph <= w_resp_orph && !clear;
			r_e_data_orph <= w_data_orph && !clear;
			r_e_early_ovf <= w_early_ovf && !clear;
			r_e_scan_hit <= w_scan_hit && !clear;
			r_e_cmd_tmo <= w_cmd_tmo && !clear;
			r_e_compl <= w_compl_clean && !clear;
			r_e_thresh <= w_thresh_evt && !clear;
			if (clear)
				r_lat_pend <= 1'b0;
			else if (w_lat_hit && (!r_lat_pend || w_lat_take)) begin
				r_lat_pend <= 1'b1;
				r_lat_id <= r_id[r_e_cslot * IW+:IW];
				r_lat_addr <= r_addr[r_e_cslot * AW+:AW];
				r_lat_latency <= r_e_latency;
			end
			else if (w_lat_take)
				r_lat_pend <= 1'b0;
			if (clear)
				r_tmo_pend <= 1'b0;
			else if (w_tmo_saved) begin
				r_tmo_pend <= 1'b1;
				if (w_tmo_save_scan) begin
					r_tmo_code <= (r_e_scan_phase ? 8'h02 : 8'h01);
					r_tmo_id <= r_id[r_e_tslot * IW+:IW];
					r_tmo_addr <= r_addr[r_e_tslot * AW+:AW];
				end
				else begin
					r_tmo_code <= 8'h00;
					r_tmo_id <= r_e_cmd_id;
					r_tmo_addr <= r_e_cmd_addr;
				end
			end
			else if (w_tmo_held_take)
				r_tmo_pend <= 1'b0;
			r_e_scan_phase <= r_phase[r_scan];
			r_e_data_decerr <= data_resp[0];
			r_e_resp_decerr <= resp_code[0];
			r_e_dslot <= (w_dhit ? w_dslot : w_free_idx);
			r_e_bslot <= w_bslot;
			r_e_tslot <= r_scan;
			r_e_cslot <= w_compl_slot;
			r_e_data_id <= data_id;
			r_e_resp_id <= resp_id;
			r_e_cmd_id <= cmd_id;
			r_e_cmd_addr <= cmd_addr;
			r_e_latency <= sv2v_cast_16(w_latency);
			r_e_occupancy <= w_occupancy;
		end
	assign w_lat_hit = (r_e_compl && cfg_threshold_enable) && ({{16 {1'b0}}, r_e_latency} > cfg_latency_threshold);
	function automatic type_allowed;
		input reg [3:0] t;
		type_allowed = !cfg_axi_pkt_mask[t];
	endfunction
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	wire w_err_en = cfg_error_enable && type_allowed(monitor_common_pkg_PktTypeError);
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	wire w_tmo_en = type_allowed(monitor_common_pkg_PktTypeTimeout);
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	wire w_cmp_en = cfg_compl_enable && type_allowed(monitor_common_pkg_PktTypeCompletion);
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	wire w_thr_en = type_allowed(monitor_common_pkg_PktTypeThreshold);
	reg w_err_v;
	reg [7:0] w_err_code;
	reg [SW - 1:0] w_err_slot;
	reg w_err_has_slot;
	reg [IW - 1:0] w_err_id;
	always @(*) begin
		if (_sv2v_0)
			;
		w_err_v = 1'b0;
		w_err_code = 1'sb0;
		w_err_slot = 1'sb0;
		w_err_has_slot = 1'b0;
		w_err_id = 1'sb0;
		if (r_e_resp_err) begin
			w_err_v = 1'b1;
			w_err_code = (r_e_resp_decerr ? 8'h01 : 8'h00);
			w_err_slot = r_e_bslot;
			w_err_has_slot = 1'b1;
		end
		else if (r_e_data_err) begin
			w_err_v = 1'b1;
			w_err_code = (r_e_data_decerr ? 8'h01 : 8'h00);
			w_err_slot = r_e_dslot;
			w_err_has_slot = 1'b1;
		end
		else if (r_e_last_early) begin
			w_err_v = 1'b1;
			w_err_code = 8'h05;
			w_err_slot = r_e_dslot;
			w_err_has_slot = 1'b1;
		end
		else if (r_e_last_late) begin
			w_err_v = 1'b1;
			w_err_code = 8'h0b;
			w_err_slot = r_e_dslot;
			w_err_has_slot = 1'b1;
		end
		else if (r_e_resp_orph) begin
			w_err_v = 1'b1;
			w_err_code = 8'h03;
			w_err_id = r_e_resp_id;
		end
		else if (r_e_data_orph) begin
			w_err_v = 1'b1;
			w_err_code = 8'h02;
			w_err_id = r_e_data_id;
		end
		else if (r_e_early_ovf) begin
			w_err_v = 1'b1;
			w_err_code = 8'h09;
		end
		w_err_v = w_err_v && w_err_en;
	end
	reg [3:0] w_err_fired;
	function automatic [3:0] sv2v_cast_4;
		input reg [3:0] inp;
		sv2v_cast_4 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_err_fired = (((((sv2v_cast_4(r_e_resp_err) + sv2v_cast_4(r_e_data_err)) + sv2v_cast_4(r_e_last_early)) + sv2v_cast_4(r_e_last_late)) + sv2v_cast_4(r_e_resp_orph)) + sv2v_cast_4(r_e_data_orph)) + sv2v_cast_4(r_e_early_ovf);
		if (!w_err_en)
			w_err_fired = 1'sb0;
	end
	wire w_tmo_fresh = (r_e_scan_hit || r_e_cmd_tmo) && w_tmo_en;
	wire w_tmo_v = w_tmo_fresh || (r_tmo_pend && w_tmo_en);
	wire [7:0] w_tmo_code = (r_tmo_pend ? r_tmo_code : (r_e_scan_hit ? (r_e_scan_phase ? 8'h02 : 8'h01) : 8'h00));
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	wire [1:0] w_tmo_fired = (w_tmo_en ? sv2v_cast_2(r_e_scan_hit) + sv2v_cast_2(r_e_cmd_tmo) : 2'd0);
	wire w_cmp_v = r_e_compl && w_cmp_en;
	wire w_thr_v = (r_e_thresh || r_lat_pend) && w_thr_en;
	wire [1:0] w_thr_fired = (w_thr_en ? sv2v_cast_2(r_e_thresh) : 2'd0);
	reg w_evt_v;
	reg [3:0] w_evt_type;
	reg [7:0] w_evt_code;
	reg w_evt_from_slot;
	reg [SW - 1:0] w_evt_slot;
	reg [IW - 1:0] w_evt_id_alt;
	reg [AW - 1:0] w_evt_addr_alt;
	reg [15:0] w_evt_hi;
	function automatic [AW - 1:0] sv2v_cast_DE851;
		input reg [AW - 1:0] inp;
		sv2v_cast_DE851 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_evt_v = 1'b0;
		w_evt_type = 1'sb0;
		w_evt_code = 1'sb0;
		w_evt_from_slot = 1'b0;
		w_evt_slot = 1'sb0;
		w_evt_id_alt = 1'sb0;
		w_evt_addr_alt = 1'sb0;
		w_evt_hi = 1'sb0;
		if (w_err_v) begin
			w_evt_v = 1'b1;
			w_evt_type = monitor_common_pkg_PktTypeError;
			w_evt_code = w_err_code;
			w_evt_from_slot = w_err_has_slot;
			w_evt_slot = w_err_slot;
			w_evt_id_alt = w_err_id;
		end
		else if (w_tmo_v) begin
			w_evt_v = 1'b1;
			w_evt_type = monitor_common_pkg_PktTypeTimeout;
			w_evt_code = w_tmo_code;
			if (r_tmo_pend) begin
				w_evt_id_alt = r_tmo_id;
				w_evt_addr_alt = r_tmo_addr;
			end
			else begin
				w_evt_from_slot = r_e_scan_hit;
				w_evt_slot = r_e_tslot;
				w_evt_id_alt = r_e_cmd_id;
				w_evt_addr_alt = r_e_cmd_addr;
			end
		end
		else if (w_cmp_v) begin
			w_evt_v = 1'b1;
			w_evt_type = monitor_common_pkg_PktTypeCompletion;
			w_evt_code = 8'h00;
			w_evt_from_slot = 1'b1;
			w_evt_slot = r_e_cslot;
			w_evt_hi = r_e_latency;
		end
		else if (w_thr_v) begin
			w_evt_v = 1'b1;
			w_evt_type = monitor_common_pkg_PktTypeThreshold;
			if (r_e_thresh) begin
				w_evt_code = 8'h00;
				w_evt_addr_alt = sv2v_cast_DE851(r_e_occupancy);
			end
			else begin
				w_evt_code = 8'h01;
				w_evt_id_alt = r_lat_id;
				w_evt_addr_alt = r_lat_addr;
				w_evt_hi = r_lat_latency;
			end
		end
	end
	wire [IW - 1:0] w_evt_id = (w_evt_from_slot ? r_id[w_evt_slot * IW+:IW] : w_evt_id_alt);
	wire [AW - 1:0] w_evt_addr = (w_evt_from_slot ? r_addr[w_evt_slot * AW+:AW] : w_evt_addr_alt);
	wire w_wr_ready;
	wire [3:0] w_offered = ((w_err_fired + sv2v_cast_4(w_tmo_fired)) + sv2v_cast_4(w_cmp_v)) + sv2v_cast_4(w_thr_fired);
	wire w_take = w_evt_v && w_wr_ready;
	assign w_lat_take = ((((w_take && w_thr_v) && !w_err_v) && !w_tmo_v) && !w_cmp_v) && !r_e_thresh;
	wire w_tmo_take = (w_take && w_tmo_v) && !w_err_v;
	assign w_tmo_held_take = w_tmo_take && r_tmo_pend;
	wire w_tmo_fresh_taken = w_tmo_take && !r_tmo_pend;
	wire [1:0] w_tmo_left = w_tmo_fired - sv2v_cast_2(w_tmo_fresh_taken);
	assign w_tmo_saved = (w_tmo_left != 2'd0) && (!r_tmo_pend || w_tmo_held_take);
	assign w_tmo_save_scan = r_e_scan_hit && !(w_tmo_fresh_taken && r_e_scan_hit);
	wire w_take_fresh = (w_take && !w_lat_take) && !w_tmo_held_take;
	wire w_lat_lost = (w_lat_hit && r_lat_pend) && !w_lat_take;
	wire [3:0] w_lost = ((w_offered - sv2v_cast_4(w_take_fresh)) - sv2v_cast_4(w_tmo_saved)) + sv2v_cast_4(w_lat_lost);
	reg [15:0] r_dropped;
	reg [15:0] r_refused;
	reg [15:0] r_completed;
	reg [15:0] r_errors;
	wire w_drop_rpt = (((r_dropped != 16'd0) && !w_evt_v) && w_wr_ready) && w_err_en;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_dropped <= 1'sb0;
			r_refused <= 1'sb0;
			r_completed <= 1'sb0;
			r_errors <= 1'sb0;
		end
		else if (clear) begin
			r_dropped <= 1'sb0;
			r_refused <= 1'sb0;
			r_completed <= 1'sb0;
			r_errors <= 1'sb0;
		end
		else begin
			if (w_drop_rpt)
				r_dropped <= 1'sb0;
			else if (&r_dropped[15:4])
				r_dropped <= 16'hffff;
			else
				r_dropped <= r_dropped + sv2v_cast_16(w_lost);
			if (w_refused && (r_refused != 16'hffff))
				r_refused <= r_refused + 1'b1;
			if (r_e_compl && (r_completed != 16'hffff))
				r_completed <= r_completed + 1'b1;
			if ((w_err_fired != {4 {1'sb0}}) && (r_errors != 16'hffff))
				r_errors <= r_errors + 1'b1;
		end
	reg [(34 + AW) - 1:0] w_entry_in;
	wire [(34 + AW) - 1:0] w_entry_out;
	function automatic [5:0] sv2v_cast_6;
		input reg [5:0] inp;
		sv2v_cast_6 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_evt_v)
			w_entry_in = {w_evt_type, w_evt_code, sv2v_cast_6(w_evt_id), w_evt_hi, sv2v_cast_DE851(w_evt_addr)};
		else
			w_entry_in = {monitor_common_pkg_PktTypeError, 30'h03800000, sv2v_cast_DE851(r_dropped)};
	end
	reg [63:0] w_out_data;
	always @(*) begin
		if (_sv2v_0)
			;
		w_out_data = 1'sb0;
		w_out_data[AW - 1:0] = w_entry_out[AW - 1-:AW];
		w_out_data[63:48] = w_entry_out[AW + 15-:((AW + 15) >= (AW + 0) ? ((AW + 15) - (AW + 0)) + 1 : ((AW + 0) - (AW + 15)) + 1)];
	end
	localparam signed [31:0] OQW = (OUT_DEPTH > 1 ? $clog2(OUT_DEPTH) : 1);
	reg [(34 + AW) - 1:0] r_q [0:OUT_DEPTH - 1];
	reg [OQW:0] r_q_wp;
	reg [OQW:0] r_q_rp;
	wire w_q_empty = r_q_wp == r_q_rp;
	wire w_q_full = (r_q_wp[OQW - 1:0] == r_q_rp[OQW - 1:0]) && (r_q_wp[OQW] != r_q_rp[OQW]);
	wire w_q_push = w_take || w_drop_rpt;
	wire w_q_ready;
	wire w_q_valid;
	wire w_q_pop = w_q_valid && w_q_ready;
	assign w_wr_ready = !w_q_full;
	assign w_entry_out = r_q[r_q_rp[OQW - 1:0]];
	assign w_q_valid = !w_q_empty;
	always @(posedge aclk)
		if (w_q_push)
			r_q[r_q_wp[OQW - 1:0]] <= w_entry_in;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_q_wp <= 1'sb0;
			r_q_rp <= 1'sb0;
		end
		else begin
			if (w_q_push)
				r_q_wp <= r_q_wp + 1'b1;
			if (w_q_pop)
				r_q_rp <= r_q_rp + 1'b1;
		end
	wire [127:0] w_q_packet;
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
	assign w_q_packet = monitor_common_pkg_create_monitor_packet(w_entry_out[12 + (AW + 21)-:((12 + (AW + 21)) >= (30 + (AW + 0)) ? ((12 + (AW + 21)) - (30 + (AW + 0))) + 1 : ((30 + (AW + 0)) - (12 + (AW + 21))) + 1)], 4'h0, w_entry_out[14 + (AW + 15)-:((14 + (AW + 15)) >= (22 + (AW + 0)) ? ((14 + (AW + 15)) - (22 + (AW + 0))) + 1 : ((22 + (AW + 0)) - (14 + (AW + 15))) + 1)], {3'b000, w_entry_out[AW + 21-:((AW + 21) >= (16 + (AW + 0)) ? ((AW + 21) - (16 + (AW + 0))) + 1 : ((16 + (AW + 0)) - (AW + 21)) + 1)]}, UNIT_ID, AGENT_ID, w_out_data);
	wire w_addr_valid;
	wire w_addr_ready;
	wire [127:0] w_addr_packet;
	wire [63:0] w_addr_ts;
	generate
		if (N_ADDR_RANGES > 0) begin : gen_addr_check
			axi_monitor_addr_check #(
				.N_ADDR_RANGES(N_ADDR_RANGES),
				.ADDR_WIDTH(AW),
				.ID_WIDTH(IW),
				.UNIT_ID(UNIT_ID),
				.AGENT_ID(AGENT_ID),
				.IS_READ(IS_READ),
				.ADDR_RANGE_IS_ERROR(ADDR_RANGE_IS_ERROR)
			) u_addr_check(
				.clk(aclk),
				.aresetn(aresetn),
				.i_mon_time(i_mon_time),
				.cmd_addr(cmd_addr),
				.cmd_id(cmd_id),
				.cmd_valid(cmd_valid),
				.cmd_ready(cmd_ready),
				.cfg_addr_check_enable(cfg_addr_check_enable),
				.cfg_debug_enable(cfg_addr_match_enable),
				.cfg_error_enable(cfg_error_enable),
				.cfg_addr_range_enable(cfg_addr_range_enable),
				.cfg_addr_range_low(cfg_addr_range_low),
				.cfg_addr_range_high(cfg_addr_range_high),
				.addr_pkt_valid(w_addr_valid),
				.addr_pkt_ready(w_addr_ready),
				.addr_pkt_data(w_addr_packet),
				.addr_pkt_timestamp(w_addr_ts)
			);
		end
		else begin : gen_no_addr_check
			assign w_addr_valid = 1'b0;
			assign w_addr_packet = 1'sb0;
			assign w_addr_ts = 1'sb0;
		end
	endgenerate
	reg r_presented;
	reg r_src_addr;
	wire w_sel_addr = (r_presented ? r_src_addr : w_addr_valid);
	assign monbus_valid = (w_sel_addr ? w_addr_valid : w_q_valid);
	assign monbus_packet = (w_sel_addr ? w_addr_packet : w_q_packet);
	assign monbus_timestamp = (w_sel_addr ? w_addr_ts : i_mon_time);
	assign w_addr_ready = w_sel_addr && monbus_ready;
	assign w_q_ready = !w_sel_addr && monbus_ready;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_presented <= 1'b0;
			r_src_addr <= 1'b0;
		end
		else if (monbus_valid && monbus_ready)
			r_presented <= 1'b0;
		else if (monbus_valid && !r_presented) begin
			r_presented <= 1'b1;
			r_src_addr <= w_sel_addr;
		end
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign active_count = sv2v_cast_8(w_occupancy);
	assign busy = (((|r_valid || monbus_valid) || w_addr_valid) || r_lat_pend) || r_tmo_pend;
	assign perf_completed_count = r_completed;
	assign perf_error_count = r_errors;
	assign dropped_count = r_dropped;
	assign refused_count = r_refused;
	initial _sv2v_0 = 0;
endmodule
module axi4_master_rd (
	aclk,
	aresetn,
	fub_axi_arid,
	fub_axi_araddr,
	fub_axi_arlen,
	fub_axi_arsize,
	fub_axi_arburst,
	fub_axi_arlock,
	fub_axi_arcache,
	fub_axi_arprot,
	fub_axi_arqos,
	fub_axi_arregion,
	fub_axi_aruser,
	fub_axi_arvalid,
	fub_axi_arready,
	fub_axi_rid,
	fub_axi_rdata,
	fub_axi_rresp,
	fub_axi_rlast,
	fub_axi_ruser,
	fub_axi_rvalid,
	fub_axi_rready,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_arlock,
	m_axi_arcache,
	m_axi_arprot,
	m_axi_arqos,
	m_axi_arregion,
	m_axi_aruser,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	m_axi_ruser,
	m_axi_rvalid,
	m_axi_rready,
	busy
);
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	parameter signed [31:0] ARSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] RSize = ((IW + DW) + 3) + UW;
	input wire aclk;
	input wire aresetn;
	input wire [IW - 1:0] fub_axi_arid;
	input wire [AW - 1:0] fub_axi_araddr;
	input wire [7:0] fub_axi_arlen;
	input wire [2:0] fub_axi_arsize;
	input wire [1:0] fub_axi_arburst;
	input wire fub_axi_arlock;
	input wire [3:0] fub_axi_arcache;
	input wire [2:0] fub_axi_arprot;
	input wire [3:0] fub_axi_arqos;
	input wire [3:0] fub_axi_arregion;
	input wire [UW - 1:0] fub_axi_aruser;
	input wire fub_axi_arvalid;
	output wire fub_axi_arready;
	output wire [IW - 1:0] fub_axi_rid;
	output wire [DW - 1:0] fub_axi_rdata;
	output wire [1:0] fub_axi_rresp;
	output wire fub_axi_rlast;
	output wire [UW - 1:0] fub_axi_ruser;
	output wire fub_axi_rvalid;
	input wire fub_axi_rready;
	output wire [IW - 1:0] m_axi_arid;
	output wire [AW - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	output wire m_axi_arlock;
	output wire [3:0] m_axi_arcache;
	output wire [2:0] m_axi_arprot;
	output wire [3:0] m_axi_arqos;
	output wire [3:0] m_axi_arregion;
	output wire [UW - 1:0] m_axi_aruser;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	input wire [IW - 1:0] m_axi_rid;
	input wire [DW - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	input wire [UW - 1:0] m_axi_ruser;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	output wire busy;
	wire [3:0] int_ar_count;
	wire [ARSize - 1:0] int_ar_pkt;
	wire int_skid_arvalid;
	wire int_skid_arready;
	wire [3:0] int_r_count;
	wire [RSize - 1:0] int_r_pkt;
	wire int_skid_rvalid;
	wire int_skid_rready;
	assign busy = (((int_ar_count > 0) || (int_r_count > 0)) || fub_axi_arvalid) || m_axi_rvalid;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AR),
		.DATA_WIDTH(ARSize)
	) ar_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_axi_arvalid),
		.wr_ready(fub_axi_arready),
		.wr_data({fub_axi_arid, fub_axi_araddr, fub_axi_arlen, fub_axi_arsize, fub_axi_arburst, fub_axi_arlock, fub_axi_arcache, fub_axi_arprot, fub_axi_arqos, fub_axi_arregion, fub_axi_aruser}),
		.rd_valid(int_skid_arvalid),
		.rd_ready(int_skid_arready),
		.rd_count(int_ar_count),
		.rd_data(int_ar_pkt),
		.count()
	);
	assign {m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst, m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos, m_axi_arregion, m_axi_aruser} = int_ar_pkt;
	assign m_axi_arvalid = int_skid_arvalid;
	assign int_skid_arready = m_axi_arready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_R),
		.DATA_WIDTH(RSize)
	) r_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(m_axi_rvalid),
		.wr_ready(m_axi_rready),
		.wr_data({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
		.rd_valid(int_skid_rvalid),
		.rd_ready(int_skid_rready),
		.rd_count(int_r_count),
		.rd_data({fub_axi_rid, fub_axi_rdata, fub_axi_rresp, fub_axi_rlast, fub_axi_ruser}),
		.count()
	);
	assign fub_axi_rvalid = int_skid_rvalid;
	assign int_skid_rready = fub_axi_rready;
endmodule
module axi4_master_rd_monlite (
	aclk,
	aresetn,
	fub_axi_arid,
	fub_axi_araddr,
	fub_axi_arlen,
	fub_axi_arsize,
	fub_axi_arburst,
	fub_axi_arlock,
	fub_axi_arcache,
	fub_axi_arprot,
	fub_axi_arqos,
	fub_axi_arregion,
	fub_axi_aruser,
	fub_axi_arvalid,
	fub_axi_arready,
	fub_axi_rid,
	fub_axi_rdata,
	fub_axi_rresp,
	fub_axi_rlast,
	fub_axi_ruser,
	fub_axi_rvalid,
	fub_axi_rready,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_arlock,
	m_axi_arcache,
	m_axi_arprot,
	m_axi_arqos,
	m_axi_arregion,
	m_axi_aruser,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	m_axi_ruser,
	m_axi_rvalid,
	m_axi_rready,
	busy,
	cam_clear,
	cfg_monitor_enable,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_compl_enable,
	cfg_threshold_enable,
	cfg_timeout_cycles,
	cfg_freq_sel,
	cfg_axi_pkt_mask,
	cfg_latency_threshold,
	cfg_addr_check_enable,
	cfg_addr_match_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	active_transactions,
	error_count,
	transaction_count,
	dropped_count,
	refused_count
);
	parameter [0:0] USE_MONITOR = 1'b1;
	parameter [7:0] UNIT_ID = 8'h01;
	parameter [15:0] AGENT_ID = 16'h000a;
	parameter signed [31:0] MAX_TRANSACTIONS = 8;
	parameter signed [31:0] ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2;
	parameter signed [31:0] OUT_DEPTH = 4;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] ADDR_RANGE_IS_ERROR = 1'sb0;
	parameter signed [31:0] ACLK_MHZ = 100;
	parameter signed [31:0] CFI_MIN_FREQ_MHZ = ACLK_MHZ;
	parameter signed [31:0] CFI_MAX_FREQ_MHZ = ACLK_MHZ;
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	parameter signed [31:0] ARSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] RSize = ((IW + DW) + 3) + UW;
	input wire aclk;
	input wire aresetn;
	input wire [IW - 1:0] fub_axi_arid;
	input wire [AW - 1:0] fub_axi_araddr;
	input wire [7:0] fub_axi_arlen;
	input wire [2:0] fub_axi_arsize;
	input wire [1:0] fub_axi_arburst;
	input wire fub_axi_arlock;
	input wire [3:0] fub_axi_arcache;
	input wire [2:0] fub_axi_arprot;
	input wire [3:0] fub_axi_arqos;
	input wire [3:0] fub_axi_arregion;
	input wire [UW - 1:0] fub_axi_aruser;
	input wire fub_axi_arvalid;
	output wire fub_axi_arready;
	output wire [IW - 1:0] fub_axi_rid;
	output wire [DW - 1:0] fub_axi_rdata;
	output wire [1:0] fub_axi_rresp;
	output wire fub_axi_rlast;
	output wire [UW - 1:0] fub_axi_ruser;
	output wire fub_axi_rvalid;
	input wire fub_axi_rready;
	output wire [IW - 1:0] m_axi_arid;
	output wire [AW - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	output wire m_axi_arlock;
	output wire [3:0] m_axi_arcache;
	output wire [2:0] m_axi_arprot;
	output wire [3:0] m_axi_arqos;
	output wire [3:0] m_axi_arregion;
	output wire [UW - 1:0] m_axi_aruser;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	input wire [IW - 1:0] m_axi_rid;
	input wire [DW - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	input wire [UW - 1:0] m_axi_ruser;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	output wire busy;
	input wire cam_clear;
	input wire cfg_monitor_enable;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_compl_enable;
	input wire cfg_threshold_enable;
	input wire [15:0] cfg_timeout_cycles;
	input wire [3:0] cfg_freq_sel;
	input wire [15:0] cfg_axi_pkt_mask;
	input wire [31:0] cfg_latency_threshold;
	input wire cfg_addr_check_enable;
	input wire cfg_addr_match_enable;
	input wire [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] cfg_addr_range_enable;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_low;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_high;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire [7:0] active_transactions;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
	output wire [15:0] dropped_count;
	output wire [15:0] refused_count;
	axi4_master_rd #(
		.SKID_DEPTH_AR(SKID_DEPTH_AR),
		.SKID_DEPTH_R(SKID_DEPTH_R),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH),
		.AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH),
		.AW(AW),
		.DW(DW),
		.IW(IW),
		.SW(SW),
		.UW(UW),
		.ARSize(ARSize),
		.RSize(RSize)
	) u_core(
		.aclk(aclk),
		.aresetn(aresetn),
		.fub_axi_arid(fub_axi_arid),
		.fub_axi_araddr(fub_axi_araddr),
		.fub_axi_arlen(fub_axi_arlen),
		.fub_axi_arsize(fub_axi_arsize),
		.fub_axi_arburst(fub_axi_arburst),
		.fub_axi_arlock(fub_axi_arlock),
		.fub_axi_arcache(fub_axi_arcache),
		.fub_axi_arprot(fub_axi_arprot),
		.fub_axi_arqos(fub_axi_arqos),
		.fub_axi_arregion(fub_axi_arregion),
		.fub_axi_aruser(fub_axi_aruser),
		.fub_axi_arvalid(fub_axi_arvalid),
		.fub_axi_arready(fub_axi_arready),
		.fub_axi_rid(fub_axi_rid),
		.fub_axi_rdata(fub_axi_rdata),
		.fub_axi_rresp(fub_axi_rresp),
		.fub_axi_rlast(fub_axi_rlast),
		.fub_axi_ruser(fub_axi_ruser),
		.fub_axi_rvalid(fub_axi_rvalid),
		.fub_axi_rready(fub_axi_rready),
		.m_axi_arid(m_axi_arid),
		.m_axi_araddr(m_axi_araddr),
		.m_axi_arlen(m_axi_arlen),
		.m_axi_arsize(m_axi_arsize),
		.m_axi_arburst(m_axi_arburst),
		.m_axi_arlock(m_axi_arlock),
		.m_axi_arcache(m_axi_arcache),
		.m_axi_arprot(m_axi_arprot),
		.m_axi_arqos(m_axi_arqos),
		.m_axi_arregion(m_axi_arregion),
		.m_axi_aruser(m_axi_aruser),
		.m_axi_arvalid(m_axi_arvalid),
		.m_axi_arready(m_axi_arready),
		.m_axi_rid(m_axi_rid),
		.m_axi_rdata(m_axi_rdata),
		.m_axi_rresp(m_axi_rresp),
		.m_axi_rlast(m_axi_rlast),
		.m_axi_ruser(m_axi_ruser),
		.m_axi_rvalid(m_axi_rvalid),
		.m_axi_rready(m_axi_rready),
		.busy(busy)
	);
	wire w_mon_cmd_valid;
	wire w_mon_data_valid;
	wire w_mon_resp_valid;
	wire [15:0] w_timeout_cnt;
	wire [15:0] w_perf_completed_count;
	wire [15:0] w_perf_error_count;
	assign w_mon_cmd_valid = m_axi_arvalid & cfg_monitor_enable;
	assign w_mon_data_valid = m_axi_rvalid & cfg_monitor_enable;
	assign w_mon_resp_valid = (m_axi_rvalid && m_axi_rlast) & cfg_monitor_enable;
	assign w_timeout_cnt = (cfg_timeout_cycles == 16'h0000 ? 16'hffff : cfg_timeout_cycles);
	function automatic signed [15:0] sv2v_cast_16_signed;
		input reg signed [15:0] inp;
		sv2v_cast_16_signed = inp;
	endfunction
	generate
		if (USE_MONITOR) begin : gen_monitor_lite
			axi_monitor_lite #(
				.UNIT_ID(UNIT_ID),
				.AGENT_ID(AGENT_ID),
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.OUT_DEPTH(OUT_DEPTH),
				.N_ADDR_RANGES(N_ADDR_RANGES),
				.ADDR_RANGE_IS_ERROR(ADDR_RANGE_IS_ERROR),
				.ADDR_WIDTH(AW),
				.ID_WIDTH(IW),
				.IS_READ(1'b1),
				.IS_AXI(1'b1),
				.CFI_MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
				.CFI_MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ)
			) axi_monitor_lite_inst(
				.aclk(aclk),
				.aresetn(aresetn),
				.clear(cam_clear | ~cfg_monitor_enable),
				.i_mon_time(i_mon_time),
				.cmd_addr(m_axi_araddr),
				.cmd_id(m_axi_arid),
				.cmd_len(m_axi_arlen),
				.cmd_valid(w_mon_cmd_valid),
				.cmd_ready(m_axi_arready),
				.data_id(m_axi_rid),
				.data_last(m_axi_rlast),
				.data_resp(m_axi_rresp),
				.data_valid(w_mon_data_valid),
				.data_ready(m_axi_rready),
				.resp_id(m_axi_rid),
				.resp_code(m_axi_rresp),
				.resp_valid(w_mon_resp_valid),
				.resp_ready(m_axi_rready),
				.cfg_freq_sel(cfg_freq_sel),
				.cfg_timeout_cnt(w_timeout_cnt),
				.cfg_error_enable(cfg_error_enable),
				.cfg_compl_enable(cfg_compl_enable),
				.cfg_timeout_enable(cfg_timeout_enable),
				.cfg_threshold_enable(cfg_threshold_enable),
				.cfg_active_trans_threshold(sv2v_cast_16_signed(ACTIVE_TRANS_THRESHOLD)),
				.cfg_axi_pkt_mask(cfg_axi_pkt_mask),
				.cfg_latency_threshold(cfg_latency_threshold),
				.cfg_addr_check_enable(cfg_addr_check_enable),
				.cfg_addr_match_enable(cfg_addr_match_enable),
				.cfg_addr_range_enable(cfg_addr_range_enable),
				.cfg_addr_range_low(cfg_addr_range_low),
				.cfg_addr_range_high(cfg_addr_range_high),
				.monbus_valid(monbus_valid),
				.monbus_ready(monbus_ready),
				.monbus_packet(monbus_packet),
				.monbus_timestamp(monbus_timestamp),
				.active_count(active_transactions),
				.busy(),
				.dropped_count(dropped_count),
				.refused_count(refused_count),
				.perf_completed_count(w_perf_completed_count),
				.perf_error_count(w_perf_error_count)
			);
		end
		else begin : gen_no_monitor
			assign monbus_valid = 1'b0;
			assign monbus_packet = 1'sb0;
			assign monbus_timestamp = 1'sb0;
			assign active_transactions = 8'h00;
			assign dropped_count = 16'h0000;
			assign refused_count = 16'h0000;
			assign w_perf_completed_count = 16'h0000;
			assign w_perf_error_count = 16'h0000;
		end
	endgenerate
	assign error_count = w_perf_error_count;
	assign transaction_count = {16'h0000, w_perf_completed_count};
endmodule
module scheduler_group_array (
	clk,
	rst_n,
	cam_clear,
	apb_valid,
	apb_ready,
	apb_addr,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_enable,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_limit,
	cfg_sched_timeout_enable,
	cfg_sched_err_enable,
	cfg_sched_compl_enable,
	cfg_sched_perf_enable,
	cfg_desceng_enable,
	cfg_desceng_prefetch,
	cfg_rd_prefetch_enable,
	cfg_desceng_fifo_thresh,
	cfg_desceng_addr0_base,
	cfg_desceng_addr0_limit,
	cfg_desceng_addr1_base,
	cfg_desceng_addr1_limit,
	cfg_desc_mon_enable,
	cfg_desc_mon_err_enable,
	cfg_desc_mon_perf_enable,
	cfg_desc_mon_compl_enable,
	cfg_desc_mon_thresh_enable,
	cfg_desc_mon_timeout_enable,
	cfg_desc_mon_timeout_cycles,
	cfg_desc_mon_latency_thresh,
	cfg_desc_mon_pkt_mask,
	cfg_desc_mon_err_select,
	cfg_desc_mon_err_mask,
	cfg_desc_mon_timeout_mask,
	cfg_desc_mon_compl_mask,
	cfg_desc_mon_thresh_mask,
	cfg_desc_mon_perf_mask,
	cfg_desc_mon_addr_mask,
	cfg_desc_mon_debug_mask,
	cfg_desc_mon_perf_run,
	descriptor_engine_idle,
	scheduler_idle,
	scheduler_state,
	sched_error,
	dbg_descriptor_error,
	dbg_read_error_sticky,
	dbg_write_error_sticky,
	dbg_timeout_expired,
	cfg_sts_desc_mon_busy,
	cfg_sts_desc_mon_active_txns,
	cfg_sts_desc_mon_error_count,
	cfg_sts_desc_mon_txn_count,
	cfg_sts_desc_mon_conflict_error,
	perf_window_active,
	perf_window_cycles,
	perf_prod_cycles,
	perf_bp_cycles,
	perf_starv_cycles,
	perf_idle_cycles,
	perf_beat_count,
	perf_byte_count,
	perf_burst_count,
	desc_axi_arvalid,
	desc_axi_arready,
	desc_axi_araddr,
	desc_axi_arlen,
	desc_axi_arsize,
	desc_axi_arburst,
	desc_axi_arid,
	desc_axi_arlock,
	desc_axi_arcache,
	desc_axi_arprot,
	desc_axi_arqos,
	desc_axi_arregion,
	desc_axi_rvalid,
	desc_axi_rready,
	desc_axi_rdata,
	desc_axi_rresp,
	desc_axi_rlast,
	desc_axi_rid,
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
	sched_wr_commit_strobe,
	sched_wr_commit_beats,
	sched_rd_error,
	sched_wr_error,
	i_mon_time,
	mon_valid,
	mon_ready,
	mon_packet,
	mon_timestamp
);
	reg _sv2v_0;
	parameter [0:0] GEN_MON = 1'b1;
	parameter signed [31:0] USE_AXI_MONITORS = 1;
	parameter [0:0] USE_DESC_AXI_MONITOR = 1'b0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] USE_ROW_COL_MAJOR_ADDRESSING = 1;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] DESC_MON_BASE_AGENT_ID = 16;
	parameter signed [31:0] SCHED_MON_BASE_AGENT_ID = 48;
	parameter signed [31:0] DESC_AXI_MON_AGENT_ID = 8;
	parameter signed [31:0] MON_UNIT_ID = 1;
	parameter signed [31:0] MON_MAX_TRANSACTIONS = 16;
	parameter [0:0] DESC_MON_ENABLE_ERROR_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_TIMEOUT_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_COMPL_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_THRESHOLD_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_PERF_LOGIC = 1'b1;
	parameter [0:0] DESC_MON_ENABLE_DEBUG_LOGIC = 1'b0;
	input wire clk;
	input wire rst_n;
	input wire cam_clear;
	input wire [NUM_CHANNELS - 1:0] apb_valid;
	output wire [NUM_CHANNELS - 1:0] apb_ready;
	input wire [(NUM_CHANNELS * ADDR_WIDTH) - 1:0] apb_addr;
	input wire [NUM_CHANNELS - 1:0] cfg_channel_enable;
	input wire [NUM_CHANNELS - 1:0] cfg_channel_reset;
	input wire cfg_sched_enable;
	input wire [31:0] cfg_sched_timeout_cycles;
	input wire [7:0] cfg_sched_timeout_limit;
	input wire cfg_sched_timeout_enable;
	input wire cfg_sched_err_enable;
	input wire cfg_sched_compl_enable;
	input wire cfg_sched_perf_enable;
	input wire cfg_desceng_enable;
	input wire cfg_desceng_prefetch;
	input wire cfg_rd_prefetch_enable;
	input wire [3:0] cfg_desceng_fifo_thresh;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_limit;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_limit;
	input wire cfg_desc_mon_enable;
	input wire cfg_desc_mon_err_enable;
	input wire cfg_desc_mon_perf_enable;
	input wire cfg_desc_mon_compl_enable;
	input wire cfg_desc_mon_thresh_enable;
	input wire cfg_desc_mon_timeout_enable;
	input wire [31:0] cfg_desc_mon_timeout_cycles;
	input wire [31:0] cfg_desc_mon_latency_thresh;
	input wire [15:0] cfg_desc_mon_pkt_mask;
	input wire [15:0] cfg_desc_mon_err_select;
	input wire [15:0] cfg_desc_mon_err_mask;
	input wire [15:0] cfg_desc_mon_timeout_mask;
	input wire [15:0] cfg_desc_mon_compl_mask;
	input wire [15:0] cfg_desc_mon_thresh_mask;
	input wire [15:0] cfg_desc_mon_perf_mask;
	input wire [15:0] cfg_desc_mon_addr_mask;
	input wire [15:0] cfg_desc_mon_debug_mask;
	input wire cfg_desc_mon_perf_run;
	output wire [NUM_CHANNELS - 1:0] descriptor_engine_idle;
	output wire [NUM_CHANNELS - 1:0] scheduler_idle;
	output wire [(NUM_CHANNELS * 7) - 1:0] scheduler_state;
	output wire [NUM_CHANNELS - 1:0] sched_error;
	output wire [NUM_CHANNELS - 1:0] dbg_descriptor_error;
	output wire [NUM_CHANNELS - 1:0] dbg_read_error_sticky;
	output wire [NUM_CHANNELS - 1:0] dbg_write_error_sticky;
	output wire [NUM_CHANNELS - 1:0] dbg_timeout_expired;
	output wire cfg_sts_desc_mon_busy;
	output wire [7:0] cfg_sts_desc_mon_active_txns;
	output wire [15:0] cfg_sts_desc_mon_error_count;
	output wire [31:0] cfg_sts_desc_mon_txn_count;
	output wire cfg_sts_desc_mon_conflict_error;
	output wire perf_window_active;
	output wire [31:0] perf_window_cycles;
	output wire [31:0] perf_prod_cycles;
	output wire [31:0] perf_bp_cycles;
	output wire [31:0] perf_starv_cycles;
	output wire [31:0] perf_idle_cycles;
	output wire [31:0] perf_beat_count;
	output wire [63:0] perf_byte_count;
	output wire [31:0] perf_burst_count;
	output wire desc_axi_arvalid;
	input wire desc_axi_arready;
	output wire [ADDR_WIDTH - 1:0] desc_axi_araddr;
	output wire [7:0] desc_axi_arlen;
	output wire [2:0] desc_axi_arsize;
	output wire [1:0] desc_axi_arburst;
	output wire [AXI_ID_WIDTH - 1:0] desc_axi_arid;
	output wire desc_axi_arlock;
	output wire [3:0] desc_axi_arcache;
	output wire [2:0] desc_axi_arprot;
	output wire [3:0] desc_axi_arqos;
	output wire [3:0] desc_axi_arregion;
	input wire desc_axi_rvalid;
	output wire desc_axi_rready;
	input wire [255:0] desc_axi_rdata;
	input wire [1:0] desc_axi_rresp;
	input wire desc_axi_rlast;
	input wire [AXI_ID_WIDTH - 1:0] desc_axi_rid;
	output wire [NUM_CHANNELS - 1:0] sched_rd_valid;
	output wire [(NUM_CHANNELS * ADDR_WIDTH) - 1:0] sched_rd_addr;
	output wire [(NUM_CHANNELS * 32) - 1:0] sched_rd_beats;
	output wire [NUM_CHANNELS - 1:0] sched_wr_valid;
	input wire [NUM_CHANNELS - 1:0] sched_wr_ready;
	output wire [(NUM_CHANNELS * ADDR_WIDTH) - 1:0] sched_wr_addr;
	output wire [(NUM_CHANNELS * 32) - 1:0] sched_wr_beats;
	input wire [NUM_CHANNELS - 1:0] sched_rd_done_strobe;
	input wire [(NUM_CHANNELS * 32) - 1:0] sched_rd_beats_done;
	input wire [NUM_CHANNELS - 1:0] sched_wr_done_strobe;
	input wire [(NUM_CHANNELS * 32) - 1:0] sched_wr_beats_done;
	input wire [NUM_CHANNELS - 1:0] sched_wr_commit_strobe;
	input wire [(NUM_CHANNELS * 32) - 1:0] sched_wr_commit_beats;
	input wire [NUM_CHANNELS - 1:0] sched_rd_error;
	input wire [NUM_CHANNELS - 1:0] sched_wr_error;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	wire [NUM_CHANNELS - 1:0] desc_ar_valid;
	reg [NUM_CHANNELS - 1:0] desc_ar_ready;
	wire [(NUM_CHANNELS * ADDR_WIDTH) - 1:0] desc_ar_addr;
	wire [(NUM_CHANNELS * 8) - 1:0] desc_ar_len;
	wire [(NUM_CHANNELS * 3) - 1:0] desc_ar_size;
	wire [(NUM_CHANNELS * 2) - 1:0] desc_ar_burst;
	wire [(NUM_CHANNELS * AXI_ID_WIDTH) - 1:0] desc_ar_id;
	wire [NUM_CHANNELS - 1:0] desc_ar_lock;
	wire [(NUM_CHANNELS * 4) - 1:0] desc_ar_cache;
	wire [(NUM_CHANNELS * 3) - 1:0] desc_ar_prot;
	wire [(NUM_CHANNELS * 4) - 1:0] desc_ar_qos;
	wire [(NUM_CHANNELS * 4) - 1:0] desc_ar_region;
	reg [NUM_CHANNELS - 1:0] desc_r_valid;
	wire [NUM_CHANNELS - 1:0] desc_r_ready;
	reg [(NUM_CHANNELS * 256) - 1:0] desc_r_data;
	reg [(NUM_CHANNELS * 2) - 1:0] desc_r_resp;
	reg [NUM_CHANNELS - 1:0] desc_r_last;
	reg [(NUM_CHANNELS * AXI_ID_WIDTH) - 1:0] desc_r_id;
	wire [NUM_CHANNELS - 1:0] mon_valid_ch;
	reg [NUM_CHANNELS - 1:0] mon_ready_ch;
	wire [127:0] mon_packet_ch [0:NUM_CHANNELS - 1];
	wire [63:0] mon_timestamp_ch [0:NUM_CHANNELS - 1];
	wire desc_ar_grant_valid;
	wire [NUM_CHANNELS - 1:0] desc_ar_grant;
	reg [NUM_CHANNELS - 1:0] desc_ar_grant_ack;
	wire [CHAN_WIDTH - 1:0] desc_ar_grant_id;
	reg desc_axi_int_arvalid;
	wire desc_axi_int_arready;
	reg [ADDR_WIDTH - 1:0] desc_axi_int_araddr;
	reg [7:0] desc_axi_int_arlen;
	reg [2:0] desc_axi_int_arsize;
	reg [1:0] desc_axi_int_arburst;
	reg [AXI_ID_WIDTH - 1:0] desc_axi_int_arid;
	reg desc_axi_int_arlock;
	reg [3:0] desc_axi_int_arcache;
	reg [2:0] desc_axi_int_arprot;
	reg [3:0] desc_axi_int_arqos;
	reg [3:0] desc_axi_int_arregion;
	wire desc_axi_int_rvalid;
	wire desc_axi_int_rready;
	wire [255:0] desc_axi_int_rdata;
	wire [1:0] desc_axi_int_rresp;
	wire desc_axi_int_rlast;
	wire [AXI_ID_WIDTH - 1:0] desc_axi_int_rid;
	wire desc_axi_mon_valid;
	reg desc_axi_mon_ready;
	wire [127:0] desc_axi_mon_packet;
	wire [63:0] desc_axi_mon_timestamp;
	localparam signed [31:0] MONBUS_SOURCES = NUM_CHANNELS + 1;
	reg [0:MONBUS_SOURCES - 1] monbus_valid_all;
	wire [0:MONBUS_SOURCES - 1] monbus_ready_all;
	reg [(MONBUS_SOURCES * monitor_common_pkg_MONBUS_PKT_WIDTH) - 1:0] monbus_packet_all;
	reg [(MONBUS_SOURCES * monitor_common_pkg_MONBUS_TS_WIDTH) - 1:0] monbus_timestamp_all;
	genvar _gv_ch_1;
	generate
		for (_gv_ch_1 = 0; _gv_ch_1 < NUM_CHANNELS; _gv_ch_1 = _gv_ch_1 + 1) begin : gen_scheduler_groups
			localparam ch = _gv_ch_1;
			scheduler_group #(
				.USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING),
				.CHANNEL_ID(ch),
				.GEN_MON(GEN_MON),
				.NUM_CHANNELS(NUM_CHANNELS),
				.CHAN_WIDTH(CHAN_WIDTH),
				.ADDR_WIDTH(ADDR_WIDTH),
				.DATA_WIDTH(DATA_WIDTH),
				.AXI_ID_WIDTH(AXI_ID_WIDTH),
				.DESC_MON_AGENT_ID(DESC_MON_BASE_AGENT_ID + ch),
				.SCHED_MON_AGENT_ID(SCHED_MON_BASE_AGENT_ID + ch),
				.MON_UNIT_ID(MON_UNIT_ID),
				.MON_CHANNEL_ID(ch)
			) u_scheduler_group(
				.clk(clk),
				.rst_n(rst_n),
				.apb_valid(apb_valid[ch]),
				.apb_ready(apb_ready[ch]),
				.apb_addr(apb_addr[ch * ADDR_WIDTH+:ADDR_WIDTH]),
				.cfg_channel_enable(cfg_channel_enable[ch]),
				.cfg_channel_reset(cfg_channel_reset[ch]),
				.cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
				.cfg_sched_timeout_limit(cfg_sched_timeout_limit),
				.cfg_sched_timeout_enable(cfg_sched_timeout_enable),
				.cfg_sched_err_enable(cfg_sched_err_enable),
				.cfg_sched_compl_enable(cfg_sched_compl_enable),
				.cfg_sched_perf_enable(cfg_sched_perf_enable),
				.cfg_desceng_prefetch(cfg_desceng_prefetch),
				.cfg_rd_prefetch_enable(cfg_rd_prefetch_enable),
				.cfg_desceng_fifo_thresh(cfg_desceng_fifo_thresh),
				.cfg_desceng_addr0_base(cfg_desceng_addr0_base),
				.cfg_desceng_addr0_limit(cfg_desceng_addr0_limit),
				.cfg_desceng_addr1_base(cfg_desceng_addr1_base),
				.cfg_desceng_addr1_limit(cfg_desceng_addr1_limit),
				.descriptor_engine_idle(descriptor_engine_idle[ch]),
				.scheduler_idle(scheduler_idle[ch]),
				.scheduler_state(scheduler_state[ch * 7+:7]),
				.sched_error(sched_error[ch]),
				.dbg_descriptor_error(dbg_descriptor_error[ch]),
				.dbg_read_error_sticky(dbg_read_error_sticky[ch]),
				.dbg_write_error_sticky(dbg_write_error_sticky[ch]),
				.dbg_timeout_expired(dbg_timeout_expired[ch]),
				.desc_ar_valid(desc_ar_valid[ch]),
				.desc_ar_ready(desc_ar_ready[ch]),
				.desc_ar_addr(desc_ar_addr[ch * ADDR_WIDTH+:ADDR_WIDTH]),
				.desc_ar_len(desc_ar_len[ch * 8+:8]),
				.desc_ar_size(desc_ar_size[ch * 3+:3]),
				.desc_ar_burst(desc_ar_burst[ch * 2+:2]),
				.desc_ar_id(desc_ar_id[ch * AXI_ID_WIDTH+:AXI_ID_WIDTH]),
				.desc_ar_lock(desc_ar_lock[ch]),
				.desc_ar_cache(desc_ar_cache[ch * 4+:4]),
				.desc_ar_prot(desc_ar_prot[ch * 3+:3]),
				.desc_ar_qos(desc_ar_qos[ch * 4+:4]),
				.desc_ar_region(desc_ar_region[ch * 4+:4]),
				.desc_r_valid(desc_r_valid[ch]),
				.desc_r_ready(desc_r_ready[ch]),
				.desc_r_data(desc_r_data[ch * 256+:256]),
				.desc_r_resp(desc_r_resp[ch * 2+:2]),
				.desc_r_last(desc_r_last[ch]),
				.desc_r_id(desc_r_id[ch * AXI_ID_WIDTH+:AXI_ID_WIDTH]),
				.sched_rd_valid(sched_rd_valid[ch]),
				.sched_rd_addr(sched_rd_addr[ch * ADDR_WIDTH+:ADDR_WIDTH]),
				.sched_rd_beats(sched_rd_beats[ch * 32+:32]),
				.sched_wr_valid(sched_wr_valid[ch]),
				.sched_wr_ready(sched_wr_ready[ch]),
				.sched_wr_addr(sched_wr_addr[ch * ADDR_WIDTH+:ADDR_WIDTH]),
				.sched_wr_beats(sched_wr_beats[ch * 32+:32]),
				.sched_rd_done_strobe(sched_rd_done_strobe[ch]),
				.sched_rd_beats_done(sched_rd_beats_done[ch * 32+:32]),
				.sched_wr_done_strobe(sched_wr_done_strobe[ch]),
				.sched_wr_beats_done(sched_wr_beats_done[ch * 32+:32]),
				.sched_wr_commit_strobe(sched_wr_commit_strobe[ch]),
				.sched_wr_commit_beats(sched_wr_commit_beats[ch * 32+:32]),
				.sched_rd_error(sched_rd_error[ch]),
				.sched_wr_error(sched_wr_error[ch]),
				.i_mon_time(i_mon_time),
				.mon_valid(mon_valid_ch[ch]),
				.mon_ready(mon_ready_ch[ch]),
				.mon_packet(mon_packet_ch[ch]),
				.mon_timestamp(mon_timestamp_ch[ch])
			);
		end
		if (NUM_CHANNELS == 1) begin : gen_single_channel
			arbiter_single_client #(.WAIT_GNT_ACK(1)) u_desc_ar_arbiter_single(
				.clk(clk),
				.rst_n(rst_n),
				.block_arb(1'b0),
				.request(desc_ar_valid[0]),
				.grant_ack(desc_ar_grant_ack[0]),
				.grant_valid(desc_ar_grant_valid),
				.grant(desc_ar_grant[0]),
				.grant_id(desc_ar_grant_id[0])
			);
		end
		else begin : gen_multi_channel
			arbiter_round_robin #(
				.CLIENTS(NUM_CHANNELS),
				.WAIT_GNT_ACK(1)
			) u_desc_ar_arbiter(
				.clk(clk),
				.rst_n(rst_n),
				.block_arb(1'b0),
				.request(desc_ar_valid),
				.grant_ack(desc_ar_grant_ack),
				.grant_valid(desc_ar_grant_valid),
				.grant(desc_ar_grant),
				.grant_id(desc_ar_grant_id),
				.last_grant()
			);
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] ch;
			for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1)
				desc_ar_grant_ack[ch] = ((desc_ar_grant_valid && desc_ar_grant[ch]) && desc_ar_valid[ch]) && desc_axi_int_arready;
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] ch;
			for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1)
				desc_ar_ready[ch] = (desc_ar_grant_valid && desc_ar_grant[ch]) && desc_axi_int_arready;
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		desc_axi_int_arvalid = 1'sb0;
		desc_axi_int_araddr = 1'sb0;
		desc_axi_int_arlen = 1'sb0;
		desc_axi_int_arsize = 1'sb0;
		desc_axi_int_arburst = 1'sb0;
		desc_axi_int_arid = 1'sb0;
		desc_axi_int_arlock = 1'sb0;
		desc_axi_int_arcache = 1'sb0;
		desc_axi_int_arprot = 1'sb0;
		desc_axi_int_arqos = 1'sb0;
		desc_axi_int_arregion = 1'sb0;
		begin : sv2v_autoblock_3
			reg signed [31:0] ch;
			for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1)
				if (desc_ar_grant[ch]) begin
					desc_axi_int_arvalid = desc_ar_valid[ch];
					desc_axi_int_araddr = desc_ar_addr[ch * ADDR_WIDTH+:ADDR_WIDTH];
					desc_axi_int_arlen = desc_ar_len[ch * 8+:8];
					desc_axi_int_arsize = desc_ar_size[ch * 3+:3];
					desc_axi_int_arburst = desc_ar_burst[ch * 2+:2];
					desc_axi_int_arid = {{AXI_ID_WIDTH - CHAN_WIDTH {1'b0}}, ch[CHAN_WIDTH - 1:0]};
					desc_axi_int_arlock = desc_ar_lock[ch];
					desc_axi_int_arcache = desc_ar_cache[ch * 4+:4];
					desc_axi_int_arprot = desc_ar_prot[ch * 3+:3];
					desc_axi_int_arqos = desc_ar_qos[ch * 4+:4];
					desc_axi_int_arregion = desc_ar_region[ch * 4+:4];
				end
		end
	end
	wire [CHAN_WIDTH - 1:0] desc_r_channel_id;
	assign desc_r_channel_id = desc_axi_int_rid[CHAN_WIDTH - 1:0];
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		desc_r_valid = 1'sb0;
		begin : sv2v_autoblock_4
			reg signed [31:0] ch;
			for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1)
				begin
					desc_r_data[ch * 256+:256] = desc_axi_int_rdata;
					desc_r_resp[ch * 2+:2] = desc_axi_int_rresp;
					desc_r_last[ch] = desc_axi_int_rlast;
					desc_r_id[ch * AXI_ID_WIDTH+:AXI_ID_WIDTH] = desc_axi_int_rid;
				end
		end
		if (desc_axi_int_rvalid && (sv2v_cast_32(desc_r_channel_id) < NUM_CHANNELS))
			desc_r_valid[desc_r_channel_id] = 1'b1;
	end
	assign desc_axi_int_rready = |desc_r_ready;
	assign perf_window_active = 1'b0;
	assign perf_window_cycles = 1'sb0;
	assign perf_prod_cycles = 1'sb0;
	assign perf_bp_cycles = 1'sb0;
	assign perf_starv_cycles = 1'sb0;
	assign perf_idle_cycles = 1'sb0;
	assign perf_beat_count = 1'sb0;
	assign perf_byte_count = 1'sb0;
	assign perf_burst_count = 1'sb0;
	assign cfg_sts_desc_mon_conflict_error = 1'b0;
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	localparam signed [31:0] sv2v_uu_u_desc_axi_monitor_N_ADDR_RANGES = 0;
	localparam [0:0] sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_enable_0 = 1'sb0;
	localparam signed [31:0] sv2v_uu_u_desc_axi_monitor_AXI_ADDR_WIDTH = ADDR_WIDTH;
	localparam signed [31:0] sv2v_uu_u_desc_axi_monitor_AW = sv2v_uu_u_desc_axi_monitor_AXI_ADDR_WIDTH;
	localparam [(1 * sv2v_uu_u_desc_axi_monitor_AW) - 1:0] sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_low_0 = 1'sb0;
	localparam [(1 * sv2v_uu_u_desc_axi_monitor_AW) - 1:0] sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_high_0 = 1'sb0;
	axi4_master_rd_monlite #(
		.USE_MONITOR((USE_AXI_MONITORS == 1) && USE_DESC_AXI_MONITOR),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(ADDR_WIDTH),
		.AXI_DATA_WIDTH(256),
		.AXI_USER_WIDTH(1),
		.UNIT_ID(MON_UNIT_ID),
		.AGENT_ID(DESC_AXI_MON_AGENT_ID),
		.MAX_TRANSACTIONS(MON_MAX_TRANSACTIONS)
	) u_desc_axi_monitor(
		.aclk(clk),
		.aresetn(rst_n),
		.cam_clear(cam_clear),
		.fub_axi_arid(desc_axi_int_arid),
		.fub_axi_araddr(desc_axi_int_araddr),
		.fub_axi_arlen(desc_axi_int_arlen),
		.fub_axi_arsize(desc_axi_int_arsize),
		.fub_axi_arburst(desc_axi_int_arburst),
		.fub_axi_arlock(desc_axi_int_arlock),
		.fub_axi_arcache(desc_axi_int_arcache),
		.fub_axi_arprot(desc_axi_int_arprot),
		.fub_axi_arqos(desc_axi_int_arqos),
		.fub_axi_arregion(desc_axi_int_arregion),
		.fub_axi_aruser(1'b0),
		.fub_axi_arvalid(desc_axi_int_arvalid),
		.fub_axi_arready(desc_axi_int_arready),
		.fub_axi_rid(desc_axi_int_rid),
		.fub_axi_rdata(desc_axi_int_rdata),
		.fub_axi_rresp(desc_axi_int_rresp),
		.fub_axi_rlast(desc_axi_int_rlast),
		.fub_axi_ruser(),
		.fub_axi_rvalid(desc_axi_int_rvalid),
		.fub_axi_rready(desc_axi_int_rready),
		.m_axi_arid(desc_axi_arid),
		.m_axi_araddr(desc_axi_araddr),
		.m_axi_arlen(desc_axi_arlen),
		.m_axi_arsize(desc_axi_arsize),
		.m_axi_arburst(desc_axi_arburst),
		.m_axi_arlock(desc_axi_arlock),
		.m_axi_arcache(desc_axi_arcache),
		.m_axi_arprot(desc_axi_arprot),
		.m_axi_arqos(desc_axi_arqos),
		.m_axi_arregion(desc_axi_arregion),
		.m_axi_aruser(),
		.m_axi_arvalid(desc_axi_arvalid),
		.m_axi_arready(desc_axi_arready),
		.m_axi_rid(desc_axi_rid),
		.m_axi_rdata(desc_axi_rdata),
		.m_axi_rresp(desc_axi_rresp),
		.m_axi_rlast(desc_axi_rlast),
		.m_axi_ruser(1'b0),
		.m_axi_rvalid(desc_axi_rvalid),
		.m_axi_rready(desc_axi_rready),
		.cfg_monitor_enable(cfg_desc_mon_enable),
		.cfg_error_enable(cfg_desc_mon_err_enable),
		.cfg_compl_enable(cfg_desc_mon_compl_enable),
		.cfg_threshold_enable(cfg_desc_mon_thresh_enable),
		.cfg_timeout_enable(cfg_desc_mon_timeout_enable),
		.cfg_timeout_cycles(sv2v_cast_16(cfg_desc_mon_timeout_cycles)),
		.cfg_freq_sel(4'b0000),
		.cfg_axi_pkt_mask(cfg_desc_mon_pkt_mask),
		.cfg_latency_threshold(cfg_desc_mon_latency_thresh),
		.cfg_addr_check_enable(1'b0),
		.cfg_addr_match_enable(1'b0),
		.cfg_addr_range_enable(sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_enable_0),
		.cfg_addr_range_low(sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_low_0),
		.cfg_addr_range_high(sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_high_0),
		.i_mon_time(i_mon_time),
		.monbus_valid(desc_axi_mon_valid),
		.monbus_ready(desc_axi_mon_ready),
		.monbus_packet(desc_axi_mon_packet),
		.monbus_timestamp(desc_axi_mon_timestamp),
		.busy(cfg_sts_desc_mon_busy),
		.active_transactions(cfg_sts_desc_mon_active_txns),
		.error_count(cfg_sts_desc_mon_error_count),
		.transaction_count(cfg_sts_desc_mon_txn_count),
		.dropped_count(),
		.refused_count()
	);
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_5
			reg signed [31:0] ch;
			for (ch = 0; ch < NUM_CHANNELS; ch = ch + 1)
				begin
					monbus_valid_all[ch] = mon_valid_ch[ch];
					mon_ready_ch[ch] = monbus_ready_all[ch];
					monbus_packet_all[((MONBUS_SOURCES - 1) - ch) * monitor_common_pkg_MONBUS_PKT_WIDTH+:monitor_common_pkg_MONBUS_PKT_WIDTH] = mon_packet_ch[ch];
					monbus_timestamp_all[((MONBUS_SOURCES - 1) - ch) * monitor_common_pkg_MONBUS_TS_WIDTH+:monitor_common_pkg_MONBUS_TS_WIDTH] = mon_timestamp_ch[ch];
				end
		end
		monbus_valid_all[NUM_CHANNELS] = desc_axi_mon_valid;
		desc_axi_mon_ready = monbus_ready_all[NUM_CHANNELS];
		monbus_packet_all[((MONBUS_SOURCES - 1) - NUM_CHANNELS) * monitor_common_pkg_MONBUS_PKT_WIDTH+:monitor_common_pkg_MONBUS_PKT_WIDTH] = desc_axi_mon_packet;
		monbus_timestamp_all[((MONBUS_SOURCES - 1) - NUM_CHANNELS) * monitor_common_pkg_MONBUS_TS_WIDTH+:monitor_common_pkg_MONBUS_TS_WIDTH] = desc_axi_mon_timestamp;
	end
	monbus_arbiter #(
		.CLIENTS(MONBUS_SOURCES),
		.INPUT_SKID_ENABLE(1),
		.OUTPUT_SKID_ENABLE(1),
		.INPUT_SKID_DEPTH(2),
		.OUTPUT_SKID_DEPTH(2)
	) u_monbus_aggregator(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.block_arb(1'b0),
		.monbus_valid_in(monbus_valid_all),
		.monbus_ready_in(monbus_ready_all),
		.monbus_packet_in(monbus_packet_all),
		.monbus_timestamp_in(monbus_timestamp_all),
		.monbus_valid(mon_valid),
		.monbus_ready(mon_ready),
		.monbus_packet(mon_packet),
		.monbus_timestamp(mon_timestamp),
		.grant_valid(),
		.grant(),
		.grant_id(),
		.last_grant()
	);
	initial _sv2v_0 = 0;
endmodule
