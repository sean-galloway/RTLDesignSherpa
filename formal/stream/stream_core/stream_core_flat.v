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
	always @(posedge clk)
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
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/rtl/common/counter_freq_invariant.sv:128:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MIN_FREQ_MHZ must be >= 1 (got %0d)", MIN_FREQ_MHZ);
		if (MAX_FREQ_MHZ < MIN_FREQ_MHZ)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/rtl/common/counter_freq_invariant.sv:130:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MAX_FREQ_MHZ (%0d) < MIN_FREQ_MHZ (%0d)", MAX_FREQ_MHZ, MIN_FREQ_MHZ);
		if (NUM_FREQ_ENTRIES < 1)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/rtl/common/counter_freq_invariant.sv:133:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: NUM_FREQ_ENTRIES must be >= 1 (got %0d)", NUM_FREQ_ENTRIES);
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
	always @(posedge clk)
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
	always @(posedge clk)
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
				always @(posedge axi_aclk)
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
			always @(posedge axi_aclk)
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
				always @(posedge axi_aclk)
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
	reg [DW - 1:0] r_data [0:DEPTH - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH < 2) || (DEPTH > 8)) begin : gen_depth_guard
			initial $display("Error [elaboration] /mnt/data/github/RTLDesignSherpa/rtl/amba/gaxi/gaxi_skid_buffer.sv:103:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
		end
	endgenerate
	genvar _gv_gi_2;
	generate
		for (_gv_gi_2 = 0; _gv_gi_2 < DEPTH; _gv_gi_2 = _gv_gi_2 + 1) begin : g_slot
			localparam gi = _gv_gi_2;
			always @(posedge axi_aclk)
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
	always @(posedge axi_aclk)
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
	always @(posedge axi_aclk)
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
module axi4_master_wr (
	aclk,
	aresetn,
	fub_axi_awid,
	fub_axi_awaddr,
	fub_axi_awlen,
	fub_axi_awsize,
	fub_axi_awburst,
	fub_axi_awlock,
	fub_axi_awcache,
	fub_axi_awprot,
	fub_axi_awqos,
	fub_axi_awregion,
	fub_axi_awuser,
	fub_axi_awvalid,
	fub_axi_awready,
	fub_axi_wdata,
	fub_axi_wstrb,
	fub_axi_wlast,
	fub_axi_wuser,
	fub_axi_wvalid,
	fub_axi_wready,
	fub_axi_bid,
	fub_axi_bresp,
	fub_axi_buser,
	fub_axi_bvalid,
	fub_axi_bready,
	m_axi_awid,
	m_axi_awaddr,
	m_axi_awlen,
	m_axi_awsize,
	m_axi_awburst,
	m_axi_awlock,
	m_axi_awcache,
	m_axi_awprot,
	m_axi_awqos,
	m_axi_awregion,
	m_axi_awuser,
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
	m_axi_buser,
	m_axi_bvalid,
	m_axi_bready,
	busy
);
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
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
	parameter signed [31:0] AWSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] WSize = ((DW + SW) + 1) + UW;
	parameter signed [31:0] BSize = (IW + 2) + UW;
	input wire aclk;
	input wire aresetn;
	input wire [IW - 1:0] fub_axi_awid;
	input wire [AW - 1:0] fub_axi_awaddr;
	input wire [7:0] fub_axi_awlen;
	input wire [2:0] fub_axi_awsize;
	input wire [1:0] fub_axi_awburst;
	input wire fub_axi_awlock;
	input wire [3:0] fub_axi_awcache;
	input wire [2:0] fub_axi_awprot;
	input wire [3:0] fub_axi_awqos;
	input wire [3:0] fub_axi_awregion;
	input wire [UW - 1:0] fub_axi_awuser;
	input wire fub_axi_awvalid;
	output wire fub_axi_awready;
	input wire [DW - 1:0] fub_axi_wdata;
	input wire [SW - 1:0] fub_axi_wstrb;
	input wire fub_axi_wlast;
	input wire [UW - 1:0] fub_axi_wuser;
	input wire fub_axi_wvalid;
	output wire fub_axi_wready;
	output wire [IW - 1:0] fub_axi_bid;
	output wire [1:0] fub_axi_bresp;
	output wire [UW - 1:0] fub_axi_buser;
	output wire fub_axi_bvalid;
	input wire fub_axi_bready;
	output wire [IW - 1:0] m_axi_awid;
	output wire [AW - 1:0] m_axi_awaddr;
	output wire [7:0] m_axi_awlen;
	output wire [2:0] m_axi_awsize;
	output wire [1:0] m_axi_awburst;
	output wire m_axi_awlock;
	output wire [3:0] m_axi_awcache;
	output wire [2:0] m_axi_awprot;
	output wire [3:0] m_axi_awqos;
	output wire [3:0] m_axi_awregion;
	output wire [UW - 1:0] m_axi_awuser;
	output wire m_axi_awvalid;
	input wire m_axi_awready;
	output wire [DW - 1:0] m_axi_wdata;
	output wire [SW - 1:0] m_axi_wstrb;
	output wire m_axi_wlast;
	output wire [UW - 1:0] m_axi_wuser;
	output wire m_axi_wvalid;
	input wire m_axi_wready;
	input wire [IW - 1:0] m_axi_bid;
	input wire [1:0] m_axi_bresp;
	input wire [UW - 1:0] m_axi_buser;
	input wire m_axi_bvalid;
	output wire m_axi_bready;
	output wire busy;
	wire [3:0] int_aw_count;
	wire [AWSize - 1:0] int_aw_pkt;
	wire int_skid_awvalid;
	wire int_skid_awready;
	wire [3:0] int_w_count;
	wire [WSize - 1:0] int_w_pkt;
	wire int_skid_wvalid;
	wire int_skid_wready;
	wire [3:0] int_b_count;
	wire [BSize - 1:0] int_b_pkt;
	wire int_skid_bvalid;
	wire int_skid_bready;
	assign busy = (((((int_aw_count > 0) || (int_w_count > 0)) || (int_b_count > 0)) || fub_axi_awvalid) || fub_axi_wvalid) || m_axi_bvalid;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AW),
		.DATA_WIDTH(AWSize)
	) aw_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_axi_awvalid),
		.wr_ready(fub_axi_awready),
		.wr_data({fub_axi_awid, fub_axi_awaddr, fub_axi_awlen, fub_axi_awsize, fub_axi_awburst, fub_axi_awlock, fub_axi_awcache, fub_axi_awprot, fub_axi_awqos, fub_axi_awregion, fub_axi_awuser}),
		.rd_valid(int_skid_awvalid),
		.rd_ready(int_skid_awready),
		.rd_count(int_aw_count),
		.rd_data(int_aw_pkt),
		.count()
	);
	assign {m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst, m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos, m_axi_awregion, m_axi_awuser} = int_aw_pkt;
	assign m_axi_awvalid = int_skid_awvalid;
	assign int_skid_awready = m_axi_awready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_W),
		.DATA_WIDTH(WSize)
	) w_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_axi_wvalid),
		.wr_ready(fub_axi_wready),
		.wr_data({fub_axi_wdata, fub_axi_wstrb, fub_axi_wlast, fub_axi_wuser}),
		.rd_valid(int_skid_wvalid),
		.rd_ready(int_skid_wready),
		.rd_count(int_w_count),
		.rd_data(int_w_pkt),
		.count()
	);
	assign {m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser} = int_w_pkt;
	assign m_axi_wvalid = int_skid_wvalid;
	assign int_skid_wready = m_axi_wready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_B),
		.DATA_WIDTH(BSize)
	) b_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(m_axi_bvalid),
		.wr_ready(m_axi_bready),
		.wr_data({m_axi_bid, m_axi_bresp, m_axi_buser}),
		.rd_valid(int_skid_bvalid),
		.rd_ready(int_skid_bready),
		.rd_count(int_b_count),
		.rd_data({fub_axi_bid, fub_axi_bresp, fub_axi_buser}),
		.count()
	);
	assign fub_axi_bvalid = int_skid_bvalid;
	assign int_skid_bready = fub_axi_bready;
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
module axi_monitor_timer (
	aclk,
	aresetn,
	cfg_freq_sel,
	timer_tick,
	timestamp
);
	parameter signed [31:0] CFI_MIN_FREQ_MHZ = 5;
	parameter signed [31:0] CFI_MAX_FREQ_MHZ = 220;
	parameter signed [31:0] CFI_NUM_FREQ_ENTRIES = 16;
	parameter signed [31:0] CFI_FREQ_STRATEGY = 0;
	parameter signed [31:0] SEL_WIDTH = (CFI_NUM_FREQ_ENTRIES > 1 ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1);
	input wire aclk;
	input wire aresetn;
	input wire [SEL_WIDTH - 1:0] cfg_freq_sel;
	output wire timer_tick;
	output wire [31:0] timestamp;
	reg [31:0] r_timestamp;
	assign timestamp = r_timestamp;
	wire w_timer_tick;
	assign timer_tick = w_timer_tick;
	always @(posedge aclk)
		if (!aresetn)
			r_timestamp <= 1'sb0;
		else
			r_timestamp <= r_timestamp + 1'b1;
	counter_freq_invariant #(
		.COUNTER_WIDTH(1),
		.MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
		.MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
		.NUM_FREQ_ENTRIES(CFI_NUM_FREQ_ENTRIES),
		.FREQ_STRATEGY(CFI_FREQ_STRATEGY)
	) timer_counter(
		.clk(aclk),
		.rst_n(aresetn),
		.sync_reset_n(1'b1),
		.freq_sel(cfg_freq_sel),
		.tick(w_timer_tick),
		.o_counter()
	);
endmodule
module axi_monitor_trans_mgr (
	aclk,
	aresetn,
	clear,
	cmd_valid,
	cmd_ready,
	cmd_id,
	cmd_addr,
	cmd_len,
	cmd_size,
	cmd_burst,
	data_valid,
	data_ready,
	data_id,
	data_last,
	data_resp,
	resp_valid,
	resp_ready,
	resp_id,
	resp_code,
	timestamp,
	i_event_reported_flags,
	i_timeout_detected,
	cfg_addr_filter_enable,
	cfg_addr_filter_low,
	cfg_addr_filter_high,
	filtered_mask,
	trans_table,
	active_count
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter [0:0] USE_WDATA_ORDER_Q = 1'b0;
	parameter signed [31:0] NUM_BANKS = 1;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	parameter [0:0] ADDR_FILTER_ENABLE = 1'b0;
	input wire aclk;
	input wire aresetn;
	input wire clear;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire [IW - 1:0] cmd_id;
	input wire [AW - 1:0] cmd_addr;
	input wire [7:0] cmd_len;
	input wire [2:0] cmd_size;
	input wire [1:0] cmd_burst;
	input wire data_valid;
	input wire data_ready;
	input wire [IW - 1:0] data_id;
	input wire data_last;
	input wire [1:0] data_resp;
	input wire resp_valid;
	input wire resp_ready;
	input wire [IW - 1:0] resp_id;
	input wire [1:0] resp_code;
	input wire [31:0] timestamp;
	input wire [MAX_TRANSACTIONS - 1:0] i_event_reported_flags;
	input wire [MAX_TRANSACTIONS - 1:0] i_timeout_detected;
	input wire cfg_addr_filter_enable;
	input wire [AW - 1:0] cfg_addr_filter_low;
	input wire [AW - 1:0] cfg_addr_filter_high;
	output wire [MAX_TRANSACTIONS - 1:0] filtered_mask;
	output wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	output wire [7:0] active_count;
	localparam signed [31:0] N = MAX_TRANSACTIONS;
	localparam signed [31:0] PAYLOAD_W = 285;
	localparam signed [31:0] BANK_SLOTS = N / NUM_BANKS;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	function automatic signed [31:0] bank_of;
		input reg [IW - 1:0] id;
		bank_of = (NUM_BANKS > 1 ? sv2v_cast_32_signed(sv2v_cast_32(id) % NUM_BANKS) : 0);
	endfunction
	generate
		if ((NUM_BANKS < 1) || ((NUM_BANKS & (NUM_BANKS - 1)) != 0)) begin : gen_bad_banks
			initial $display("Error [elaboration] .sv2v_prep/axi_monitor_trans_mgr.sv:228:9 - axi_monitor_trans_mgr.gen_bad_banks\n msg: ", "axi_monitor_trans_mgr: NUM_BANKS=%0d must be a power of 2.", NUM_BANKS);
		end
		if ((NUM_BANKS > 1) && ((MAX_TRANSACTIONS % NUM_BANKS) != 0)) begin : gen_ragged_banks
			initial $display("Error [elaboration] .sv2v_prep/axi_monitor_trans_mgr.sv:231:9 - axi_monitor_trans_mgr.gen_ragged_banks\n msg: ", "axi_monitor_trans_mgr: MAX_TRANSACTIONS=%0d is not divisible by NUM_BANKS=%0d.", MAX_TRANSACTIONS, NUM_BANKS);
		end
		if (((NUM_BANKS > 1) && !IS_READ) && !USE_WDATA_ORDER_Q) begin : gen_banked_wr_needs_widq
			initial $display("Error [elaboration] .sv2v_prep/axi_monitor_trans_mgr.sv:247:9 - axi_monitor_trans_mgr.gen_banked_wr_needs_widq\n msg: ", "axi_monitor_trans_mgr: NUM_BANKS=%0d on a write monitor requires USE_WDATA_ORDER_Q=1 (the WID-less fallback double-counts one W beat across banks).", NUM_BANKS);
		end
		if (ID_WIDTH > 8) begin : gen_id_width_unsupported
			initial $display("Error [elaboration] .sv2v_prep/axi_monitor_trans_mgr.sv:284:9 - axi_monitor_trans_mgr.gen_id_width_unsupported\n msg: ", "axi_monitor_trans_mgr: ID_WIDTH=%0d exceeds the 8-bit id field in bus_transaction_t; the table and the CAM key would disagree. Widen bus_transaction_t.id or reduce ID_WIDTH.", ID_WIDTH);
		end
	endgenerate
	reg [N - 1:0] addr_match_oh;
	reg [N - 1:0] data_match_oh;
	reg [N - 1:0] resp_match_oh;
	reg [N - 1:0] cam_data_match_first_oh;
	reg [N - 1:0] free_oh;
	reg [N - 1:0] addr_alloc_oh;
	reg [N - 1:0] data_alloc_oh;
	reg [N - 1:0] resp_alloc_oh;
	wire w_addr_filtered;
	assign w_addr_filtered = (ADDR_FILTER_ENABLE && cfg_addr_filter_enable) && !((cmd_addr >= cfg_addr_filter_low) && (cmd_addr <= cfg_addr_filter_high));
	reg [N - 1:0] r_filtered;
	assign filtered_mask = r_filtered;
	always @(posedge aclk)
		if (!aresetn)
			r_filtered <= 1'sb0;
		else if (clear)
			r_filtered <= 1'sb0;
		else begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (addr_alloc_oh[i])
					r_filtered[i] <= w_addr_filtered;
		end
	reg [N - 1:0] cam_entry_valid;
	reg [(N * 285) - 1:0] cam_entry_payload;
	wire [N - 1:0] cam_entry_we;
	wire [N - 1:0] cam_entry_valid_next;
	wire [IW - 1:0] cam_entry_id_next [0:N - 1];
	wire [284:0] cam_entry_payload_next [0:N - 1];
	wire addr_wants_alloc;
	reg data_wants_alloc;
	reg resp_wants_alloc;
	reg [N - 1:0] w_addr_bank_mask;
	reg [N - 1:0] w_data_bank_mask;
	reg [N - 1:0] w_resp_bank_mask;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin
					w_addr_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(cmd_id));
					w_data_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(data_id));
					w_resp_bank_mask[i] = (NUM_BANKS == 1) || ((i / BANK_SLOTS) == bank_of(resp_id));
				end
		end
	end
	wire [BANK_SLOTS - 1:0] wb_addr_match [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_data_match [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_resp_match [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_data_first [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_free [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_addr_alloc [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_data_alloc [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_resp_alloc [0:NUM_BANKS - 1];
	wire [BANK_SLOTS - 1:0] wb_entry_valid [0:NUM_BANKS - 1];
	wire [(BANK_SLOTS * 285) - 1:0] wb_entry_payload [0:NUM_BANKS - 1];
	reg [BANK_SLOTS - 1:0] wb_entry_we [0:NUM_BANKS - 1];
	reg [BANK_SLOTS - 1:0] wb_valid_next [0:NUM_BANKS - 1];
	reg [(BANK_SLOTS * IW) - 1:0] wb_id_next [0:NUM_BANKS - 1];
	reg [(BANK_SLOTS * 285) - 1:0] wb_payload_next [0:NUM_BANKS - 1];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_3
			reg signed [31:0] b;
			for (b = 0; b < NUM_BANKS; b = b + 1)
				begin : sv2v_autoblock_4
					reg signed [31:0] i;
					for (i = 0; i < BANK_SLOTS; i = i + 1)
						begin
							wb_entry_we[b][i] = cam_entry_we[(b * BANK_SLOTS) + i];
							wb_valid_next[b][i] = cam_entry_valid_next[(b * BANK_SLOTS) + i];
							wb_id_next[b][((BANK_SLOTS - 1) - i) * IW+:IW] = cam_entry_id_next[(b * BANK_SLOTS) + i];
							wb_payload_next[b][((BANK_SLOTS - 1) - i) * 285+:285] = cam_entry_payload_next[(b * BANK_SLOTS) + i];
						end
				end
		end
	end
	genvar _gv_gb_1;
	generate
		for (_gv_gb_1 = 0; _gv_gb_1 < NUM_BANKS; _gv_gb_1 = _gv_gb_1 + 1) begin : g_cam_bank
			localparam gb = _gv_gb_1;
			monitor_trans_cam #(
				.DEPTH(BANK_SLOTS),
				.ID_WIDTH(IW),
				.PAYLOAD_WIDTH(PAYLOAD_W)
			) u_cam(
				.clk(aclk),
				.rst_n(aresetn),
				.clear(clear),
				.lookup_addr_id(cmd_id),
				.lookup_data_id(data_id),
				.lookup_resp_id(resp_id),
				.addr_match_oh(wb_addr_match[gb]),
				.data_match_oh(wb_data_match[gb]),
				.resp_match_oh(wb_resp_match[gb]),
				.data_match_first_oh(wb_data_first[gb]),
				.free_oh(wb_free[gb]),
				.addr_wants_alloc(addr_wants_alloc && (bank_of(cmd_id) == gb)),
				.data_wants_alloc(data_wants_alloc && (bank_of(data_id) == gb)),
				.resp_wants_alloc(resp_wants_alloc && (bank_of(resp_id) == gb)),
				.addr_alloc_mask({BANK_SLOTS {1'b1}}),
				.data_alloc_mask({BANK_SLOTS {1'b1}}),
				.resp_alloc_mask({BANK_SLOTS {1'b1}}),
				.addr_alloc_oh(wb_addr_alloc[gb]),
				.data_alloc_oh(wb_data_alloc[gb]),
				.resp_alloc_oh(wb_resp_alloc[gb]),
				.entry_we(wb_entry_we[gb]),
				.entry_valid_next(wb_valid_next[gb]),
				.entry_id_next(wb_id_next[gb]),
				.entry_payload_next(wb_payload_next[gb]),
				.entry_valid(wb_entry_valid[gb]),
				.entry_id(),
				.entry_payload(wb_entry_payload[gb])
			);
		end
	endgenerate
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_5
			reg signed [31:0] b;
			for (b = 0; b < NUM_BANKS; b = b + 1)
				begin : sv2v_autoblock_6
					reg signed [31:0] i;
					for (i = 0; i < BANK_SLOTS; i = i + 1)
						begin
							addr_match_oh[(b * BANK_SLOTS) + i] = wb_addr_match[b][i];
							data_match_oh[(b * BANK_SLOTS) + i] = wb_data_match[b][i];
							resp_match_oh[(b * BANK_SLOTS) + i] = wb_resp_match[b][i];
							cam_data_match_first_oh[(b * BANK_SLOTS) + i] = wb_data_first[b][i];
							free_oh[(b * BANK_SLOTS) + i] = wb_free[b][i];
							addr_alloc_oh[(b * BANK_SLOTS) + i] = wb_addr_alloc[b][i];
							data_alloc_oh[(b * BANK_SLOTS) + i] = wb_data_alloc[b][i];
							resp_alloc_oh[(b * BANK_SLOTS) + i] = wb_resp_alloc[b][i];
							cam_entry_valid[(b * BANK_SLOTS) + i] = wb_entry_valid[b][i];
							cam_entry_payload[((N - 1) - ((b * BANK_SLOTS) + i)) * 285+:285] = wb_entry_payload[b][((BANK_SLOTS - 1) - i) * 285+:285];
						end
				end
		end
	end
	localparam signed [31:0] AGEW = (N > 1 ? $clog2(N) : 1);
	reg [AGEW - 1:0] r_age [0:N - 1];
	reg [(N * AGEW) - 1:0] w_age_flat;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_age_flat[i * AGEW+:AGEW] = r_age[i];
		end
	end
	function automatic [N - 1:0] pick_oldest;
		input reg [N - 1:0] cand;
		input reg [(N * AGEW) - 1:0] ages;
		reg [N - 1:0] res;
		reg lose;
		begin
			begin : sv2v_autoblock_8
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					begin
						lose = 1'b0;
						begin : sv2v_autoblock_9
							reg signed [31:0] j;
							for (j = 0; j < N; j = j + 1)
								if (((((i / BANK_SLOTS) == (j / BANK_SLOTS)) && (j != i)) && cand[j]) && ((ages[j * AGEW+:AGEW] < ages[i * AGEW+:AGEW]) || ((ages[j * AGEW+:AGEW] == ages[i * AGEW+:AGEW]) && (j < i))))
									lose = 1'b1;
						end
						res[i] = cand[i] && !lose;
					end
			end
			pick_oldest = res;
		end
	endfunction
	(* keep = "true" *) reg [N - 1:0] w_data_state_pred_oh;
	wire [N - 1:0] w_data_state_first_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_10
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_data_state_pred_oh[i] = ((cam_entry_valid[i] && ((cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1) || (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h2))) && cam_entry_payload[(((N - 1) - i) * 285) + 283]) && !cam_entry_payload[(((N - 1) - i) * 285) + 281];
		end
	end
	reg [N - 1:0] w_freeing_oh;
	localparam signed [31:0] SLOTW = (N > 1 ? $clog2(N) : 1);
	localparam signed [31:0] WQW = (N > 1 ? $clog2(N + 1) : 1);
	reg [IW - 1:0] r_widq [0:N - 1];
	reg [WQW - 1:0] r_widq_count;
	wire [IW - 1:0] w_widq_head;
	reg [N - 1:0] w_widq_cand_oh;
	wire w_widq_push;
	wire w_widq_pop;
	wire w_widq_head_dead;
	wire w_widq_bypass;
	assign w_widq_push = ((!IS_READ && USE_WDATA_ORDER_Q) && cmd_valid) && cmd_ready;
	assign w_widq_bypass = (r_widq_count == {WQW {1'sb0}}) && w_widq_push;
	assign w_widq_head = (w_widq_bypass ? cmd_id : r_widq[0]);
	always @(*) begin
		if (_sv2v_0)
			;
		w_widq_cand_oh = 1'sb0;
		if ((!IS_READ && USE_WDATA_ORDER_Q) && ((r_widq_count != {WQW {1'sb0}}) || w_widq_bypass)) begin : sv2v_autoblock_11
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_widq_cand_oh[i] = (w_data_state_pred_oh[i] && (cam_entry_payload[(((N - 1) - i) * 285) + 242-:8] == w_widq_head)) && !w_freeing_oh[i];
		end
	end
	assign w_widq_head_dead = (r_widq_count != {WQW {1'sb0}}) && !(|w_widq_cand_oh);
	assign w_widq_pop = (r_widq_count != {WQW {1'sb0}}) && (((data_valid && data_ready) && data_last) || w_widq_head_dead);
	assign w_data_state_first_oh = (USE_WDATA_ORDER_Q ? pick_oldest(w_widq_cand_oh, w_age_flat) : pick_oldest(w_data_state_pred_oh, w_age_flat));
	function automatic signed [WQW - 1:0] sv2v_cast_6C857_signed;
		input reg signed [WQW - 1:0] inp;
		sv2v_cast_6C857_signed = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_widq_count <= 1'sb0;
			begin : sv2v_autoblock_12
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_widq[i] <= 1'sb0;
			end
		end
		else if (clear) begin
			r_widq_count <= 1'sb0;
			begin : sv2v_autoblock_13
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_widq[i] <= 1'sb0;
			end
		end
		else if (!IS_READ && USE_WDATA_ORDER_Q) begin : sv2v_autoblock_14
			reg [WQW - 1:0] v_cnt;
			v_cnt = r_widq_count;
			if (w_widq_pop && (v_cnt != {WQW {1'sb0}})) begin
				begin : sv2v_autoblock_15
					reg signed [31:0] i;
					for (i = 0; i < (N - 1); i = i + 1)
						r_widq[i] <= r_widq[i + 1];
				end
				v_cnt = v_cnt - 1'b1;
			end
			if (w_widq_push && (v_cnt < sv2v_cast_6C857_signed(N))) begin
				r_widq[v_cnt[SLOTW - 1:0]] <= cmd_id;
				v_cnt = v_cnt + 1'b1;
			end
			r_widq_count <= v_cnt;
		end
	reg [N - 1:0] w_can_cleanup;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_16
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (cam_entry_valid[i])
					(* full_case, parallel_case *)
					case (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3])
						3'h3, 3'h4, 3'h5: w_can_cleanup[i] = cam_entry_payload[(((N - 1) - i) * 285) + 279];
						default: w_can_cleanup[i] = 1'b0;
					endcase
				else
					w_can_cleanup[i] = 1'b0;
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_17
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_freeing_oh[i] = cam_entry_valid[i] && w_can_cleanup[i];
		end
	end
	reg [N - 1:0] w_addr_pend_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_18
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_addr_pend_oh[i] = (addr_match_oh[i] && !cam_entry_payload[(((N - 1) - i) * 285) + 283]) && !w_freeing_oh[i];
		end
	end
	reg [N - 1:0] w_addr_alloc_mirror_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_alloc_mirror_oh = 1'sb0;
		if (addr_wants_alloc) begin : sv2v_autoblock_19
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (((w_addr_alloc_mirror_oh == {N {1'sb0}}) && free_oh[i]) && w_addr_bank_mask[i])
					w_addr_alloc_mirror_oh[i] = 1'b1;
		end
	end
	wire [N - 1:0] addr_update_oh;
	wire [N - 1:0] data_update_oh;
	wire [N - 1:0] resp_update_oh;
	reg [N - 1:0] w_data_cmd_bypass_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_data_cmd_bypass_oh = 1'sb0;
		if (((!IS_READ && data_valid) && data_ready) && !(|w_data_state_pred_oh)) begin : sv2v_autoblock_20
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_data_cmd_bypass_oh[i] = w_addr_alloc_mirror_oh[i] || ((cmd_valid && addr_update_oh[i]) && (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1));
		end
	end
	wire addr_hit_any;
	wire data_hit_any;
	wire resp_hit_any;
	assign addr_hit_any = |w_addr_pend_oh;
	assign resp_hit_any = |resp_match_oh;
	assign data_hit_any = (IS_READ ? |data_match_oh : |w_data_state_pred_oh || |w_data_cmd_bypass_oh);
	function automatic signed [31:0] monitor_common_pkg_cmd_entry_reserve;
		input reg signed [31:0] max_transactions;
		monitor_common_pkg_cmd_entry_reserve = (max_transactions >= 16 ? 4 : 0);
	endfunction
	localparam signed [31:0] CMD_ENTRY_RESERVE = monitor_common_pkg_cmd_entry_reserve(N);
	reg [$clog2(N + 1) - 1:0] w_cmd_entry_count;
	function automatic signed [$clog2(N + 1) - 1:0] sv2v_cast_54CAC_signed;
		input reg signed [$clog2(N + 1) - 1:0] inp;
		sv2v_cast_54CAC_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_cmd_entry_count = 1'sb0;
		begin : sv2v_autoblock_21
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (cam_entry_valid[i] && (cam_entry_payload[(((N - 1) - i) * 285) + 283] || (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1)))
					w_cmd_entry_count = w_cmd_entry_count + sv2v_cast_54CAC_signed(1);
		end
	end
	wire w_cmd_headroom;
	assign w_cmd_headroom = (CMD_ENTRY_RESERVE == 0) || (w_cmd_entry_count < sv2v_cast_54CAC_signed(N - CMD_ENTRY_RESERVE));
	assign addr_wants_alloc = (cmd_valid && !addr_hit_any) && w_cmd_headroom;
	always @(*) begin
		if (_sv2v_0)
			;
		if (IS_READ)
			data_wants_alloc = (data_valid && data_ready) && !data_hit_any;
		else
			data_wants_alloc = ((data_valid && data_ready) && !IS_AXI) && !data_hit_any;
		resp_wants_alloc = ((!IS_READ && resp_valid) && resp_ready) && !resp_hit_any;
	end
	reg [N - 1:0] w_data_cand_open;
	reg [N - 1:0] w_data_cand_any;
	reg [N - 1:0] w_resp_cand_open;
	reg [N - 1:0] w_resp_cand_any;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_22
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin
					w_data_cand_any[i] = data_match_oh[i] && !w_freeing_oh[i];
					w_data_cand_open[i] = w_data_cand_any[i] && !cam_entry_payload[(((N - 1) - i) * 285) + 281];
					w_resp_cand_any[i] = resp_match_oh[i] && !w_freeing_oh[i];
					w_resp_cand_open[i] = w_resp_cand_any[i] && !cam_entry_payload[(((N - 1) - i) * 285) + 280];
				end
		end
	end
	assign addr_update_oh = pick_oldest(w_addr_pend_oh, w_age_flat);
	assign data_update_oh = (IS_READ ? (|w_data_cand_open ? pick_oldest(w_data_cand_open, w_age_flat) : (data_last ? pick_oldest(w_data_cand_any, w_age_flat) : {N {1'sb0}})) : w_data_state_first_oh | w_data_cmd_bypass_oh);
	assign resp_update_oh = (|w_resp_cand_open ? pick_oldest(w_resp_cand_open, w_age_flat) : pick_oldest(w_resp_cand_any, w_age_flat));
	reg [5:0] w_addr_chan_idx;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_chan_idx = (IS_AXI ? {24'h000000, cmd_id} % 64 : 0);
	end
	wire cmd_handshake;
	assign cmd_handshake = cmd_valid && cmd_ready;
	reg [N - 1:0] r_rpt_stale_mask;
	always @(posedge aclk)
		if (!aresetn)
			r_rpt_stale_mask <= 1'sb0;
		else if (clear)
			r_rpt_stale_mask <= 1'sb0;
		else begin : sv2v_autoblock_23
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (w_freeing_oh[i])
					r_rpt_stale_mask[i] <= 1'b1;
				else if (!i_event_reported_flags[i])
					r_rpt_stale_mask[i] <= 1'b0;
		end
	wire w_addr_alloc_fire;
	wire w_data_alloc_fire;
	wire w_resp_alloc_fire;
	assign w_addr_alloc_fire = |addr_alloc_oh;
	assign w_data_alloc_fire = |data_alloc_oh;
	assign w_resp_alloc_fire = |resp_alloc_oh;
	reg [AGEW - 1:0] w_age_addr_new;
	reg [AGEW - 1:0] w_age_data_new;
	reg [AGEW - 1:0] w_age_resp_new;
	function automatic [AGEW - 1:0] sv2v_cast_D1065;
		input reg [AGEW - 1:0] inp;
		sv2v_cast_D1065 = inp;
	endfunction
	always @(*) begin : sv2v_autoblock_24
		reg signed [31:0] surv_bank [0:NUM_BANKS - 1];
		reg signed [31:0] ab;
		reg signed [31:0] db;
		reg signed [31:0] rb;
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_25
			reg signed [31:0] b;
			for (b = 0; b < NUM_BANKS; b = b + 1)
				surv_bank[b] = 0;
		end
		begin : sv2v_autoblock_26
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (cam_entry_valid[i] && !w_freeing_oh[i])
					surv_bank[i / BANK_SLOTS] = surv_bank[i / BANK_SLOTS] + 1;
		end
		ab = bank_of(cmd_id);
		db = bank_of(data_id);
		rb = bank_of(resp_id);
		w_age_addr_new = sv2v_cast_D1065(surv_bank[ab]);
		w_age_data_new = sv2v_cast_D1065(surv_bank[db] + (w_addr_alloc_fire && (ab == db) ? 1 : 0));
		w_age_resp_new = sv2v_cast_D1065((surv_bank[rb] + (w_addr_alloc_fire && (ab == rb) ? 1 : 0)) + (w_data_alloc_fire && (db == rb) ? 1 : 0));
	end
	reg [AGEW - 1:0] w_age_next [0:N - 1];
	function automatic signed [AGEW - 1:0] sv2v_cast_D1065_signed;
		input reg signed [AGEW - 1:0] inp;
		sv2v_cast_D1065_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_27
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin : sv2v_autoblock_28
					reg signed [31:0] dec;
					dec = 0;
					w_age_next[i] = r_age[i];
					if (addr_alloc_oh[i])
						w_age_next[i] = w_age_addr_new;
					else if (data_alloc_oh[i])
						w_age_next[i] = w_age_data_new;
					else if (resp_alloc_oh[i])
						w_age_next[i] = w_age_resp_new;
					else if (cam_entry_valid[i] && !w_freeing_oh[i]) begin
						begin : sv2v_autoblock_29
							reg signed [31:0] j;
							for (j = 0; j < N; j = j + 1)
								if ((((i / BANK_SLOTS) == (j / BANK_SLOTS)) && w_freeing_oh[j]) && (r_age[j] < r_age[i]))
									dec = dec + 1;
						end
						w_age_next[i] = r_age[i] - sv2v_cast_D1065_signed(dec);
					end
				end
		end
	end
	genvar _gv_ga_1;
	generate
		for (_gv_ga_1 = 0; _gv_ga_1 < N; _gv_ga_1 = _gv_ga_1 + 1) begin : g_age
			localparam ga = _gv_ga_1;
			always @(posedge aclk)
				if (!aresetn)
					r_age[ga] <= 1'sb0;
				else if (clear)
					r_age[ga] <= 1'sb0;
				else
					r_age[ga] <= w_age_next[ga];
		end
	endgenerate
	genvar _gv_gi_3;
	localparam [7:0] monitor_amba4_pkg_EVT_CMD_TIMEOUT = 8'h00;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_ORPHAN = 8'h02;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_TIMEOUT = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_PROTOCOL = 8'h04;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_DECERR = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_ORPHAN = 8'h03;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_SLVERR = 8'h00;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_TIMEOUT = 8'h02;
	generate
		for (_gv_gi_3 = 0; _gv_gi_3 < N; _gv_gi_3 = _gv_gi_3 + 1) begin : g_entry_next
			localparam gi = _gv_gi_3;
			reg [284:0] next;
			reg next_we;
			reg [IW - 1:0] next_id;
			always @(*) begin
				if (_sv2v_0)
					;
				next = cam_entry_payload[((N - 1) - gi) * 285+:285];
				next_we = 1'b0;
				next_id = cam_entry_payload[(((N - 1) - gi) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))];
				if (addr_alloc_oh[gi]) begin
					next[284] = 1'b1;
					next[277-:3] = 3'h1;
					next[242-:8] = 1'sb0;
					next[234 + IW:235] = cmd_id;
					next[274-:32] = sv2v_cast_32(cmd_addr);
					next[234-:8] = cmd_len;
					next[226-:3] = cmd_size;
					next[223-:2] = cmd_burst;
					next[283] = cmd_ready;
					next[215-:32] = 1'sb0;
					next[282] = 1'b0;
					next[281] = 1'b0;
					next[280] = 1'b0;
					next[7-:8] = 8'h00;
					next[279] = 1'b0;
					next[183-:32] = 1'sb0;
					next[151-:32] = 1'sb0;
					next[119-:32] = timestamp;
					next[23-:8] = (IS_AXI ? cmd_len + 8'h01 : 8'h01);
					next[15-:8] = 1'sb0;
					next[221-:6] = w_addr_chan_idx;
					next[278] = 1'b0;
					next_we = 1'b1;
					next_id = cmd_id;
				end
				if (addr_update_oh[gi] && cmd_handshake) begin
					next[283] = 1'b1;
					next[215-:32] = 1'sb0;
					next[119-:32] = timestamp;
					next_we = 1'b1;
				end
				if (data_valid && data_ready) begin
					if (data_update_oh[gi]) begin
						next[282] = 1'b1;
						next[15-:8] = next[15-:8] + 1'b1;
						next[183-:32] = 1'sb0;
						if (next[277-:3] != 3'h4) begin
							if ((IS_READ || next[283]) || (next[277-:3] != 3'h1))
								next[277-:3] = 3'h2;
						end
						if (IS_READ) begin
							if (data_last) begin
								next[281] = 1'b1;
								next[87-:32] = timestamp;
							end
							if (data_resp[1]) begin
								next[277-:3] = 3'h4;
								next[7-:8] = (data_resp[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
							end
							else if (data_last)
								next[277-:3] = 3'h3;
						end
						else if (data_last || (next[15-:8] == next[23-:8])) begin
							next[281] = 1'b1;
							next[87-:32] = timestamp;
						end
						next_we = 1'b1;
					end
					else if (data_alloc_oh[gi]) begin
						next[284] = 1'b1;
						next[283] = 1'b0;
						next[279] = 1'b0;
						next[277-:3] = 3'h5;
						next[242-:8] = 1'sb0;
						if (IS_AXI) begin
							next[234 + IW:235] = data_id;
							next[221-:6] = {24'h000000, data_id} % 64;
							next[23-:8] = (IS_READ ? 8'h00 : 8'h01);
						end
						else begin
							next[23-:8] = 8'h01;
							next[221-:6] = 6'h00;
						end
						next[282] = 1'b1;
						next[281] = data_last;
						next[15-:8] = 8'h01;
						next[87-:32] = timestamp;
						next[7-:8] = monitor_amba4_pkg_EVT_DATA_ORPHAN;
						next_we = 1'b1;
						next_id = (IS_AXI ? data_id : {IW {1'sb0}});
					end
				end
				if ((!IS_READ && resp_valid) && resp_ready) begin
					if (resp_update_oh[gi]) begin
						next[280] = 1'b1;
						next[55-:32] = timestamp;
						next[151-:32] = 1'sb0;
						if (resp_code[1]) begin
							next[277-:3] = 3'h4;
							next[7-:8] = (resp_code[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
						end
						else if (cam_entry_payload[(((N - 1) - gi) * 285) + 281]) begin
							if (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h4)
								next[277-:3] = 3'h3;
						end
						else begin
							next[277-:3] = 3'h4;
							next[7-:8] = monitor_amba4_pkg_EVT_PROTOCOL;
						end
						next_we = 1'b1;
					end
					else if (resp_alloc_oh[gi]) begin
						next[284] = 1'b1;
						next[283] = 1'b0;
						next[279] = 1'b0;
						next[277-:3] = 3'h5;
						next[242-:8] = 1'sb0;
						if (IS_AXI) begin
							next[234 + IW:235] = resp_id;
							next[221-:6] = resp_id % 64;
						end
						else
							next[221-:6] = 6'h00;
						next[280] = 1'b1;
						next[55-:32] = timestamp;
						next[7-:8] = monitor_amba4_pkg_EVT_RESP_ORPHAN;
						next_we = 1'b1;
						next_id = (IS_AXI ? resp_id : {IW {1'sb0}});
					end
				end
				if ((((i_timeout_detected[gi] && cam_entry_valid[gi]) && (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h3)) && (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h4)) && (cam_entry_payload[(((N - 1) - gi) * 285) + 277-:3] != 3'h5)) begin
					next[277-:3] = 3'h4;
					if (!cam_entry_payload[(((N - 1) - gi) * 285) + 283])
						next[7-:8] = monitor_amba4_pkg_EVT_CMD_TIMEOUT;
					else if (cam_entry_payload[(((N - 1) - gi) * 285) + 281] && !cam_entry_payload[(((N - 1) - gi) * 285) + 280])
						next[7-:8] = monitor_amba4_pkg_EVT_RESP_TIMEOUT;
					else
						next[7-:8] = monitor_amba4_pkg_EVT_DATA_TIMEOUT;
					next_we = 1'b1;
				end
				if (cam_entry_valid[gi] && w_can_cleanup[gi]) begin
					next[284] = 1'b0;
					next_we = 1'b1;
				end
				if ((((i_event_reported_flags[gi] && !r_rpt_stale_mask[gi]) && cam_entry_valid[gi]) && !w_can_cleanup[gi]) && !cam_entry_payload[(((N - 1) - gi) * 285) + 279]) begin
					next[279] = 1'b1;
					next_we = 1'b1;
				end
			end
			assign cam_entry_we[gi] = next_we;
			assign cam_entry_valid_next[gi] = next[284];
			assign cam_entry_id_next[gi] = next_id;
			assign cam_entry_payload_next[gi] = next;
		end
	endgenerate
	assign trans_table = cam_entry_payload;
	reg [7:0] r_active_count;
	reg [$clog2(N + 1) - 1:0] w_occupancy;
	always @(*) begin
		if (_sv2v_0)
			;
		w_occupancy = 1'sb0;
		begin : sv2v_autoblock_30
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_occupancy = w_occupancy + {{$clog2(N + 1) - 1 {1'b0}}, cam_entry_valid[i]};
		end
	end
	always @(posedge aclk)
		if (!aresetn)
			r_active_count <= 1'sb0;
		else if (clear)
			r_active_count <= 1'sb0;
		else
			r_active_count <= {{8 - $clog2(N + 1) {1'b0}}, w_occupancy};
	assign active_count = r_active_count;
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_timeout (
	aclk,
	aresetn,
	trans_table,
	timer_tick,
	cfg_addr_cnt,
	cfg_data_cnt,
	cfg_resp_cnt,
	cfg_timeout_enable,
	timeout_detected
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter [0:0] IS_READ = 1;
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire timer_tick;
	input wire [15:0] cfg_addr_cnt;
	input wire [15:0] cfg_data_cnt;
	input wire [15:0] cfg_resp_cnt;
	input wire cfg_timeout_enable;
	output wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	localparam signed [31:0] TIMER_W = 16;
	reg [15:0] r_addr_timer [0:MAX_TRANSACTIONS - 1];
	reg [15:0] r_data_timer [0:MAX_TRANSACTIONS - 1];
	reg [15:0] r_resp_timer [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] r_timeout_detected;
	assign timeout_detected = (cfg_timeout_enable ? r_timeout_detected : {MAX_TRANSACTIONS {1'b0}});
	reg [MAX_TRANSACTIONS - 1:0] w_addr_pending;
	reg [MAX_TRANSACTIONS - 1:0] w_data_pending;
	reg [MAX_TRANSACTIONS - 1:0] w_resp_pending;
	reg [MAX_TRANSACTIONS - 1:0] w_slot_retired;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				begin
					w_addr_pending[idx] = (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h1)) && !trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 283];
					w_data_pending[idx] = ((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && ((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h1) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h2))) && trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 283]) && !trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 281];
					w_resp_pending[idx] = (((!IS_READ && trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284]) && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h2)) && trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 281]) && !trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 280];
					w_slot_retired[idx] = (!trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h0);
				end
		end
	end
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_2
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						r_addr_timer[idx] <= 1'sb0;
						r_data_timer[idx] <= 1'sb0;
						r_resp_timer[idx] <= 1'sb0;
					end
			end
			r_timeout_detected <= 1'sb0;
		end
		else if (!cfg_timeout_enable) begin
			r_timeout_detected <= 1'sb0;
			begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						r_addr_timer[idx] <= 1'sb0;
						r_data_timer[idx] <= 1'sb0;
						r_resp_timer[idx] <= 1'sb0;
					end
			end
		end
		else begin : sv2v_autoblock_4
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				begin
					if (w_slot_retired[idx])
						r_timeout_detected[idx] <= 1'b0;
					if (!w_addr_pending[idx])
						r_addr_timer[idx] <= 1'sb0;
					if (!w_data_pending[idx])
						r_data_timer[idx] <= 1'sb0;
					if (!w_resp_pending[idx])
						r_resp_timer[idx] <= 1'sb0;
					if ((cfg_timeout_enable && timer_tick) && !r_timeout_detected[idx]) begin
						if (w_addr_pending[idx]) begin
							if (r_addr_timer[idx] >= cfg_addr_cnt)
								r_timeout_detected[idx] <= 1'b1;
							else
								r_addr_timer[idx] <= r_addr_timer[idx] + 1'b1;
						end
						if (w_data_pending[idx]) begin
							if (r_data_timer[idx] >= cfg_data_cnt)
								r_timeout_detected[idx] <= 1'b1;
							else
								r_data_timer[idx] <= r_data_timer[idx] + 1'b1;
						end
						if (w_resp_pending[idx]) begin
							if (r_resp_timer[idx] >= cfg_resp_cnt)
								r_timeout_detected[idx] <= 1'b1;
							else
								r_resp_timer[idx] <= r_resp_timer[idx] + 1'b1;
						end
					end
				end
		end
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_reporter (
	aclk,
	aresetn,
	trans_table,
	timeout_detected,
	filtered_mask,
	cfg_error_enable,
	cfg_compl_enable,
	cfg_threshold_enable,
	cfg_timeout_enable,
	cfg_perf_enable,
	cfg_debug_enable,
	monbus_ready,
	monbus_valid,
	monbus_packet,
	event_count,
	perf_completed_count,
	perf_error_count,
	active_trans_threshold,
	latency_threshold,
	event_reported_flags
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter [7:0] UNIT_ID = 8'h09;
	parameter [15:0] AGENT_ID = 16'h0063;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter signed [31:0] INTR_FIFO_DEPTH = 8;
	parameter [0:0] ENABLE_ERROR_LOGIC = 1'b1;
	parameter [0:0] ENABLE_TIMEOUT_LOGIC = 1'b1;
	parameter [0:0] ENABLE_COMPL_LOGIC = 1'b1;
	parameter [0:0] ENABLE_THRESHOLD_LOGIC = 1'b1;
	parameter [0:0] ENABLE_PERF_LOGIC = ENABLE_PERF_PACKETS;
	parameter [0:0] ENABLE_DEBUG_LOGIC = 1'b0;
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	input wire [MAX_TRANSACTIONS - 1:0] filtered_mask;
	input wire cfg_error_enable;
	input wire cfg_compl_enable;
	input wire cfg_threshold_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire cfg_debug_enable;
	input wire monbus_ready;
	output reg monbus_valid;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output reg [127:0] monbus_packet;
	output wire [15:0] event_count;
	output wire [15:0] perf_completed_count;
	output wire [15:0] perf_error_count;
	input wire [15:0] active_trans_threshold;
	input wire [31:0] latency_threshold;
	output wire [MAX_TRANSACTIONS - 1:0] event_reported_flags;
	localparam signed [31:0] IDX_W = $clog2(MAX_TRANSACTIONS);
	reg [(MAX_TRANSACTIONS * 285) - 1:0] r_trans_table_local;
	reg [MAX_TRANSACTIONS - 1:0] r_event_reported;
	reg [15:0] r_event_count;
	assign event_reported_flags = r_event_reported;
	assign event_count = r_event_count;
	wire unused_cfg_debug_enable;
	assign unused_cfg_debug_enable = cfg_debug_enable;
	reg w_fifo_wr_valid;
	wire w_fifo_wr_ready;
	reg [84:0] w_fifo_wr_data;
	wire w_fifo_rd_valid;
	wire w_fifo_rd_ready;
	wire [84:0] w_fifo_rd_data;
	wire [$clog2(INTR_FIFO_DEPTH):0] w_fifo_count;
	gaxi_fifo_sync #(
		.REGISTERED(1),
		.DATA_WIDTH(85),
		.DEPTH(INTR_FIFO_DEPTH),
		.ALMOST_WR_MARGIN(1),
		.ALMOST_RD_MARGIN(1)
	) intr_fifo(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(w_fifo_wr_valid),
		.wr_ready(w_fifo_wr_ready),
		.wr_data(w_fifo_wr_data),
		.rd_ready(w_fifo_rd_ready),
		.count(w_fifo_count),
		.rd_valid(w_fifo_rd_valid),
		.rd_data(w_fifo_rd_data)
	);
	wire err_valid;
	wire to_valid;
	wire compl_valid;
	wire err_valid_f;
	wire to_valid_f;
	wire compl_valid_f;
	wire [3:0] err_type;
	wire [3:0] to_type;
	wire [3:0] compl_type;
	wire [7:0] err_code;
	wire [7:0] to_code;
	wire [7:0] compl_code;
	wire [8:0] err_chan;
	wire [8:0] to_chan;
	wire [8:0] compl_chan;
	wire [63:0] err_data;
	wire [63:0] to_data;
	wire [63:0] compl_data;
	wire [IDX_W - 1:0] err_idx;
	wire [IDX_W - 1:0] to_idx;
	wire [IDX_W - 1:0] compl_idx;
	generate
		if (ENABLE_ERROR_LOGIC) begin : g_err
			axi_monitor_reporter_error #(
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.IDX_W(IDX_W)
			) u_err(
				.trans_table(r_trans_table_local),
				.event_reported(r_event_reported),
				.timeout_detected(timeout_detected),
				.cfg_error_enable(cfg_error_enable),
				.pkt_valid(err_valid),
				.pkt_type(err_type),
				.pkt_event_code(err_code),
				.pkt_channel(err_chan),
				.pkt_data(err_data),
				.sel_idx(err_idx)
			);
		end
		else begin : g_no_err
			assign err_valid = 1'b0;
			assign err_type = 1'sb0;
			assign err_code = 1'sb0;
			assign err_chan = 1'sb0;
			assign err_data = 1'sb0;
			assign err_idx = 1'sb0;
		end
		if (ENABLE_TIMEOUT_LOGIC) begin : g_to
			axi_monitor_reporter_timeout #(
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.IDX_W(IDX_W)
			) u_to(
				.trans_table(r_trans_table_local),
				.event_reported(r_event_reported),
				.timeout_detected(timeout_detected),
				.cfg_timeout_enable(cfg_timeout_enable),
				.pkt_valid(to_valid),
				.pkt_type(to_type),
				.pkt_event_code(to_code),
				.pkt_channel(to_chan),
				.pkt_data(to_data),
				.sel_idx(to_idx)
			);
		end
		else begin : g_no_to
			assign to_valid = 1'b0;
			assign to_type = 1'sb0;
			assign to_code = 1'sb0;
			assign to_chan = 1'sb0;
			assign to_data = 1'sb0;
			assign to_idx = 1'sb0;
		end
		if (ENABLE_COMPL_LOGIC) begin : g_compl
			axi_monitor_reporter_compl #(
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.IDX_W(IDX_W)
			) u_compl(
				.trans_table(r_trans_table_local),
				.event_reported(r_event_reported),
				.cfg_compl_enable(cfg_compl_enable),
				.pkt_valid(compl_valid),
				.pkt_type(compl_type),
				.pkt_event_code(compl_code),
				.pkt_channel(compl_chan),
				.pkt_data(compl_data),
				.sel_idx(compl_idx)
			);
		end
		else begin : g_no_compl
			assign compl_valid = 1'b0;
			assign compl_type = 1'sb0;
			assign compl_code = 1'sb0;
			assign compl_chan = 1'sb0;
			assign compl_data = 1'sb0;
			assign compl_idx = 1'sb0;
		end
	endgenerate
	assign err_valid_f = err_valid && !filtered_mask[err_idx];
	assign to_valid_f = to_valid && !filtered_mask[to_idx];
	assign compl_valid_f = compl_valid && !filtered_mask[compl_idx];
	always @(*) begin
		if (_sv2v_0)
			;
		w_fifo_wr_valid = 1'b0;
		w_fifo_wr_data = 85'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
		if (err_valid_f) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = err_type;
			w_fifo_wr_data[80-:8] = err_code;
			w_fifo_wr_data[72-:9] = err_chan;
			w_fifo_wr_data[63-:64] = err_data;
		end
		else if (to_valid_f) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = to_type;
			w_fifo_wr_data[80-:8] = to_code;
			w_fifo_wr_data[72-:9] = to_chan;
			w_fifo_wr_data[63-:64] = to_data;
		end
		else if (compl_valid_f) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = compl_type;
			w_fifo_wr_data[80-:8] = compl_code;
			w_fifo_wr_data[72-:9] = compl_chan;
			w_fifo_wr_data[63-:64] = compl_data;
		end
	end
	assign w_fifo_rd_ready = !monbus_valid;
	reg [MAX_TRANSACTIONS - 1:0] w_events_to_mark;
	reg [MAX_TRANSACTIONS - 1:0] w_error_events;
	reg [MAX_TRANSACTIONS - 1:0] w_completion_events;
	wire w_fifo_wr_accept;
	reg [IDX_W - 1:0] w_mark_idx;
	reg w_mark_is_error;
	reg w_mark_is_compl;
	assign w_fifo_wr_accept = w_fifo_wr_valid && w_fifo_wr_ready;
	always @(*) begin
		if (_sv2v_0)
			;
		w_events_to_mark = 1'sb0;
		w_error_events = 1'sb0;
		w_completion_events = 1'sb0;
		w_mark_idx = 1'sb0;
		w_mark_is_error = 1'b0;
		w_mark_is_compl = 1'b0;
		if (err_valid_f) begin
			w_mark_idx = err_idx;
			w_mark_is_error = 1'b1;
		end
		else if (to_valid_f) begin
			w_mark_idx = to_idx;
			w_mark_is_error = 1'b1;
		end
		else if (compl_valid_f) begin
			w_mark_idx = compl_idx;
			w_mark_is_compl = 1'b1;
		end
		if (w_fifo_wr_accept) begin
			w_events_to_mark[w_mark_idx] = 1'b1;
			w_error_events[w_mark_idx] = w_mark_is_error;
			w_completion_events[w_mark_idx] = w_mark_is_compl;
		end
	end
	reg [MAX_TRANSACTIONS - 1:0] w_auto_retire;
	always @(*) begin
		if (_sv2v_0)
			;
		w_auto_retire = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && filtered_mask[idx])
					case (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3])
						3'h3, 3'h4, 3'h5: w_auto_retire[idx] = 1'b1;
						default:
							;
					endcase
				else if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284])
					case (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3])
						3'h3: w_auto_retire[idx] = !ENABLE_COMPL_LOGIC || !cfg_compl_enable;
						3'h4: w_auto_retire[idx] = (timeout_detected[idx] ? !ENABLE_TIMEOUT_LOGIC || !cfg_timeout_enable : !ENABLE_ERROR_LOGIC || !cfg_error_enable);
						3'h5: w_auto_retire[idx] = !ENABLE_ERROR_LOGIC || !cfg_error_enable;
						default:
							;
					endcase
		end
	end
	wire thresh_valid;
	wire thresh_taken;
	wire [3:0] thresh_type;
	wire [7:0] thresh_code;
	wire [8:0] thresh_chan;
	wire [63:0] thresh_data;
	wire w_output_busy;
	assign w_output_busy = monbus_valid || w_fifo_rd_valid;
	generate
		if (ENABLE_THRESHOLD_LOGIC) begin : g_thresh
			axi_monitor_reporter_threshold #(
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.IS_READ(IS_READ),
				.IDX_W(IDX_W)
			) u_thresh(
				.aclk(aclk),
				.aresetn(aresetn),
				.trans_table(r_trans_table_local),
				.cfg_threshold_enable(cfg_threshold_enable),
				.active_trans_threshold(active_trans_threshold),
				.latency_threshold(latency_threshold),
				.output_busy(w_output_busy),
				.pkt_taken(thresh_taken),
				.pkt_valid(thresh_valid),
				.pkt_type(thresh_type),
				.pkt_event_code(thresh_code),
				.pkt_channel(thresh_chan),
				.pkt_data(thresh_data)
			);
		end
		else begin : g_no_thresh
			assign thresh_valid = 1'b0;
			assign thresh_type = 1'sb0;
			assign thresh_code = 1'sb0;
			assign thresh_chan = 1'sb0;
			assign thresh_data = 1'sb0;
		end
	endgenerate
	wire perf_valid;
	wire perf_taken;
	wire [3:0] perf_type;
	wire [7:0] perf_code;
	wire [8:0] perf_chan;
	wire [63:0] perf_data;
	wire [15:0] perf_completed_count_w;
	wire [15:0] perf_error_count_w;
	generate
		if (ENABLE_PERF_LOGIC) begin : g_perf
			axi_monitor_reporter_perf #(.MAX_TRANSACTIONS(MAX_TRANSACTIONS)) u_perf(
				.aclk(aclk),
				.aresetn(aresetn),
				.cfg_perf_enable(cfg_perf_enable),
				.output_busy(w_output_busy),
				.pkt_taken(perf_taken),
				.error_marked_mask(w_error_events),
				.compl_marked_mask(w_completion_events),
				.pkt_valid(perf_valid),
				.pkt_type(perf_type),
				.pkt_event_code(perf_code),
				.pkt_channel(perf_chan),
				.pkt_data(perf_data),
				.perf_completed_count(perf_completed_count_w),
				.perf_error_count(perf_error_count_w)
			);
		end
		else begin : g_no_perf
			assign perf_valid = 1'b0;
			assign perf_type = 1'sb0;
			assign perf_code = 1'sb0;
			assign perf_chan = 1'sb0;
			assign perf_data = 1'sb0;
			assign perf_completed_count_w = 1'sb0;
			assign perf_error_count_w = 1'sb0;
		end
	endgenerate
	assign perf_completed_count = perf_completed_count_w;
	assign perf_error_count = perf_error_count_w;
	wire debug_valid;
	wire debug_taken;
	wire [3:0] debug_type;
	wire [7:0] debug_code;
	wire [8:0] debug_chan;
	wire [63:0] debug_data;
	generate
		if (ENABLE_DEBUG_LOGIC) begin : g_debug
			axi_monitor_reporter_debug #(
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.IDX_W(IDX_W)
			) u_debug(
				.aclk(aclk),
				.aresetn(aresetn),
				.trans_table(r_trans_table_local),
				.cfg_debug_enable(cfg_debug_enable),
				.output_busy(w_output_busy),
				.pkt_taken(debug_taken),
				.pkt_valid(debug_valid),
				.pkt_type(debug_type),
				.pkt_event_code(debug_code),
				.pkt_channel(debug_chan),
				.pkt_data(debug_data)
			);
		end
		else begin : g_no_debug
			assign debug_valid = 1'b0;
			assign debug_type = 1'sb0;
			assign debug_code = 1'sb0;
			assign debug_chan = 1'sb0;
			assign debug_data = 1'sb0;
		end
	endgenerate
	reg [3:0] r_packet_type;
	reg [7:0] r_event_code;
	reg [63:0] r_event_data;
	reg [8:0] r_event_channel;
	localparam [7:0] monitor_amba4_pkg_EVT_NONE = 8'h00;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_2
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table_local[((MAX_TRANSACTIONS - 1) - idx) * 285+:285] <= 1'sb0;
			end
			monbus_valid <= 1'b0;
			r_event_count <= 1'sb0;
			r_event_reported <= 1'sb0;
			r_packet_type <= monitor_common_pkg_PktTypeError;
			r_event_code <= monitor_amba4_pkg_EVT_NONE;
			r_event_data <= 1'sb0;
			r_event_channel <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table_local[((MAX_TRANSACTIONS - 1) - idx) * 285+:285] <= trans_table[((MAX_TRANSACTIONS - 1) - idx) * 285+:285];
			end
			if (monbus_valid && monbus_ready)
				monbus_valid <= 1'b0;
			begin : sv2v_autoblock_4
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (!r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284])
						r_event_reported[idx] <= 1'b0;
					else if (w_events_to_mark[idx] || w_auto_retire[idx])
						r_event_reported[idx] <= 1'b1;
			end
			r_event_count <= (r_event_count + sv2v_cast_16(w_fifo_wr_accept)) + sv2v_cast_16(thresh_taken);
			if (!monbus_valid && w_fifo_rd_valid) begin
				monbus_valid <= 1'b1;
				r_packet_type <= w_fifo_rd_data[84-:4];
				r_event_code <= w_fifo_rd_data[80-:8];
				r_event_data <= w_fifo_rd_data[63-:64];
				r_event_channel <= w_fifo_rd_data[72-:9];
			end
			else if ((thresh_valid && !monbus_valid) && !w_fifo_rd_valid) begin
				monbus_valid <= 1'b1;
				r_packet_type <= thresh_type;
				r_event_code <= thresh_code;
				r_event_data <= thresh_data;
				r_event_channel <= thresh_chan;
			end
			else if ((perf_valid && !monbus_valid) && !w_fifo_rd_valid) begin
				monbus_valid <= 1'b1;
				r_packet_type <= perf_type;
				r_event_code <= perf_code;
				r_event_data <= perf_data;
				r_event_channel <= perf_chan;
			end
			else if ((debug_valid && !monbus_valid) && !w_fifo_rd_valid) begin
				monbus_valid <= 1'b1;
				r_packet_type <= debug_type;
				r_event_code <= debug_code;
				r_event_data <= debug_data;
				r_event_channel <= debug_chan;
			end
		end
	assign thresh_taken = (thresh_valid && !monbus_valid) && !w_fifo_rd_valid;
	assign perf_taken = ((perf_valid && !monbus_valid) && !w_fifo_rd_valid) && !thresh_valid;
	assign debug_taken = (((debug_valid && !monbus_valid) && !w_fifo_rd_valid) && !thresh_valid) && !perf_valid;
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
	always @(*) begin
		if (_sv2v_0)
			;
		monbus_packet = monitor_common_pkg_create_monitor_packet(r_packet_type, 4'h0, r_event_code, r_event_channel, UNIT_ID, AGENT_ID, r_event_data);
	end
	wire unused_fifo_count;
	assign unused_fifo_count = |w_fifo_count;
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_base (
	aclk,
	aresetn,
	clear,
	cfg_id_filter_enable,
	cfg_id_match_base,
	cfg_id_match_count,
	cfg_addr_filter_enable,
	cfg_addr_filter_low,
	cfg_addr_filter_high,
	cmd_addr,
	cmd_id,
	cmd_len,
	cmd_size,
	cmd_burst,
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
	cfg_addr_cnt,
	cfg_data_cnt,
	cfg_resp_cnt,
	cfg_error_enable,
	cfg_compl_enable,
	cfg_threshold_enable,
	cfg_timeout_enable,
	cfg_perf_enable,
	cfg_debug_enable,
	cfg_debug_level,
	cfg_debug_mask,
	cfg_active_trans_threshold,
	cfg_latency_threshold,
	cfg_addr_check_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	cfg_start_event_sel,
	cfg_end_event_sel,
	cfg_start_trigger,
	cfg_end_trigger,
	cfg_window_force_close,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	block_ready,
	busy,
	active_count,
	window_active,
	window_cycles,
	perf_prod_cycles,
	perf_bp_cycles,
	perf_starv_cycles,
	perf_idle_cycles,
	perf_beat_count,
	perf_byte_count,
	perf_burst_count,
	perf_completed_count,
	perf_error_count
);
	reg _sv2v_0;
	parameter [7:0] UNIT_ID = 8'h09;
	parameter [15:0] AGENT_ID = 16'h0063;
	parameter [0:0] USE_WDATA_ORDER_Q = 1'b0;
	parameter signed [31:0] NUM_BANKS = 1;
	parameter [0:0] ID_FILTER_ENABLE = 1'b0;
	parameter signed [31:0] ID_MATCH_BASE = 0;
	parameter signed [31:0] ID_MATCH_COUNT = 0;
	parameter [0:0] ADDR_FILTER_ENABLE = 1'b0;
	parameter signed [31:0] CFI_MIN_FREQ_MHZ = 100;
	parameter signed [31:0] CFI_MAX_FREQ_MHZ = 100;
	parameter signed [31:0] CFI_NUM_FREQ_ENTRIES = 16;
	parameter signed [31:0] CFI_FREQ_STRATEGY = 0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] ADDR_BITS_IN_PKT = 38;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter [0:0] ENABLE_DEBUG_MODULE = 1'b0;
	parameter [0:0] ENABLE_ERROR_LOGIC = 1'b1;
	parameter [0:0] ENABLE_TIMEOUT_LOGIC = 1'b1;
	parameter [0:0] ENABLE_COMPL_LOGIC = 1'b1;
	parameter [0:0] ENABLE_THRESHOLD_LOGIC = 1'b1;
	parameter [0:0] ENABLE_PERF_LOGIC = ENABLE_PERF_PACKETS;
	parameter [0:0] ENABLE_DEBUG_LOGIC = 1'b0;
	parameter signed [31:0] INTR_FIFO_DEPTH = 8;
	parameter signed [31:0] DEBUG_FIFO_DEPTH = 8;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] ADDR_RANGE_IS_ERROR = 1'sb0;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	parameter signed [31:0] ADDR_BITS = (ADDR_BITS_IN_PKT > AW ? AW : ADDR_BITS_IN_PKT);
	input wire aclk;
	input wire aresetn;
	input wire clear;
	input wire cfg_id_filter_enable;
	input wire [ID_WIDTH - 1:0] cfg_id_match_base;
	input wire [ID_WIDTH:0] cfg_id_match_count;
	input wire cfg_addr_filter_enable;
	input wire [ADDR_WIDTH - 1:0] cfg_addr_filter_low;
	input wire [ADDR_WIDTH - 1:0] cfg_addr_filter_high;
	input wire [AW - 1:0] cmd_addr;
	input wire [IW - 1:0] cmd_id;
	input wire [7:0] cmd_len;
	input wire [2:0] cmd_size;
	input wire [1:0] cmd_burst;
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
	input wire [3:0] cfg_freq_sel;
	input wire [15:0] cfg_addr_cnt;
	input wire [15:0] cfg_data_cnt;
	input wire [15:0] cfg_resp_cnt;
	input wire cfg_error_enable;
	input wire cfg_compl_enable;
	input wire cfg_threshold_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire cfg_debug_enable;
	input wire [3:0] cfg_debug_level;
	input wire [15:0] cfg_debug_mask;
	input wire [15:0] cfg_active_trans_threshold;
	input wire [31:0] cfg_latency_threshold;
	input wire cfg_addr_check_enable;
	input wire [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] cfg_addr_range_enable;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_low;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_high;
	input wire [2:0] cfg_start_event_sel;
	input wire [2:0] cfg_end_event_sel;
	input wire cfg_start_trigger;
	input wire cfg_end_trigger;
	input wire cfg_window_force_close;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output reg monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output reg [127:0] monbus_packet;
	output reg [63:0] monbus_timestamp;
	output wire block_ready;
	output wire busy;
	output wire [7:0] active_count;
	output wire window_active;
	output wire [31:0] window_cycles;
	output wire [31:0] perf_prod_cycles;
	output wire [31:0] perf_bp_cycles;
	output wire [31:0] perf_starv_cycles;
	output wire [31:0] perf_idle_cycles;
	output wire [31:0] perf_beat_count;
	output wire [63:0] perf_byte_count;
	output wire [31:0] perf_burst_count;
	output wire [15:0] perf_completed_count;
	output wire [15:0] perf_error_count;
	wire [(MAX_TRANSACTIONS * 285) - 1:0] w_trans_table;
	wire [MAX_TRANSACTIONS - 1:0] w_event_reported_flags;
	wire [7:0] w_active_count;
	wire [15:0] w_event_count;
	wire [15:0] w_debug_count;
	wire w_timer_tick;
	wire [31:0] r_timestamp;
	wire [MAX_TRANSACTIONS - 1:0] w_filtered_mask;
	wire [MAX_TRANSACTIONS - 1:0] w_timeout_detected;
	wire w_reporter_monbus_valid;
	wire [127:0] w_reporter_monbus_packet;
	wire w_debug_monbus_valid;
	wire [127:0] w_debug_monbus_packet;
	reg r_addr_hold;
	wire w_addr_pkt_valid;
	wire [127:0] w_addr_pkt_data;
	wire [63:0] w_addr_pkt_timestamp;
	wire w_addr_pkt_ready;
	assign w_debug_monbus_valid = 1'b0;
	assign w_debug_monbus_packet = 1'sb0;
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	function automatic id_owned;
		input reg [IW - 1:0] id;
		if (cfg_id_filter_enable) begin
			if (cfg_id_match_count == 0)
				id_owned = 1'b1;
			else
				id_owned = (sv2v_cast_32_signed(id) >= sv2v_cast_32_signed(cfg_id_match_base)) && (sv2v_cast_32_signed(id) < (sv2v_cast_32_signed(cfg_id_match_base) + sv2v_cast_32_signed(cfg_id_match_count)));
		end
		else if (!ID_FILTER_ENABLE || (ID_MATCH_COUNT == 0))
			id_owned = 1'b1;
		else
			id_owned = (sv2v_cast_32_signed(id) >= ID_MATCH_BASE) && (sv2v_cast_32_signed(id) < (ID_MATCH_BASE + ID_MATCH_COUNT));
	endfunction
	wire w_cmd_valid_f;
	wire w_data_valid_f;
	wire w_resp_valid_f;
	assign w_cmd_valid_f = cmd_valid && id_owned(cmd_id);
	assign w_data_valid_f = data_valid && id_owned(data_id);
	assign w_resp_valid_f = resp_valid && id_owned(resp_id);
	axi_monitor_trans_mgr #(
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(ADDR_WIDTH),
		.ID_WIDTH(ID_WIDTH),
		.IS_READ(IS_READ),
		.IS_AXI(IS_AXI),
		.USE_WDATA_ORDER_Q(USE_WDATA_ORDER_Q),
		.NUM_BANKS(NUM_BANKS),
		.ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS),
		.ADDR_FILTER_ENABLE(ADDR_FILTER_ENABLE)
	) trans_mgr(
		.aclk(aclk),
		.aresetn(aresetn),
		.clear(clear),
		.cmd_valid(w_cmd_valid_f),
		.cmd_ready(cmd_ready),
		.cmd_id(cmd_id),
		.cmd_addr(cmd_addr),
		.cmd_len(cmd_len),
		.cmd_size(cmd_size),
		.cmd_burst(cmd_burst),
		.data_valid(w_data_valid_f),
		.data_ready(data_ready),
		.data_id(data_id),
		.data_last(data_last),
		.data_resp(data_resp),
		.resp_valid(w_resp_valid_f),
		.resp_ready(resp_ready),
		.resp_id(resp_id),
		.resp_code(resp_code),
		.timestamp(r_timestamp),
		.i_event_reported_flags(w_event_reported_flags),
		.i_timeout_detected(w_timeout_detected),
		.trans_table(w_trans_table),
		.active_count(w_active_count),
		.cfg_addr_filter_enable(cfg_addr_filter_enable),
		.cfg_addr_filter_low(cfg_addr_filter_low),
		.cfg_addr_filter_high(cfg_addr_filter_high),
		.filtered_mask(w_filtered_mask)
	);
	axi_monitor_timer #(
		.CFI_MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
		.CFI_MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
		.CFI_NUM_FREQ_ENTRIES(CFI_NUM_FREQ_ENTRIES),
		.CFI_FREQ_STRATEGY(CFI_FREQ_STRATEGY)
	) timer(
		.aclk(aclk),
		.aresetn(aresetn),
		.cfg_freq_sel(cfg_freq_sel),
		.timer_tick(w_timer_tick),
		.timestamp(r_timestamp)
	);
	generate
		if (ENABLE_TIMEOUT_LOGIC) begin : gen_timeout
			axi_monitor_timeout #(
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.ADDR_WIDTH(ADDR_WIDTH),
				.IS_READ(IS_READ)
			) timeout(
				.aclk(aclk),
				.aresetn(aresetn),
				.trans_table(w_trans_table),
				.timer_tick(w_timer_tick),
				.cfg_addr_cnt(cfg_addr_cnt),
				.cfg_data_cnt(cfg_data_cnt),
				.cfg_resp_cnt(cfg_resp_cnt),
				.cfg_timeout_enable(cfg_timeout_enable),
				.timeout_detected(w_timeout_detected)
			);
		end
		else begin : gen_no_timeout
			assign w_timeout_detected = 1'sb0;
		end
	endgenerate
	axi_monitor_reporter #(
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(ADDR_WIDTH),
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.IS_READ(IS_READ),
		.ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS),
		.INTR_FIFO_DEPTH(INTR_FIFO_DEPTH),
		.ENABLE_ERROR_LOGIC(ENABLE_ERROR_LOGIC),
		.ENABLE_TIMEOUT_LOGIC(ENABLE_TIMEOUT_LOGIC),
		.ENABLE_COMPL_LOGIC(ENABLE_COMPL_LOGIC),
		.ENABLE_THRESHOLD_LOGIC(ENABLE_THRESHOLD_LOGIC),
		.ENABLE_PERF_LOGIC(ENABLE_PERF_LOGIC),
		.ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC)
	) reporter(
		.aclk(aclk),
		.aresetn(aresetn),
		.trans_table(w_trans_table),
		.filtered_mask(w_filtered_mask),
		.timeout_detected(w_timeout_detected),
		.cfg_error_enable(cfg_error_enable),
		.cfg_compl_enable(cfg_compl_enable),
		.cfg_threshold_enable(cfg_threshold_enable),
		.cfg_timeout_enable(cfg_timeout_enable),
		.cfg_perf_enable(cfg_perf_enable),
		.cfg_debug_enable(cfg_debug_enable),
		.monbus_ready(monbus_ready && !r_addr_hold),
		.monbus_valid(w_reporter_monbus_valid),
		.monbus_packet(w_reporter_monbus_packet),
		.event_count(w_event_count),
		.perf_completed_count(perf_completed_count),
		.perf_error_count(perf_error_count),
		.active_trans_threshold(cfg_active_trans_threshold),
		.latency_threshold(cfg_latency_threshold),
		.event_reported_flags(w_event_reported_flags)
	);
	generate
		if (N_ADDR_RANGES > 0) begin : gen_addr_check
			axi_monitor_addr_check #(
				.N_ADDR_RANGES(N_ADDR_RANGES),
				.ADDR_WIDTH(ADDR_WIDTH),
				.ID_WIDTH((ID_WIDTH > 0 ? ID_WIDTH : 1)),
				.UNIT_ID(UNIT_ID),
				.AGENT_ID(AGENT_ID),
				.IS_READ(IS_READ),
				.ADDR_RANGE_IS_ERROR(ADDR_RANGE_IS_ERROR)
			) addr_check(
				.clk(aclk),
				.aresetn(aresetn),
				.i_mon_time(i_mon_time),
				.cmd_addr(cmd_addr),
				.cmd_id(cmd_id),
				.cmd_valid(w_cmd_valid_f),
				.cmd_ready(cmd_ready),
				.cfg_addr_check_enable(cfg_addr_check_enable),
				.cfg_debug_enable(cfg_debug_enable),
				.cfg_error_enable(cfg_error_enable),
				.cfg_addr_range_enable(cfg_addr_range_enable),
				.cfg_addr_range_low(cfg_addr_range_low),
				.cfg_addr_range_high(cfg_addr_range_high),
				.addr_pkt_valid(w_addr_pkt_valid),
				.addr_pkt_ready(w_addr_pkt_ready),
				.addr_pkt_data(w_addr_pkt_data),
				.addr_pkt_timestamp(w_addr_pkt_timestamp)
			);
		end
		else begin : gen_no_addr_check
			assign w_addr_pkt_valid = 1'b0;
			assign w_addr_pkt_data = 1'sb0;
			assign w_addr_pkt_timestamp = 1'sb0;
		end
	endgenerate
	always @(posedge aclk)
		if (!aresetn)
			r_addr_hold <= 1'b0;
		else if (!r_addr_hold)
			r_addr_hold <= ((w_addr_pkt_valid && !w_reporter_monbus_valid) && !w_debug_monbus_valid) && !monbus_ready;
		else if (monbus_ready)
			r_addr_hold <= 1'b0;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r_addr_hold) begin
			monbus_valid = w_addr_pkt_valid;
			monbus_packet = w_addr_pkt_data;
			monbus_timestamp = w_addr_pkt_timestamp;
		end
		else if (w_reporter_monbus_valid) begin
			monbus_valid = w_reporter_monbus_valid;
			monbus_packet = w_reporter_monbus_packet;
			monbus_timestamp = i_mon_time;
		end
		else if (w_debug_monbus_valid) begin
			monbus_valid = w_debug_monbus_valid;
			monbus_packet = w_debug_monbus_packet;
			monbus_timestamp = i_mon_time;
		end
		else if (w_addr_pkt_valid) begin
			monbus_valid = w_addr_pkt_valid;
			monbus_packet = w_addr_pkt_data;
			monbus_timestamp = w_addr_pkt_timestamp;
		end
		else begin
			monbus_valid = 1'b0;
			monbus_packet = 1'sb0;
			monbus_timestamp = 1'sb0;
		end
	end
	assign w_addr_pkt_ready = monbus_ready && (r_addr_hold || (!w_reporter_monbus_valid && !w_debug_monbus_valid));
	function automatic signed [31:0] monitor_common_pkg_cmd_entry_reserve;
		input reg signed [31:0] max_transactions;
		monitor_common_pkg_cmd_entry_reserve = (max_transactions >= 16 ? 4 : 0);
	endfunction
	localparam [31:0] CMD_ENTRY_RESERVE = $unsigned(monitor_common_pkg_cmd_entry_reserve(MAX_TRANSACTIONS));
	localparam [31:0] BLOCK_MARGIN = (CMD_ENTRY_RESERVE > 0 ? CMD_ENTRY_RESERVE - 1 : 3);
	assign block_ready = (MAX_TRANSACTIONS > BLOCK_MARGIN ? {24'h000000, w_active_count} < (MAX_TRANSACTIONS - BLOCK_MARGIN) : 1'b1);
	assign busy = w_active_count > 0;
	assign active_count = w_active_count;
	reg [1:0] r_win_state;
	reg [31:0] r_window_cycles;
	reg r_perf_enable_d1;
	wire w_perf_enable_rising;
	wire w_perf_enable_falling;
	wire w_cmd_handshake;
	wire w_data_handshake;
	wire w_resp_handshake;
	wire w_window_saturate;
	reg w_start_event;
	reg w_end_event;
	assign w_cmd_handshake = cmd_valid && cmd_ready;
	assign w_data_handshake = data_valid && data_ready;
	assign w_resp_handshake = resp_valid && resp_ready;
	assign w_window_saturate = r_window_cycles == 32'hfffffffe;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_perf_enable_d1 <= 1'b0;
		else
			r_perf_enable_d1 <= cfg_perf_enable;
	assign w_perf_enable_rising = cfg_perf_enable && !r_perf_enable_d1;
	assign w_perf_enable_falling = !cfg_perf_enable && r_perf_enable_d1;
	always @(*) begin
		if (_sv2v_0)
			;
		case (cfg_start_event_sel)
			3'b000: w_start_event = cfg_start_trigger;
			3'b001: w_start_event = w_cmd_handshake;
			3'b010: w_start_event = w_perf_enable_rising;
			3'b011: w_start_event = w_data_handshake;
			3'b100: w_start_event = cfg_start_trigger;
			default: w_start_event = 1'b0;
		endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		case (cfg_end_event_sel)
			3'b000: w_end_event = cfg_end_trigger;
			3'b001: w_end_event = (IS_READ ? w_data_handshake && data_last : w_resp_handshake);
			3'b010: w_end_event = w_perf_enable_falling;
			3'b011: w_end_event = w_window_saturate;
			3'b100: w_end_event = cfg_end_trigger;
			default: w_end_event = 1'b0;
		endcase
	end
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_win_state <= 2'b00;
			r_window_cycles <= 32'h00000000;
		end
		else
			(* full_case, parallel_case *)
			case (r_win_state)
				2'b00:
					if (w_start_event) begin
						r_win_state <= 2'b01;
						r_window_cycles <= 32'h00000001;
					end
				2'b01: begin
					if (!w_window_saturate)
						r_window_cycles <= r_window_cycles + 32'h00000001;
					if (w_end_event || cfg_window_force_close)
						r_win_state <= 2'b10;
				end
				2'b10: r_win_state <= 2'b00;
				default: r_win_state <= 2'b00;
			endcase
	assign window_active = r_win_state == 2'b01;
	assign window_cycles = r_window_cycles;
	reg [31:0] r_prod_cycles;
	reg [31:0] r_bp_cycles;
	reg [31:0] r_starv_cycles;
	reg [31:0] r_idle_cycles;
	reg [31:0] r_burst_count;
	reg [63:0] r_byte_count;
	reg [2:0] r_axsize_latched;
	wire w_window_starting;
	assign w_window_starting = (r_win_state == 2'b00) && w_start_event;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_axsize_latched <= 3'h0;
		else if (w_cmd_handshake)
			r_axsize_latched <= cmd_size;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_prod_cycles <= 32'h00000000;
			r_bp_cycles <= 32'h00000000;
			r_starv_cycles <= 32'h00000000;
			r_idle_cycles <= 32'h00000000;
			r_burst_count <= 32'h00000000;
			r_byte_count <= 64'h0000000000000000;
		end
		else if (w_window_starting) begin
			r_prod_cycles <= 32'h00000000;
			r_bp_cycles <= 32'h00000000;
			r_starv_cycles <= 32'h00000000;
			r_idle_cycles <= 32'h00000000;
			r_burst_count <= 32'h00000000;
			r_byte_count <= 64'h0000000000000000;
		end
		else if (r_win_state == 2'b01) begin
			if (data_valid && data_ready) begin
				if (r_prod_cycles != 32'hffffffff)
					r_prod_cycles <= r_prod_cycles + 32'h00000001;
				if (r_byte_count < (64'hffffffffffffffff - (64'h0000000000000001 << r_axsize_latched)))
					r_byte_count <= r_byte_count + (64'h0000000000000001 << r_axsize_latched);
				else
					r_byte_count <= 64'hffffffffffffffff;
			end
			else if (data_valid && !data_ready) begin
				if (r_bp_cycles != 32'hffffffff)
					r_bp_cycles <= r_bp_cycles + 32'h00000001;
			end
			else if (!data_valid && data_ready) begin
				if (r_starv_cycles != 32'hffffffff)
					r_starv_cycles <= r_starv_cycles + 32'h00000001;
			end
			else if (r_idle_cycles != 32'hffffffff)
				r_idle_cycles <= r_idle_cycles + 32'h00000001;
			if (w_cmd_handshake && (r_burst_count != 32'hffffffff))
				r_burst_count <= r_burst_count + 32'h00000001;
		end
	assign perf_prod_cycles = r_prod_cycles;
	assign perf_bp_cycles = r_bp_cycles;
	assign perf_starv_cycles = r_starv_cycles;
	assign perf_idle_cycles = r_idle_cycles;
	assign perf_beat_count = r_prod_cycles;
	assign perf_byte_count = r_byte_count;
	assign perf_burst_count = r_burst_count;
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_filtered (
	aclk,
	aresetn,
	clear,
	cmd_addr,
	cmd_id,
	cmd_len,
	cmd_size,
	cmd_burst,
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
	cfg_addr_cnt,
	cfg_data_cnt,
	cfg_resp_cnt,
	cfg_error_enable,
	cfg_compl_enable,
	cfg_threshold_enable,
	cfg_timeout_enable,
	cfg_perf_enable,
	cfg_debug_enable,
	cfg_debug_level,
	cfg_debug_mask,
	cfg_active_trans_threshold,
	cfg_latency_threshold,
	cfg_axi_pkt_mask,
	cfg_axi_err_select,
	cfg_axi_error_mask,
	cfg_axi_timeout_mask,
	cfg_axi_compl_mask,
	cfg_axi_thresh_mask,
	cfg_axi_perf_mask,
	cfg_axi_addr_mask,
	cfg_axi_debug_mask,
	cfg_addr_check_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	cfg_id_filter_enable,
	cfg_id_match_base,
	cfg_id_match_count,
	cfg_addr_filter_enable,
	cfg_addr_filter_low,
	cfg_addr_filter_high,
	cfg_start_event_sel,
	cfg_end_event_sel,
	cfg_start_trigger,
	cfg_end_trigger,
	cfg_window_force_close,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	block_ready,
	busy,
	active_count,
	window_active,
	window_cycles,
	perf_prod_cycles,
	perf_bp_cycles,
	perf_starv_cycles,
	perf_idle_cycles,
	perf_beat_count,
	perf_byte_count,
	perf_burst_count,
	perf_completed_count,
	perf_error_count,
	cfg_conflict_error
);
	reg _sv2v_0;
	parameter [7:0] UNIT_ID = 8'h01;
	parameter [15:0] AGENT_ID = 16'h000a;
	parameter signed [31:0] CFI_MIN_FREQ_MHZ = 100;
	parameter signed [31:0] CFI_MAX_FREQ_MHZ = 100;
	parameter signed [31:0] CFI_NUM_FREQ_ENTRIES = 16;
	parameter signed [31:0] CFI_FREQ_STRATEGY = 0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter [0:0] USE_WDATA_ORDER_Q = 1'b0;
	parameter signed [31:0] NUM_BANKS = 1;
	parameter [0:0] ID_FILTER_ENABLE = 1'b0;
	parameter [0:0] ADDR_FILTER_ENABLE = 1'b0;
	parameter signed [31:0] ID_MATCH_BASE = 0;
	parameter signed [31:0] ID_MATCH_COUNT = 0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b1;
	parameter [0:0] ENABLE_DEBUG_MODULE = 1'b0;
	parameter [0:0] ENABLE_ERROR_LOGIC = 1'b1;
	parameter [0:0] ENABLE_TIMEOUT_LOGIC = 1'b1;
	parameter [0:0] ENABLE_COMPL_LOGIC = 1'b1;
	parameter [0:0] ENABLE_THRESHOLD_LOGIC = 1'b1;
	parameter [0:0] ENABLE_PERF_LOGIC = ENABLE_PERF_PACKETS;
	parameter [0:0] ENABLE_DEBUG_LOGIC = 1'b0;
	parameter [0:0] ENABLE_FILTERING = 1;
	parameter [0:0] ADD_PIPELINE_STAGE = 0;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] ADDR_RANGE_IS_ERROR = 1'sb0;
	input wire aclk;
	input wire aresetn;
	input wire clear;
	input wire [ADDR_WIDTH - 1:0] cmd_addr;
	input wire [ID_WIDTH - 1:0] cmd_id;
	input wire [7:0] cmd_len;
	input wire [2:0] cmd_size;
	input wire [1:0] cmd_burst;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire [ID_WIDTH - 1:0] data_id;
	input wire data_last;
	input wire [1:0] data_resp;
	input wire data_valid;
	input wire data_ready;
	input wire [ID_WIDTH - 1:0] resp_id;
	input wire [1:0] resp_code;
	input wire resp_valid;
	input wire resp_ready;
	input wire [3:0] cfg_freq_sel;
	input wire [15:0] cfg_addr_cnt;
	input wire [15:0] cfg_data_cnt;
	input wire [15:0] cfg_resp_cnt;
	input wire cfg_error_enable;
	input wire cfg_compl_enable;
	input wire cfg_threshold_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire cfg_debug_enable;
	input wire [3:0] cfg_debug_level;
	input wire [15:0] cfg_debug_mask;
	input wire [15:0] cfg_active_trans_threshold;
	input wire [31:0] cfg_latency_threshold;
	input wire [15:0] cfg_axi_pkt_mask;
	input wire [15:0] cfg_axi_err_select;
	input wire [15:0] cfg_axi_error_mask;
	input wire [15:0] cfg_axi_timeout_mask;
	input wire [15:0] cfg_axi_compl_mask;
	input wire [15:0] cfg_axi_thresh_mask;
	input wire [15:0] cfg_axi_perf_mask;
	input wire [15:0] cfg_axi_addr_mask;
	input wire [15:0] cfg_axi_debug_mask;
	input wire cfg_addr_check_enable;
	input wire [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] cfg_addr_range_enable;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * ADDR_WIDTH) - 1:0] cfg_addr_range_low;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * ADDR_WIDTH) - 1:0] cfg_addr_range_high;
	input wire cfg_id_filter_enable;
	input wire [ID_WIDTH - 1:0] cfg_id_match_base;
	input wire [ID_WIDTH:0] cfg_id_match_count;
	input wire cfg_addr_filter_enable;
	input wire [ADDR_WIDTH - 1:0] cfg_addr_filter_low;
	input wire [ADDR_WIDTH - 1:0] cfg_addr_filter_high;
	input wire [2:0] cfg_start_event_sel;
	input wire [2:0] cfg_end_event_sel;
	input wire cfg_start_trigger;
	input wire cfg_end_trigger;
	input wire cfg_window_force_close;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire block_ready;
	output wire busy;
	output wire [7:0] active_count;
	output wire window_active;
	output wire [31:0] window_cycles;
	output wire [31:0] perf_prod_cycles;
	output wire [31:0] perf_bp_cycles;
	output wire [31:0] perf_starv_cycles;
	output wire [31:0] perf_idle_cycles;
	output wire [31:0] perf_beat_count;
	output wire [63:0] perf_byte_count;
	output wire [31:0] perf_burst_count;
	output wire [15:0] perf_completed_count;
	output wire [15:0] perf_error_count;
	output wire cfg_conflict_error;
	wire base_monbus_valid;
	wire base_monbus_ready;
	wire [127:0] base_monbus_packet;
	wire [63:0] base_monbus_timestamp;
	wire [3:0] pkt_type;
	wire [3:0] pkt_protocol;
	wire [7:0] pkt_event_code;
	wire [63:0] pkt_event_data;
	reg pkt_drop;
	reg pkt_event_masked;
	wire pipe_valid;
	wire pipe_ready;
	wire [127:0] pipe_packet;
	wire [63:0] pipe_timestamp;
	assign cfg_conflict_error = |(cfg_axi_pkt_mask & cfg_axi_err_select);
	axi_monitor_base #(
		.CFI_MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
		.CFI_MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
		.CFI_NUM_FREQ_ENTRIES(CFI_NUM_FREQ_ENTRIES),
		.CFI_FREQ_STRATEGY(CFI_FREQ_STRATEGY),
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.USE_WDATA_ORDER_Q(USE_WDATA_ORDER_Q),
		.NUM_BANKS(NUM_BANKS),
		.ID_FILTER_ENABLE(ID_FILTER_ENABLE),
		.ADDR_FILTER_ENABLE(ADDR_FILTER_ENABLE),
		.ID_MATCH_BASE(ID_MATCH_BASE),
		.ID_MATCH_COUNT(ID_MATCH_COUNT),
		.ADDR_WIDTH(ADDR_WIDTH),
		.ID_WIDTH(ID_WIDTH),
		.IS_READ(IS_READ),
		.IS_AXI(IS_AXI),
		.ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS),
		.ENABLE_DEBUG_MODULE(ENABLE_DEBUG_MODULE),
		.ENABLE_ERROR_LOGIC(ENABLE_ERROR_LOGIC),
		.ENABLE_TIMEOUT_LOGIC(ENABLE_TIMEOUT_LOGIC),
		.ENABLE_COMPL_LOGIC(ENABLE_COMPL_LOGIC),
		.ENABLE_THRESHOLD_LOGIC(ENABLE_THRESHOLD_LOGIC),
		.ENABLE_PERF_LOGIC(ENABLE_PERF_LOGIC),
		.ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
		.N_ADDR_RANGES(N_ADDR_RANGES),
		.ADDR_RANGE_IS_ERROR(ADDR_RANGE_IS_ERROR)
	) u_axi_monitor_base(
		.aclk(aclk),
		.aresetn(aresetn),
		.clear(clear),
		.i_mon_time(i_mon_time),
		.cmd_addr(cmd_addr),
		.cmd_id(cmd_id),
		.cmd_len(cmd_len),
		.cmd_size(cmd_size),
		.cmd_burst(cmd_burst),
		.cmd_valid(cmd_valid),
		.cmd_ready(cmd_ready),
		.data_id(data_id),
		.data_last(data_last),
		.data_resp(data_resp),
		.data_valid(data_valid),
		.data_ready(data_ready),
		.resp_id(resp_id),
		.resp_code(resp_code),
		.resp_valid(resp_valid),
		.resp_ready(resp_ready),
		.cfg_freq_sel(cfg_freq_sel),
		.cfg_addr_cnt(cfg_addr_cnt),
		.cfg_data_cnt(cfg_data_cnt),
		.cfg_resp_cnt(cfg_resp_cnt),
		.cfg_error_enable(cfg_error_enable),
		.cfg_compl_enable(cfg_compl_enable),
		.cfg_threshold_enable(cfg_threshold_enable),
		.cfg_timeout_enable(cfg_timeout_enable),
		.cfg_perf_enable(cfg_perf_enable),
		.cfg_debug_enable(cfg_debug_enable),
		.cfg_debug_level(cfg_debug_level),
		.cfg_debug_mask(cfg_debug_mask),
		.cfg_active_trans_threshold(cfg_active_trans_threshold),
		.cfg_latency_threshold(cfg_latency_threshold),
		.cfg_addr_check_enable(cfg_addr_check_enable),
		.cfg_addr_range_enable(cfg_addr_range_enable),
		.cfg_addr_range_low(cfg_addr_range_low),
		.cfg_addr_range_high(cfg_addr_range_high),
		.cfg_id_filter_enable(cfg_id_filter_enable),
		.cfg_id_match_base(cfg_id_match_base),
		.cfg_id_match_count(cfg_id_match_count),
		.cfg_addr_filter_enable(cfg_addr_filter_enable),
		.cfg_addr_filter_low(cfg_addr_filter_low),
		.cfg_addr_filter_high(cfg_addr_filter_high),
		.cfg_start_event_sel(cfg_start_event_sel),
		.cfg_end_event_sel(cfg_end_event_sel),
		.cfg_start_trigger(cfg_start_trigger),
		.cfg_end_trigger(cfg_end_trigger),
		.cfg_window_force_close(cfg_window_force_close),
		.monbus_valid(base_monbus_valid),
		.monbus_ready(base_monbus_ready),
		.monbus_packet(base_monbus_packet),
		.monbus_timestamp(base_monbus_timestamp),
		.block_ready(block_ready),
		.busy(busy),
		.active_count(active_count),
		.window_active(window_active),
		.window_cycles(window_cycles),
		.perf_prod_cycles(perf_prod_cycles),
		.perf_bp_cycles(perf_bp_cycles),
		.perf_starv_cycles(perf_starv_cycles),
		.perf_idle_cycles(perf_idle_cycles),
		.perf_beat_count(perf_beat_count),
		.perf_byte_count(perf_byte_count),
		.perf_burst_count(perf_burst_count),
		.perf_completed_count(perf_completed_count),
		.perf_error_count(perf_error_count)
	);
	function automatic [3:0] monitor_common_pkg_get_packet_type;
		input reg [127:0] pkt;
		monitor_common_pkg_get_packet_type = pkt[127:124];
	endfunction
	assign pkt_type = monitor_common_pkg_get_packet_type(base_monbus_packet);
	assign pkt_protocol = base_monbus_packet[108:105];
	function automatic [7:0] monitor_common_pkg_get_event_code;
		input reg [127:0] pkt;
		monitor_common_pkg_get_event_code = pkt[104:97];
	endfunction
	assign pkt_event_code = monitor_common_pkg_get_event_code(base_monbus_packet);
	function automatic [63:0] monitor_common_pkg_get_event_data;
		input reg [127:0] pkt;
		monitor_common_pkg_get_event_data = pkt[63:0];
	endfunction
	assign pkt_event_data = monitor_common_pkg_get_event_data(base_monbus_packet);
	wire [3:0] ec_idx;
	assign ec_idx = pkt_event_code[3:0];
	localparam [3:0] monitor_common_pkg_PktTypeAddrMatch = 4'h8;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeDebug = 4'hf;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	always @(*) begin
		if (_sv2v_0)
			;
		pkt_drop = 1'b0;
		pkt_event_masked = 1'b0;
		if (ENABLE_FILTERING && base_monbus_valid) begin
			if (pkt_protocol == 4'h0) begin
				pkt_drop = cfg_axi_pkt_mask[pkt_type];
				if (!pkt_drop) begin
					case (pkt_type)
						monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_axi_error_mask[ec_idx];
						monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_axi_timeout_mask[ec_idx];
						monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask[ec_idx];
						monitor_common_pkg_PktTypeThreshold: pkt_event_masked = cfg_axi_thresh_mask[ec_idx];
						monitor_common_pkg_PktTypePerf: pkt_event_masked = cfg_axi_perf_mask[ec_idx];
						monitor_common_pkg_PktTypeAddrMatch: pkt_event_masked = cfg_axi_addr_mask[ec_idx];
						monitor_common_pkg_PktTypeDebug: pkt_event_masked = cfg_axi_debug_mask[ec_idx];
						default: pkt_event_masked = 1'b0;
					endcase
					if (pkt_event_masked)
						pkt_drop = 1'b1;
				end
			end
			else
				pkt_drop = 1'b1;
		end
	end
	assign base_monbus_ready = pkt_drop || (ADD_PIPELINE_STAGE ? pipe_ready : monbus_ready);
	generate
		if (ADD_PIPELINE_STAGE) begin : gen_pipeline
			reg pipe_valid_reg;
			reg [127:0] pipe_packet_reg;
			reg [63:0] pipe_timestamp_reg;
			always @(posedge aclk)
				if (!aresetn) begin
					pipe_valid_reg <= 1'b0;
					pipe_packet_reg <= 1'sb0;
					pipe_timestamp_reg <= 1'sb0;
				end
				else if (pipe_ready) begin
					pipe_valid_reg <= base_monbus_valid && !pkt_drop;
					pipe_packet_reg <= base_monbus_packet;
					pipe_timestamp_reg <= base_monbus_timestamp;
				end
			assign pipe_valid = pipe_valid_reg;
			assign pipe_packet = pipe_packet_reg;
			assign pipe_timestamp = pipe_timestamp_reg;
			assign pipe_ready = !pipe_valid || monbus_ready;
			assign monbus_valid = pipe_valid;
			assign monbus_packet = pipe_packet;
			assign monbus_timestamp = pipe_timestamp;
		end
		else begin : gen_no_pipeline
			assign monbus_valid = base_monbus_valid && !pkt_drop;
			assign monbus_packet = base_monbus_packet;
			assign monbus_timestamp = base_monbus_timestamp;
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module axi4_master_rd_mon (
	aclk,
	aresetn,
	cam_clear,
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
	cfg_monitor_enable,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_perf_enable,
	cfg_compl_enable,
	cfg_threshold_enable,
	cfg_debug_enable,
	cfg_timeout_cycles,
	cfg_freq_sel,
	cfg_latency_threshold,
	cfg_axi_pkt_mask,
	cfg_axi_err_select,
	cfg_axi_error_mask,
	cfg_axi_timeout_mask,
	cfg_axi_compl_mask,
	cfg_axi_thresh_mask,
	cfg_axi_perf_mask,
	cfg_axi_addr_mask,
	cfg_axi_debug_mask,
	cfg_addr_check_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	cfg_id_filter_enable,
	cfg_id_match_base,
	cfg_id_match_count,
	cfg_addr_filter_enable,
	cfg_addr_filter_low,
	cfg_addr_filter_high,
	cfg_start_event_sel,
	cfg_end_event_sel,
	cfg_start_trigger,
	cfg_end_trigger,
	cfg_window_force_close,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	busy,
	active_transactions,
	error_count,
	transaction_count,
	debug_block_ready,
	window_active,
	window_cycles,
	perf_prod_cycles,
	perf_bp_cycles,
	perf_starv_cycles,
	perf_idle_cycles,
	perf_beat_count,
	perf_byte_count,
	perf_burst_count,
	cfg_conflict_error
);
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] ACLK_MHZ = 100;
	parameter signed [31:0] CFI_MIN_FREQ_MHZ = ACLK_MHZ;
	parameter signed [31:0] CFI_MAX_FREQ_MHZ = ACLK_MHZ;
	parameter [0:0] USE_MONITOR = 1'b1;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] ADDR_RANGE_IS_ERROR = 1'sb0;
	parameter [7:0] UNIT_ID = 8'h01;
	parameter [15:0] AGENT_ID = 16'h000a;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter [0:0] USE_WDATA_ORDER_Q = 1'b0;
	parameter signed [31:0] NUM_BANKS = 1;
	parameter [0:0] ID_FILTER_ENABLE = 1'b0;
	parameter [0:0] ADDR_FILTER_ENABLE = 1'b0;
	parameter signed [31:0] ID_MATCH_BASE = 0;
	parameter signed [31:0] ID_MATCH_COUNT = 0;
	parameter signed [31:0] ACTIVE_TRANS_THRESHOLD = MAX_TRANSACTIONS / 2;
	parameter [0:0] ENABLE_FILTERING = 1;
	parameter [0:0] ADD_PIPELINE_STAGE = 0;
	parameter [0:0] ENABLE_ERROR_LOGIC = 1'b1;
	parameter [0:0] ENABLE_TIMEOUT_LOGIC = 1'b1;
	parameter [0:0] ENABLE_COMPL_LOGIC = 1'b1;
	parameter [0:0] ENABLE_THRESHOLD_LOGIC = 1'b1;
	parameter [0:0] ENABLE_PERF_LOGIC = 1'b1;
	parameter [0:0] ENABLE_DEBUG_LOGIC = 1'b0;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire cam_clear;
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
	input wire cfg_monitor_enable;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire cfg_compl_enable;
	input wire cfg_threshold_enable;
	input wire cfg_debug_enable;
	input wire [15:0] cfg_timeout_cycles;
	input wire [3:0] cfg_freq_sel;
	input wire [31:0] cfg_latency_threshold;
	input wire [15:0] cfg_axi_pkt_mask;
	input wire [15:0] cfg_axi_err_select;
	input wire [15:0] cfg_axi_error_mask;
	input wire [15:0] cfg_axi_timeout_mask;
	input wire [15:0] cfg_axi_compl_mask;
	input wire [15:0] cfg_axi_thresh_mask;
	input wire [15:0] cfg_axi_perf_mask;
	input wire [15:0] cfg_axi_addr_mask;
	input wire [15:0] cfg_axi_debug_mask;
	input wire cfg_addr_check_enable;
	input wire [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] cfg_addr_range_enable;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_low;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_high;
	input wire cfg_id_filter_enable;
	input wire [IW - 1:0] cfg_id_match_base;
	input wire [IW:0] cfg_id_match_count;
	input wire cfg_addr_filter_enable;
	input wire [AW - 1:0] cfg_addr_filter_low;
	input wire [AW - 1:0] cfg_addr_filter_high;
	input wire [2:0] cfg_start_event_sel;
	input wire [2:0] cfg_end_event_sel;
	input wire cfg_start_trigger;
	input wire cfg_end_trigger;
	input wire cfg_window_force_close;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire busy;
	output wire [7:0] active_transactions;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
	output wire debug_block_ready;
	output wire window_active;
	output wire [31:0] window_cycles;
	output wire [31:0] perf_prod_cycles;
	output wire [31:0] perf_bp_cycles;
	output wire [31:0] perf_starv_cycles;
	output wire [31:0] perf_idle_cycles;
	output wire [31:0] perf_beat_count;
	output wire [63:0] perf_byte_count;
	output wire [31:0] perf_burst_count;
	output wire cfg_conflict_error;
	wire w_core_fub_axi_arready;
	wire w_block_ready;
	wire w_gated_arvalid;
	assign w_gated_arvalid = fub_axi_arvalid & (w_block_ready | ~cfg_monitor_enable);
	assign debug_block_ready = w_block_ready;
	axi4_master_rd #(
		.SKID_DEPTH_AR(SKID_DEPTH_AR),
		.SKID_DEPTH_R(SKID_DEPTH_R),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH),
		.AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH)
	) axi4_master_rd_inst(
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
		.fub_axi_arvalid(w_gated_arvalid),
		.fub_axi_arready(w_core_fub_axi_arready),
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
		if (USE_MONITOR) begin : gen_monitor
			axi_monitor_filtered #(
				.CFI_MIN_FREQ_MHZ(CFI_MIN_FREQ_MHZ),
				.CFI_MAX_FREQ_MHZ(CFI_MAX_FREQ_MHZ),
				.UNIT_ID(UNIT_ID),
				.AGENT_ID(AGENT_ID),
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.USE_WDATA_ORDER_Q(USE_WDATA_ORDER_Q),
				.NUM_BANKS(NUM_BANKS),
				.ID_FILTER_ENABLE(ID_FILTER_ENABLE),
				.ADDR_FILTER_ENABLE(ADDR_FILTER_ENABLE),
				.ID_MATCH_BASE(ID_MATCH_BASE),
				.ID_MATCH_COUNT(ID_MATCH_COUNT),
				.ADDR_WIDTH(AW),
				.ID_WIDTH(IW),
				.IS_READ(1'b1),
				.IS_AXI(1'b1),
				.ENABLE_PERF_PACKETS(1'b1),
				.ENABLE_DEBUG_MODULE(1'b0),
				.ENABLE_ERROR_LOGIC(ENABLE_ERROR_LOGIC),
				.ENABLE_TIMEOUT_LOGIC(ENABLE_TIMEOUT_LOGIC),
				.ENABLE_COMPL_LOGIC(ENABLE_COMPL_LOGIC),
				.ENABLE_THRESHOLD_LOGIC(ENABLE_THRESHOLD_LOGIC),
				.ENABLE_PERF_LOGIC(ENABLE_PERF_LOGIC),
				.ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
				.ENABLE_FILTERING(ENABLE_FILTERING),
				.ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE),
				.N_ADDR_RANGES(N_ADDR_RANGES),
				.ADDR_RANGE_IS_ERROR(ADDR_RANGE_IS_ERROR)
			) axi_monitor_inst(
				.aclk(aclk),
				.aresetn(aresetn),
				.clear(cam_clear | ~cfg_monitor_enable),
				.i_mon_time(i_mon_time),
				.cmd_addr(m_axi_araddr),
				.cmd_id(m_axi_arid),
				.cmd_len(m_axi_arlen),
				.cmd_size(m_axi_arsize),
				.cmd_burst(m_axi_arburst),
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
				.cfg_addr_cnt(w_timeout_cnt),
				.cfg_data_cnt(w_timeout_cnt),
				.cfg_resp_cnt(w_timeout_cnt),
				.cfg_error_enable(cfg_error_enable),
				.cfg_compl_enable(cfg_compl_enable),
				.cfg_threshold_enable(cfg_threshold_enable),
				.cfg_timeout_enable(cfg_timeout_enable),
				.cfg_perf_enable(cfg_perf_enable),
				.cfg_debug_enable(cfg_debug_enable),
				.cfg_debug_level(4'h0),
				.cfg_debug_mask(16'h0000),
				.cfg_active_trans_threshold(sv2v_cast_16_signed(ACTIVE_TRANS_THRESHOLD)),
				.cfg_latency_threshold(cfg_latency_threshold),
				.cfg_axi_pkt_mask(cfg_axi_pkt_mask),
				.cfg_axi_err_select(cfg_axi_err_select),
				.cfg_axi_error_mask(cfg_axi_error_mask),
				.cfg_axi_timeout_mask(cfg_axi_timeout_mask),
				.cfg_axi_compl_mask(cfg_axi_compl_mask),
				.cfg_axi_thresh_mask(cfg_axi_thresh_mask),
				.cfg_axi_perf_mask(cfg_axi_perf_mask),
				.cfg_axi_addr_mask(cfg_axi_addr_mask),
				.cfg_axi_debug_mask(cfg_axi_debug_mask),
				.cfg_addr_check_enable(cfg_addr_check_enable),
				.cfg_addr_range_enable(cfg_addr_range_enable),
				.cfg_addr_range_low(cfg_addr_range_low),
				.cfg_addr_range_high(cfg_addr_range_high),
				.cfg_id_filter_enable(cfg_id_filter_enable),
				.cfg_id_match_base(cfg_id_match_base),
				.cfg_id_match_count(cfg_id_match_count),
				.cfg_addr_filter_enable(cfg_addr_filter_enable),
				.cfg_addr_filter_low(cfg_addr_filter_low),
				.cfg_addr_filter_high(cfg_addr_filter_high),
				.cfg_start_event_sel(cfg_start_event_sel),
				.cfg_end_event_sel(cfg_end_event_sel),
				.cfg_start_trigger(cfg_start_trigger),
				.cfg_end_trigger(cfg_end_trigger),
				.cfg_window_force_close(cfg_window_force_close),
				.monbus_valid(monbus_valid),
				.monbus_ready(monbus_ready),
				.monbus_packet(monbus_packet),
				.monbus_timestamp(monbus_timestamp),
				.block_ready(w_block_ready),
				.busy(),
				.window_active(window_active),
				.window_cycles(window_cycles),
				.perf_prod_cycles(perf_prod_cycles),
				.perf_bp_cycles(perf_bp_cycles),
				.perf_starv_cycles(perf_starv_cycles),
				.perf_idle_cycles(perf_idle_cycles),
				.perf_beat_count(perf_beat_count),
				.perf_byte_count(perf_byte_count),
				.perf_burst_count(perf_burst_count),
				.perf_completed_count(w_perf_completed_count),
				.perf_error_count(w_perf_error_count),
				.active_count(active_transactions),
				.cfg_conflict_error(cfg_conflict_error)
			);
		end
		else begin : gen_no_monitor
			assign monbus_valid = 1'b0;
			assign monbus_packet = 1'sb0;
			assign monbus_timestamp = 1'sb0;
			assign active_transactions = 8'h00;
			assign cfg_conflict_error = 1'b0;
			assign w_block_ready = 1'b1;
			assign w_perf_completed_count = 16'h0000;
			assign w_perf_error_count = 16'h0000;
			assign window_active = 1'b0;
			assign window_cycles = 32'h00000000;
			assign perf_prod_cycles = 32'h00000000;
			assign perf_bp_cycles = 32'h00000000;
			assign perf_starv_cycles = 32'h00000000;
			assign perf_idle_cycles = 32'h00000000;
			assign perf_beat_count = 32'h00000000;
			assign perf_byte_count = 64'h0000000000000000;
			assign perf_burst_count = 32'h00000000;
		end
	endgenerate
	assign fub_axi_arready = w_core_fub_axi_arready & (w_block_ready | ~cfg_monitor_enable);
	assign error_count = w_perf_error_count;
	assign transaction_count = {16'h0000, w_perf_completed_count};
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
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dmas/stream/rtl/fub/descriptor_engine.sv:153:13 - descriptor_engine.<unnamed_block>.<unnamed_block>\n msg: ", $time, "AXI_ID_WIDTH (%0d) must be >= CHAN_WIDTH (%0d)", AXI_ID_WIDTH, CHAN_WIDTH);
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
	always @(posedge clk)
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
	always @(posedge clk)
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
					if (ar_ready)
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
	assign ar_valid = ((r_current_state == 3'b001) || (r_current_state == 3'b101)) && !r_axi_read_active;
	function automatic signed [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5_signed;
		input reg signed [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5_signed = inp;
	endfunction
	assign ar_addr = (r_current_state == 3'b101 ? r_axi_read_addr + sv2v_cast_A5DC5_signed(32) : r_axi_read_addr);
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
	always @(posedge clk)
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
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dmas/stream/rtl/fub/scheduler.sv:175:13 - scheduler.<unnamed_block>.<unnamed_block>\n msg: ", $time, "scheduler (STREAM): DESC_WIDTH must be 256, got %0d. For RAPIDS, use rapids_scheduler.", DESC_WIDTH);
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
	always @(posedge clk)
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
	always @(posedge clk)
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
	always @(posedge clk)
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
	always @(posedge clk)
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
	always @(posedge clk)
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
	always @(posedge axi_aclk)
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
	always @(posedge axi_aclk)
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
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dmas/stream/rtl/fub/stream_drain_ctrl.sv:177:13 - stream_drain_ctrl.<unnamed_block>.<unnamed_block>\n msg: ", $time, "stream_drain_ctrl: over-drain -- rd_size=%0d exceeds data_available=%0d; rd_ptr will overshoot wr_ptr and permanently corrupt the occupancy count", rd_size, data_available);
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
	always @(posedge clk)
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
	stream_drain_ctrl #(
		.DEPTH(SD),
		.REGISTERED(1)
	) u_drain_ctrl(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(axi_rd_sram_valid && axi_rd_sram_ready),
		.wr_ready(),
		.rd_valid(axi_wr_drain_req),
		.rd_size(axi_wr_drain_size),
		.rd_ready(),
		.data_available(drain_data_available),
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
	always @(posedge clk)
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
	genvar _gv_i_3;
	generate
		for (_gv_i_3 = 0; _gv_i_3 < NC; _gv_i_3 = _gv_i_3 + 1) begin : gen_channel_units
			localparam i = _gv_i_3;
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
	always @(posedge clk)
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
module axi_read_engine (
	clk,
	rst_n,
	cfg_axi_rd_xfer_beats,
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
	parameter signed [31:0] PIPELINE = 0;
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
			always @(posedge clk)
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
						r_outstanding_limit[i] = r_outstanding_count[i * MOW+:MOW] >= sv2v_cast_04DDF_signed(AR_MAX_OUTSTANDING);
				end
			end
		end
	endgenerate
	reg [NC - 1:0] r_all_complete;
	reg [NC - 1:0] r_all_complete_prev;
	always @(posedge clk)
		if (!rst_n) begin
			r_all_complete <= 1'sb1;
			r_all_complete_prev <= 1'sb1;
		end
		else begin
			r_all_complete_prev <= r_all_complete;
			begin : sv2v_autoblock_5
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
		begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					w_transfer_size[i * 8+:8] = sv2v_cast_8((sched_rd_beats[i * 32+:32] <= (sv2v_cast_32(cfg_axi_rd_xfer_beats) + 32'd1) ? sched_rd_beats[i * 32+:32] - 32'd1 : sv2v_cast_32(cfg_axi_rd_xfer_beats)));
					w_space_ok[i] = sv2v_cast_14961(axi_rd_alloc_space_free[i * SCW+:SCW]) >= sv2v_cast_14961(w_transfer_size[i * 8+:8] + 8'd1);
					w_below_outstanding_limit[i] = !r_outstanding_limit[i];
					w_arb_request[i] = (sched_rd_valid[i] && w_space_ok[i]) && w_below_outstanding_limit[i];
				end
		end
	end
	reg [NC - 1:0] r_arb_request;
	always @(posedge clk)
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
	assign m_axi_arvalid = w_arb_grant_valid && sched_rd_valid[w_arb_grant_id];
	assign m_axi_arid = {{IW - CW {1'b0}}, w_arb_grant_id};
	assign m_axi_araddr = sched_rd_addr[w_arb_grant_id * AW+:AW];
	assign m_axi_arlen = w_transfer_size[w_arb_grant_id * 8+:8];
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign m_axi_arsize = sv2v_cast_3_signed(AXSIZE);
	assign m_axi_arburst = 2'b01;
	wire [NC - 1:0] w_stale_grant;
	assign w_stale_grant = w_arb_grant & ~sched_rd_valid;
	assign w_arb_grant_ack = (w_arb_grant & {NC {m_axi_arvalid && m_axi_arready}}) | w_stale_grant;
	reg r_alloc_req;
	reg [7:0] r_alloc_size;
	reg [IW - 1:0] r_alloc_id;
	always @(posedge clk)
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
	assign axi_rd_sram_valid = m_axi_rvalid;
	assign axi_rd_sram_id = m_axi_rid;
	assign axi_rd_sram_data = m_axi_rdata;
	assign m_axi_rready = axi_rd_sram_ready;
	reg [NC - 1:0] r_done_strobe;
	reg [(NC * 32) - 1:0] r_beats_done;
	always @(posedge clk)
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
		end
	assign sched_rd_done_strobe = r_done_strobe;
	assign sched_rd_beats_done = r_beats_done;
	reg [NC - 1:0] r_rd_error;
	always @(posedge clk)
		if (!rst_n)
			r_rd_error <= 1'sb0;
		else if ((m_axi_rvalid && m_axi_rready) && (m_axi_rresp != 2'b00)) begin : sv2v_autoblock_7
			reg [CW - 1:0] ch_id;
			ch_id = m_axi_rid[CW - 1:0];
			r_rd_error[ch_id] <= 1'b1;
		end
	assign sched_rd_error = r_rd_error;
	reg [31:0] r_r_beats_rcvd;
	reg [31:0] r_sram_writes;
	always @(posedge clk)
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
	sched_wr_commit_strobe,
	sched_wr_commit_beats,
	axi_wr_drain_req,
	axi_wr_drain_size,
	axi_wr_drain_data_avail,
	axi_wr_sram_valid,
	axi_wr_sram_valid_comb,
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
	dbg_w_beats,
	o_active_channel_id,
	o_active_channel_valid
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
	output wire [NC - 1:0] sched_wr_commit_strobe;
	output wire [(NC * 32) - 1:0] sched_wr_commit_beats;
	output wire [NC - 1:0] axi_wr_drain_req;
	output wire [(NC * 8) - 1:0] axi_wr_drain_size;
	input wire [(NC * SCW) - 1:0] axi_wr_drain_data_avail;
	input wire [NC - 1:0] axi_wr_sram_valid;
	input wire [NC - 1:0] axi_wr_sram_valid_comb;
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
	output wire [CIW - 1:0] o_active_channel_id;
	output wire o_active_channel_valid;
	localparam signed [31:0] BYTES_PER_BEAT = DW / 8;
	localparam signed [31:0] AXSIZE = $clog2(BYTES_PER_BEAT);
	localparam signed [31:0] MOW = $clog2(AW_MAX_OUTSTANDING + 1);
	reg [7:0] r_aw_len;
	reg [CIW - 1:0] r_aw_channel_id;
	reg r_aw_valid;
	reg [(NC * 32) - 1:0] r_beats_written;
	reg w_phase_txn_fifo_wr;
	wire w_phase_txn_fifo_rd;
	reg [(8 + CIW) - 1:0] w_phase_txn_fifo_din;
	wire [(8 + CIW) - 1:0] w_phase_txn_fifo_dout;
	wire w_phase_txn_fifo_empty;
	wire w_phase_txn_fifo_full;
	wire w_phase_txn_fifo_wr_ready;
	wire w_phase_txn_fifo_rd_valid;
	reg [NC - 1:0] b_phase_txn_fifo_wr;
	reg [NC - 1:0] b_phase_txn_fifo_rd;
	reg [(NC * 9) - 1:0] b_phase_txn_fifo_din;
	wire [(NC * 9) - 1:0] b_phase_txn_fifo_dout;
	wire [NC - 1:0] b_phase_txn_fifo_empty;
	wire [NC - 1:0] b_phase_txn_fifo_full;
	reg [NC - 1:0] r_outstanding_limit;
	reg [(NC * MOW) - 1:0] r_outstanding_count;
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
	reg [(NC * SCW) - 1:0] w_drain_t;
	reg [(NC * SCW) - 1:0] r_drain_tminus1;
	reg [(NC * SCW) - 1:0] w_pending_drain;
	reg [(NC * SCW) - 1:0] w_effective_avail;
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
		w_drain_t = {NC {sv2v_cast_14961(0)}};
		if (m_axi_awvalid && m_axi_awready)
			w_drain_t[r_aw_channel_id * SCW+:SCW] = sv2v_cast_14961(m_axi_awlen) + sv2v_cast_14961_signed(1);
	end
	always @(posedge clk)
		if (!rst_n)
			r_drain_tminus1 <= {NC {sv2v_cast_14961(0)}};
		else
			r_drain_tminus1 <= w_drain_t;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					w_pending_drain[i * SCW+:SCW] = r_drain_tminus1[i * SCW+:SCW] + w_drain_t[i * SCW+:SCW];
					w_effective_avail[i * SCW+:SCW] = (axi_wr_drain_data_avail[i * SCW+:SCW] >= w_pending_drain[i * SCW+:SCW] ? axi_wr_drain_data_avail[i * SCW+:SCW] - w_pending_drain[i * SCW+:SCW] : {SCW * 1 {1'sb0}});
				end
		end
	end
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
		begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < NC; i = i + 1)
				begin
					if (sched_wr_valid[i]) begin
						w_transfer_size[i * 8+:8] = sv2v_cast_8((sched_wr_beats[i * 32+:32] <= (sv2v_cast_32(cfg_axi_wr_xfer_beats) + 32'd1) ? sched_wr_beats[i * 32+:32] - 32'd1 : sv2v_cast_32(cfg_axi_wr_xfer_beats)));
						w_has_data[i] = sv2v_cast_14961(w_effective_avail[i * SCW+:SCW]) >= sv2v_cast_14961(w_transfer_size[i * 8+:8] + 8'd1);
						w_final_burst[i] = ((sched_wr_beats[i * 32+:32] > 0) && (sched_wr_beats[i * 32+:32] <= (sv2v_cast_32(cfg_axi_wr_xfer_beats) + 32'd1))) && (sv2v_cast_14961(w_effective_avail[i * SCW+:SCW]) >= sv2v_cast_14961(sched_wr_beats[i * 32+:32]));
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
	reg [NC - 1:0] r_arb_request;
	always @(posedge clk)
		if (!rst_n)
			r_arb_request <= 1'sb0;
		else
			r_arb_request <= w_arb_request;
	wire w_arb_grant_valid;
	wire [NC - 1:0] w_arb_grant;
	wire [CIW - 1:0] w_arb_grant_id;
	wire [NC - 1:0] w_arb_grant_ack;
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
	wire [NC - 1:0] w_stale_grant;
	assign w_stale_grant = w_arb_grant & ~sched_wr_valid;
	assign w_arb_grant_ack = (w_arb_grant & {NC {m_axi_awvalid && m_axi_awready}}) | w_stale_grant;
	always @(posedge clk)
		if (!rst_n) begin
			r_aw_valid <= 1'b0;
			r_aw_len <= 1'sb0;
			r_aw_channel_id <= 1'sb0;
		end
		else begin
			if ((w_arb_grant_valid && !r_aw_valid) && sched_wr_valid[w_arb_grant_id]) begin
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
			if (m_axi_bvalid && m_axi_bready) begin : sv2v_autoblock_9
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
	assign axi_wr_sram_drain = m_axi_wvalid && m_axi_wready;
	assign axi_wr_sram_id = r_w_channel_id;
	assign m_axi_wvalid = (r_w_active && axi_wr_sram_valid[r_w_channel_id]) && axi_wr_sram_valid_comb[r_w_channel_id];
	assign m_axi_wdata = axi_wr_sram_data;
	assign m_axi_wstrb = {DW / 8 {1'b1}};
	assign m_axi_wlast = r_w_beats_remaining == 8'd1;
	function automatic [UW - 1:0] sv2v_cast_FDCE5;
		input reg [UW - 1:0] inp;
		sv2v_cast_FDCE5 = inp;
	endfunction
	assign m_axi_wuser = sv2v_cast_FDCE5(r_w_channel_id);
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
	reg [NC - 1:0] r_commit_strobe;
	reg [(NC * 32) - 1:0] r_commit_beats;
	always @(posedge clk)
		if (!rst_n) begin
			r_commit_strobe <= {NC {1'd0}};
			r_commit_beats <= {NC {32'd0}};
		end
		else begin
			r_commit_strobe <= {NC {1'd0}};
			begin : sv2v_autoblock_10
				reg signed [31:0] i;
				for (i = 0; i < NC; i = i + 1)
					if ((m_axi_bvalid && m_axi_bready) && (m_axi_bid[CIW - 1:0] == i[CIW - 1:0])) begin
						r_commit_strobe[i] <= 1'b1;
						r_commit_beats[i * 32+:32] <= {24'h000000, b_phase_txn_fifo_dout[(i * 9) + 8-:8]};
					end
			end
		end
	assign sched_wr_commit_strobe = r_commit_strobe;
	assign sched_wr_commit_beats = r_commit_beats;
	reg [15:0] r_stuck_counter [0:NC - 1];
	initial begin : sv2v_autoblock_11
		reg signed [31:0] i;
		for (i = 0; i < NC; i = i + 1)
			r_stuck_counter[i] = 0;
	end
	always @(posedge clk) begin : sv2v_autoblock_12
		reg signed [31:0] i;
		for (i = 0; i < NC; i = i + 1)
			if ((sched_wr_valid[i] && !w_arb_request[i]) && !(m_axi_bvalid && m_axi_bready)) begin
				r_stuck_counter[i] <= r_stuck_counter[i] + 1;
				if (r_stuck_counter[i] == 1024)
					$display("[%0t] WR ENGINE STUCK ch%0d: sched_wr_beats=%0d transfer_size=%0d has_data=%b final=%b data_ok=%b no_out=%b arb_req=%b drain_avail=%0d", $time, i, sched_wr_beats[i * 32+:32], w_transfer_size[i * 8+:8], w_has_data[i], w_final_burst[i], w_data_ok[i], w_no_outstanding[i], w_arb_request[i], axi_wr_drain_data_avail[i * SCW+:SCW]);
			end
			else
				r_stuck_counter[i] <= 1'sb0;
	end
	assign m_axi_bready = 1'b1;
	reg [NC - 1:0] r_wr_error;
	always @(posedge clk)
		if (!rst_n)
			r_wr_error <= 1'sb0;
		else if ((m_axi_bvalid && m_axi_bready) && (m_axi_bresp != 2'b00)) begin : sv2v_autoblock_13
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
	assign o_active_channel_id = r_w_channel_id;
	assign o_active_channel_valid = r_w_active;
	initial _sv2v_0 = 0;
endmodule
module perf_profiler (
	clk,
	rst_n,
	channel_idle,
	cfg_enable,
	cfg_mode,
	cfg_clear,
	perf_fifo_rd,
	perf_fifo_data_low,
	perf_fifo_data_high,
	perf_fifo_empty,
	perf_fifo_full,
	perf_fifo_count
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHANNEL_WIDTH = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	parameter signed [31:0] TIMESTAMP_WIDTH = 32;
	parameter signed [31:0] FIFO_DEPTH = 256;
	parameter signed [31:0] FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH);
	input wire clk;
	input wire rst_n;
	input wire [NUM_CHANNELS - 1:0] channel_idle;
	input wire cfg_enable;
	input wire cfg_mode;
	input wire cfg_clear;
	input wire perf_fifo_rd;
	output wire [31:0] perf_fifo_data_low;
	output wire [31:0] perf_fifo_data_high;
	output wire perf_fifo_empty;
	output wire perf_fifo_full;
	output wire [15:0] perf_fifo_count;
	localparam [0:0] MODE_TIMESTAMP = 1'b0;
	localparam [0:0] MODE_ELAPSED = 1'b1;
	localparam [0:0] EVENT_START = 1'b0;
	localparam [0:0] EVENT_END = 1'b1;
	reg [TIMESTAMP_WIDTH - 1:0] r_timestamp_counter;
	reg [NUM_CHANNELS - 1:0] r_idle_prev;
	wire [NUM_CHANNELS - 1:0] w_idle_rising;
	wire [NUM_CHANNELS - 1:0] w_idle_falling;
	reg [TIMESTAMP_WIDTH - 1:0] r_start_time [0:NUM_CHANNELS - 1];
	reg [NUM_CHANNELS - 1:0] r_channel_active;
	reg w_fifo_wr;
	reg [35:0] w_fifo_wr_data;
	wire w_fifo_wr_ready_internal;
	wire w_fifo_full_internal;
	wire w_fifo_rd_valid_internal;
	wire [35:0] w_fifo_rd_data;
	reg [35:0] r_fifo_data_latched;
	wire [FIFO_ADDR_WIDTH:0] w_fifo_count_internal;
	reg [CHANNEL_WIDTH - 1:0] w_active_channel;
	reg w_channel_event;
	wire [TIMESTAMP_WIDTH - 1:0] w_elapsed_time;
	always @(posedge clk)
		if (!rst_n)
			r_timestamp_counter <= 1'sb0;
		else if (cfg_clear)
			r_timestamp_counter <= 1'sb0;
		else if (cfg_enable)
			r_timestamp_counter <= r_timestamp_counter + 1'b1;
	always @(posedge clk)
		if (!rst_n)
			r_idle_prev <= 1'sb1;
		else if (cfg_enable)
			r_idle_prev <= channel_idle;
	assign w_idle_rising = channel_idle & ~r_idle_prev;
	assign w_idle_falling = ~channel_idle & r_idle_prev;
	genvar _gv_ch_1;
	generate
		for (_gv_ch_1 = 0; _gv_ch_1 < NUM_CHANNELS; _gv_ch_1 = _gv_ch_1 + 1) begin : gen_channel_tracking
			localparam ch = _gv_ch_1;
			always @(posedge clk)
				if (!rst_n) begin
					r_start_time[ch] <= 1'sb0;
					r_channel_active[ch] <= 1'b0;
				end
				else if (cfg_clear) begin
					r_start_time[ch] <= 1'sb0;
					r_channel_active[ch] <= 1'b0;
				end
				else if (cfg_enable && (cfg_mode == MODE_ELAPSED)) begin
					if (w_idle_falling[ch]) begin
						r_start_time[ch] <= r_timestamp_counter;
						r_channel_active[ch] <= 1'b1;
					end
					else if (w_idle_rising[ch])
						r_channel_active[ch] <= 1'b0;
				end
		end
	endgenerate
	always @(*) begin : sv2v_autoblock_1
		reg [0:1] _sv2v_jump;
		_sv2v_jump = 2'b00;
		if (_sv2v_0)
			;
		w_active_channel = 1'sb0;
		w_channel_event = 1'b0;
		if (cfg_mode == MODE_TIMESTAMP) begin : sv2v_autoblock_2
			reg signed [31:0] i;
			begin : sv2v_autoblock_3
				reg signed [31:0] _sv2v_value_on_break;
				for (i = 0; i < NUM_CHANNELS; i = i + 1)
					if (_sv2v_jump < 2'b10) begin
						_sv2v_jump = 2'b00;
						if (w_idle_rising[i] || w_idle_falling[i]) begin
							w_active_channel = i[CHANNEL_WIDTH - 1:0];
							w_channel_event = 1'b1;
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
		else begin : sv2v_autoblock_4
			reg signed [31:0] i;
			begin : sv2v_autoblock_5
				reg signed [31:0] _sv2v_value_on_break;
				for (i = 0; i < NUM_CHANNELS; i = i + 1)
					if (_sv2v_jump < 2'b10) begin
						_sv2v_jump = 2'b00;
						if (w_idle_rising[i]) begin
							w_active_channel = i[CHANNEL_WIDTH - 1:0];
							w_channel_event = 1'b1;
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
	assign w_elapsed_time = r_timestamp_counter - r_start_time[w_active_channel];
	function automatic [2:0] sv2v_cast_3;
		input reg [2:0] inp;
		sv2v_cast_3 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_fifo_wr = 1'b0;
		w_fifo_wr_data = 1'sb0;
		if ((cfg_enable && w_channel_event) && !w_fifo_full_internal) begin
			w_fifo_wr = 1'b1;
			if (cfg_mode == MODE_TIMESTAMP)
				w_fifo_wr_data = {(w_idle_rising[w_active_channel] ? EVENT_END : EVENT_START), sv2v_cast_3(w_active_channel), r_timestamp_counter};
			else
				w_fifo_wr_data = {EVENT_END, sv2v_cast_3(w_active_channel), w_elapsed_time};
		end
	end
	gaxi_fifo_sync #(
		.DATA_WIDTH(36),
		.DEPTH(FIFO_DEPTH)
	) u_perf_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n && !cfg_clear),
		.wr_valid(w_fifo_wr),
		.wr_data(w_fifo_wr_data),
		.wr_ready(w_fifo_wr_ready_internal),
		.rd_valid(w_fifo_rd_valid_internal),
		.rd_data(w_fifo_rd_data),
		.rd_ready(perf_fifo_rd),
		.count(w_fifo_count_internal)
	);
	assign w_fifo_full_internal = !w_fifo_wr_ready_internal;
	assign perf_fifo_empty = !w_fifo_rd_valid_internal;
	assign perf_fifo_full = w_fifo_full_internal;
	assign perf_fifo_count = {{(16 - FIFO_ADDR_WIDTH) - 1 {1'b0}}, w_fifo_count_internal};
	always @(posedge clk)
		if (!rst_n)
			r_fifo_data_latched <= 1'sb0;
		else if (cfg_clear)
			r_fifo_data_latched <= 1'sb0;
		else if (perf_fifo_rd && !perf_fifo_empty)
			r_fifo_data_latched <= w_fifo_rd_data;
	assign perf_fifo_data_low = r_fifo_data_latched[31:0];
	assign perf_fifo_data_high = {28'b0000000000000000000000000000, r_fifo_data_latched[35:32]};
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
	genvar _gv_ch_2;
	generate
		for (_gv_ch_2 = 0; _gv_ch_2 < NUM_CHANNELS; _gv_ch_2 = _gv_ch_2 + 1) begin : gen_scheduler_groups
			localparam ch = _gv_ch_2;
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
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	localparam signed [31:0] sv2v_uu_u_desc_axi_monitor_AXI_ADDR_WIDTH = ADDR_WIDTH;
	localparam signed [31:0] sv2v_uu_u_desc_axi_monitor_AW = sv2v_uu_u_desc_axi_monitor_AXI_ADDR_WIDTH;
	localparam signed [31:0] sv2v_uu_u_desc_axi_monitor_N_ADDR_RANGES = 0;
	localparam [(1 * sv2v_uu_u_desc_axi_monitor_AW) - 1:0] sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_low_0 = 1'sb0;
	localparam [(1 * sv2v_uu_u_desc_axi_monitor_AW) - 1:0] sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_high_0 = 1'sb0;
	axi4_master_rd_mon #(
		.USE_MONITOR((USE_AXI_MONITORS == 1) && USE_DESC_AXI_MONITOR),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(ADDR_WIDTH),
		.AXI_DATA_WIDTH(256),
		.AXI_USER_WIDTH(1),
		.UNIT_ID(MON_UNIT_ID),
		.AGENT_ID(DESC_AXI_MON_AGENT_ID),
		.MAX_TRANSACTIONS(MON_MAX_TRANSACTIONS),
		.ENABLE_FILTERING(1),
		.ENABLE_ERROR_LOGIC(DESC_MON_ENABLE_ERROR_LOGIC),
		.ENABLE_TIMEOUT_LOGIC(DESC_MON_ENABLE_TIMEOUT_LOGIC),
		.ENABLE_COMPL_LOGIC(DESC_MON_ENABLE_COMPL_LOGIC),
		.ENABLE_THRESHOLD_LOGIC(DESC_MON_ENABLE_THRESHOLD_LOGIC),
		.ENABLE_PERF_LOGIC(DESC_MON_ENABLE_PERF_LOGIC),
		.ENABLE_DEBUG_LOGIC(DESC_MON_ENABLE_DEBUG_LOGIC)
	) u_desc_axi_monitor(
		.aclk(clk),
		.aresetn(rst_n),
		.debug_block_ready(),
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
		.cfg_perf_enable(cfg_desc_mon_perf_enable),
		.cfg_compl_enable(cfg_desc_mon_compl_enable),
		.cfg_threshold_enable(cfg_desc_mon_thresh_enable),
		.cfg_debug_enable(1'b0),
		.cfg_timeout_enable(cfg_desc_mon_timeout_enable),
		.cfg_timeout_cycles(sv2v_cast_16(cfg_desc_mon_timeout_cycles)),
		.cfg_freq_sel(4'b0000),
		.cfg_latency_threshold(cfg_desc_mon_latency_thresh),
		.cfg_axi_pkt_mask(cfg_desc_mon_pkt_mask),
		.cfg_axi_err_select(cfg_desc_mon_err_select),
		.cfg_axi_error_mask(cfg_desc_mon_err_mask),
		.cfg_axi_timeout_mask(cfg_desc_mon_timeout_mask),
		.cfg_axi_compl_mask(cfg_desc_mon_compl_mask),
		.cfg_axi_thresh_mask(cfg_desc_mon_thresh_mask),
		.cfg_axi_perf_mask(cfg_desc_mon_perf_mask),
		.cfg_axi_addr_mask(cfg_desc_mon_addr_mask),
		.cfg_axi_debug_mask(cfg_desc_mon_debug_mask),
		.cfg_addr_check_enable(1'b0),
		.cfg_addr_range_enable(1'b0),
		.cfg_addr_range_low(sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_low_0),
		.cfg_addr_range_high(sv2v_uu_u_desc_axi_monitor_ext_cfg_addr_range_high_0),
		.cfg_start_event_sel(3'b000),
		.cfg_end_event_sel(3'b000),
		.cfg_start_trigger(cfg_desc_mon_perf_run),
		.cfg_end_trigger(~cfg_desc_mon_perf_run),
		.cfg_window_force_close(1'b0),
		.i_mon_time(i_mon_time),
		.monbus_valid(desc_axi_mon_valid),
		.monbus_ready(desc_axi_mon_ready),
		.monbus_packet(desc_axi_mon_packet),
		.monbus_timestamp(desc_axi_mon_timestamp),
		.busy(cfg_sts_desc_mon_busy),
		.active_transactions(cfg_sts_desc_mon_active_txns),
		.error_count(cfg_sts_desc_mon_error_count),
		.transaction_count(cfg_sts_desc_mon_txn_count),
		.window_active(perf_window_active),
		.window_cycles(perf_window_cycles),
		.perf_prod_cycles(perf_prod_cycles),
		.perf_bp_cycles(perf_bp_cycles),
		.perf_starv_cycles(perf_starv_cycles),
		.perf_idle_cycles(perf_idle_cycles),
		.perf_beat_count(perf_beat_count),
		.perf_byte_count(perf_byte_count),
		.perf_burst_count(perf_burst_count),
		.cfg_conflict_error(cfg_sts_desc_mon_conflict_error)
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
module stream_core (
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
	cfg_rdeng_mon_enable,
	cfg_rdeng_mon_err_enable,
	cfg_rdeng_mon_perf_enable,
	cfg_rdeng_mon_compl_enable,
	cfg_rdeng_mon_thresh_enable,
	cfg_rdeng_mon_timeout_enable,
	cfg_rdeng_mon_timeout_cycles,
	cfg_rdeng_mon_latency_thresh,
	cfg_rdeng_mon_pkt_mask,
	cfg_rdeng_mon_err_select,
	cfg_rdeng_mon_err_mask,
	cfg_rdeng_mon_timeout_mask,
	cfg_rdeng_mon_compl_mask,
	cfg_rdeng_mon_thresh_mask,
	cfg_rdeng_mon_perf_mask,
	cfg_rdeng_mon_addr_mask,
	cfg_rdeng_mon_debug_mask,
	cfg_wreng_mon_enable,
	cfg_wreng_mon_err_enable,
	cfg_wreng_mon_perf_enable,
	cfg_wreng_mon_compl_enable,
	cfg_wreng_mon_thresh_enable,
	cfg_wreng_mon_timeout_enable,
	cfg_wreng_mon_timeout_cycles,
	cfg_wreng_mon_latency_thresh,
	cfg_wreng_mon_pkt_mask,
	cfg_wreng_mon_err_select,
	cfg_wreng_mon_err_mask,
	cfg_wreng_mon_timeout_mask,
	cfg_wreng_mon_compl_mask,
	cfg_wreng_mon_thresh_mask,
	cfg_wreng_mon_perf_mask,
	cfg_wreng_mon_addr_mask,
	cfg_wreng_mon_debug_mask,
	cfg_rdeng_mon_perf_run,
	cfg_wreng_mon_perf_run,
	cfg_rdeng_mon_addr_range_low,
	cfg_rdeng_mon_addr_range_high,
	cfg_rdeng_mon_addr_range_en,
	cfg_rdeng_mon_addr_check_en,
	cfg_rdeng_mon_addr_match_en,
	cfg_rdeng_mon_addr_miss_en,
	cfg_wreng_mon_addr_range_low,
	cfg_wreng_mon_addr_range_high,
	cfg_wreng_mon_addr_range_en,
	cfg_wreng_mon_addr_check_en,
	cfg_wreng_mon_addr_match_en,
	cfg_wreng_mon_addr_miss_en,
	cfg_perf_ch_sel,
	cfg_perf_hist_bus,
	cfg_perf_hist_metric,
	cfg_perf_hist_bin,
	perf_hist_data,
	perf_hist_total,
	cfg_axi_rd_xfer_beats,
	cfg_axi_wr_xfer_beats,
	cfg_perf_enable,
	cfg_perf_mode,
	cfg_perf_clear,
	system_idle,
	descriptor_engine_idle,
	scheduler_idle,
	scheduler_state,
	sched_error,
	axi_rd_all_complete,
	axi_wr_all_complete,
	perf_fifo_empty,
	perf_fifo_full,
	perf_fifo_count,
	perf_fifo_rd,
	perf_fifo_data_low,
	perf_fifo_data_high,
	cfg_obs_ch_sel,
	cfg_obs_cat_sel,
	obs_flags,
	obs_data0,
	obs_data1,
	m_axi_desc_arid,
	m_axi_desc_araddr,
	m_axi_desc_arlen,
	m_axi_desc_arsize,
	m_axi_desc_arburst,
	m_axi_desc_arlock,
	m_axi_desc_arcache,
	m_axi_desc_arprot,
	m_axi_desc_arqos,
	m_axi_desc_arregion,
	m_axi_desc_aruser,
	m_axi_desc_arvalid,
	m_axi_desc_arready,
	m_axi_desc_rid,
	m_axi_desc_rdata,
	m_axi_desc_rresp,
	m_axi_desc_rlast,
	m_axi_desc_ruser,
	m_axi_desc_rvalid,
	m_axi_desc_rready,
	m_axi_rd_arid,
	m_axi_rd_araddr,
	m_axi_rd_arlen,
	m_axi_rd_arsize,
	m_axi_rd_arburst,
	m_axi_rd_arlock,
	m_axi_rd_arcache,
	m_axi_rd_arprot,
	m_axi_rd_arqos,
	m_axi_rd_arregion,
	m_axi_rd_aruser,
	m_axi_rd_arvalid,
	m_axi_rd_arready,
	m_axi_rd_rid,
	m_axi_rd_rdata,
	m_axi_rd_rresp,
	m_axi_rd_rlast,
	m_axi_rd_ruser,
	m_axi_rd_rvalid,
	m_axi_rd_rready,
	m_axi_wr_awid,
	m_axi_wr_awaddr,
	m_axi_wr_awlen,
	m_axi_wr_awsize,
	m_axi_wr_awburst,
	m_axi_wr_awlock,
	m_axi_wr_awcache,
	m_axi_wr_awprot,
	m_axi_wr_awqos,
	m_axi_wr_awregion,
	m_axi_wr_awuser,
	m_axi_wr_awvalid,
	m_axi_wr_awready,
	m_axi_wr_wdata,
	m_axi_wr_wstrb,
	m_axi_wr_wlast,
	m_axi_wr_wuser,
	m_axi_wr_wvalid,
	m_axi_wr_wready,
	m_axi_wr_bid,
	m_axi_wr_bresp,
	m_axi_wr_buser,
	m_axi_wr_bvalid,
	m_axi_wr_bready,
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
	cfg_sts_rdeng_skid_busy,
	cfg_sts_rdeng_mon_active_txns,
	cfg_sts_rdeng_mon_error_count,
	cfg_sts_rdeng_mon_txn_count,
	cfg_sts_rdeng_mon_conflict_error,
	rdmon_perf_window_active,
	rdmon_perf_window_cycles,
	rdmon_perf_prod_cycles,
	rdmon_perf_bp_cycles,
	rdmon_perf_starv_cycles,
	rdmon_perf_idle_cycles,
	rdmon_perf_beat_count,
	rdmon_perf_byte_count,
	rdmon_perf_burst_count,
	cfg_sts_wreng_skid_busy,
	cfg_sts_wreng_mon_active_txns,
	cfg_sts_wreng_mon_error_count,
	cfg_sts_wreng_mon_txn_count,
	cfg_sts_wreng_mon_conflict_error,
	wrmon_perf_window_active,
	wrmon_perf_window_cycles,
	wrmon_perf_prod_cycles,
	wrmon_perf_bp_cycles,
	wrmon_perf_starv_cycles,
	wrmon_perf_idle_cycles,
	wrmon_perf_beat_count,
	wrmon_perf_byte_count,
	wrmon_perf_burst_count,
	rdmon_ch_prod_cycles,
	rdmon_ch_bp_cycles,
	rdmon_ch_starv_cycles,
	rdmon_ch_idle_cycles,
	rdmon_ch_overflow,
	wrmon_ch_prod_cycles,
	wrmon_ch_bp_cycles,
	wrmon_ch_starv_cycles,
	wrmon_ch_idle_cycles,
	wrmon_ch_overflow,
	i_mon_time,
	mon_valid,
	mon_ready,
	mon_packet,
	mon_timestamp
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] USE_ROW_COL_MAJOR_ADDRESSING = 1;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] FIFO_DEPTH = 512;
	parameter signed [31:0] AR_MAX_OUTSTANDING = 8;
	parameter signed [31:0] AW_MAX_OUTSTANDING = 8;
	parameter signed [31:0] MON_TRANS_MARGIN = 8;
	parameter signed [31:0] RD_MON_MAX_TRANS = (((NUM_CHANNELS * AR_MAX_OUTSTANDING) + MON_TRANS_MARGIN) < 16 ? 16 : (NUM_CHANNELS * AR_MAX_OUTSTANDING) + MON_TRANS_MARGIN);
	parameter signed [31:0] WR_MON_MAX_TRANS = (((NUM_CHANNELS * AW_MAX_OUTSTANDING) + MON_TRANS_MARGIN) < 16 ? 16 : (NUM_CHANNELS * AW_MAX_OUTSTANDING) + MON_TRANS_MARGIN);
	parameter signed [31:0] MON_NUM_BANKS = 1;
	parameter [0:0] MON_USE_WDATA_ORDER_Q = MON_NUM_BANKS > 1;
	parameter signed [31:0] USE_AXI_MONITORS = 1;
	parameter [0:0] GEN_MON = 1'b1;
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	parameter DESC_MON_BASE_AGENT_ID = 16;
	parameter SCHED_MON_BASE_AGENT_ID = 48;
	parameter DESC_AXI_MON_AGENT_ID = 8;
	parameter RD_AXI_MON_AGENT_ID = 9;
	parameter WR_AXI_MON_AGENT_ID = 10;
	parameter MON_UNIT_ID = 1;
	parameter [0:0] DESC_MON_ENABLE_ERROR_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_TIMEOUT_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_COMPL_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_THRESHOLD_LOGIC = 1'b0;
	parameter [0:0] DESC_MON_ENABLE_PERF_LOGIC = 1'b1;
	parameter [0:0] DESC_MON_ENABLE_DEBUG_LOGIC = 1'b0;
	parameter [0:0] DATA_MON_ENABLE_ERROR_LOGIC = 1'b0;
	parameter [0:0] DATA_MON_ENABLE_TIMEOUT_LOGIC = 1'b0;
	parameter [0:0] DATA_MON_ENABLE_COMPL_LOGIC = 1'b0;
	parameter [0:0] DATA_MON_ENABLE_THRESHOLD_LOGIC = 1'b0;
	parameter [0:0] DATA_MON_ENABLE_PERF_LOGIC = 1'b1;
	parameter [0:0] DATA_MON_ENABLE_DEBUG_LOGIC = 1'b0;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] MON_ADDR_RANGE_IS_ERROR = 1'sb0;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] UW = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	input wire clk;
	input wire rst_n;
	input wire cam_clear;
	input wire [NC - 1:0] apb_valid;
	output wire [NC - 1:0] apb_ready;
	input wire [(NC * AW) - 1:0] apb_addr;
	input wire [NC - 1:0] cfg_channel_enable;
	input wire [NC - 1:0] cfg_channel_reset;
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
	input wire [AW - 1:0] cfg_desceng_addr0_base;
	input wire [AW - 1:0] cfg_desceng_addr0_limit;
	input wire [AW - 1:0] cfg_desceng_addr1_base;
	input wire [AW - 1:0] cfg_desceng_addr1_limit;
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
	input wire cfg_rdeng_mon_enable;
	input wire cfg_rdeng_mon_err_enable;
	input wire cfg_rdeng_mon_perf_enable;
	input wire cfg_rdeng_mon_compl_enable;
	input wire cfg_rdeng_mon_thresh_enable;
	input wire cfg_rdeng_mon_timeout_enable;
	input wire [31:0] cfg_rdeng_mon_timeout_cycles;
	input wire [31:0] cfg_rdeng_mon_latency_thresh;
	input wire [15:0] cfg_rdeng_mon_pkt_mask;
	input wire [15:0] cfg_rdeng_mon_err_select;
	input wire [15:0] cfg_rdeng_mon_err_mask;
	input wire [15:0] cfg_rdeng_mon_timeout_mask;
	input wire [15:0] cfg_rdeng_mon_compl_mask;
	input wire [15:0] cfg_rdeng_mon_thresh_mask;
	input wire [15:0] cfg_rdeng_mon_perf_mask;
	input wire [15:0] cfg_rdeng_mon_addr_mask;
	input wire [15:0] cfg_rdeng_mon_debug_mask;
	input wire cfg_wreng_mon_enable;
	input wire cfg_wreng_mon_err_enable;
	input wire cfg_wreng_mon_perf_enable;
	input wire cfg_wreng_mon_compl_enable;
	input wire cfg_wreng_mon_thresh_enable;
	input wire cfg_wreng_mon_timeout_enable;
	input wire [31:0] cfg_wreng_mon_timeout_cycles;
	input wire [31:0] cfg_wreng_mon_latency_thresh;
	input wire [15:0] cfg_wreng_mon_pkt_mask;
	input wire [15:0] cfg_wreng_mon_err_select;
	input wire [15:0] cfg_wreng_mon_err_mask;
	input wire [15:0] cfg_wreng_mon_timeout_mask;
	input wire [15:0] cfg_wreng_mon_compl_mask;
	input wire [15:0] cfg_wreng_mon_thresh_mask;
	input wire [15:0] cfg_wreng_mon_perf_mask;
	input wire [15:0] cfg_wreng_mon_addr_mask;
	input wire [15:0] cfg_wreng_mon_debug_mask;
	input wire cfg_rdeng_mon_perf_run;
	input wire cfg_wreng_mon_perf_run;
	input wire [127:0] cfg_rdeng_mon_addr_range_low;
	input wire [127:0] cfg_rdeng_mon_addr_range_high;
	input wire [3:0] cfg_rdeng_mon_addr_range_en;
	input wire cfg_rdeng_mon_addr_check_en;
	input wire cfg_rdeng_mon_addr_match_en;
	input wire cfg_rdeng_mon_addr_miss_en;
	input wire [127:0] cfg_wreng_mon_addr_range_low;
	input wire [127:0] cfg_wreng_mon_addr_range_high;
	input wire [3:0] cfg_wreng_mon_addr_range_en;
	input wire cfg_wreng_mon_addr_check_en;
	input wire cfg_wreng_mon_addr_match_en;
	input wire cfg_wreng_mon_addr_miss_en;
	input wire [CHAN_WIDTH - 1:0] cfg_perf_ch_sel;
	input wire cfg_perf_hist_bus;
	input wire cfg_perf_hist_metric;
	input wire [3:0] cfg_perf_hist_bin;
	output wire [31:0] perf_hist_data;
	output wire [31:0] perf_hist_total;
	input wire [7:0] cfg_axi_rd_xfer_beats;
	input wire [7:0] cfg_axi_wr_xfer_beats;
	input wire cfg_perf_enable;
	input wire cfg_perf_mode;
	input wire cfg_perf_clear;
	output wire system_idle;
	output wire [NC - 1:0] descriptor_engine_idle;
	output wire [NC - 1:0] scheduler_idle;
	output wire [(NC * 7) - 1:0] scheduler_state;
	output wire [NC - 1:0] sched_error;
	output wire [NC - 1:0] axi_rd_all_complete;
	output wire [NC - 1:0] axi_wr_all_complete;
	output wire perf_fifo_empty;
	output wire perf_fifo_full;
	output wire [15:0] perf_fifo_count;
	input wire perf_fifo_rd;
	output wire [31:0] perf_fifo_data_low;
	output wire [31:0] perf_fifo_data_high;
	input wire [2:0] cfg_obs_ch_sel;
	input wire [1:0] cfg_obs_cat_sel;
	output reg [31:0] obs_flags;
	output reg [31:0] obs_data0;
	output reg [31:0] obs_data1;
	output wire [IW - 1:0] m_axi_desc_arid;
	output wire [AW - 1:0] m_axi_desc_araddr;
	output wire [7:0] m_axi_desc_arlen;
	output wire [2:0] m_axi_desc_arsize;
	output wire [1:0] m_axi_desc_arburst;
	output wire m_axi_desc_arlock;
	output wire [3:0] m_axi_desc_arcache;
	output wire [2:0] m_axi_desc_arprot;
	output wire [3:0] m_axi_desc_arqos;
	output wire [3:0] m_axi_desc_arregion;
	output wire [UW - 1:0] m_axi_desc_aruser;
	output wire m_axi_desc_arvalid;
	input wire m_axi_desc_arready;
	input wire [IW - 1:0] m_axi_desc_rid;
	input wire [255:0] m_axi_desc_rdata;
	input wire [1:0] m_axi_desc_rresp;
	input wire m_axi_desc_rlast;
	input wire [UW - 1:0] m_axi_desc_ruser;
	input wire m_axi_desc_rvalid;
	output wire m_axi_desc_rready;
	output wire [IW - 1:0] m_axi_rd_arid;
	output wire [AW - 1:0] m_axi_rd_araddr;
	output wire [7:0] m_axi_rd_arlen;
	output wire [2:0] m_axi_rd_arsize;
	output wire [1:0] m_axi_rd_arburst;
	output wire m_axi_rd_arlock;
	output wire [3:0] m_axi_rd_arcache;
	output wire [2:0] m_axi_rd_arprot;
	output wire [3:0] m_axi_rd_arqos;
	output wire [3:0] m_axi_rd_arregion;
	output wire [UW - 1:0] m_axi_rd_aruser;
	output wire m_axi_rd_arvalid;
	input wire m_axi_rd_arready;
	input wire [IW - 1:0] m_axi_rd_rid;
	input wire [DW - 1:0] m_axi_rd_rdata;
	input wire [1:0] m_axi_rd_rresp;
	input wire m_axi_rd_rlast;
	input wire [UW - 1:0] m_axi_rd_ruser;
	input wire m_axi_rd_rvalid;
	output wire m_axi_rd_rready;
	output wire [IW - 1:0] m_axi_wr_awid;
	output wire [AW - 1:0] m_axi_wr_awaddr;
	output wire [7:0] m_axi_wr_awlen;
	output wire [2:0] m_axi_wr_awsize;
	output wire [1:0] m_axi_wr_awburst;
	output wire m_axi_wr_awlock;
	output wire [3:0] m_axi_wr_awcache;
	output wire [2:0] m_axi_wr_awprot;
	output wire [3:0] m_axi_wr_awqos;
	output wire [3:0] m_axi_wr_awregion;
	output wire [UW - 1:0] m_axi_wr_awuser;
	output wire m_axi_wr_awvalid;
	input wire m_axi_wr_awready;
	output wire [DW - 1:0] m_axi_wr_wdata;
	output wire [(DW / 8) - 1:0] m_axi_wr_wstrb;
	output wire m_axi_wr_wlast;
	output wire [UW - 1:0] m_axi_wr_wuser;
	output wire m_axi_wr_wvalid;
	input wire m_axi_wr_wready;
	input wire [IW - 1:0] m_axi_wr_bid;
	input wire [1:0] m_axi_wr_bresp;
	input wire [UW - 1:0] m_axi_wr_buser;
	input wire m_axi_wr_bvalid;
	output wire m_axi_wr_bready;
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
	output wire cfg_sts_rdeng_skid_busy;
	output wire [7:0] cfg_sts_rdeng_mon_active_txns;
	output wire [15:0] cfg_sts_rdeng_mon_error_count;
	output wire [31:0] cfg_sts_rdeng_mon_txn_count;
	output wire cfg_sts_rdeng_mon_conflict_error;
	output wire rdmon_perf_window_active;
	output wire [31:0] rdmon_perf_window_cycles;
	output wire [31:0] rdmon_perf_prod_cycles;
	output wire [31:0] rdmon_perf_bp_cycles;
	output wire [31:0] rdmon_perf_starv_cycles;
	output wire [31:0] rdmon_perf_idle_cycles;
	output wire [31:0] rdmon_perf_beat_count;
	output wire [63:0] rdmon_perf_byte_count;
	output wire [31:0] rdmon_perf_burst_count;
	output wire cfg_sts_wreng_skid_busy;
	output wire [7:0] cfg_sts_wreng_mon_active_txns;
	output wire [15:0] cfg_sts_wreng_mon_error_count;
	output wire [31:0] cfg_sts_wreng_mon_txn_count;
	output wire cfg_sts_wreng_mon_conflict_error;
	output wire wrmon_perf_window_active;
	output wire [31:0] wrmon_perf_window_cycles;
	output wire [31:0] wrmon_perf_prod_cycles;
	output wire [31:0] wrmon_perf_bp_cycles;
	output wire [31:0] wrmon_perf_starv_cycles;
	output wire [31:0] wrmon_perf_idle_cycles;
	output wire [31:0] wrmon_perf_beat_count;
	output wire [63:0] wrmon_perf_byte_count;
	output wire [31:0] wrmon_perf_burst_count;
	output reg [15:0] rdmon_ch_prod_cycles;
	output reg [15:0] rdmon_ch_bp_cycles;
	output reg [15:0] rdmon_ch_starv_cycles;
	output reg [15:0] rdmon_ch_idle_cycles;
	output wire [(NC * 4) - 1:0] rdmon_ch_overflow;
	output reg [15:0] wrmon_ch_prod_cycles;
	output reg [15:0] wrmon_ch_bp_cycles;
	output reg [15:0] wrmon_ch_starv_cycles;
	output reg [15:0] wrmon_ch_idle_cycles;
	output wire [(NC * 4) - 1:0] wrmon_ch_overflow;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	wire [IW - 1:0] fub_rd_axi_arid;
	wire [AW - 1:0] fub_rd_axi_araddr;
	wire [7:0] fub_rd_axi_arlen;
	wire [2:0] fub_rd_axi_arsize;
	wire [1:0] fub_rd_axi_arburst;
	wire fub_rd_axi_arlock;
	wire [3:0] fub_rd_axi_arcache;
	wire [2:0] fub_rd_axi_arprot;
	wire [3:0] fub_rd_axi_arqos;
	wire [3:0] fub_rd_axi_arregion;
	wire [UW - 1:0] fub_rd_axi_aruser;
	wire fub_rd_axi_arvalid;
	wire fub_rd_axi_arready;
	wire [IW - 1:0] fub_rd_axi_rid;
	wire [DW - 1:0] fub_rd_axi_rdata;
	wire [1:0] fub_rd_axi_rresp;
	wire fub_rd_axi_rlast;
	wire [UW - 1:0] fub_rd_axi_ruser;
	wire fub_rd_axi_rvalid;
	wire fub_rd_axi_rready;
	wire [IW - 1:0] fub_wr_axi_awid;
	wire [AW - 1:0] fub_wr_axi_awaddr;
	wire [7:0] fub_wr_axi_awlen;
	wire [2:0] fub_wr_axi_awsize;
	wire [1:0] fub_wr_axi_awburst;
	wire fub_wr_axi_awlock;
	wire [3:0] fub_wr_axi_awcache;
	wire [2:0] fub_wr_axi_awprot;
	wire [3:0] fub_wr_axi_awqos;
	wire [3:0] fub_wr_axi_awregion;
	wire [UW - 1:0] fub_wr_axi_awuser;
	wire fub_wr_axi_awvalid;
	wire fub_wr_axi_awready;
	wire [DW - 1:0] fub_wr_axi_wdata;
	wire [(DW / 8) - 1:0] fub_wr_axi_wstrb;
	wire fub_wr_axi_wlast;
	wire [UW - 1:0] fub_wr_axi_wuser;
	wire fub_wr_axi_wvalid;
	wire fub_wr_axi_wready;
	wire [IW - 1:0] fub_wr_axi_bid;
	wire [1:0] fub_wr_axi_bresp;
	wire [UW - 1:0] fub_wr_axi_buser;
	wire fub_wr_axi_bvalid;
	wire fub_wr_axi_bready;
	wire [CHAN_WIDTH - 1:0] wr_active_channel_id;
	wire wr_active_channel_valid;
	wire [NC - 1:0] sched_rd_valid;
	wire [(NC * AW) - 1:0] sched_rd_addr;
	wire [(NC * 32) - 1:0] sched_rd_beats;
	wire [NC - 1:0] sched_wr_valid;
	wire [NC - 1:0] sched_wr_ready;
	wire [(NC * AW) - 1:0] sched_wr_addr;
	wire [(NC * 32) - 1:0] sched_wr_beats;
	wire [NC - 1:0] sched_rd_done_strobe;
	wire [(NC * 32) - 1:0] sched_rd_beats_done;
	wire [NC - 1:0] sched_wr_done_strobe;
	wire [(NC * 32) - 1:0] sched_wr_beats_done;
	wire [NC - 1:0] sched_wr_commit_strobe;
	wire [(NC * 32) - 1:0] sched_wr_commit_beats;
	wire [NC - 1:0] sched_rd_error;
	wire [NC - 1:0] dbg_sched_desc_error;
	wire [NC - 1:0] dbg_sched_rd_sticky;
	wire [NC - 1:0] dbg_sched_wr_sticky;
	wire [NC - 1:0] dbg_sched_timeout;
	wire [NC - 1:0] sched_wr_error;
	wire axi_rd_alloc_req;
	wire [7:0] axi_rd_alloc_size;
	wire [IW - 1:0] axi_rd_alloc_id;
	wire [(($clog2(FIFO_DEPTH) + 0) >= 0 ? (NC * ($clog2(FIFO_DEPTH) + 1)) - 1 : (NC * (1 - ($clog2(FIFO_DEPTH) + 0))) + ($clog2(FIFO_DEPTH) - 1)):(($clog2(FIFO_DEPTH) + 0) >= 0 ? 0 : $clog2(FIFO_DEPTH) + 0)] axi_rd_space_free;
	wire axi_rd_sram_valid;
	wire axi_rd_sram_ready;
	wire [IW - 1:0] axi_rd_sram_id;
	wire [DW - 1:0] axi_rd_sram_data;
	wire [NC - 1:0] axi_wr_drain_req;
	wire [(NC * 8) - 1:0] axi_wr_drain_size;
	wire [(($clog2(FIFO_DEPTH) + 0) >= 0 ? (NC * ($clog2(FIFO_DEPTH) + 1)) - 1 : (NC * (1 - ($clog2(FIFO_DEPTH) + 0))) + ($clog2(FIFO_DEPTH) - 1)):(($clog2(FIFO_DEPTH) + 0) >= 0 ? 0 : $clog2(FIFO_DEPTH) + 0)] axi_wr_drain_data_avail;
	wire [NC - 1:0] axi_wr_sram_valid;
	wire [NC - 1:0] axi_wr_sram_valid_comb;
	wire axi_wr_sram_drain;
	wire [CHAN_WIDTH - 1:0] axi_wr_sram_id;
	wire [DW - 1:0] axi_wr_sram_data;
	wire schedgrp_mon_valid;
	wire schedgrp_mon_ready;
	wire [127:0] schedgrp_mon_packet;
	wire [63:0] schedgrp_mon_timestamp;
	wire rdmon_mon_valid;
	wire rdmon_mon_ready;
	wire [127:0] rdmon_mon_packet;
	wire [63:0] rdmon_mon_timestamp;
	wire wrmon_mon_valid;
	wire wrmon_mon_ready;
	wire [127:0] wrmon_mon_packet;
	wire [63:0] wrmon_mon_timestamp;
	wire int_cfg_desc_mon_enable;
	wire int_cfg_desc_mon_err_enable;
	wire int_cfg_desc_mon_perf_enable;
	wire int_cfg_desc_mon_compl_enable;
	wire int_cfg_desc_mon_thresh_enable;
	wire int_cfg_desc_mon_timeout_enable;
	wire [31:0] int_cfg_desc_mon_timeout_cycles;
	wire [31:0] int_cfg_desc_mon_latency_thresh;
	wire [15:0] int_cfg_desc_mon_pkt_mask;
	wire [15:0] int_cfg_desc_mon_err_select;
	wire [15:0] int_cfg_desc_mon_err_mask;
	wire [15:0] int_cfg_desc_mon_timeout_mask;
	wire [15:0] int_cfg_desc_mon_compl_mask;
	wire [15:0] int_cfg_desc_mon_thresh_mask;
	wire [15:0] int_cfg_desc_mon_perf_mask;
	wire [15:0] int_cfg_desc_mon_addr_mask;
	wire [15:0] int_cfg_desc_mon_debug_mask;
	wire int_cfg_desc_mon_perf_run;
	wire int_cfg_rdeng_mon_enable;
	wire int_cfg_rdeng_mon_err_enable;
	wire int_cfg_rdeng_mon_perf_enable;
	wire int_cfg_rdeng_mon_compl_enable;
	wire int_cfg_rdeng_mon_thresh_enable;
	wire int_cfg_rdeng_mon_timeout_enable;
	wire [31:0] int_cfg_rdeng_mon_timeout_cycles;
	wire [31:0] int_cfg_rdeng_mon_latency_thresh;
	wire [15:0] int_cfg_rdeng_mon_pkt_mask;
	wire [15:0] int_cfg_rdeng_mon_err_select;
	wire [15:0] int_cfg_rdeng_mon_err_mask;
	wire [15:0] int_cfg_rdeng_mon_timeout_mask;
	wire [15:0] int_cfg_rdeng_mon_compl_mask;
	wire [15:0] int_cfg_rdeng_mon_thresh_mask;
	wire [15:0] int_cfg_rdeng_mon_perf_mask;
	wire [15:0] int_cfg_rdeng_mon_addr_mask;
	wire [15:0] int_cfg_rdeng_mon_debug_mask;
	wire int_cfg_rdeng_mon_perf_run;
	wire int_cfg_wreng_mon_enable;
	wire int_cfg_wreng_mon_err_enable;
	wire int_cfg_wreng_mon_perf_enable;
	wire int_cfg_wreng_mon_compl_enable;
	wire int_cfg_wreng_mon_thresh_enable;
	wire int_cfg_wreng_mon_timeout_enable;
	wire [31:0] int_cfg_wreng_mon_timeout_cycles;
	wire [31:0] int_cfg_wreng_mon_latency_thresh;
	wire [15:0] int_cfg_wreng_mon_pkt_mask;
	wire [15:0] int_cfg_wreng_mon_err_select;
	wire [15:0] int_cfg_wreng_mon_err_mask;
	wire [15:0] int_cfg_wreng_mon_timeout_mask;
	wire [15:0] int_cfg_wreng_mon_compl_mask;
	wire [15:0] int_cfg_wreng_mon_thresh_mask;
	wire [15:0] int_cfg_wreng_mon_perf_mask;
	wire [15:0] int_cfg_wreng_mon_addr_mask;
	wire [15:0] int_cfg_wreng_mon_debug_mask;
	wire int_cfg_wreng_mon_perf_run;
	generate
		if (USE_AXI_MONITORS == 1) begin : g_monitors_enabled
			assign int_cfg_desc_mon_enable = cfg_desc_mon_enable;
			assign int_cfg_desc_mon_err_enable = cfg_desc_mon_err_enable;
			assign int_cfg_desc_mon_perf_enable = cfg_desc_mon_perf_enable;
			assign int_cfg_desc_mon_compl_enable = cfg_desc_mon_compl_enable;
			assign int_cfg_desc_mon_thresh_enable = cfg_desc_mon_thresh_enable;
			assign int_cfg_desc_mon_timeout_enable = cfg_desc_mon_timeout_enable;
			assign int_cfg_desc_mon_timeout_cycles = cfg_desc_mon_timeout_cycles;
			assign int_cfg_desc_mon_latency_thresh = cfg_desc_mon_latency_thresh;
			assign int_cfg_desc_mon_pkt_mask = cfg_desc_mon_pkt_mask;
			assign int_cfg_desc_mon_err_select = cfg_desc_mon_err_select;
			assign int_cfg_desc_mon_err_mask = cfg_desc_mon_err_mask;
			assign int_cfg_desc_mon_timeout_mask = cfg_desc_mon_timeout_mask;
			assign int_cfg_desc_mon_compl_mask = cfg_desc_mon_compl_mask;
			assign int_cfg_desc_mon_thresh_mask = cfg_desc_mon_thresh_mask;
			assign int_cfg_desc_mon_perf_mask = cfg_desc_mon_perf_mask;
			assign int_cfg_desc_mon_addr_mask = cfg_desc_mon_addr_mask;
			assign int_cfg_desc_mon_debug_mask = cfg_desc_mon_debug_mask;
			assign int_cfg_desc_mon_perf_run = cfg_desc_mon_perf_run;
			assign int_cfg_rdeng_mon_enable = cfg_rdeng_mon_enable;
			assign int_cfg_rdeng_mon_err_enable = cfg_rdeng_mon_err_enable;
			assign int_cfg_rdeng_mon_perf_enable = cfg_rdeng_mon_perf_enable;
			assign int_cfg_rdeng_mon_compl_enable = cfg_rdeng_mon_compl_enable;
			assign int_cfg_rdeng_mon_thresh_enable = cfg_rdeng_mon_thresh_enable;
			assign int_cfg_rdeng_mon_timeout_enable = cfg_rdeng_mon_timeout_enable;
			assign int_cfg_rdeng_mon_timeout_cycles = cfg_rdeng_mon_timeout_cycles;
			assign int_cfg_rdeng_mon_latency_thresh = cfg_rdeng_mon_latency_thresh;
			assign int_cfg_rdeng_mon_pkt_mask = cfg_rdeng_mon_pkt_mask;
			assign int_cfg_rdeng_mon_err_select = cfg_rdeng_mon_err_select;
			assign int_cfg_rdeng_mon_err_mask = cfg_rdeng_mon_err_mask;
			assign int_cfg_rdeng_mon_timeout_mask = cfg_rdeng_mon_timeout_mask;
			assign int_cfg_rdeng_mon_compl_mask = cfg_rdeng_mon_compl_mask;
			assign int_cfg_rdeng_mon_thresh_mask = cfg_rdeng_mon_thresh_mask;
			assign int_cfg_rdeng_mon_perf_mask = cfg_rdeng_mon_perf_mask;
			assign int_cfg_rdeng_mon_addr_mask = cfg_rdeng_mon_addr_mask;
			assign int_cfg_rdeng_mon_debug_mask = cfg_rdeng_mon_debug_mask;
			assign int_cfg_rdeng_mon_perf_run = cfg_rdeng_mon_perf_run;
			assign int_cfg_wreng_mon_enable = cfg_wreng_mon_enable;
			assign int_cfg_wreng_mon_err_enable = cfg_wreng_mon_err_enable;
			assign int_cfg_wreng_mon_perf_enable = cfg_wreng_mon_perf_enable;
			assign int_cfg_wreng_mon_compl_enable = cfg_wreng_mon_compl_enable;
			assign int_cfg_wreng_mon_thresh_enable = cfg_wreng_mon_thresh_enable;
			assign int_cfg_wreng_mon_timeout_enable = cfg_wreng_mon_timeout_enable;
			assign int_cfg_wreng_mon_timeout_cycles = cfg_wreng_mon_timeout_cycles;
			assign int_cfg_wreng_mon_latency_thresh = cfg_wreng_mon_latency_thresh;
			assign int_cfg_wreng_mon_pkt_mask = cfg_wreng_mon_pkt_mask;
			assign int_cfg_wreng_mon_err_select = cfg_wreng_mon_err_select;
			assign int_cfg_wreng_mon_err_mask = cfg_wreng_mon_err_mask;
			assign int_cfg_wreng_mon_timeout_mask = cfg_wreng_mon_timeout_mask;
			assign int_cfg_wreng_mon_compl_mask = cfg_wreng_mon_compl_mask;
			assign int_cfg_wreng_mon_thresh_mask = cfg_wreng_mon_thresh_mask;
			assign int_cfg_wreng_mon_perf_mask = cfg_wreng_mon_perf_mask;
			assign int_cfg_wreng_mon_addr_mask = cfg_wreng_mon_addr_mask;
			assign int_cfg_wreng_mon_debug_mask = cfg_wreng_mon_debug_mask;
			assign int_cfg_wreng_mon_perf_run = cfg_wreng_mon_perf_run;
		end
		else begin : g_monitors_disabled
			assign int_cfg_desc_mon_enable = 1'b0;
			assign int_cfg_desc_mon_err_enable = 1'b0;
			assign int_cfg_desc_mon_perf_enable = 1'b0;
			assign int_cfg_desc_mon_compl_enable = 1'b0;
			assign int_cfg_desc_mon_thresh_enable = 1'b0;
			assign int_cfg_desc_mon_timeout_enable = 1'b0;
			assign int_cfg_desc_mon_timeout_cycles = 32'h00000000;
			assign int_cfg_desc_mon_latency_thresh = 32'h00000000;
			assign int_cfg_desc_mon_pkt_mask = 16'h0000;
			assign int_cfg_desc_mon_err_select = 16'h0000;
			assign int_cfg_desc_mon_err_mask = 16'h0000;
			assign int_cfg_desc_mon_timeout_mask = 16'h0000;
			assign int_cfg_desc_mon_compl_mask = 16'h0000;
			assign int_cfg_desc_mon_thresh_mask = 16'h0000;
			assign int_cfg_desc_mon_perf_mask = 16'h0000;
			assign int_cfg_desc_mon_addr_mask = 16'h0000;
			assign int_cfg_desc_mon_debug_mask = 16'h0000;
			assign int_cfg_desc_mon_perf_run = cfg_desc_mon_perf_run;
			assign int_cfg_rdeng_mon_enable = 1'b0;
			assign int_cfg_rdeng_mon_err_enable = 1'b0;
			assign int_cfg_rdeng_mon_perf_enable = 1'b0;
			assign int_cfg_rdeng_mon_compl_enable = 1'b0;
			assign int_cfg_rdeng_mon_thresh_enable = 1'b0;
			assign int_cfg_rdeng_mon_timeout_enable = 1'b0;
			assign int_cfg_rdeng_mon_timeout_cycles = 32'h00000000;
			assign int_cfg_rdeng_mon_latency_thresh = 32'h00000000;
			assign int_cfg_rdeng_mon_pkt_mask = 16'h0000;
			assign int_cfg_rdeng_mon_err_select = 16'h0000;
			assign int_cfg_rdeng_mon_err_mask = 16'h0000;
			assign int_cfg_rdeng_mon_timeout_mask = 16'h0000;
			assign int_cfg_rdeng_mon_compl_mask = 16'h0000;
			assign int_cfg_rdeng_mon_thresh_mask = 16'h0000;
			assign int_cfg_rdeng_mon_perf_mask = 16'h0000;
			assign int_cfg_rdeng_mon_addr_mask = 16'h0000;
			assign int_cfg_rdeng_mon_debug_mask = 16'h0000;
			assign int_cfg_rdeng_mon_perf_run = cfg_rdeng_mon_perf_run;
			assign int_cfg_wreng_mon_enable = 1'b0;
			assign int_cfg_wreng_mon_err_enable = 1'b0;
			assign int_cfg_wreng_mon_perf_enable = 1'b0;
			assign int_cfg_wreng_mon_compl_enable = 1'b0;
			assign int_cfg_wreng_mon_thresh_enable = 1'b0;
			assign int_cfg_wreng_mon_timeout_enable = 1'b0;
			assign int_cfg_wreng_mon_timeout_cycles = 32'h00000000;
			assign int_cfg_wreng_mon_latency_thresh = 32'h00000000;
			assign int_cfg_wreng_mon_pkt_mask = 16'h0000;
			assign int_cfg_wreng_mon_err_select = 16'h0000;
			assign int_cfg_wreng_mon_err_mask = 16'h0000;
			assign int_cfg_wreng_mon_timeout_mask = 16'h0000;
			assign int_cfg_wreng_mon_compl_mask = 16'h0000;
			assign int_cfg_wreng_mon_thresh_mask = 16'h0000;
			assign int_cfg_wreng_mon_perf_mask = 16'h0000;
			assign int_cfg_wreng_mon_addr_mask = 16'h0000;
			assign int_cfg_wreng_mon_debug_mask = 16'h0000;
			assign int_cfg_wreng_mon_perf_run = cfg_wreng_mon_perf_run;
		end
	endgenerate
	scheduler_group_array #(
		.GEN_MON(GEN_MON),
		.USE_AXI_MONITORS(USE_AXI_MONITORS),
		.NUM_CHANNELS(NC),
		.CHAN_WIDTH(CHAN_WIDTH),
		.ADDR_WIDTH(AW),
		.DATA_WIDTH(DW),
		.USE_ROW_COL_MAJOR_ADDRESSING(USE_ROW_COL_MAJOR_ADDRESSING),
		.AXI_ID_WIDTH(IW),
		.DESC_MON_BASE_AGENT_ID(DESC_MON_BASE_AGENT_ID),
		.SCHED_MON_BASE_AGENT_ID(SCHED_MON_BASE_AGENT_ID),
		.DESC_AXI_MON_AGENT_ID(DESC_AXI_MON_AGENT_ID),
		.MON_UNIT_ID(MON_UNIT_ID),
		.DESC_MON_ENABLE_ERROR_LOGIC(DESC_MON_ENABLE_ERROR_LOGIC),
		.DESC_MON_ENABLE_TIMEOUT_LOGIC(DESC_MON_ENABLE_TIMEOUT_LOGIC),
		.DESC_MON_ENABLE_COMPL_LOGIC(DESC_MON_ENABLE_COMPL_LOGIC),
		.DESC_MON_ENABLE_THRESHOLD_LOGIC(DESC_MON_ENABLE_THRESHOLD_LOGIC),
		.DESC_MON_ENABLE_PERF_LOGIC(DESC_MON_ENABLE_PERF_LOGIC),
		.DESC_MON_ENABLE_DEBUG_LOGIC(DESC_MON_ENABLE_DEBUG_LOGIC)
	) u_scheduler_group_array(
		.clk(clk),
		.rst_n(rst_n),
		.cam_clear(cam_clear),
		.apb_valid(apb_valid),
		.apb_ready(apb_ready),
		.apb_addr(apb_addr),
		.cfg_channel_enable(cfg_channel_enable),
		.cfg_channel_reset(cfg_channel_reset),
		.cfg_sched_enable(cfg_sched_enable),
		.cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
		.cfg_sched_timeout_limit(cfg_sched_timeout_limit),
		.cfg_sched_timeout_enable(cfg_sched_timeout_enable),
		.cfg_sched_err_enable(cfg_sched_err_enable),
		.cfg_sched_compl_enable(cfg_sched_compl_enable),
		.cfg_sched_perf_enable(cfg_sched_perf_enable),
		.cfg_desceng_enable(cfg_desceng_enable),
		.cfg_desceng_prefetch(cfg_desceng_prefetch),
		.cfg_rd_prefetch_enable(cfg_rd_prefetch_enable),
		.cfg_desceng_fifo_thresh(cfg_desceng_fifo_thresh),
		.cfg_desceng_addr0_base(cfg_desceng_addr0_base),
		.cfg_desceng_addr0_limit(cfg_desceng_addr0_limit),
		.cfg_desceng_addr1_base(cfg_desceng_addr1_base),
		.cfg_desceng_addr1_limit(cfg_desceng_addr1_limit),
		.cfg_desc_mon_enable(int_cfg_desc_mon_enable),
		.cfg_desc_mon_err_enable(int_cfg_desc_mon_err_enable),
		.cfg_desc_mon_perf_enable(int_cfg_desc_mon_perf_enable),
		.cfg_desc_mon_compl_enable(int_cfg_desc_mon_compl_enable),
		.cfg_desc_mon_thresh_enable(int_cfg_desc_mon_thresh_enable),
		.cfg_desc_mon_timeout_enable(int_cfg_desc_mon_timeout_enable),
		.cfg_desc_mon_timeout_cycles(int_cfg_desc_mon_timeout_cycles),
		.cfg_desc_mon_latency_thresh(int_cfg_desc_mon_latency_thresh),
		.cfg_desc_mon_pkt_mask(int_cfg_desc_mon_pkt_mask),
		.cfg_desc_mon_err_select(int_cfg_desc_mon_err_select),
		.cfg_desc_mon_err_mask(int_cfg_desc_mon_err_mask),
		.cfg_desc_mon_timeout_mask(int_cfg_desc_mon_timeout_mask),
		.cfg_desc_mon_compl_mask(int_cfg_desc_mon_compl_mask),
		.cfg_desc_mon_thresh_mask(int_cfg_desc_mon_thresh_mask),
		.cfg_desc_mon_perf_mask(int_cfg_desc_mon_perf_mask),
		.cfg_desc_mon_addr_mask(int_cfg_desc_mon_addr_mask),
		.cfg_desc_mon_debug_mask(int_cfg_desc_mon_debug_mask),
		.cfg_desc_mon_perf_run(int_cfg_desc_mon_perf_run),
		.descriptor_engine_idle(descriptor_engine_idle),
		.scheduler_idle(scheduler_idle),
		.scheduler_state(scheduler_state),
		.sched_error(sched_error),
		.dbg_descriptor_error(dbg_sched_desc_error),
		.dbg_read_error_sticky(dbg_sched_rd_sticky),
		.dbg_write_error_sticky(dbg_sched_wr_sticky),
		.dbg_timeout_expired(dbg_sched_timeout),
		.cfg_sts_desc_mon_busy(cfg_sts_desc_mon_busy),
		.cfg_sts_desc_mon_active_txns(cfg_sts_desc_mon_active_txns),
		.cfg_sts_desc_mon_error_count(cfg_sts_desc_mon_error_count),
		.cfg_sts_desc_mon_txn_count(cfg_sts_desc_mon_txn_count),
		.cfg_sts_desc_mon_conflict_error(cfg_sts_desc_mon_conflict_error),
		.perf_window_active(perf_window_active),
		.perf_window_cycles(perf_window_cycles),
		.perf_prod_cycles(perf_prod_cycles),
		.perf_bp_cycles(perf_bp_cycles),
		.perf_starv_cycles(perf_starv_cycles),
		.perf_idle_cycles(perf_idle_cycles),
		.perf_beat_count(perf_beat_count),
		.perf_byte_count(perf_byte_count),
		.perf_burst_count(perf_burst_count),
		.desc_axi_arvalid(m_axi_desc_arvalid),
		.desc_axi_arready(m_axi_desc_arready),
		.desc_axi_araddr(m_axi_desc_araddr),
		.desc_axi_arlen(m_axi_desc_arlen),
		.desc_axi_arsize(m_axi_desc_arsize),
		.desc_axi_arburst(m_axi_desc_arburst),
		.desc_axi_arid(m_axi_desc_arid),
		.desc_axi_arlock(m_axi_desc_arlock),
		.desc_axi_arcache(m_axi_desc_arcache),
		.desc_axi_arprot(m_axi_desc_arprot),
		.desc_axi_arqos(m_axi_desc_arqos),
		.desc_axi_arregion(m_axi_desc_arregion),
		.desc_axi_rvalid(m_axi_desc_rvalid),
		.desc_axi_rready(m_axi_desc_rready),
		.desc_axi_rdata(m_axi_desc_rdata),
		.desc_axi_rresp(m_axi_desc_rresp),
		.desc_axi_rlast(m_axi_desc_rlast),
		.desc_axi_rid(m_axi_desc_rid),
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
		.mon_valid(schedgrp_mon_valid),
		.mon_ready(schedgrp_mon_ready),
		.mon_packet(schedgrp_mon_packet),
		.mon_timestamp(schedgrp_mon_timestamp)
	);
	localparam signed [31:0] MON_CLIENTS = 3;
	wire [0:2] mon_arb_valid_in;
	wire [0:2] mon_arb_ready_in;
	wire [(MON_CLIENTS * monitor_common_pkg_MONBUS_PKT_WIDTH) - 1:0] mon_arb_packet_in;
	wire [(MON_CLIENTS * monitor_common_pkg_MONBUS_TS_WIDTH) - 1:0] mon_arb_ts_in;
	assign mon_arb_valid_in[0] = schedgrp_mon_valid;
	assign mon_arb_packet_in[256+:monitor_common_pkg_MONBUS_PKT_WIDTH] = schedgrp_mon_packet;
	assign mon_arb_ts_in[128+:monitor_common_pkg_MONBUS_TS_WIDTH] = schedgrp_mon_timestamp;
	assign schedgrp_mon_ready = mon_arb_ready_in[0];
	assign mon_arb_valid_in[1] = rdmon_mon_valid;
	assign mon_arb_packet_in[128+:monitor_common_pkg_MONBUS_PKT_WIDTH] = rdmon_mon_packet;
	assign mon_arb_ts_in[64+:monitor_common_pkg_MONBUS_TS_WIDTH] = rdmon_mon_timestamp;
	assign rdmon_mon_ready = mon_arb_ready_in[1];
	assign mon_arb_valid_in[2] = wrmon_mon_valid;
	assign mon_arb_packet_in[0+:monitor_common_pkg_MONBUS_PKT_WIDTH] = wrmon_mon_packet;
	assign mon_arb_ts_in[0+:monitor_common_pkg_MONBUS_TS_WIDTH] = wrmon_mon_timestamp;
	assign wrmon_mon_ready = mon_arb_ready_in[2];
	monbus_arbiter #(
		.CLIENTS(MON_CLIENTS),
		.INPUT_SKID_ENABLE(1),
		.OUTPUT_SKID_ENABLE(1),
		.INPUT_SKID_DEPTH(2),
		.OUTPUT_SKID_DEPTH(2)
	) u_mon_arbiter(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.block_arb(1'b0),
		.monbus_valid_in(mon_arb_valid_in),
		.monbus_ready_in(mon_arb_ready_in),
		.monbus_packet_in(mon_arb_packet_in),
		.monbus_timestamp_in(mon_arb_ts_in),
		.monbus_valid(mon_valid),
		.monbus_ready(mon_ready),
		.monbus_packet(mon_packet),
		.monbus_timestamp(mon_timestamp),
		.grant_valid(),
		.grant(),
		.grant_id(),
		.last_grant()
	);
	wire w_rd_data_beat = m_axi_rd_rvalid & m_axi_rd_rready;
	wire w_wr_data_beat = m_axi_wr_wvalid & m_axi_wr_wready;
	wire w_rd_outstanding = |(~axi_rd_all_complete & cfg_channel_enable);
	wire w_wr_outstanding = |(~axi_wr_all_complete & cfg_channel_enable);
	localparam [31:0] PERF_SETTLE = 16;
	wire w_perf_run_any;
	wire w_perf_dma_busy;
	reg r_perf_armed;
	reg r_perf_started;
	reg r_perf_win_active;
	wire w_perf_begin;
	reg [4:0] r_perf_settle;
	wire w_perf_close;
	wire w_perf_clear;
	assign w_perf_run_any = int_cfg_rdeng_mon_perf_run | int_cfg_wreng_mon_perf_run;
	assign w_perf_dma_busy = (((|(~scheduler_idle & cfg_channel_enable) | w_rd_outstanding) | w_wr_outstanding) | w_rd_data_beat) | w_wr_data_beat;
	assign w_perf_begin = ((w_perf_run_any & w_perf_dma_busy) & ~r_perf_win_active) & ~r_perf_started;
	assign w_perf_clear = w_perf_begin;
	assign w_perf_close = r_perf_win_active & ((~w_perf_dma_busy & (r_perf_settle == PERF_SETTLE[4:0])) | ~w_perf_run_any);
	always @(posedge clk)
		if (!rst_n) begin
			r_perf_armed <= 1'b0;
			r_perf_started <= 1'b0;
			r_perf_win_active <= 1'b0;
			r_perf_settle <= 5'd0;
		end
		else begin
			r_perf_armed <= w_perf_run_any;
			if (!w_perf_run_any) begin
				r_perf_started <= 1'b0;
				r_perf_win_active <= 1'b0;
				r_perf_settle <= 5'd0;
			end
			else if (w_perf_begin) begin
				r_perf_win_active <= 1'b1;
				r_perf_started <= 1'b1;
				r_perf_settle <= 5'd0;
			end
			else if (r_perf_win_active) begin
				if (w_perf_dma_busy)
					r_perf_settle <= 5'd0;
				else if (r_perf_settle != PERF_SETTLE[4:0])
					r_perf_settle <= r_perf_settle + 5'd1;
				if (w_perf_close)
					r_perf_win_active <= 1'b0;
			end
		end
	reg r_rd_beat_seen;
	reg r_wr_beat_seen;
	wire w_rd_bucket_en = (r_perf_win_active & (r_rd_beat_seen | w_rd_data_beat)) & (w_rd_outstanding | w_rd_data_beat);
	wire w_wr_bucket_en = (r_perf_win_active & (r_wr_beat_seen | w_wr_data_beat)) & (w_wr_outstanding | w_wr_data_beat);
	always @(posedge clk)
		if (!rst_n) begin
			r_rd_beat_seen <= 1'b0;
			r_wr_beat_seen <= 1'b0;
		end
		else if (!r_perf_win_active) begin
			r_rd_beat_seen <= 1'b0;
			r_wr_beat_seen <= 1'b0;
		end
		else begin
			if (w_rd_data_beat)
				r_rd_beat_seen <= 1'b1;
			if (w_wr_data_beat)
				r_wr_beat_seen <= 1'b1;
		end
	wire [31:0] w_rd_mon_prod_nc;
	wire [31:0] w_rd_mon_bp_nc;
	wire [31:0] w_rd_mon_starv_nc;
	wire [31:0] w_rd_mon_idle_nc;
	wire [31:0] w_wr_mon_prod_nc;
	wire [31:0] w_wr_mon_bp_nc;
	wire [31:0] w_wr_mon_starv_nc;
	wire [31:0] w_wr_mon_idle_nc;
	wire w_rd_mon_winact_nc;
	wire w_wr_mon_winact_nc;
	wire [31:0] w_rd_mon_wincyc_nc;
	wire [31:0] w_wr_mon_wincyc_nc;
	wire [31:0] w_rd_mon_beat_nc;
	wire [31:0] w_wr_mon_beat_nc;
	wire [63:0] w_rd_mon_byte_nc;
	wire [63:0] w_wr_mon_byte_nc;
	wire [31:0] w_rd_mon_burst_nc;
	wire [31:0] w_wr_mon_burst_nc;
	axi_read_engine #(
		.NUM_CHANNELS(NC),
		.ADDR_WIDTH(AW),
		.DATA_WIDTH(DW),
		.ID_WIDTH(IW),
		.SEG_COUNT_WIDTH($clog2(FIFO_DEPTH) + 1),
		.PIPELINE(1),
		.AR_MAX_OUTSTANDING(AR_MAX_OUTSTANDING),
		.STROBE_EVERY_BEAT(0)
	) u_axi_read_engine(
		.clk(clk),
		.rst_n(rst_n),
		.cfg_axi_rd_xfer_beats(cfg_axi_rd_xfer_beats),
		.sched_rd_valid(sched_rd_valid),
		.sched_rd_addr(sched_rd_addr),
		.sched_rd_beats(sched_rd_beats),
		.m_axi_arid(fub_rd_axi_arid),
		.m_axi_araddr(fub_rd_axi_araddr),
		.m_axi_arlen(fub_rd_axi_arlen),
		.m_axi_arsize(fub_rd_axi_arsize),
		.m_axi_arburst(fub_rd_axi_arburst),
		.m_axi_arvalid(fub_rd_axi_arvalid),
		.m_axi_arready(fub_rd_axi_arready),
		.m_axi_rid(fub_rd_axi_rid),
		.m_axi_rdata(fub_rd_axi_rdata),
		.m_axi_rresp(fub_rd_axi_rresp),
		.m_axi_rlast(fub_rd_axi_rlast),
		.m_axi_rvalid(fub_rd_axi_rvalid),
		.m_axi_rready(fub_rd_axi_rready),
		.axi_rd_alloc_req(axi_rd_alloc_req),
		.axi_rd_alloc_size(axi_rd_alloc_size),
		.axi_rd_alloc_id(axi_rd_alloc_id),
		.axi_rd_alloc_space_free(axi_rd_space_free),
		.axi_rd_sram_valid(axi_rd_sram_valid),
		.axi_rd_sram_ready(axi_rd_sram_ready),
		.axi_rd_sram_id(axi_rd_sram_id),
		.axi_rd_sram_data(axi_rd_sram_data),
		.sched_rd_done_strobe(sched_rd_done_strobe),
		.sched_rd_beats_done(sched_rd_beats_done),
		.dbg_rd_all_complete(axi_rd_all_complete),
		.sched_rd_error(sched_rd_error),
		.dbg_r_beats_rcvd(),
		.dbg_sram_writes(),
		.dbg_arb_request()
	);
	axi_write_engine #(
		.NUM_CHANNELS(NC),
		.ADDR_WIDTH(AW),
		.DATA_WIDTH(DW),
		.ID_WIDTH(IW),
		.USER_WIDTH(UW),
		.SEG_COUNT_WIDTH($clog2(FIFO_DEPTH) + 1),
		.PIPELINE(1),
		.AW_MAX_OUTSTANDING(AW_MAX_OUTSTANDING)
	) u_axi_write_engine(
		.clk(clk),
		.rst_n(rst_n),
		.cfg_axi_wr_xfer_beats(cfg_axi_wr_xfer_beats),
		.sched_wr_valid(sched_wr_valid),
		.sched_wr_ready(sched_wr_ready),
		.sched_wr_addr(sched_wr_addr),
		.sched_wr_beats(sched_wr_beats),
		.sched_wr_burst_len({NC {cfg_axi_wr_xfer_beats}}),
		.axi_wr_drain_req(axi_wr_drain_req),
		.axi_wr_drain_size(axi_wr_drain_size),
		.axi_wr_drain_data_avail(axi_wr_drain_data_avail),
		.m_axi_awid(fub_wr_axi_awid),
		.m_axi_awaddr(fub_wr_axi_awaddr),
		.m_axi_awlen(fub_wr_axi_awlen),
		.m_axi_awsize(fub_wr_axi_awsize),
		.m_axi_awburst(fub_wr_axi_awburst),
		.m_axi_awvalid(fub_wr_axi_awvalid),
		.m_axi_awready(fub_wr_axi_awready),
		.m_axi_wdata(fub_wr_axi_wdata),
		.m_axi_wstrb(fub_wr_axi_wstrb),
		.m_axi_wlast(fub_wr_axi_wlast),
		.m_axi_wuser(fub_wr_axi_wuser),
		.m_axi_wvalid(fub_wr_axi_wvalid),
		.m_axi_wready(fub_wr_axi_wready),
		.m_axi_bid(fub_wr_axi_bid),
		.m_axi_bresp(fub_wr_axi_bresp),
		.m_axi_bvalid(fub_wr_axi_bvalid),
		.m_axi_bready(fub_wr_axi_bready),
		.axi_wr_sram_valid(axi_wr_sram_valid),
		.axi_wr_sram_valid_comb(axi_wr_sram_valid_comb),
		.axi_wr_sram_drain(axi_wr_sram_drain),
		.axi_wr_sram_id(axi_wr_sram_id),
		.axi_wr_sram_data(axi_wr_sram_data),
		.sched_wr_done_strobe(sched_wr_done_strobe),
		.sched_wr_beats_done(sched_wr_beats_done),
		.sched_wr_commit_strobe(sched_wr_commit_strobe),
		.sched_wr_commit_beats(sched_wr_commit_beats),
		.dbg_wr_all_complete(axi_wr_all_complete),
		.sched_wr_error(sched_wr_error),
		.dbg_aw_transactions(),
		.dbg_w_beats(),
		.o_active_channel_id(wr_active_channel_id),
		.o_active_channel_valid(wr_active_channel_valid)
	);
	sram_controller #(
		.NUM_CHANNELS(NC),
		.DATA_WIDTH(DW),
		.SRAM_DEPTH(FIFO_DEPTH)
	) u_sram_controller(
		.clk(clk),
		.rst_n(rst_n),
		.axi_rd_sram_valid(axi_rd_sram_valid),
		.axi_rd_sram_id(axi_rd_sram_id[CHAN_WIDTH - 1:0]),
		.axi_rd_sram_ready(axi_rd_sram_ready),
		.axi_rd_sram_data(axi_rd_sram_data),
		.axi_rd_alloc_req(axi_rd_alloc_req),
		.axi_rd_alloc_size(axi_rd_alloc_size),
		.axi_rd_alloc_id(axi_rd_alloc_id[CHAN_WIDTH - 1:0]),
		.axi_rd_alloc_space_free(axi_rd_space_free),
		.axi_wr_drain_req(axi_wr_drain_req),
		.axi_wr_drain_size(axi_wr_drain_size),
		.axi_wr_drain_data_avail(axi_wr_drain_data_avail),
		.axi_wr_sram_valid(axi_wr_sram_valid),
		.axi_wr_sram_valid_comb(axi_wr_sram_valid_comb),
		.axi_wr_sram_drain(axi_wr_sram_drain),
		.axi_wr_sram_id(axi_wr_sram_id),
		.axi_wr_sram_data(axi_wr_sram_data),
		.dbg_bridge_pending(),
		.dbg_bridge_out_valid()
	);
	perf_profiler #(
		.NUM_CHANNELS(NC),
		.CHANNEL_WIDTH(CHAN_WIDTH),
		.TIMESTAMP_WIDTH(32),
		.FIFO_DEPTH(256)
	) u_perf_profiler(
		.clk(clk),
		.rst_n(rst_n),
		.channel_idle(scheduler_idle),
		.cfg_enable(cfg_perf_enable),
		.cfg_mode(cfg_perf_mode),
		.cfg_clear(cfg_perf_clear),
		.perf_fifo_rd(perf_fifo_rd),
		.perf_fifo_data_low(perf_fifo_data_low),
		.perf_fifo_data_high(perf_fifo_data_high),
		.perf_fifo_empty(perf_fifo_empty),
		.perf_fifo_full(perf_fifo_full),
		.perf_fifo_count(perf_fifo_count)
	);
	assign fub_rd_axi_arlock = 1'b0;
	assign fub_rd_axi_arcache = 4'h0;
	assign fub_rd_axi_arprot = 3'h0;
	assign fub_rd_axi_arqos = 4'h0;
	assign fub_rd_axi_arregion = 4'h0;
	function automatic [UW - 1:0] sv2v_cast_FDCE5;
		input reg [UW - 1:0] inp;
		sv2v_cast_FDCE5 = inp;
	endfunction
	assign fub_rd_axi_aruser = sv2v_cast_FDCE5(fub_rd_axi_arid);
	localparam signed [31:0] NAR = (N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1);
	reg [(NAR * AW) - 1:0] w_rdmon_range_low;
	reg [(NAR * AW) - 1:0] w_rdmon_range_high;
	reg [(NAR * AW) - 1:0] w_wrmon_range_low;
	reg [(NAR * AW) - 1:0] w_wrmon_range_high;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] gi;
			for (gi = 0; gi < NAR; gi = gi + 1)
				begin
					w_rdmon_range_low[gi * AW+:AW] = {{AW - 32 {1'b0}}, cfg_rdeng_mon_addr_range_low[gi * 32+:32]};
					w_rdmon_range_high[gi * AW+:AW] = {{AW - 32 {1'b0}}, cfg_rdeng_mon_addr_range_high[gi * 32+:32]};
					w_wrmon_range_low[gi * AW+:AW] = {{AW - 32 {1'b0}}, cfg_wreng_mon_addr_range_low[gi * 32+:32]};
					w_wrmon_range_high[gi * AW+:AW] = {{AW - 32 {1'b0}}, cfg_wreng_mon_addr_range_high[gi * 32+:32]};
				end
		end
	end
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	axi4_master_rd_mon #(
		.SKID_DEPTH_AR(SKID_DEPTH_AR),
		.SKID_DEPTH_R(SKID_DEPTH_R),
		.AXI_ID_WIDTH(IW),
		.AXI_ADDR_WIDTH(AW),
		.AXI_DATA_WIDTH(DW),
		.AXI_USER_WIDTH(UW),
		.USE_MONITOR(USE_AXI_MONITORS == 1),
		.UNIT_ID(MON_UNIT_ID),
		.AGENT_ID(RD_AXI_MON_AGENT_ID),
		.MAX_TRANSACTIONS(RD_MON_MAX_TRANS),
		.NUM_BANKS(MON_NUM_BANKS),
		.ENABLE_FILTERING(1),
		.ENABLE_ERROR_LOGIC(DATA_MON_ENABLE_ERROR_LOGIC),
		.ENABLE_TIMEOUT_LOGIC(DATA_MON_ENABLE_TIMEOUT_LOGIC),
		.ENABLE_COMPL_LOGIC(DATA_MON_ENABLE_COMPL_LOGIC),
		.ENABLE_THRESHOLD_LOGIC(DATA_MON_ENABLE_THRESHOLD_LOGIC),
		.ENABLE_PERF_LOGIC(DATA_MON_ENABLE_PERF_LOGIC),
		.ENABLE_DEBUG_LOGIC(DATA_MON_ENABLE_DEBUG_LOGIC),
		.N_ADDR_RANGES(N_ADDR_RANGES),
		.ADDR_RANGE_IS_ERROR(MON_ADDR_RANGE_IS_ERROR)
	) u_rd_axi_skid(
		.aclk(clk),
		.aresetn(rst_n),
		.debug_block_ready(),
		.cam_clear(cam_clear),
		.fub_axi_arid(fub_rd_axi_arid),
		.fub_axi_araddr(fub_rd_axi_araddr),
		.fub_axi_arlen(fub_rd_axi_arlen),
		.fub_axi_arsize(fub_rd_axi_arsize),
		.fub_axi_arburst(fub_rd_axi_arburst),
		.fub_axi_arlock(fub_rd_axi_arlock),
		.fub_axi_arcache(fub_rd_axi_arcache),
		.fub_axi_arprot(fub_rd_axi_arprot),
		.fub_axi_arqos(fub_rd_axi_arqos),
		.fub_axi_arregion(fub_rd_axi_arregion),
		.fub_axi_aruser(fub_rd_axi_aruser),
		.fub_axi_arvalid(fub_rd_axi_arvalid),
		.fub_axi_arready(fub_rd_axi_arready),
		.fub_axi_rid(fub_rd_axi_rid),
		.fub_axi_rdata(fub_rd_axi_rdata),
		.fub_axi_rresp(fub_rd_axi_rresp),
		.fub_axi_rlast(fub_rd_axi_rlast),
		.fub_axi_ruser(fub_rd_axi_ruser),
		.fub_axi_rvalid(fub_rd_axi_rvalid),
		.fub_axi_rready(fub_rd_axi_rready),
		.m_axi_arid(m_axi_rd_arid),
		.m_axi_araddr(m_axi_rd_araddr),
		.m_axi_arlen(m_axi_rd_arlen),
		.m_axi_arsize(m_axi_rd_arsize),
		.m_axi_arburst(m_axi_rd_arburst),
		.m_axi_arlock(m_axi_rd_arlock),
		.m_axi_arcache(m_axi_rd_arcache),
		.m_axi_arprot(m_axi_rd_arprot),
		.m_axi_arqos(m_axi_rd_arqos),
		.m_axi_arregion(m_axi_rd_arregion),
		.m_axi_aruser(m_axi_rd_aruser),
		.m_axi_arvalid(m_axi_rd_arvalid),
		.m_axi_arready(m_axi_rd_arready),
		.m_axi_rid(m_axi_rd_rid),
		.m_axi_rdata(m_axi_rd_rdata),
		.m_axi_rresp(m_axi_rd_rresp),
		.m_axi_rlast(m_axi_rd_rlast),
		.m_axi_ruser(m_axi_rd_ruser),
		.m_axi_rvalid(m_axi_rd_rvalid),
		.m_axi_rready(m_axi_rd_rready),
		.cfg_monitor_enable(int_cfg_rdeng_mon_enable),
		.cfg_error_enable(int_cfg_rdeng_mon_err_enable | cfg_rdeng_mon_addr_miss_en),
		.cfg_perf_enable(int_cfg_rdeng_mon_perf_enable),
		.cfg_compl_enable(int_cfg_rdeng_mon_compl_enable),
		.cfg_threshold_enable(int_cfg_rdeng_mon_thresh_enable),
		.cfg_debug_enable(cfg_rdeng_mon_addr_match_en),
		.cfg_timeout_enable(int_cfg_rdeng_mon_timeout_enable),
		.cfg_timeout_cycles(sv2v_cast_16(int_cfg_rdeng_mon_timeout_cycles)),
		.cfg_freq_sel(4'b0000),
		.cfg_latency_threshold(int_cfg_rdeng_mon_latency_thresh),
		.cfg_axi_pkt_mask(int_cfg_rdeng_mon_pkt_mask),
		.cfg_axi_err_select(int_cfg_rdeng_mon_err_select),
		.cfg_axi_error_mask(int_cfg_rdeng_mon_err_mask),
		.cfg_axi_timeout_mask(int_cfg_rdeng_mon_timeout_mask),
		.cfg_axi_compl_mask(int_cfg_rdeng_mon_compl_mask),
		.cfg_axi_thresh_mask(int_cfg_rdeng_mon_thresh_mask),
		.cfg_axi_perf_mask(int_cfg_rdeng_mon_perf_mask),
		.cfg_axi_addr_mask(int_cfg_rdeng_mon_addr_mask),
		.cfg_axi_debug_mask(int_cfg_rdeng_mon_debug_mask),
		.cfg_addr_check_enable(cfg_rdeng_mon_addr_check_en),
		.cfg_addr_range_enable(cfg_rdeng_mon_addr_range_en[NAR - 1:0]),
		.cfg_addr_range_low(w_rdmon_range_low),
		.cfg_addr_range_high(w_rdmon_range_high),
		.cfg_start_event_sel(3'b000),
		.cfg_end_event_sel(3'b000),
		.cfg_start_trigger(w_perf_clear),
		.cfg_end_trigger(w_perf_close),
		.cfg_window_force_close(1'b0),
		.i_mon_time(i_mon_time),
		.monbus_valid(rdmon_mon_valid),
		.monbus_packet(rdmon_mon_packet),
		.monbus_timestamp(rdmon_mon_timestamp),
		.monbus_ready(rdmon_mon_ready),
		.busy(cfg_sts_rdeng_skid_busy),
		.active_transactions(cfg_sts_rdeng_mon_active_txns),
		.error_count(cfg_sts_rdeng_mon_error_count),
		.transaction_count(cfg_sts_rdeng_mon_txn_count),
		.window_active(w_rd_mon_winact_nc),
		.window_cycles(w_rd_mon_wincyc_nc),
		.perf_prod_cycles(w_rd_mon_prod_nc),
		.perf_bp_cycles(w_rd_mon_bp_nc),
		.perf_starv_cycles(w_rd_mon_starv_nc),
		.perf_idle_cycles(w_rd_mon_idle_nc),
		.perf_beat_count(w_rd_mon_beat_nc),
		.perf_byte_count(w_rd_mon_byte_nc),
		.perf_burst_count(w_rd_mon_burst_nc),
		.cfg_conflict_error(cfg_sts_rdeng_mon_conflict_error)
	);
	assign fub_wr_axi_awlock = 1'b0;
	assign fub_wr_axi_awcache = 4'h0;
	assign fub_wr_axi_awprot = 3'h0;
	assign fub_wr_axi_awqos = 4'h0;
	assign fub_wr_axi_awregion = 4'h0;
	assign fub_wr_axi_awuser = sv2v_cast_FDCE5(fub_wr_axi_awid);
	axi4_master_wr_mon #(
		.SKID_DEPTH_AW(SKID_DEPTH_AW),
		.SKID_DEPTH_W(SKID_DEPTH_W),
		.SKID_DEPTH_B(SKID_DEPTH_B),
		.AXI_ID_WIDTH(IW),
		.AXI_ADDR_WIDTH(AW),
		.AXI_DATA_WIDTH(DW),
		.AXI_USER_WIDTH(UW),
		.USE_MONITOR(USE_AXI_MONITORS == 1),
		.UNIT_ID(MON_UNIT_ID),
		.AGENT_ID(WR_AXI_MON_AGENT_ID),
		.MAX_TRANSACTIONS(WR_MON_MAX_TRANS),
		.NUM_BANKS(MON_NUM_BANKS),
		.USE_WDATA_ORDER_Q(MON_USE_WDATA_ORDER_Q),
		.ENABLE_FILTERING(1),
		.ENABLE_ERROR_LOGIC(DATA_MON_ENABLE_ERROR_LOGIC),
		.ENABLE_TIMEOUT_LOGIC(DATA_MON_ENABLE_TIMEOUT_LOGIC),
		.ENABLE_COMPL_LOGIC(DATA_MON_ENABLE_COMPL_LOGIC),
		.ENABLE_THRESHOLD_LOGIC(DATA_MON_ENABLE_THRESHOLD_LOGIC),
		.ENABLE_PERF_LOGIC(DATA_MON_ENABLE_PERF_LOGIC),
		.ENABLE_DEBUG_LOGIC(DATA_MON_ENABLE_DEBUG_LOGIC),
		.N_ADDR_RANGES(N_ADDR_RANGES),
		.ADDR_RANGE_IS_ERROR(MON_ADDR_RANGE_IS_ERROR)
	) u_wr_axi_skid(
		.aclk(clk),
		.aresetn(rst_n),
		.debug_block_ready(),
		.cam_clear(cam_clear),
		.fub_axi_awid(fub_wr_axi_awid),
		.fub_axi_awaddr(fub_wr_axi_awaddr),
		.fub_axi_awlen(fub_wr_axi_awlen),
		.fub_axi_awsize(fub_wr_axi_awsize),
		.fub_axi_awburst(fub_wr_axi_awburst),
		.fub_axi_awlock(fub_wr_axi_awlock),
		.fub_axi_awcache(fub_wr_axi_awcache),
		.fub_axi_awprot(fub_wr_axi_awprot),
		.fub_axi_awqos(fub_wr_axi_awqos),
		.fub_axi_awregion(fub_wr_axi_awregion),
		.fub_axi_awuser(fub_wr_axi_awuser),
		.fub_axi_awvalid(fub_wr_axi_awvalid),
		.fub_axi_awready(fub_wr_axi_awready),
		.fub_axi_wdata(fub_wr_axi_wdata),
		.fub_axi_wstrb(fub_wr_axi_wstrb),
		.fub_axi_wlast(fub_wr_axi_wlast),
		.fub_axi_wuser(fub_wr_axi_wuser),
		.fub_axi_wvalid(fub_wr_axi_wvalid),
		.fub_axi_wready(fub_wr_axi_wready),
		.fub_axi_bid(fub_wr_axi_bid),
		.fub_axi_bresp(fub_wr_axi_bresp),
		.fub_axi_buser(fub_wr_axi_buser),
		.fub_axi_bvalid(fub_wr_axi_bvalid),
		.fub_axi_bready(fub_wr_axi_bready),
		.m_axi_awid(m_axi_wr_awid),
		.m_axi_awaddr(m_axi_wr_awaddr),
		.m_axi_awlen(m_axi_wr_awlen),
		.m_axi_awsize(m_axi_wr_awsize),
		.m_axi_awburst(m_axi_wr_awburst),
		.m_axi_awlock(m_axi_wr_awlock),
		.m_axi_awcache(m_axi_wr_awcache),
		.m_axi_awprot(m_axi_wr_awprot),
		.m_axi_awqos(m_axi_wr_awqos),
		.m_axi_awregion(m_axi_wr_awregion),
		.m_axi_awuser(m_axi_wr_awuser),
		.m_axi_awvalid(m_axi_wr_awvalid),
		.m_axi_awready(m_axi_wr_awready),
		.m_axi_wdata(m_axi_wr_wdata),
		.m_axi_wstrb(m_axi_wr_wstrb),
		.m_axi_wlast(m_axi_wr_wlast),
		.m_axi_wuser(m_axi_wr_wuser),
		.m_axi_wvalid(m_axi_wr_wvalid),
		.m_axi_wready(m_axi_wr_wready),
		.m_axi_bid(m_axi_wr_bid),
		.m_axi_bresp(m_axi_wr_bresp),
		.m_axi_buser(m_axi_wr_buser),
		.m_axi_bvalid(m_axi_wr_bvalid),
		.m_axi_bready(m_axi_wr_bready),
		.cfg_monitor_enable(int_cfg_wreng_mon_enable),
		.cfg_error_enable(int_cfg_wreng_mon_err_enable | cfg_wreng_mon_addr_miss_en),
		.cfg_perf_enable(int_cfg_wreng_mon_perf_enable),
		.cfg_compl_enable(int_cfg_wreng_mon_compl_enable),
		.cfg_threshold_enable(int_cfg_wreng_mon_thresh_enable),
		.cfg_debug_enable(cfg_wreng_mon_addr_match_en),
		.cfg_timeout_enable(int_cfg_wreng_mon_timeout_enable),
		.cfg_timeout_cycles(sv2v_cast_16(int_cfg_wreng_mon_timeout_cycles)),
		.cfg_freq_sel(4'b0000),
		.cfg_latency_threshold(int_cfg_wreng_mon_latency_thresh),
		.cfg_axi_pkt_mask(int_cfg_wreng_mon_pkt_mask),
		.cfg_axi_err_select(int_cfg_wreng_mon_err_select),
		.cfg_axi_error_mask(int_cfg_wreng_mon_err_mask),
		.cfg_axi_timeout_mask(int_cfg_wreng_mon_timeout_mask),
		.cfg_axi_compl_mask(int_cfg_wreng_mon_compl_mask),
		.cfg_axi_thresh_mask(int_cfg_wreng_mon_thresh_mask),
		.cfg_axi_perf_mask(int_cfg_wreng_mon_perf_mask),
		.cfg_axi_addr_mask(int_cfg_wreng_mon_addr_mask),
		.cfg_axi_debug_mask(int_cfg_wreng_mon_debug_mask),
		.cfg_addr_check_enable(cfg_wreng_mon_addr_check_en),
		.cfg_addr_range_enable(cfg_wreng_mon_addr_range_en[NAR - 1:0]),
		.cfg_addr_range_low(w_wrmon_range_low),
		.cfg_addr_range_high(w_wrmon_range_high),
		.cfg_start_event_sel(3'b000),
		.cfg_end_event_sel(3'b000),
		.cfg_start_trigger(w_perf_clear),
		.cfg_end_trigger(w_perf_close),
		.cfg_window_force_close(1'b0),
		.i_mon_time(i_mon_time),
		.monbus_valid(wrmon_mon_valid),
		.monbus_packet(wrmon_mon_packet),
		.monbus_timestamp(wrmon_mon_timestamp),
		.monbus_ready(wrmon_mon_ready),
		.busy(cfg_sts_wreng_skid_busy),
		.active_transactions(cfg_sts_wreng_mon_active_txns),
		.error_count(cfg_sts_wreng_mon_error_count),
		.transaction_count(cfg_sts_wreng_mon_txn_count),
		.window_active(w_wr_mon_winact_nc),
		.window_cycles(w_wr_mon_wincyc_nc),
		.perf_prod_cycles(w_wr_mon_prod_nc),
		.perf_bp_cycles(w_wr_mon_bp_nc),
		.perf_starv_cycles(w_wr_mon_starv_nc),
		.perf_idle_cycles(w_wr_mon_idle_nc),
		.perf_beat_count(w_wr_mon_beat_nc),
		.perf_byte_count(w_wr_mon_byte_nc),
		.perf_burst_count(w_wr_mon_burst_nc),
		.cfg_conflict_error(cfg_sts_wreng_mon_conflict_error)
	);
	wire [(NC * 16) - 1:0] rd_ch_prod;
	wire [(NC * 16) - 1:0] rd_ch_bp;
	wire [(NC * 16) - 1:0] rd_ch_starv;
	wire [(NC * 16) - 1:0] rd_ch_idle;
	wire [(NC * 16) - 1:0] wr_ch_prod;
	wire [(NC * 16) - 1:0] wr_ch_bp;
	wire [(NC * 16) - 1:0] wr_ch_starv;
	wire [(NC * 16) - 1:0] wr_ch_idle;
	axi_bus_meter #(.NUM_CHANNELS(NC)) u_rd_bus_meter(
		.aclk(clk),
		.aresetn(rst_n),
		.i_clear(w_perf_clear),
		.i_freeze(~w_rd_bucket_en),
		.i_valid(m_axi_rd_rvalid),
		.i_ready(m_axi_rd_rready),
		.i_channel_id(m_axi_rd_rid[CHAN_WIDTH - 1:0]),
		.i_channel_valid(m_axi_rd_rvalid),
		.o_agg_productive(rdmon_perf_prod_cycles),
		.o_agg_backpressure(rdmon_perf_bp_cycles),
		.o_agg_starvation(rdmon_perf_starv_cycles),
		.o_agg_idle(rdmon_perf_idle_cycles),
		.o_ch_productive(rd_ch_prod),
		.o_ch_backpressure(rd_ch_bp),
		.o_ch_starvation(rd_ch_starv),
		.o_ch_idle(rd_ch_idle),
		.o_ch_overflow(rdmon_ch_overflow)
	);
	axi_bus_meter #(.NUM_CHANNELS(NC)) u_wr_bus_meter(
		.aclk(clk),
		.aresetn(rst_n),
		.i_clear(w_perf_clear),
		.i_freeze(~w_wr_bucket_en),
		.i_valid(m_axi_wr_wvalid),
		.i_ready(m_axi_wr_wready),
		.i_channel_id(wr_active_channel_id),
		.i_channel_valid(wr_active_channel_valid),
		.o_agg_productive(wrmon_perf_prod_cycles),
		.o_agg_backpressure(wrmon_perf_bp_cycles),
		.o_agg_starvation(wrmon_perf_starv_cycles),
		.o_agg_idle(wrmon_perf_idle_cycles),
		.o_ch_productive(wr_ch_prod),
		.o_ch_backpressure(wr_ch_bp),
		.o_ch_starvation(wr_ch_starv),
		.o_ch_idle(wr_ch_idle),
		.o_ch_overflow(wrmon_ch_overflow)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		rdmon_ch_prod_cycles = rd_ch_prod[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
		rdmon_ch_bp_cycles = rd_ch_bp[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
		rdmon_ch_starv_cycles = rd_ch_starv[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
		rdmon_ch_idle_cycles = rd_ch_idle[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
		wrmon_ch_prod_cycles = wr_ch_prod[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
		wrmon_ch_bp_cycles = wr_ch_bp[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
		wrmon_ch_starv_cycles = wr_ch_starv[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
		wrmon_ch_idle_cycles = wr_ch_idle[((NC - 1) - cfg_perf_ch_sel) * 16+:16];
	end
	reg [31:0] r_rd_win_cycles;
	reg [31:0] r_wr_win_cycles;
	reg [31:0] r_rd_burst_cnt;
	reg [31:0] r_wr_burst_cnt;
	assign rdmon_perf_window_active = r_perf_win_active;
	assign wrmon_perf_window_active = r_perf_win_active;
	always @(posedge clk)
		if (!rst_n) begin
			r_rd_win_cycles <= 32'h00000000;
			r_wr_win_cycles <= 32'h00000000;
			r_rd_burst_cnt <= 32'h00000000;
			r_wr_burst_cnt <= 32'h00000000;
		end
		else if (w_perf_clear) begin
			r_rd_win_cycles <= 32'h00000000;
			r_wr_win_cycles <= 32'h00000000;
			r_rd_burst_cnt <= 32'h00000000;
			r_wr_burst_cnt <= 32'h00000000;
		end
		else if (r_perf_win_active) begin
			r_rd_win_cycles <= r_rd_win_cycles + 32'h00000001;
			r_wr_win_cycles <= r_wr_win_cycles + 32'h00000001;
			if (m_axi_rd_arvalid & m_axi_rd_arready)
				r_rd_burst_cnt <= r_rd_burst_cnt + 32'h00000001;
			if (m_axi_wr_awvalid & m_axi_wr_awready)
				r_wr_burst_cnt <= r_wr_burst_cnt + 32'h00000001;
		end
	assign rdmon_perf_window_cycles = r_rd_win_cycles;
	assign wrmon_perf_window_cycles = r_wr_win_cycles;
	assign rdmon_perf_burst_count = r_rd_burst_cnt;
	assign wrmon_perf_burst_count = r_wr_burst_cnt;
	assign rdmon_perf_beat_count = rdmon_perf_prod_cycles;
	assign wrmon_perf_beat_count = wrmon_perf_prod_cycles;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	assign rdmon_perf_byte_count = sv2v_cast_64(rdmon_perf_beat_count) * (DW / 8);
	assign wrmon_perf_byte_count = sv2v_cast_64(wrmon_perf_beat_count) * (DW / 8);
	generate
		if (USE_AXI_MONITORS == 1) begin : g_perf_hist
			wire [31:0] rd_hist_count;
			wire [31:0] rd_hist_total;
			wire [31:0] wr_hist_count;
			wire [31:0] wr_hist_total;
			axi_perf_latency_hist #(
				.ID_WIDTH(IW),
				.NUM_CHANNELS(NC),
				.MAX_OUTSTANDING(AR_MAX_OUTSTANDING),
				.NUM_BINS(16),
				.IS_READ(1'b1)
			) u_rd_lat_hist(
				.aclk(clk),
				.aresetn(rst_n),
				.o_cmd_block(),
				.i_clear(w_perf_clear),
				.i_freeze(~r_perf_win_active),
				.cmd_valid(m_axi_rd_arvalid),
				.cmd_ready(m_axi_rd_arready),
				.cmd_id(m_axi_rd_arid),
				.data_valid(m_axi_rd_rvalid),
				.data_ready(m_axi_rd_rready),
				.data_last(m_axi_rd_rlast),
				.data_id(m_axi_rd_rid),
				.resp_valid(1'b0),
				.resp_ready(1'b0),
				.resp_id(1'sb0),
				.i_hist_metric(cfg_perf_hist_metric),
				.i_hist_bin(cfg_perf_hist_bin),
				.o_hist_count(rd_hist_count),
				.o_hist_total(rd_hist_total)
			);
			axi_perf_latency_hist #(
				.ID_WIDTH(IW),
				.NUM_CHANNELS(NC),
				.MAX_OUTSTANDING(AW_MAX_OUTSTANDING),
				.NUM_BINS(16),
				.IS_READ(1'b0)
			) u_wr_lat_hist(
				.aclk(clk),
				.aresetn(rst_n),
				.o_cmd_block(),
				.i_clear(w_perf_clear),
				.i_freeze(~r_perf_win_active),
				.cmd_valid(m_axi_wr_awvalid),
				.cmd_ready(m_axi_wr_awready),
				.cmd_id(m_axi_wr_awid),
				.data_valid(1'b0),
				.data_ready(1'b0),
				.data_last(1'b0),
				.data_id(1'sb0),
				.resp_valid(m_axi_wr_bvalid),
				.resp_ready(m_axi_wr_bready),
				.resp_id(m_axi_wr_bid),
				.i_hist_metric(cfg_perf_hist_metric),
				.i_hist_bin(cfg_perf_hist_bin),
				.o_hist_count(wr_hist_count),
				.o_hist_total(wr_hist_total)
			);
			assign perf_hist_data = (cfg_perf_hist_bus ? wr_hist_count : rd_hist_count);
			assign perf_hist_total = (cfg_perf_hist_bus ? wr_hist_total : rd_hist_total);
		end
		else begin : g_no_perf_hist
			assign perf_hist_data = 32'h00000000;
			assign perf_hist_total = 32'h00000000;
		end
	endgenerate
	assign system_idle = &scheduler_idle;
	localparam signed [31:0] OBS_CW = (NC > 1 ? $clog2(NC) : 1);
	wire [OBS_CW - 1:0] w_obs_ch;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [OBS_CW - 1:0] sv2v_cast_F71C6;
		input reg [OBS_CW - 1:0] inp;
		sv2v_cast_F71C6 = inp;
	endfunction
	assign w_obs_ch = (sv2v_cast_32(cfg_obs_ch_sel) < NC ? sv2v_cast_F71C6(cfg_obs_ch_sel) : {OBS_CW {1'sb0}});
	always @(*) begin
		if (_sv2v_0)
			;
		obs_flags = 1'sb0;
		obs_flags[6:0] = scheduler_state[w_obs_ch * 7+:7];
		obs_flags[7] = sched_rd_valid[w_obs_ch];
		obs_flags[8] = sched_wr_valid[w_obs_ch];
		obs_flags[9] = sched_wr_ready[w_obs_ch];
		obs_flags[10] = sched_rd_error[w_obs_ch];
		obs_flags[11] = sched_wr_error[w_obs_ch];
		obs_flags[12] = sched_error[w_obs_ch];
		obs_flags[13] = descriptor_engine_idle[w_obs_ch];
		obs_flags[14] = scheduler_idle[w_obs_ch];
		obs_flags[15] = cfg_channel_enable[w_obs_ch];
		obs_flags[16] = axi_rd_all_complete[w_obs_ch];
		obs_flags[17] = axi_wr_all_complete[w_obs_ch];
		obs_flags[18] = dbg_sched_desc_error[w_obs_ch];
		obs_flags[19] = dbg_sched_rd_sticky[w_obs_ch];
		obs_flags[20] = dbg_sched_wr_sticky[w_obs_ch];
		obs_flags[21] = dbg_sched_timeout[w_obs_ch];
	end
	always @(*) begin
		if (_sv2v_0)
			;
		obs_data0 = 1'sb0;
		obs_data1 = 1'sb0;
		case (cfg_obs_cat_sel)
			2'd0: begin
				obs_data0 = sched_rd_beats[w_obs_ch * 32+:32];
				obs_data1 = sched_wr_beats[w_obs_ch * 32+:32];
			end
			2'd1: begin
				obs_data0 = sched_rd_addr[(w_obs_ch * AW) + 31-:32];
				obs_data1 = (AW > 32 ? sv2v_cast_32(sched_rd_addr[w_obs_ch * AW+:AW] >> 32) : 32'h00000000);
			end
			2'd2: begin
				obs_data0 = sched_wr_addr[(w_obs_ch * AW) + 31-:32];
				obs_data1 = (AW > 32 ? sv2v_cast_32(sched_wr_addr[w_obs_ch * AW+:AW] >> 32) : 32'h00000000);
			end
			2'd3: begin
				obs_data0 = {{32 - ($clog2(FIFO_DEPTH) + 1) {1'b0}}, axi_rd_space_free[(($clog2(FIFO_DEPTH) + 0) >= 0 ? 0 : $clog2(FIFO_DEPTH) + 0) + (w_obs_ch * (($clog2(FIFO_DEPTH) + 0) >= 0 ? $clog2(FIFO_DEPTH) + 1 : 1 - ($clog2(FIFO_DEPTH) + 0)))+:(($clog2(FIFO_DEPTH) + 0) >= 0 ? $clog2(FIFO_DEPTH) + 1 : 1 - ($clog2(FIFO_DEPTH) + 0))]};
				obs_data1 = {{32 - ($clog2(FIFO_DEPTH) + 1) {1'b0}}, axi_wr_drain_data_avail[(($clog2(FIFO_DEPTH) + 0) >= 0 ? 0 : $clog2(FIFO_DEPTH) + 0) + (w_obs_ch * (($clog2(FIFO_DEPTH) + 0) >= 0 ? $clog2(FIFO_DEPTH) + 1 : 1 - ($clog2(FIFO_DEPTH) + 0)))+:(($clog2(FIFO_DEPTH) + 0) >= 0 ? $clog2(FIFO_DEPTH) + 1 : 1 - ($clog2(FIFO_DEPTH) + 0))]};
			end
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
