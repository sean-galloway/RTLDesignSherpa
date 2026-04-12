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
	trans_table,
	active_count,
	state_change
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	input wire aclk;
	input wire aresetn;
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
	output wire [(MAX_TRANSACTIONS * 281) - 1:0] trans_table;
	output wire [7:0] active_count;
	output wire [MAX_TRANSACTIONS - 1:0] state_change;
	reg [(MAX_TRANSACTIONS * 281) - 1:0] r_trans_table;
	reg [(MAX_TRANSACTIONS * 281) - 1:0] r_trans_table_prev;
	assign trans_table = r_trans_table;
	reg [7:0] r_active_count;
	assign active_count = r_active_count;
	reg [MAX_TRANSACTIONS - 1:0] r_state_change;
	assign state_change = r_state_change;
	localparam signed [31:0] ADDR_PAD_BITS = (AW > 32 ? 0 : 32 - AW);
	localparam [0:0] ADDR_NEEDS_TRUNC = AW > 32;
	reg signed [31:0] w_addr_trans_idx;
	reg signed [31:0] w_addr_free_idx;
	reg signed [31:0] w_data_trans_idx;
	reg signed [31:0] w_data_free_idx;
	reg signed [31:0] w_resp_trans_idx;
	reg w_addr_will_alloc;
	reg w_data_will_alloc_orphan;
	reg signed [31:0] w_resp_free_idx;
	reg [5:0] w_addr_chan_idx;
	reg [MAX_TRANSACTIONS - 1:0] w_can_cleanup;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_trans_idx = -1;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (((w_addr_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] == cmd_id))
					w_addr_trans_idx = idx;
		end
		w_addr_free_idx = -1;
		begin : sv2v_autoblock_2
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((w_addr_free_idx == -1) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280])
					w_addr_free_idx = idx;
		end
		w_addr_chan_idx = (IS_AXI ? {24'h000000, cmd_id} % 64 : 0);
		if (IS_READ) begin
			w_data_trans_idx = -1;
			begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (((w_data_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] == data_id))
						w_data_trans_idx = idx;
			end
		end
		else begin
			w_data_trans_idx = -1;
			begin : sv2v_autoblock_4
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (((((w_data_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && ((r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h1) || (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h2))) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 279]) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 277])
						w_data_trans_idx = idx;
			end
		end
		w_addr_will_alloc = (cmd_valid && (w_addr_trans_idx < 0)) && (w_addr_free_idx >= 0);
		w_data_free_idx = -1;
		begin : sv2v_autoblock_5
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (((w_data_free_idx == -1) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && !(w_addr_will_alloc && (idx == w_addr_free_idx)))
					w_data_free_idx = idx;
		end
		if (IS_READ)
			w_data_will_alloc_orphan = ((data_valid && data_ready) && (w_data_trans_idx < 0)) && (w_data_free_idx >= 0);
		else
			w_data_will_alloc_orphan = (((data_valid && data_ready) && !IS_AXI) && (w_data_trans_idx < 0)) && (w_data_free_idx >= 0);
		if (!IS_READ) begin
			w_resp_trans_idx = -1;
			begin : sv2v_autoblock_6
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (((w_resp_trans_idx == -1) && r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] == resp_id))
						w_resp_trans_idx = idx;
			end
			w_resp_free_idx = -1;
			begin : sv2v_autoblock_7
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if ((((w_resp_free_idx == -1) && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) && !(w_addr_will_alloc && (idx == w_addr_free_idx))) && !(w_data_will_alloc_orphan && (idx == w_data_free_idx)))
						w_resp_free_idx = idx;
			end
		end
		else begin
			w_resp_trans_idx = -1;
			w_resp_free_idx = -1;
		end
		begin : sv2v_autoblock_8
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280])
					case (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3])
						3'h3: w_can_cleanup[idx] = r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275];
						3'h4, 3'h5: w_can_cleanup[idx] = r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275];
						default: w_can_cleanup[idx] = 1'b0;
					endcase
				else
					w_can_cleanup[idx] = 1'b0;
		end
	end
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_9
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table_prev[((MAX_TRANSACTIONS - 1) - idx) * 281+:281] <= 1'sb0;
			end
			r_state_change <= 1'sb0;
		end
		else begin
			r_trans_table_prev <= r_trans_table;
			begin : sv2v_autoblock_10
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && r_trans_table_prev[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) begin
						if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] != r_trans_table_prev[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3])
							r_state_change[idx] <= 1'b1;
						else
							r_state_change[idx] <= 1'b0;
					end
					else
						r_state_change[idx] <= 1'b0;
			end
		end
	reg [7:0] w_active_delta_inc;
	reg [7:0] w_active_delta_dec;
	localparam [3:0] monitor_amba4_pkg_EVT_DATA_ORPHAN = 4'h2;
	localparam [3:0] monitor_amba4_pkg_EVT_PROTOCOL = 4'h4;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_DECERR = 4'h1;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_ORPHAN = 4'h3;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_SLVERR = 4'h0;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_11
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table[((MAX_TRANSACTIONS - 1) - idx) * 281+:281] <= 1'sb0;
			end
			r_active_count <= 1'sb0;
		end
		else begin
			w_active_delta_inc = 1'sb0;
			w_active_delta_dec = 1'sb0;
			if (cmd_valid) begin
				if ((w_addr_trans_idx < 0) && (w_addr_free_idx >= 0)) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 280] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 273-:3] <= 3'h1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 238-:8] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] <= cmd_id;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 270-:32] <= sv2v_cast_32(cmd_addr);
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 230-:8] <= cmd_len;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 222-:3] <= cmd_size;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 219-:2] <= cmd_burst;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 279] <= (cmd_ready ? 1'b1 : 1'b0);
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 211-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 278] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 277] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 276] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 3-:4] <= 4'h0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 275] <= 1'b0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 179-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 147-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 115-:32] <= timestamp;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 19-:8] <= (IS_AXI ? cmd_len + 8'h01 : 8'h01);
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 11-:8] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 217-:6] <= w_addr_chan_idx;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_free_idx) * 281) + 274] <= 1'b0;
					w_active_delta_inc = w_active_delta_inc + 1'b1;
				end
			end
			if (cmd_valid && cmd_ready) begin
				if (w_addr_trans_idx >= 0) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_trans_idx) * 281) + 279] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_trans_idx) * 281) + 211-:32] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_addr_trans_idx) * 281) + 115-:32] <= timestamp;
				end
			end
			if (data_valid && data_ready) begin
				if (IS_READ) begin
					if (w_data_trans_idx >= 0) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 278] <= 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] <= r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] + 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 179-:32] <= 1'sb0;
						if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] != 3'h4)
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h2;
						if (data_last) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 277] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 83-:32] <= timestamp;
						end
						if (data_resp[1]) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h4;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 3-:4] <= (data_resp[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
						end
						else if (data_last) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h3;
							if (ENABLE_PERF_PACKETS)
								;
						end
					end
					else if (w_data_free_idx >= 0) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 280] <= 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 273-:3] <= 3'h5;
						if (IS_AXI) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 238-:8] <= 1'sb0;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] <= data_id;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 217-:6] <= {24'h000000, data_id} % 64;
						end
						else begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 238-:8] <= 1'sb0;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 19-:8] <= 8'h01;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 217-:6] <= 6'h00;
						end
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 278] <= 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 277] <= data_last;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 11-:8] <= 8'h01;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 83-:32] <= timestamp;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_DATA_ORPHAN;
						w_active_delta_inc = w_active_delta_inc + 1'b1;
					end
				end
				else if (w_data_trans_idx >= 0) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 278] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] <= r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] + 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 179-:32] <= 1'sb0;
					if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] != 3'h4)
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 273-:3] <= 3'h2;
					if (data_last || ((r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 11-:8] + 1) == r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 19-:8])) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 277] <= 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_trans_idx) * 281) + 83-:32] <= timestamp;
						if (ENABLE_PERF_PACKETS)
							;
					end
				end
				else if (!IS_AXI && (w_data_free_idx >= 0)) begin
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 280] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 273-:3] <= 3'h5;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 238-:8] <= 1'sb0;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 278] <= 1'b1;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 277] <= data_last;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 11-:8] <= 8'h01;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 19-:8] <= 8'h01;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 83-:32] <= timestamp;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_DATA_ORPHAN;
					r_trans_table[(((MAX_TRANSACTIONS - 1) - w_data_free_idx) * 281) + 217-:6] <= 6'h00;
					w_active_delta_inc = w_active_delta_inc + 1'b1;
				end
			end
			if (!IS_READ) begin
				if (resp_valid && resp_ready) begin
					if (w_resp_trans_idx >= 0) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 276] <= 1'b1;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 51-:32] <= timestamp;
						r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 147-:32] <= 1'sb0;
						if (resp_code[1]) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h4;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 3-:4] <= (resp_code[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
						end
						else if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 277]) begin
							if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] != 3'h4) begin
								r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h3;
								if (ENABLE_PERF_PACKETS)
									;
							end
						end
						else if (r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 278]) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h4;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_PROTOCOL;
						end
						else begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 273-:3] <= 3'h4;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_trans_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_PROTOCOL;
						end
					end
					else if (w_resp_free_idx >= 0) begin
						if (IS_AXI) begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 280] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 273-:3] <= 3'h5;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 238-:8] <= 1'sb0;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + ((230 + IW) >= 231 ? 230 + IW : ((230 + IW) + ((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))) - 1)-:((230 + IW) >= 231 ? (230 + IW) - 230 : 232 - (230 + IW))] <= resp_id;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 276] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 51-:32] <= timestamp;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_RESP_ORPHAN;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 217-:6] <= resp_id % 64;
						end
						else begin
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 280] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 273-:3] <= 3'h5;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 238-:8] <= 1'sb0;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 276] <= 1'b1;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 51-:32] <= timestamp;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 3-:4] <= monitor_amba4_pkg_EVT_RESP_ORPHAN;
							r_trans_table[(((MAX_TRANSACTIONS - 1) - w_resp_free_idx) * 281) + 217-:6] <= 6'h00;
						end
						w_active_delta_inc = w_active_delta_inc + 1'b1;
					end
				end
			end
			begin : sv2v_autoblock_12
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && w_can_cleanup[idx]) begin
						r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] <= 1'b0;
						w_active_delta_dec = w_active_delta_dec + 1'b1;
					end
			end
			begin : sv2v_autoblock_13
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (i_event_reported_flags[idx] && !r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275])
						r_trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 275] <= 1'b1;
			end
			r_active_count <= (r_active_count + w_active_delta_inc) - w_active_delta_dec;
		end
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
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter [0:0] IS_READ = 1;
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 281) - 1:0] trans_table;
	input wire timer_tick;
	input wire [3:0] cfg_addr_cnt;
	input wire [3:0] cfg_data_cnt;
	input wire [3:0] cfg_resp_cnt;
	input wire cfg_timeout_enable;
	output wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	reg [280:0] r_trans_table_local [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] r_timeout_detected;
	assign timeout_detected = r_timeout_detected;
	localparam [3:0] monitor_amba4_pkg_EVT_CMD_TIMEOUT = 4'h0;
	localparam [3:0] monitor_amba4_pkg_EVT_DATA_TIMEOUT = 4'h1;
	localparam [3:0] monitor_amba4_pkg_EVT_RESP_TIMEOUT = 4'h2;
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_1
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table_local[idx] <= 1'sb0;
			end
			r_timeout_detected <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_2
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						r_trans_table_local[idx] <= trans_table[((MAX_TRANSACTIONS - 1) - idx) * 281+:281];
						if (((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h3) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h4)) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h0))
							r_timeout_detected[idx] <= 1'b0;
					end
			end
			if (timer_tick) begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table_local[idx][280] && !r_timeout_detected[idx]) begin
						if ((r_trans_table_local[idx][273-:3] == 3'h1) && !r_trans_table_local[idx][279]) begin
							r_trans_table_local[idx][211-:32] <= r_trans_table_local[idx][211-:32] + 1'b1;
							if (r_trans_table_local[idx][211-:32] >= {12'h000, cfg_addr_cnt}) begin
								r_trans_table_local[idx][273-:3] <= 3'h4;
								r_trans_table_local[idx][3-:4] <= monitor_amba4_pkg_EVT_CMD_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
						if (((((r_trans_table_local[idx][273-:3] == 3'h1) || (r_trans_table_local[idx][273-:3] == 3'h2)) && r_trans_table_local[idx][279]) && r_trans_table_local[idx][278]) && !r_trans_table_local[idx][277]) begin
							r_trans_table_local[idx][179-:32] <= r_trans_table_local[idx][179-:32] + 1'b1;
							if (r_trans_table_local[idx][179-:32] >= {12'h000, cfg_data_cnt}) begin
								r_trans_table_local[idx][273-:3] <= 3'h4;
								r_trans_table_local[idx][3-:4] <= monitor_amba4_pkg_EVT_DATA_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
						if (((!IS_READ && (r_trans_table_local[idx][273-:3] == 3'h2)) && r_trans_table_local[idx][277]) && !r_trans_table_local[idx][276]) begin
							r_trans_table_local[idx][147-:32] <= r_trans_table_local[idx][147-:32] + 1'b1;
							if (r_trans_table_local[idx][147-:32] >= {12'h000, cfg_resp_cnt}) begin
								r_trans_table_local[idx][273-:3] <= 3'h4;
								r_trans_table_local[idx][3-:4] <= monitor_amba4_pkg_EVT_RESP_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
					end
			end
		end
endmodule
module axi_monitor_reporter (
	aclk,
	aresetn,
	trans_table,
	timeout_detected,
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
	parameter signed [31:0] UNIT_ID = 9;
	parameter signed [31:0] AGENT_ID = 99;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter signed [31:0] INTR_FIFO_DEPTH = 8;
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 281) - 1:0] trans_table;
	input wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	input wire cfg_error_enable;
	input wire cfg_compl_enable;
	input wire cfg_threshold_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire cfg_debug_enable;
	input wire monbus_ready;
	output reg monbus_valid;
	output reg [63:0] monbus_packet;
	output wire [15:0] event_count;
	output wire [15:0] perf_completed_count;
	output wire [15:0] perf_error_count;
	input wire [15:0] active_trans_threshold;
	input wire [31:0] latency_threshold;
	output wire [MAX_TRANSACTIONS - 1:0] event_reported_flags;
	reg [(MAX_TRANSACTIONS * 281) - 1:0] r_trans_table_local;
	reg [MAX_TRANSACTIONS - 1:0] r_event_reported;
	assign event_reported_flags = r_event_reported;
	function automatic [37:0] sv2v_cast_38;
		input reg [37:0] inp;
		sv2v_cast_38 = inp;
	endfunction
	function automatic [37:0] pad_address;
		input reg [31:0] addr;
		pad_address = sv2v_cast_38(addr);
	endfunction
	reg r_active_threshold_crossed;
	reg r_latency_threshold_crossed;
	reg [15:0] r_event_count;
	assign event_count = r_event_count;
	reg [15:0] r_perf_completed_count;
	reg [15:0] r_perf_error_count;
	assign perf_completed_count = r_perf_completed_count;
	assign perf_error_count = r_perf_error_count;
	reg [2:0] r_perf_report_state;
	reg w_fifo_wr_valid;
	wire w_fifo_wr_ready;
	reg [51:0] w_fifo_wr_data;
	wire w_fifo_rd_valid;
	wire w_fifo_rd_ready;
	wire [51:0] w_fifo_rd_data;
	wire [$clog2(INTR_FIFO_DEPTH):0] w_fifo_count;
	gaxi_fifo_sync #(
		.REGISTERED(1),
		.DATA_WIDTH(52),
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
	reg [3:0] r_packet_type;
	reg [3:0] r_event_code;
	reg [37:0] r_event_data;
	reg [5:0] r_event_channel;
	reg [MAX_TRANSACTIONS - 1:0] w_error_events_detected;
	reg [MAX_TRANSACTIONS - 1:0] w_timeout_events_detected;
	reg [MAX_TRANSACTIONS - 1:0] w_completion_events_detected;
	reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_selected_error_idx;
	reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_selected_timeout_idx;
	reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_selected_completion_idx;
	reg w_has_error_event;
	reg w_has_timeout_event;
	reg w_has_completion_event;
	reg [MAX_TRANSACTIONS - 1:0] w_events_to_mark;
	reg [MAX_TRANSACTIONS - 1:0] w_error_events;
	reg [MAX_TRANSACTIONS - 1:0] w_completion_events;
	reg [7:0] w_active_count_current;
	reg w_active_threshold_detection;
	reg [MAX_TRANSACTIONS - 1:0] w_latency_threshold_events;
	reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_selected_latency_idx;
	reg w_has_latency_event;
	reg [31:0] w_total_latency;
	reg [31:0] w_selected_latency_value;
	reg w_generate_perf_packet_completed;
	reg w_generate_perf_packet_errors;
	reg [2:0] w_next_perf_report_state;
	always @(*) begin
		if (_sv2v_0)
			;
		w_error_events_detected = 1'sb0;
		w_selected_error_idx = 1'sb0;
		w_has_error_event = 1'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && !r_event_reported[idx]) && cfg_error_enable) && (((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h4) && !timeout_detected[idx]) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h5)))
					w_error_events_detected[idx] = 1'b1;
		end
		begin : sv2v_autoblock_2
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (w_error_events_detected[idx] && !w_has_error_event) begin
					w_selected_error_idx = idx[$clog2(MAX_TRANSACTIONS) - 1:0];
					w_has_error_event = 1'b1;
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_timeout_events_detected = 1'sb0;
		w_selected_timeout_idx = 1'sb0;
		w_has_timeout_event = 1'b0;
		begin : sv2v_autoblock_3
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && !r_event_reported[idx]) && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h4)) && cfg_timeout_enable) && timeout_detected[idx])
					w_timeout_events_detected[idx] = 1'b1;
		end
		begin : sv2v_autoblock_4
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (w_timeout_events_detected[idx] && !w_has_timeout_event) begin
					w_selected_timeout_idx = idx[$clog2(MAX_TRANSACTIONS) - 1:0];
					w_has_timeout_event = 1'b1;
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_completion_events_detected = 1'sb0;
		w_selected_completion_idx = 1'sb0;
		w_has_completion_event = 1'b0;
		begin : sv2v_autoblock_5
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && !r_event_reported[idx]) && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h3)) && cfg_compl_enable)
					w_completion_events_detected[idx] = 1'b1;
		end
		begin : sv2v_autoblock_6
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (w_completion_events_detected[idx] && !w_has_completion_event) begin
					w_selected_completion_idx = idx[$clog2(MAX_TRANSACTIONS) - 1:0];
					w_has_completion_event = 1'b1;
				end
		end
	end
	localparam [3:0] monitor_amba4_pkg_EVT_TRANS_COMPLETE = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	always @(*) begin
		if (_sv2v_0)
			;
		w_fifo_wr_valid = 1'b0;
		w_fifo_wr_data = 52'b0000000000000000000000000000000000000000000000000000;
		if (w_has_error_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeError;
			w_fifo_wr_data[47-:4] = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_error_idx) * 281) + 3-:4];
			w_fifo_wr_data[43-:6] = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_error_idx) * 281) + 217-:6];
			w_fifo_wr_data[37-:38] = pad_address(r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_error_idx) * 281) + 270-:32]);
		end
		else if (w_has_timeout_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeTimeout;
			w_fifo_wr_data[47-:4] = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_timeout_idx) * 281) + 3-:4];
			w_fifo_wr_data[43-:6] = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_timeout_idx) * 281) + 217-:6];
			w_fifo_wr_data[37-:38] = pad_address(r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_timeout_idx) * 281) + 270-:32]);
		end
		else if (w_has_completion_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeCompletion;
			w_fifo_wr_data[47-:4] = monitor_amba4_pkg_EVT_TRANS_COMPLETE;
			w_fifo_wr_data[43-:6] = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_completion_idx) * 281) + 217-:6];
			w_fifo_wr_data[37-:38] = pad_address(r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_completion_idx) * 281) + 270-:32]);
		end
	end
	assign w_fifo_rd_ready = monbus_ready && monbus_valid;
	always @(*) begin
		if (_sv2v_0)
			;
		w_events_to_mark = 1'sb0;
		w_error_events = 1'sb0;
		w_completion_events = 1'sb0;
		begin : sv2v_autoblock_7
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280]) begin
					if ((((((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h4) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h5)) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h3)) && !r_event_reported[idx]) && w_fifo_wr_valid) && w_fifo_wr_ready) begin
						w_events_to_mark[idx] = 1'b1;
						if ((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h4) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h5))
							w_error_events[idx] = 1'b1;
						else if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h3)
							w_completion_events[idx] = 1'b1;
					end
				end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_active_count_current = 1'sb0;
		begin : sv2v_autoblock_8
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] != 3'h3)) && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] != 3'h4))
					w_active_count_current = w_active_count_current + 1'b1;
		end
		w_active_threshold_detection = ((({8'h00, w_active_count_current} > active_trans_threshold) && !r_active_threshold_crossed) && !monbus_valid) && (w_fifo_rd_valid == 0);
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_latency_threshold_events = 1'sb0;
		w_selected_latency_idx = 1'sb0;
		w_has_latency_event = 1'b0;
		w_total_latency = 1'sb0;
		if ((ENABLE_PERF_PACKETS && cfg_perf_enable) && cfg_threshold_enable) begin
			begin : sv2v_autoblock_9
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280] && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 273-:3] == 3'h3)) begin
						if (IS_READ)
							w_total_latency = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 83-:32] - r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 115-:32];
						else
							w_total_latency = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 51-:32] - r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 115-:32];
						if ((w_total_latency > latency_threshold) && !r_latency_threshold_crossed)
							w_latency_threshold_events[idx] = 1'b1;
					end
			end
			begin : sv2v_autoblock_10
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (w_latency_threshold_events[idx] && !w_has_latency_event) begin
						w_selected_latency_idx = idx[$clog2(MAX_TRANSACTIONS) - 1:0];
						w_has_latency_event = 1'b1;
					end
			end
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_selected_latency_value = 1'sb0;
		if (w_has_latency_event) begin
			if (IS_READ)
				w_selected_latency_value = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_latency_idx) * 281) + 83-:32] - r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_latency_idx) * 281) + 115-:32];
			else
				w_selected_latency_value = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_latency_idx) * 281) + 51-:32] - r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_latency_idx) * 281) + 115-:32];
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_perf_report_state = 3'h0;
		w_generate_perf_packet_completed = 1'b0;
		w_generate_perf_packet_errors = 1'b0;
		if (((ENABLE_PERF_PACKETS && cfg_perf_enable) && !monbus_valid) && (w_fifo_rd_valid == 0))
			case (r_perf_report_state)
				3'h0: w_next_perf_report_state = 3'h1;
				3'h1: w_next_perf_report_state = 3'h2;
				3'h2: w_next_perf_report_state = 3'h3;
				3'h3: begin
					w_next_perf_report_state = 3'h4;
					if (r_perf_completed_count > 0)
						w_generate_perf_packet_completed = 1'b1;
				end
				3'h4: begin
					w_next_perf_report_state = 3'h0;
					if (r_perf_error_count > 0)
						w_generate_perf_packet_errors = 1'b1;
				end
				default: w_next_perf_report_state = 3'h0;
			endcase
	end
	localparam [3:0] monitor_amba4_pkg_EVT_NONE = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	always @(posedge aclk)
		if (!aresetn) begin
			r_trans_table_local <= {MAX_TRANSACTIONS {281'b0}};
			monbus_valid <= 1'b0;
			r_event_count <= 1'sb0;
			r_event_reported <= 1'sb0;
			r_perf_completed_count <= 1'sb0;
			r_perf_error_count <= 1'sb0;
			r_active_threshold_crossed <= 1'b0;
			r_latency_threshold_crossed <= 1'b0;
			r_packet_type <= monitor_common_pkg_PktTypeError;
			r_event_code <= monitor_amba4_pkg_EVT_NONE;
			r_event_data <= 1'sb0;
			r_event_channel <= 1'sb0;
			r_perf_report_state <= 3'h0;
		end
		else begin
			begin : sv2v_autoblock_11
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_trans_table_local[((MAX_TRANSACTIONS - 1) - idx) * 281+:281] <= trans_table[((MAX_TRANSACTIONS - 1) - idx) * 281+:281];
			end
			if (monbus_valid && monbus_ready)
				monbus_valid <= 1'b0;
			if (!monbus_valid && w_fifo_rd_valid) begin
				monbus_valid <= 1'b1;
				r_packet_type <= w_fifo_rd_data[51-:4];
				r_event_code <= w_fifo_rd_data[47-:4];
				r_event_data <= w_fifo_rd_data[37-:38];
				r_event_channel <= w_fifo_rd_data[43-:6];
			end
			begin : sv2v_autoblock_12
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						if (!r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 281) + 280])
							r_event_reported[idx] <= 1'b0;
						else if (w_events_to_mark[idx]) begin
							r_event_reported[idx] <= 1'b1;
							r_event_count <= r_event_count + 1'b1;
						end
						if (ENABLE_PERF_PACKETS) begin
							if (w_error_events[idx])
								r_perf_error_count <= r_perf_error_count + 1'b1;
							if (w_completion_events[idx])
								r_perf_completed_count <= r_perf_completed_count + 1'b1;
						end
					end
			end
			if (cfg_threshold_enable) begin
				if (w_active_threshold_detection) begin
					monbus_valid <= 1'b1;
					r_packet_type <= monitor_common_pkg_PktTypeThreshold;
					r_event_code <= 4'h0;
					r_event_data <= {30'h00000000, w_active_count_current};
					r_event_channel <= 1'sb0;
					r_active_threshold_crossed <= 1'b1;
					r_event_count <= r_event_count + 1'b1;
				end
				else if ({8'h00, w_active_count_current} <= active_trans_threshold)
					r_active_threshold_crossed <= 1'b0;
				if ((w_has_latency_event && !monbus_valid) && (w_fifo_rd_valid == 0)) begin
					monbus_valid <= 1'b1;
					r_packet_type <= monitor_common_pkg_PktTypeThreshold;
					r_event_code <= 4'h1;
					r_event_data <= pad_address(w_selected_latency_value);
					r_event_channel <= r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_latency_idx) * 281) + 217-:6];
					r_latency_threshold_crossed <= 1'b1;
					r_event_count <= r_event_count + 1'b1;
				end
			end
			if (w_generate_perf_packet_completed) begin
				monbus_valid <= 1'b1;
				r_packet_type <= monitor_common_pkg_PktTypePerf;
				r_event_code <= 4'h7;
				r_event_data <= {22'h000000, r_perf_completed_count};
				r_event_channel <= 1'sb0;
			end
			if (w_generate_perf_packet_errors) begin
				monbus_valid <= 1'b1;
				r_packet_type <= monitor_common_pkg_PktTypePerf;
				r_event_code <= 4'h8;
				r_event_data <= {22'h000000, r_perf_error_count};
				r_event_channel <= 1'sb0;
			end
			r_perf_report_state <= w_next_perf_report_state;
		end
	always @(*) begin
		if (_sv2v_0)
			;
		monbus_packet[63:60] = r_packet_type;
		monbus_packet[59:57] = 3'b000;
		monbus_packet[56:53] = r_event_code;
		monbus_packet[52:47] = r_event_channel;
		monbus_packet[46:43] = UNIT_ID[3:0];
		monbus_packet[42:35] = AGENT_ID[7:0];
		monbus_packet[34:0] = r_event_data[34:0];
	end
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_base (
	aclk,
	aresetn,
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
	monbus_valid,
	monbus_ready,
	monbus_packet,
	block_ready,
	busy,
	active_count
);
	reg _sv2v_0;
	parameter signed [31:0] UNIT_ID = 9;
	parameter signed [31:0] AGENT_ID = 99;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] ADDR_BITS_IN_PKT = 38;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter [0:0] ENABLE_DEBUG_MODULE = 1'b0;
	parameter signed [31:0] INTR_FIFO_DEPTH = 8;
	parameter signed [31:0] DEBUG_FIFO_DEPTH = 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	parameter signed [31:0] ADDR_BITS = (ADDR_BITS_IN_PKT > AW ? AW : ADDR_BITS_IN_PKT);
	input wire aclk;
	input wire aresetn;
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
	input wire [3:0] cfg_addr_cnt;
	input wire [3:0] cfg_data_cnt;
	input wire [3:0] cfg_resp_cnt;
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
	output reg monbus_valid;
	input wire monbus_ready;
	output reg [63:0] monbus_packet;
	output wire block_ready;
	output wire busy;
	output wire [7:0] active_count;
	wire [(MAX_TRANSACTIONS * 281) - 1:0] w_trans_table;
	wire [MAX_TRANSACTIONS - 1:0] w_event_reported_flags;
	wire [7:0] w_active_count;
	wire [15:0] w_event_count;
	wire [15:0] w_debug_count;
	wire w_timer_tick;
	wire [31:0] r_timestamp;
	wire [MAX_TRANSACTIONS - 1:0] w_state_change_detected;
	wire [MAX_TRANSACTIONS - 1:0] w_timeout_detected;
	wire w_reporter_monbus_valid;
	wire [63:0] w_reporter_monbus_packet;
	wire w_debug_monbus_valid;
	wire [63:0] w_debug_monbus_packet;
	generate
		if (!ENABLE_DEBUG_MODULE) begin : gen_no_debug
			assign w_debug_monbus_valid = 1'b0;
			assign w_debug_monbus_packet = 1'sb0;
		end
	endgenerate
	wire [15:0] r_perf_completed_count;
	wire [15:0] r_perf_error_count;
	axi_monitor_trans_mgr #(
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(ADDR_WIDTH),
		.ID_WIDTH(ID_WIDTH),
		.IS_READ(IS_READ),
		.IS_AXI(IS_AXI),
		.ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS)
	) trans_mgr(
		.aclk(aclk),
		.aresetn(aresetn),
		.cmd_valid(cmd_valid),
		.cmd_ready(cmd_ready),
		.cmd_id(cmd_id),
		.cmd_addr(cmd_addr),
		.cmd_len(cmd_len),
		.cmd_size(cmd_size),
		.cmd_burst(cmd_burst),
		.data_valid(data_valid),
		.data_ready(data_ready),
		.data_id(data_id),
		.data_last(data_last),
		.data_resp(data_resp),
		.resp_valid(resp_valid),
		.resp_ready(resp_ready),
		.resp_id(resp_id),
		.resp_code(resp_code),
		.timestamp(r_timestamp),
		.i_event_reported_flags(w_event_reported_flags),
		.trans_table(w_trans_table),
		.active_count(w_active_count),
		.state_change(w_state_change_detected)
	);
	axi_monitor_timer timer(
		.aclk(aclk),
		.aresetn(aresetn),
		.cfg_freq_sel(cfg_freq_sel),
		.timer_tick(w_timer_tick),
		.timestamp(r_timestamp)
	);
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
	axi_monitor_reporter #(
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(ADDR_WIDTH),
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.IS_READ(IS_READ),
		.ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS),
		.INTR_FIFO_DEPTH(INTR_FIFO_DEPTH)
	) reporter(
		.aclk(aclk),
		.aresetn(aresetn),
		.trans_table(w_trans_table),
		.timeout_detected(w_timeout_detected),
		.cfg_error_enable(cfg_error_enable),
		.cfg_compl_enable(cfg_compl_enable),
		.cfg_threshold_enable(cfg_threshold_enable),
		.cfg_timeout_enable(cfg_timeout_enable),
		.cfg_perf_enable(cfg_perf_enable),
		.cfg_debug_enable(cfg_debug_enable),
		.monbus_ready(monbus_ready),
		.monbus_valid(w_reporter_monbus_valid),
		.monbus_packet(w_reporter_monbus_packet),
		.event_count(w_event_count),
		.perf_completed_count(r_perf_completed_count),
		.perf_error_count(r_perf_error_count),
		.active_trans_threshold(cfg_active_trans_threshold),
		.latency_threshold(cfg_latency_threshold),
		.event_reported_flags(w_event_reported_flags)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_reporter_monbus_valid) begin
			monbus_valid = w_reporter_monbus_valid;
			monbus_packet = w_reporter_monbus_packet;
		end
		else if (w_debug_monbus_valid) begin
			monbus_valid = w_debug_monbus_valid;
			monbus_packet = w_debug_monbus_packet;
		end
		else begin
			monbus_valid = 1'b0;
			monbus_packet = 1'sb0;
		end
	end
	assign block_ready = (MAX_TRANSACTIONS > 2 ? {24'h000000, w_active_count} >= (MAX_TRANSACTIONS - 2) : 1'b0);
	assign busy = w_active_count > 0;
	assign active_count = w_active_count;
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_filtered (
	aclk,
	aresetn,
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
	monbus_valid,
	monbus_ready,
	monbus_packet,
	block_ready,
	busy,
	active_count,
	cfg_conflict_error
);
	reg _sv2v_0;
	parameter signed [31:0] UNIT_ID = 1;
	parameter signed [31:0] AGENT_ID = 10;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b1;
	parameter [0:0] ENABLE_DEBUG_MODULE = 1'b0;
	parameter [0:0] ENABLE_FILTERING = 1;
	parameter [0:0] ADD_PIPELINE_STAGE = 0;
	input wire aclk;
	input wire aresetn;
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
	input wire [3:0] cfg_addr_cnt;
	input wire [3:0] cfg_data_cnt;
	input wire [3:0] cfg_resp_cnt;
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
	output wire monbus_valid;
	input wire monbus_ready;
	output wire [63:0] monbus_packet;
	output wire block_ready;
	output wire busy;
	output wire [7:0] active_count;
	output wire cfg_conflict_error;
	wire base_monbus_valid;
	wire base_monbus_ready;
	wire [63:0] base_monbus_packet;
	wire [3:0] pkt_type;
	wire [2:0] pkt_protocol;
	wire [3:0] pkt_event_code;
	wire [34:0] pkt_event_data;
	reg pkt_drop;
	reg pkt_event_masked;
	wire pipe_valid;
	wire pipe_ready;
	wire [63:0] pipe_packet;
	assign cfg_conflict_error = |(cfg_axi_pkt_mask & cfg_axi_err_select);
	axi_monitor_base #(
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(ADDR_WIDTH),
		.ID_WIDTH(ID_WIDTH),
		.IS_READ(IS_READ),
		.IS_AXI(IS_AXI),
		.ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS),
		.ENABLE_DEBUG_MODULE(ENABLE_DEBUG_MODULE)
	) u_axi_monitor_base(
		.aclk(aclk),
		.aresetn(aresetn),
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
		.monbus_valid(base_monbus_valid),
		.monbus_ready(base_monbus_ready),
		.monbus_packet(base_monbus_packet),
		.block_ready(block_ready),
		.busy(busy),
		.active_count(active_count)
	);
	function automatic [3:0] monitor_common_pkg_get_packet_type;
		input reg [63:0] pkt;
		monitor_common_pkg_get_packet_type = pkt[63:60];
	endfunction
	assign pkt_type = monitor_common_pkg_get_packet_type(base_monbus_packet);
	assign pkt_protocol = base_monbus_packet[59:57];
	function automatic [3:0] monitor_common_pkg_get_event_code;
		input reg [63:0] pkt;
		monitor_common_pkg_get_event_code = pkt[56:53];
	endfunction
	assign pkt_event_code = monitor_common_pkg_get_event_code(base_monbus_packet);
	function automatic [34:0] monitor_common_pkg_get_event_data;
		input reg [63:0] pkt;
		monitor_common_pkg_get_event_data = pkt[34:0];
	endfunction
	assign pkt_event_data = monitor_common_pkg_get_event_data(base_monbus_packet);
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
			if (pkt_protocol == 3'b000) begin
				pkt_drop = cfg_axi_pkt_mask[pkt_type];
				if (!pkt_drop) begin
					case (pkt_type)
						monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_axi_error_mask[pkt_event_code];
						monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_axi_timeout_mask[pkt_event_code];
						monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask[pkt_event_code];
						monitor_common_pkg_PktTypeThreshold: pkt_event_masked = cfg_axi_thresh_mask[pkt_event_code];
						monitor_common_pkg_PktTypePerf: pkt_event_masked = cfg_axi_perf_mask[pkt_event_code];
						monitor_common_pkg_PktTypeAddrMatch: pkt_event_masked = cfg_axi_addr_mask[pkt_event_code];
						monitor_common_pkg_PktTypeDebug: pkt_event_masked = cfg_axi_debug_mask[pkt_event_code];
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
			reg [63:0] pipe_packet_reg;
			always @(posedge aclk)
				if (!aresetn) begin
					pipe_valid_reg <= 1'b0;
					pipe_packet_reg <= 1'sb0;
				end
				else if (pipe_ready) begin
					pipe_valid_reg <= base_monbus_valid && !pkt_drop;
					pipe_packet_reg <= base_monbus_packet;
				end
			assign pipe_valid = pipe_valid_reg;
			assign pipe_packet = pipe_packet_reg;
			assign pipe_ready = !pipe_valid || monbus_ready;
			assign monbus_valid = pipe_valid;
			assign monbus_packet = pipe_packet;
		end
		else begin : gen_no_pipeline
			assign monbus_valid = base_monbus_valid && !pkt_drop;
			assign monbus_packet = base_monbus_packet;
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
module axi4_master_rd_mon (
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
	cfg_monitor_enable,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_perf_enable,
	cfg_timeout_cycles,
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
	monbus_valid,
	monbus_ready,
	monbus_packet,
	busy,
	active_transactions,
	error_count,
	transaction_count,
	cfg_conflict_error
);
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] UNIT_ID = 32'd1;
	parameter signed [31:0] AGENT_ID = 32'd10;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter [0:0] ENABLE_FILTERING = 1;
	parameter [0:0] ADD_PIPELINE_STAGE = 0;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
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
	input wire cfg_monitor_enable;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire [15:0] cfg_timeout_cycles;
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
	output wire monbus_valid;
	input wire monbus_ready;
	output wire [63:0] monbus_packet;
	output wire busy;
	output wire [7:0] active_transactions;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
	output wire cfg_conflict_error;
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
	axi_monitor_filtered #(
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(AW),
		.ID_WIDTH(IW),
		.IS_READ(1'b1),
		.IS_AXI(1'b1),
		.ENABLE_PERF_PACKETS(1'b1),
		.ENABLE_DEBUG_MODULE(1'b0),
		.ENABLE_FILTERING(ENABLE_FILTERING),
		.ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE)
	) axi_monitor_inst(
		.aclk(aclk),
		.aresetn(aresetn),
		.cmd_addr(m_axi_araddr),
		.cmd_id(m_axi_arid),
		.cmd_len(m_axi_arlen),
		.cmd_size(m_axi_arsize),
		.cmd_burst(m_axi_arburst),
		.cmd_valid(m_axi_arvalid),
		.cmd_ready(m_axi_arready),
		.data_id(m_axi_rid),
		.data_last(m_axi_rlast),
		.data_resp(m_axi_rresp),
		.data_valid(m_axi_rvalid),
		.data_ready(m_axi_rready),
		.resp_id(m_axi_rid),
		.resp_code(m_axi_rresp),
		.resp_valid(m_axi_rvalid && m_axi_rlast),
		.resp_ready(m_axi_rready),
		.cfg_freq_sel(4'b0001),
		.cfg_addr_cnt(4'd15),
		.cfg_data_cnt(4'd15),
		.cfg_resp_cnt(4'd15),
		.cfg_error_enable(cfg_error_enable),
		.cfg_compl_enable(cfg_monitor_enable),
		.cfg_threshold_enable(cfg_perf_enable),
		.cfg_timeout_enable(cfg_timeout_enable),
		.cfg_perf_enable(cfg_perf_enable),
		.cfg_debug_enable(1'b0),
		.cfg_debug_level(4'h0),
		.cfg_debug_mask(16'h0000),
		.cfg_active_trans_threshold(16'd8),
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
		.monbus_valid(monbus_valid),
		.monbus_ready(monbus_ready),
		.monbus_packet(monbus_packet),
		.block_ready(),
		.busy(),
		.active_count(active_transactions),
		.cfg_conflict_error(cfg_conflict_error)
	);
	assign error_count = 16'h0000;
	assign transaction_count = 32'h00000000;
endmodule
module axi4_master_wr_mon (
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
	cfg_monitor_enable,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_perf_enable,
	cfg_timeout_cycles,
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
	monbus_valid,
	monbus_ready,
	monbus_packet,
	busy,
	active_transactions,
	error_count,
	transaction_count,
	cfg_conflict_error
);
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] UNIT_ID = 32'd1;
	parameter signed [31:0] AGENT_ID = 32'd11;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter [0:0] ENABLE_FILTERING = 1;
	parameter [0:0] ADD_PIPELINE_STAGE = 0;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
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
	input wire cfg_monitor_enable;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire [15:0] cfg_timeout_cycles;
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
	output wire monbus_valid;
	input wire monbus_ready;
	output wire [63:0] monbus_packet;
	output wire busy;
	output wire [7:0] active_transactions;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
	output wire cfg_conflict_error;
	axi4_master_wr #(
		.SKID_DEPTH_AW(SKID_DEPTH_AW),
		.SKID_DEPTH_W(SKID_DEPTH_W),
		.SKID_DEPTH_B(SKID_DEPTH_B),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH),
		.AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH)
	) axi4_master_wr_inst(
		.aclk(aclk),
		.aresetn(aresetn),
		.fub_axi_awid(fub_axi_awid),
		.fub_axi_awaddr(fub_axi_awaddr),
		.fub_axi_awlen(fub_axi_awlen),
		.fub_axi_awsize(fub_axi_awsize),
		.fub_axi_awburst(fub_axi_awburst),
		.fub_axi_awlock(fub_axi_awlock),
		.fub_axi_awcache(fub_axi_awcache),
		.fub_axi_awprot(fub_axi_awprot),
		.fub_axi_awqos(fub_axi_awqos),
		.fub_axi_awregion(fub_axi_awregion),
		.fub_axi_awuser(fub_axi_awuser),
		.fub_axi_awvalid(fub_axi_awvalid),
		.fub_axi_awready(fub_axi_awready),
		.fub_axi_wdata(fub_axi_wdata),
		.fub_axi_wstrb(fub_axi_wstrb),
		.fub_axi_wlast(fub_axi_wlast),
		.fub_axi_wuser(fub_axi_wuser),
		.fub_axi_wvalid(fub_axi_wvalid),
		.fub_axi_wready(fub_axi_wready),
		.fub_axi_bid(fub_axi_bid),
		.fub_axi_bresp(fub_axi_bresp),
		.fub_axi_buser(fub_axi_buser),
		.fub_axi_bvalid(fub_axi_bvalid),
		.fub_axi_bready(fub_axi_bready),
		.m_axi_awid(m_axi_awid),
		.m_axi_awaddr(m_axi_awaddr),
		.m_axi_awlen(m_axi_awlen),
		.m_axi_awsize(m_axi_awsize),
		.m_axi_awburst(m_axi_awburst),
		.m_axi_awlock(m_axi_awlock),
		.m_axi_awcache(m_axi_awcache),
		.m_axi_awprot(m_axi_awprot),
		.m_axi_awqos(m_axi_awqos),
		.m_axi_awregion(m_axi_awregion),
		.m_axi_awuser(m_axi_awuser),
		.m_axi_awvalid(m_axi_awvalid),
		.m_axi_awready(m_axi_awready),
		.m_axi_wdata(m_axi_wdata),
		.m_axi_wstrb(m_axi_wstrb),
		.m_axi_wlast(m_axi_wlast),
		.m_axi_wuser(m_axi_wuser),
		.m_axi_wvalid(m_axi_wvalid),
		.m_axi_wready(m_axi_wready),
		.m_axi_bid(m_axi_bid),
		.m_axi_bresp(m_axi_bresp),
		.m_axi_buser(m_axi_buser),
		.m_axi_bvalid(m_axi_bvalid),
		.m_axi_bready(m_axi_bready),
		.busy(busy)
	);
	axi_monitor_filtered #(
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(AW),
		.ID_WIDTH(IW),
		.IS_READ(1'b0),
		.IS_AXI(1'b1),
		.ENABLE_PERF_PACKETS(1'b1),
		.ENABLE_DEBUG_MODULE(1'b0),
		.ENABLE_FILTERING(ENABLE_FILTERING),
		.ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE)
	) axi_monitor_inst(
		.aclk(aclk),
		.aresetn(aresetn),
		.cmd_addr(m_axi_awaddr),
		.cmd_id(m_axi_awid),
		.cmd_len(m_axi_awlen),
		.cmd_size(m_axi_awsize),
		.cmd_burst(m_axi_awburst),
		.cmd_valid(m_axi_awvalid),
		.cmd_ready(m_axi_awready),
		.data_id(m_axi_awid),
		.data_last(m_axi_wlast),
		.data_resp(2'b00),
		.data_valid(m_axi_wvalid),
		.data_ready(m_axi_wready),
		.resp_id(m_axi_bid),
		.resp_code(m_axi_bresp),
		.resp_valid(m_axi_bvalid),
		.resp_ready(m_axi_bready),
		.cfg_freq_sel(4'b0001),
		.cfg_addr_cnt(4'd15),
		.cfg_data_cnt(4'd15),
		.cfg_resp_cnt(4'd15),
		.cfg_error_enable(cfg_error_enable),
		.cfg_compl_enable(cfg_monitor_enable),
		.cfg_threshold_enable(cfg_perf_enable),
		.cfg_timeout_enable(cfg_timeout_enable),
		.cfg_perf_enable(cfg_perf_enable),
		.cfg_debug_enable(1'b0),
		.cfg_debug_level(4'h0),
		.cfg_debug_mask(16'h0000),
		.cfg_active_trans_threshold(16'd8),
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
		.monbus_valid(monbus_valid),
		.monbus_ready(monbus_ready),
		.monbus_packet(monbus_packet),
		.block_ready(),
		.busy(),
		.active_count(active_transactions),
		.cfg_conflict_error(cfg_conflict_error)
	);
	assign error_count = 16'h0000;
	assign transaction_count = 32'h00000000;
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
	always @(posedge clk)
		if (!rst_n)
			;
		else if (apb_valid && !w_apb_addr_valid)
			r_descriptor_error <= 1'b1;
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
		.MEM_STYLE(32'sd0),
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
	function automatic [SCW - 1:0] sv2v_cast_14961;
		input reg [SCW - 1:0] inp;
		sv2v_cast_14961 = inp;
	endfunction
	assign axi_wr_drain_data_avail = drain_data_available + sv2v_cast_14961(bridge_occupancy);
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
	output wire [(NC * SCW) - 1:0] axi_rd_alloc_space_free;
	input wire axi_rd_sram_valid;
	output reg axi_rd_sram_ready;
	input wire [CIW - 1:0] axi_rd_sram_id;
	input wire [DW - 1:0] axi_rd_sram_data;
	output wire [(NC * SCW) - 1:0] axi_wr_drain_data_avail;
	input wire [NC - 1:0] axi_wr_drain_req;
	input wire [(NC * 8) - 1:0] axi_wr_drain_size;
	output wire [NC - 1:0] axi_wr_sram_valid;
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
				.axi_wr_sram_valid(axi_wr_sram_valid[i]),
				.axi_wr_sram_ready(axi_wr_sram_drain_decoded[i]),
				.axi_wr_sram_data(axi_wr_sram_data_per_channel[i * DW+:DW]),
				.axi_rd_alloc_req(axi_rd_alloc_req_decoded[i]),
				.axi_rd_alloc_size(axi_rd_alloc_size),
				.axi_rd_alloc_space_free(axi_rd_alloc_space_free[i * SCW+:SCW]),
				.axi_wr_drain_req(axi_wr_drain_req[i]),
				.axi_wr_drain_size(axi_wr_drain_size[i * 8+:8]),
				.axi_wr_drain_data_avail(axi_wr_drain_data_avail[i * SCW+:SCW]),
				.dbg_bridge_pending(dbg_bridge_pending[i]),
				.dbg_bridge_out_valid(dbg_bridge_out_valid[i])
			);
		end
	endgenerate
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
	wire [CW - 1:0] w_arb_grant_id;
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
	wire w_arb_grant_valid;
	wire [NC - 1:0] w_arb_grant;
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
	assign m_axi_arvalid = w_arb_grant_valid;
	assign m_axi_arid = {{IW - CW {1'b0}}, w_arb_grant_id};
	assign m_axi_araddr = sched_rd_addr[w_arb_grant_id * AW+:AW];
	assign m_axi_arlen = w_transfer_size[w_arb_grant_id * 8+:8];
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign m_axi_arsize = sv2v_cast_3_signed(AXSIZE);
	assign m_axi_arburst = 2'b01;
	assign w_arb_grant_ack = w_arb_grant & {NC {m_axi_arvalid && m_axi_arready}};
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
	parameter signed [31:0] CHANNEL_WIDTH = $clog2(NUM_CHANNELS);
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
	always @(*) begin
		if (_sv2v_0)
			;
		w_fifo_wr = 1'b0;
		w_fifo_wr_data = 1'sb0;
		if ((cfg_enable && w_channel_event) && !w_fifo_full_internal) begin
			w_fifo_wr = 1'b1;
			if (cfg_mode == MODE_TIMESTAMP)
				w_fifo_wr_data = {(w_idle_rising[w_active_channel] ? EVENT_END : EVENT_START), w_active_channel[2:0], r_timestamp_counter};
			else
				w_fifo_wr_data = {EVENT_END, w_active_channel[2:0], w_elapsed_time};
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
module scheduler_group_array (
	clk,
	rst_n,
	apb_valid,
	apb_ready,
	apb_addr,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_enable,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_enable,
	cfg_sched_err_enable,
	cfg_sched_compl_enable,
	cfg_sched_perf_enable,
	cfg_desceng_enable,
	cfg_desceng_prefetch,
	cfg_desceng_fifo_thresh,
	cfg_desceng_addr0_base,
	cfg_desceng_addr0_limit,
	cfg_desceng_addr1_base,
	cfg_desceng_addr1_limit,
	cfg_desc_mon_enable,
	cfg_desc_mon_err_enable,
	cfg_desc_mon_perf_enable,
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
	descriptor_engine_idle,
	scheduler_idle,
	scheduler_state,
	sched_error,
	cfg_sts_desc_mon_busy,
	cfg_sts_desc_mon_active_txns,
	cfg_sts_desc_mon_error_count,
	cfg_sts_desc_mon_txn_count,
	cfg_sts_desc_mon_conflict_error,
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
	sched_rd_error,
	sched_wr_error,
	mon_valid,
	mon_ready,
	mon_packet
);
	reg _sv2v_0;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] DESC_MON_BASE_AGENT_ID = 16;
	parameter signed [31:0] SCHED_MON_BASE_AGENT_ID = 48;
	parameter signed [31:0] DESC_AXI_MON_AGENT_ID = 8;
	parameter signed [31:0] MON_UNIT_ID = 1;
	parameter signed [31:0] MON_MAX_TRANSACTIONS = 16;
	input wire clk;
	input wire rst_n;
	input wire [NUM_CHANNELS - 1:0] apb_valid;
	output wire [NUM_CHANNELS - 1:0] apb_ready;
	input wire [(NUM_CHANNELS * ADDR_WIDTH) - 1:0] apb_addr;
	input wire [NUM_CHANNELS - 1:0] cfg_channel_enable;
	input wire [NUM_CHANNELS - 1:0] cfg_channel_reset;
	input wire cfg_sched_enable;
	input wire [15:0] cfg_sched_timeout_cycles;
	input wire cfg_sched_timeout_enable;
	input wire cfg_sched_err_enable;
	input wire cfg_sched_compl_enable;
	input wire cfg_sched_perf_enable;
	input wire cfg_desceng_enable;
	input wire cfg_desceng_prefetch;
	input wire [3:0] cfg_desceng_fifo_thresh;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr0_limit;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_base;
	input wire [ADDR_WIDTH - 1:0] cfg_desceng_addr1_limit;
	input wire cfg_desc_mon_enable;
	input wire cfg_desc_mon_err_enable;
	input wire cfg_desc_mon_perf_enable;
	input wire cfg_desc_mon_timeout_enable;
	input wire [31:0] cfg_desc_mon_timeout_cycles;
	input wire [31:0] cfg_desc_mon_latency_thresh;
	input wire [15:0] cfg_desc_mon_pkt_mask;
	input wire [3:0] cfg_desc_mon_err_select;
	input wire [7:0] cfg_desc_mon_err_mask;
	input wire [7:0] cfg_desc_mon_timeout_mask;
	input wire [7:0] cfg_desc_mon_compl_mask;
	input wire [7:0] cfg_desc_mon_thresh_mask;
	input wire [7:0] cfg_desc_mon_perf_mask;
	input wire [7:0] cfg_desc_mon_addr_mask;
	input wire [7:0] cfg_desc_mon_debug_mask;
	output wire [NUM_CHANNELS - 1:0] descriptor_engine_idle;
	output wire [NUM_CHANNELS - 1:0] scheduler_idle;
	output wire [(NUM_CHANNELS * 7) - 1:0] scheduler_state;
	output wire [NUM_CHANNELS - 1:0] sched_error;
	output wire cfg_sts_desc_mon_busy;
	output wire [7:0] cfg_sts_desc_mon_active_txns;
	output wire [15:0] cfg_sts_desc_mon_error_count;
	output wire [31:0] cfg_sts_desc_mon_txn_count;
	output wire cfg_sts_desc_mon_conflict_error;
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
	input wire [NUM_CHANNELS - 1:0] sched_rd_error;
	input wire [NUM_CHANNELS - 1:0] sched_wr_error;
	output wire mon_valid;
	input wire mon_ready;
	output wire [63:0] mon_packet;
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
	wire [(NUM_CHANNELS * 64) - 1:0] mon_packet_ch;
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
	wire [63:0] desc_axi_mon_packet;
	localparam signed [31:0] MONBUS_SOURCES = NUM_CHANNELS + 1;
	reg [0:MONBUS_SOURCES - 1] monbus_valid_all;
	wire [0:MONBUS_SOURCES - 1] monbus_ready_all;
	reg [(MONBUS_SOURCES * 64) - 1:0] monbus_packet_all;
	genvar _gv_ch_2;
	generate
		for (_gv_ch_2 = 0; _gv_ch_2 < NUM_CHANNELS; _gv_ch_2 = _gv_ch_2 + 1) begin : gen_scheduler_groups
			localparam ch = _gv_ch_2;
			scheduler_group #(
				.CHANNEL_ID(ch),
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
				.cfg_sched_timeout_enable(cfg_sched_timeout_enable),
				.cfg_sched_err_enable(cfg_sched_err_enable),
				.cfg_sched_compl_enable(cfg_sched_compl_enable),
				.cfg_sched_perf_enable(cfg_sched_perf_enable),
				.cfg_desceng_prefetch(cfg_desceng_prefetch),
				.cfg_desceng_fifo_thresh(cfg_desceng_fifo_thresh),
				.cfg_desceng_addr0_base(cfg_desceng_addr0_base),
				.cfg_desceng_addr0_limit(cfg_desceng_addr0_limit),
				.cfg_desceng_addr1_base(cfg_desceng_addr1_base),
				.cfg_desceng_addr1_limit(cfg_desceng_addr1_limit),
				.descriptor_engine_idle(descriptor_engine_idle[ch]),
				.scheduler_idle(scheduler_idle[ch]),
				.scheduler_state(scheduler_state[ch * 7+:7]),
				.sched_error(sched_error[ch]),
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
				.sched_rd_error(sched_rd_error[ch]),
				.sched_wr_error(sched_wr_error[ch]),
				.mon_valid(mon_valid_ch[ch]),
				.mon_ready(mon_ready_ch[ch]),
				.mon_packet(mon_packet_ch[ch * 64+:64])
			);
		end
	endgenerate
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
	axi4_master_rd_mon #(
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(ADDR_WIDTH),
		.AXI_DATA_WIDTH(256),
		.AXI_USER_WIDTH(1),
		.UNIT_ID(MON_UNIT_ID),
		.AGENT_ID(DESC_AXI_MON_AGENT_ID),
		.MAX_TRANSACTIONS(MON_MAX_TRANSACTIONS),
		.ENABLE_FILTERING(1)
	) u_desc_axi_monitor(
		.aclk(clk),
		.aresetn(rst_n),
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
		.cfg_timeout_enable(cfg_desc_mon_timeout_enable),
		.cfg_timeout_cycles(sv2v_cast_16(cfg_desc_mon_timeout_cycles)),
		.cfg_latency_threshold(cfg_desc_mon_latency_thresh),
		.cfg_axi_pkt_mask(cfg_desc_mon_pkt_mask),
		.cfg_axi_err_select(sv2v_cast_16(cfg_desc_mon_err_select)),
		.cfg_axi_error_mask(sv2v_cast_16(cfg_desc_mon_err_mask)),
		.cfg_axi_timeout_mask(sv2v_cast_16(cfg_desc_mon_timeout_mask)),
		.cfg_axi_compl_mask(sv2v_cast_16(cfg_desc_mon_compl_mask)),
		.cfg_axi_thresh_mask(sv2v_cast_16(cfg_desc_mon_thresh_mask)),
		.cfg_axi_perf_mask(sv2v_cast_16(cfg_desc_mon_perf_mask)),
		.cfg_axi_addr_mask(sv2v_cast_16(cfg_desc_mon_addr_mask)),
		.cfg_axi_debug_mask(sv2v_cast_16(cfg_desc_mon_debug_mask)),
		.monbus_valid(desc_axi_mon_valid),
		.monbus_ready(desc_axi_mon_ready),
		.monbus_packet(desc_axi_mon_packet),
		.busy(cfg_sts_desc_mon_busy),
		.active_transactions(cfg_sts_desc_mon_active_txns),
		.error_count(cfg_sts_desc_mon_error_count),
		.transaction_count(cfg_sts_desc_mon_txn_count),
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
					monbus_packet_all[((MONBUS_SOURCES - 1) - ch) * 64+:64] = mon_packet_ch[ch * 64+:64];
				end
		end
		monbus_valid_all[NUM_CHANNELS] = desc_axi_mon_valid;
		desc_axi_mon_ready = monbus_ready_all[NUM_CHANNELS];
		monbus_packet_all[((MONBUS_SOURCES - 1) - NUM_CHANNELS) * 64+:64] = desc_axi_mon_packet;
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
		.monbus_valid(mon_valid),
		.monbus_ready(mon_ready),
		.monbus_packet(mon_packet),
		.grant_valid(),
		.grant(),
		.grant_id(),
		.last_grant()
	);
	initial _sv2v_0 = 0;
endmodule
module stream_core_mon (
	clk,
	rst_n,
	apb_valid,
	apb_ready,
	apb_addr,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_enable,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_enable,
	cfg_sched_err_enable,
	cfg_sched_compl_enable,
	cfg_sched_perf_enable,
	cfg_desceng_enable,
	cfg_desceng_prefetch,
	cfg_desceng_fifo_thresh,
	cfg_desceng_addr0_base,
	cfg_desceng_addr0_limit,
	cfg_desceng_addr1_base,
	cfg_desceng_addr1_limit,
	cfg_desc_mon_enable,
	cfg_desc_mon_err_enable,
	cfg_desc_mon_perf_enable,
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
	cfg_rdeng_mon_enable,
	cfg_rdeng_mon_err_enable,
	cfg_rdeng_mon_perf_enable,
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
	cfg_axi_rd_xfer_beats,
	cfg_axi_wr_xfer_beats,
	cfg_perf_enable,
	cfg_perf_mode,
	cfg_perf_clear,
	descriptor_engine_idle,
	scheduler_idle,
	scheduler_state,
	axi_rd_all_complete,
	axi_wr_all_complete,
	cfg_sts_desc_mon_busy,
	cfg_sts_desc_mon_active_txns,
	cfg_sts_desc_mon_error_count,
	cfg_sts_desc_mon_txn_count,
	cfg_sts_desc_mon_conflict_error,
	cfg_sts_rdeng_skid_busy,
	cfg_sts_rdeng_mon_active_txns,
	cfg_sts_rdeng_mon_error_count,
	cfg_sts_rdeng_mon_txn_count,
	cfg_sts_rdeng_mon_conflict_error,
	cfg_sts_wreng_skid_busy,
	cfg_sts_wreng_mon_active_txns,
	cfg_sts_wreng_mon_error_count,
	cfg_sts_wreng_mon_txn_count,
	cfg_sts_wreng_mon_conflict_error,
	perf_fifo_empty,
	perf_fifo_full,
	perf_fifo_count,
	perf_fifo_rd,
	perf_fifo_data_low,
	perf_fifo_data_high,
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
	cfg_sts_desc_axi_busy,
	cfg_sts_desc_axi_active_txns,
	cfg_sts_desc_axi_error_count,
	cfg_sts_desc_axi_txn_count,
	cfg_sts_desc_axi_conflict_error,
	cfg_sts_desc_rd_skid_busy,
	cfg_sts_data_rd_skid_busy,
	cfg_sts_data_wr_skid_busy,
	mon_valid,
	mon_ready,
	mon_packet
);
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = $clog2(NUM_CHANNELS);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] FIFO_DEPTH = 512;
	parameter signed [31:0] TIMEOUT_CYCLES = 5000;
	parameter signed [31:0] AR_MAX_OUTSTANDING = 8;
	parameter signed [31:0] AW_MAX_OUTSTANDING = 8;
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	parameter signed [31:0] MON_UNIT_ID = 1;
	parameter signed [31:0] DESC_MON_BASE_AGENT_ID = 16;
	parameter signed [31:0] SCHED_MON_BASE_AGENT_ID = 48;
	parameter signed [31:0] DESC_AXI_MON_AGENT_ID = 8;
	parameter signed [31:0] RDENG_AGENT_ID = 1;
	parameter signed [31:0] WRENG_AGENT_ID = 1;
	parameter signed [31:0] MON_MAX_TRANSACTIONS = 16;
	parameter signed [31:0] NC = NUM_CHANNELS;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] UW = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	input wire clk;
	input wire rst_n;
	input wire [NC - 1:0] apb_valid;
	output wire [NC - 1:0] apb_ready;
	input wire [(NC * AW) - 1:0] apb_addr;
	input wire [NC - 1:0] cfg_channel_enable;
	input wire [NC - 1:0] cfg_channel_reset;
	input wire cfg_sched_enable;
	input wire [15:0] cfg_sched_timeout_cycles;
	input wire cfg_sched_timeout_enable;
	input wire cfg_sched_err_enable;
	input wire cfg_sched_compl_enable;
	input wire cfg_sched_perf_enable;
	input wire cfg_desceng_enable;
	input wire cfg_desceng_prefetch;
	input wire [3:0] cfg_desceng_fifo_thresh;
	input wire [AW - 1:0] cfg_desceng_addr0_base;
	input wire [AW - 1:0] cfg_desceng_addr0_limit;
	input wire [AW - 1:0] cfg_desceng_addr1_base;
	input wire [AW - 1:0] cfg_desceng_addr1_limit;
	input wire cfg_desc_mon_enable;
	input wire cfg_desc_mon_err_enable;
	input wire cfg_desc_mon_perf_enable;
	input wire cfg_desc_mon_timeout_enable;
	input wire [31:0] cfg_desc_mon_timeout_cycles;
	input wire [31:0] cfg_desc_mon_latency_thresh;
	input wire [15:0] cfg_desc_mon_pkt_mask;
	input wire [3:0] cfg_desc_mon_err_select;
	input wire [7:0] cfg_desc_mon_err_mask;
	input wire [7:0] cfg_desc_mon_timeout_mask;
	input wire [7:0] cfg_desc_mon_compl_mask;
	input wire [7:0] cfg_desc_mon_thresh_mask;
	input wire [7:0] cfg_desc_mon_perf_mask;
	input wire [7:0] cfg_desc_mon_addr_mask;
	input wire [7:0] cfg_desc_mon_debug_mask;
	input wire cfg_rdeng_mon_enable;
	input wire cfg_rdeng_mon_err_enable;
	input wire cfg_rdeng_mon_perf_enable;
	input wire cfg_rdeng_mon_timeout_enable;
	input wire [31:0] cfg_rdeng_mon_timeout_cycles;
	input wire [31:0] cfg_rdeng_mon_latency_thresh;
	input wire [15:0] cfg_rdeng_mon_pkt_mask;
	input wire [3:0] cfg_rdeng_mon_err_select;
	input wire [7:0] cfg_rdeng_mon_err_mask;
	input wire [7:0] cfg_rdeng_mon_timeout_mask;
	input wire [7:0] cfg_rdeng_mon_compl_mask;
	input wire [7:0] cfg_rdeng_mon_thresh_mask;
	input wire [7:0] cfg_rdeng_mon_perf_mask;
	input wire [7:0] cfg_rdeng_mon_addr_mask;
	input wire [7:0] cfg_rdeng_mon_debug_mask;
	input wire cfg_wreng_mon_enable;
	input wire cfg_wreng_mon_err_enable;
	input wire cfg_wreng_mon_perf_enable;
	input wire cfg_wreng_mon_timeout_enable;
	input wire [31:0] cfg_wreng_mon_timeout_cycles;
	input wire [31:0] cfg_wreng_mon_latency_thresh;
	input wire [15:0] cfg_wreng_mon_pkt_mask;
	input wire [3:0] cfg_wreng_mon_err_select;
	input wire [7:0] cfg_wreng_mon_err_mask;
	input wire [7:0] cfg_wreng_mon_timeout_mask;
	input wire [7:0] cfg_wreng_mon_compl_mask;
	input wire [7:0] cfg_wreng_mon_thresh_mask;
	input wire [7:0] cfg_wreng_mon_perf_mask;
	input wire [7:0] cfg_wreng_mon_addr_mask;
	input wire [7:0] cfg_wreng_mon_debug_mask;
	input wire [7:0] cfg_axi_rd_xfer_beats;
	input wire [7:0] cfg_axi_wr_xfer_beats;
	input wire cfg_perf_enable;
	input wire cfg_perf_mode;
	input wire cfg_perf_clear;
	output wire [NC - 1:0] descriptor_engine_idle;
	output wire [NC - 1:0] scheduler_idle;
	output wire [(NC * 7) - 1:0] scheduler_state;
	output wire [NC - 1:0] axi_rd_all_complete;
	output wire [NC - 1:0] axi_wr_all_complete;
	output wire cfg_sts_desc_mon_busy;
	output wire [7:0] cfg_sts_desc_mon_active_txns;
	output wire [15:0] cfg_sts_desc_mon_error_count;
	output wire [31:0] cfg_sts_desc_mon_txn_count;
	output wire cfg_sts_desc_mon_conflict_error;
	output wire cfg_sts_rdeng_skid_busy;
	output wire [7:0] cfg_sts_rdeng_mon_active_txns;
	output wire [15:0] cfg_sts_rdeng_mon_error_count;
	output wire [31:0] cfg_sts_rdeng_mon_txn_count;
	output wire cfg_sts_rdeng_mon_conflict_error;
	output wire cfg_sts_wreng_skid_busy;
	output wire [7:0] cfg_sts_wreng_mon_active_txns;
	output wire [15:0] cfg_sts_wreng_mon_error_count;
	output wire [31:0] cfg_sts_wreng_mon_txn_count;
	output wire cfg_sts_wreng_mon_conflict_error;
	output wire perf_fifo_empty;
	output wire perf_fifo_full;
	output wire [15:0] perf_fifo_count;
	input wire perf_fifo_rd;
	output wire [31:0] perf_fifo_data_low;
	output wire [31:0] perf_fifo_data_high;
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
	output wire cfg_sts_desc_axi_busy;
	output wire [7:0] cfg_sts_desc_axi_active_txns;
	output wire [15:0] cfg_sts_desc_axi_error_count;
	output wire [31:0] cfg_sts_desc_axi_txn_count;
	output wire cfg_sts_desc_axi_conflict_error;
	output wire cfg_sts_desc_rd_skid_busy;
	output wire cfg_sts_data_rd_skid_busy;
	output wire cfg_sts_data_wr_skid_busy;
	output wire mon_valid;
	input wire mon_ready;
	output wire [63:0] mon_packet;
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
	wire [NC - 1:0] sched_rd_error;
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
	wire axi_wr_sram_drain;
	wire [CHAN_WIDTH - 1:0] axi_wr_sram_id;
	wire [DW - 1:0] axi_wr_sram_data;
	wire schedgrp_mon_valid;
	wire schedgrp_mon_ready;
	wire [63:0] schedgrp_mon_packet;
	wire axi_rdeng_mon_valid;
	wire axi_rdeng_mon_ready;
	wire [63:0] axi_rdeng_mon_packet;
	wire axi_wreng_mon_valid;
	wire axi_wreng_mon_ready;
	wire [63:0] axi_wreng_mon_packet;
	assign cfg_sts_desc_axi_busy = 1'b0;
	assign cfg_sts_desc_axi_active_txns = 8'h00;
	assign cfg_sts_desc_axi_error_count = 16'h0000;
	assign cfg_sts_desc_axi_txn_count = 32'h00000000;
	assign cfg_sts_desc_axi_conflict_error = 1'b0;
	scheduler_group_array #(
		.NUM_CHANNELS(NC),
		.CHAN_WIDTH(CHAN_WIDTH),
		.ADDR_WIDTH(AW),
		.DATA_WIDTH(DW),
		.AXI_ID_WIDTH(IW),
		.DESC_MON_BASE_AGENT_ID(DESC_MON_BASE_AGENT_ID),
		.SCHED_MON_BASE_AGENT_ID(SCHED_MON_BASE_AGENT_ID),
		.DESC_AXI_MON_AGENT_ID(DESC_AXI_MON_AGENT_ID),
		.MON_UNIT_ID(MON_UNIT_ID)
	) u_scheduler_group_array(
		.clk(clk),
		.rst_n(rst_n),
		.apb_valid(apb_valid),
		.apb_ready(apb_ready),
		.apb_addr(apb_addr),
		.cfg_channel_enable(cfg_channel_enable),
		.cfg_channel_reset(cfg_channel_reset),
		.cfg_sched_enable(cfg_sched_enable),
		.cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
		.cfg_sched_timeout_enable(cfg_sched_timeout_enable),
		.cfg_sched_err_enable(cfg_sched_err_enable),
		.cfg_sched_compl_enable(cfg_sched_compl_enable),
		.cfg_sched_perf_enable(cfg_sched_perf_enable),
		.cfg_desceng_enable(cfg_desceng_enable),
		.cfg_desceng_prefetch(cfg_desceng_prefetch),
		.cfg_desceng_fifo_thresh(cfg_desceng_fifo_thresh),
		.cfg_desceng_addr0_base(cfg_desceng_addr0_base),
		.cfg_desceng_addr0_limit(cfg_desceng_addr0_limit),
		.cfg_desceng_addr1_base(cfg_desceng_addr1_base),
		.cfg_desceng_addr1_limit(cfg_desceng_addr1_limit),
		.cfg_desc_mon_enable(cfg_desc_mon_enable),
		.cfg_desc_mon_err_enable(cfg_desc_mon_err_enable),
		.cfg_desc_mon_perf_enable(cfg_desc_mon_perf_enable),
		.cfg_desc_mon_timeout_enable(cfg_desc_mon_timeout_enable),
		.cfg_desc_mon_timeout_cycles(cfg_desc_mon_timeout_cycles),
		.cfg_desc_mon_latency_thresh(cfg_desc_mon_latency_thresh),
		.cfg_desc_mon_pkt_mask(cfg_desc_mon_pkt_mask),
		.cfg_desc_mon_err_select(cfg_desc_mon_err_select),
		.cfg_desc_mon_err_mask(cfg_desc_mon_err_mask),
		.cfg_desc_mon_timeout_mask(cfg_desc_mon_timeout_mask),
		.cfg_desc_mon_compl_mask(cfg_desc_mon_compl_mask),
		.cfg_desc_mon_thresh_mask(cfg_desc_mon_thresh_mask),
		.cfg_desc_mon_perf_mask(cfg_desc_mon_perf_mask),
		.cfg_desc_mon_addr_mask(cfg_desc_mon_addr_mask),
		.cfg_desc_mon_debug_mask(cfg_desc_mon_debug_mask),
		.cfg_sts_desc_mon_busy(cfg_sts_desc_mon_busy),
		.cfg_sts_desc_mon_active_txns(cfg_sts_desc_mon_active_txns),
		.cfg_sts_desc_mon_error_count(cfg_sts_desc_mon_error_count),
		.cfg_sts_desc_mon_txn_count(cfg_sts_desc_mon_txn_count),
		.cfg_sts_desc_mon_conflict_error(cfg_sts_desc_mon_conflict_error),
		.descriptor_engine_idle(descriptor_engine_idle),
		.scheduler_idle(scheduler_idle),
		.scheduler_state(scheduler_state),
		.sched_error(),
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
		.sched_rd_error(sched_rd_error),
		.sched_wr_error(sched_wr_error),
		.mon_valid(schedgrp_mon_valid),
		.mon_ready(schedgrp_mon_ready),
		.mon_packet(schedgrp_mon_packet)
	);
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
		.axi_wr_sram_drain(axi_wr_sram_drain),
		.axi_wr_sram_id(axi_wr_sram_id),
		.axi_wr_sram_data(axi_wr_sram_data),
		.sched_wr_done_strobe(sched_wr_done_strobe),
		.sched_wr_beats_done(sched_wr_beats_done),
		.dbg_wr_all_complete(axi_wr_all_complete),
		.sched_wr_error(sched_wr_error),
		.dbg_aw_transactions(),
		.dbg_w_beats()
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
	assign cfg_sts_desc_rd_skid_busy = 1'b0;
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
	assign fub_rd_axi_ruser = 1'sb0;
	axi4_master_rd_mon #(
		.SKID_DEPTH_AR(SKID_DEPTH_AR),
		.SKID_DEPTH_R(SKID_DEPTH_R),
		.AXI_ID_WIDTH(IW),
		.AXI_ADDR_WIDTH(AW),
		.AXI_DATA_WIDTH(DW),
		.AXI_USER_WIDTH(UW),
		.UNIT_ID(MON_UNIT_ID),
		.AGENT_ID(RDENG_AGENT_ID),
		.MAX_TRANSACTIONS(MON_MAX_TRANSACTIONS),
		.ENABLE_FILTERING(1)
	) u_rd_axi_skid(
		.aclk(clk),
		.aresetn(rst_n),
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
		.cfg_monitor_enable(cfg_rdeng_mon_enable),
		.cfg_error_enable(cfg_rdeng_mon_err_enable),
		.cfg_perf_enable(cfg_rdeng_mon_perf_enable),
		.cfg_timeout_enable(cfg_rdeng_mon_timeout_enable),
		.cfg_timeout_cycles(cfg_rdeng_mon_timeout_cycles),
		.cfg_latency_threshold(cfg_rdeng_mon_latency_thresh),
		.cfg_axi_pkt_mask(cfg_rdeng_mon_pkt_mask),
		.cfg_axi_err_select(cfg_rdeng_mon_err_select),
		.cfg_axi_error_mask(cfg_rdeng_mon_err_mask),
		.cfg_axi_timeout_mask(cfg_rdeng_mon_timeout_mask),
		.cfg_axi_compl_mask(cfg_rdeng_mon_compl_mask),
		.cfg_axi_thresh_mask(cfg_rdeng_mon_thresh_mask),
		.cfg_axi_perf_mask(cfg_rdeng_mon_perf_mask),
		.cfg_axi_addr_mask(cfg_rdeng_mon_addr_mask),
		.cfg_axi_debug_mask(cfg_rdeng_mon_debug_mask),
		.monbus_valid(axi_rdeng_mon_valid),
		.monbus_ready(axi_rdeng_mon_ready),
		.monbus_packet(axi_rdeng_mon_packet),
		.busy(cfg_sts_rdeng_skid_busy),
		.active_transactions(cfg_sts_rdeng_mon_active_txns),
		.error_count(cfg_sts_rdeng_mon_error_count),
		.transaction_count(cfg_sts_rdeng_mon_txn_count),
		.cfg_conflict_error(cfg_sts_rdeng_mon_conflict_error)
	);
	assign fub_wr_axi_awlock = 1'b0;
	assign fub_wr_axi_awcache = 4'h0;
	assign fub_wr_axi_awprot = 3'h0;
	assign fub_wr_axi_awqos = 4'h0;
	assign fub_wr_axi_awregion = 4'h0;
	assign fub_wr_axi_awuser = sv2v_cast_FDCE5(fub_wr_axi_awid);
	assign fub_wr_axi_buser = 1'sb0;
	axi4_master_wr_mon #(
		.SKID_DEPTH_AW(SKID_DEPTH_AW),
		.SKID_DEPTH_W(SKID_DEPTH_W),
		.SKID_DEPTH_B(SKID_DEPTH_B),
		.AXI_ID_WIDTH(IW),
		.AXI_ADDR_WIDTH(AW),
		.AXI_DATA_WIDTH(DW),
		.AXI_USER_WIDTH(UW),
		.UNIT_ID(MON_UNIT_ID),
		.AGENT_ID(WRENG_AGENT_ID),
		.MAX_TRANSACTIONS(MON_MAX_TRANSACTIONS),
		.ENABLE_FILTERING(1)
	) u_wr_axi_skid(
		.aclk(clk),
		.aresetn(rst_n),
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
		.cfg_monitor_enable(cfg_wreng_mon_enable),
		.cfg_error_enable(cfg_wreng_mon_err_enable),
		.cfg_perf_enable(cfg_wreng_mon_perf_enable),
		.cfg_timeout_enable(cfg_wreng_mon_timeout_enable),
		.cfg_timeout_cycles(cfg_wreng_mon_timeout_cycles),
		.cfg_latency_threshold(cfg_wreng_mon_latency_thresh),
		.cfg_axi_pkt_mask(cfg_wreng_mon_pkt_mask),
		.cfg_axi_err_select(cfg_wreng_mon_err_select),
		.cfg_axi_error_mask(cfg_wreng_mon_err_mask),
		.cfg_axi_timeout_mask(cfg_wreng_mon_timeout_mask),
		.cfg_axi_compl_mask(cfg_wreng_mon_compl_mask),
		.cfg_axi_thresh_mask(cfg_wreng_mon_thresh_mask),
		.cfg_axi_perf_mask(cfg_wreng_mon_perf_mask),
		.cfg_axi_addr_mask(cfg_wreng_mon_addr_mask),
		.cfg_axi_debug_mask(cfg_wreng_mon_debug_mask),
		.monbus_valid(axi_wreng_mon_valid),
		.monbus_ready(axi_wreng_mon_ready),
		.monbus_packet(axi_wreng_mon_packet),
		.busy(cfg_sts_wreng_skid_busy),
		.active_transactions(cfg_sts_wreng_mon_active_txns),
		.error_count(cfg_sts_wreng_mon_error_count),
		.transaction_count(cfg_sts_wreng_mon_txn_count),
		.cfg_conflict_error(cfg_sts_wreng_mon_conflict_error)
	);
	monbus_arbiter #(
		.CLIENTS(3),
		.INPUT_SKID_ENABLE(1),
		.OUTPUT_SKID_ENABLE(1),
		.INPUT_SKID_DEPTH(2),
		.OUTPUT_SKID_DEPTH(4)
	) u_monbus_arbiter(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.block_arb(1'b0),
		.monbus_valid_in({axi_wreng_mon_valid, axi_rdeng_mon_valid, schedgrp_mon_valid}),
		.monbus_ready_in({axi_wreng_mon_ready, axi_rdeng_mon_ready, schedgrp_mon_ready}),
		.monbus_packet_in({axi_wreng_mon_packet, axi_rdeng_mon_packet, schedgrp_mon_packet}),
		.monbus_valid(mon_valid),
		.monbus_ready(mon_ready),
		.monbus_packet(mon_packet),
		.grant_valid(),
		.grant(),
		.grant_id(),
		.last_grant()
	);
endmodule
