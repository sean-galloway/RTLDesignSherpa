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
module axis_monitor_lite (
	aclk,
	aresetn,
	clear,
	i_mon_time,
	axis_tvalid,
	axis_tready,
	axis_tlast,
	axis_tid,
	axis_tdest,
	axis_tstrb,
	cfg_freq_sel,
	cfg_timeout_cnt,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_compl_enable,
	cfg_credit_enable,
	cfg_channel_enable,
	cfg_stream_enable,
	cfg_strb_check_enable,
	cfg_stall_threshold,
	cfg_axis_pkt_mask,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	busy,
	in_packet,
	packet_count,
	error_count,
	dropped_count
);
	reg _sv2v_0;
	parameter [7:0] UNIT_ID = 8'h09;
	parameter [15:0] AGENT_ID = 16'h0064;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] DEST_WIDTH = 4;
	parameter signed [31:0] AGE_WIDTH = 16;
	parameter signed [31:0] OUT_DEPTH = 4;
	parameter signed [31:0] CFI_MIN_FREQ_MHZ = 5;
	parameter signed [31:0] CFI_MAX_FREQ_MHZ = 220;
	parameter signed [31:0] CFI_NUM_FREQ_ENTRIES = 16;
	parameter signed [31:0] CFI_FREQ_STRATEGY = 0;
	parameter signed [31:0] SW = DATA_WIDTH / 8;
	parameter signed [31:0] IW = (ID_WIDTH > 0 ? ID_WIDTH : 1);
	parameter signed [31:0] DESTW = (DEST_WIDTH > 0 ? DEST_WIDTH : 1);
	parameter signed [31:0] SELW = (CFI_NUM_FREQ_ENTRIES > 1 ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1);
	input wire aclk;
	input wire aresetn;
	input wire clear;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	input wire axis_tvalid;
	input wire axis_tready;
	input wire axis_tlast;
	input wire [IW - 1:0] axis_tid;
	input wire [DESTW - 1:0] axis_tdest;
	input wire [SW - 1:0] axis_tstrb;
	input wire [SELW - 1:0] cfg_freq_sel;
	input wire [15:0] cfg_timeout_cnt;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_compl_enable;
	input wire cfg_credit_enable;
	input wire cfg_channel_enable;
	input wire cfg_stream_enable;
	input wire cfg_strb_check_enable;
	input wire [31:0] cfg_stall_threshold;
	input wire [15:0] cfg_axis_pkt_mask;
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire busy;
	output wire in_packet;
	output wire [31:0] packet_count;
	output wire [15:0] error_count;
	output wire [15:0] dropped_count;
	wire w_hs = axis_tvalid && axis_tready;
	reg [AGE_WIDTH - 1:0] r_us;
	wire w_tick;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn)
			r_us <= 1'sb0;
		else if (w_tick)
			r_us <= r_us + 1'b1;
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
	reg r_in_pkt;
	reg [31:0] r_pkt_beats;
	reg [31:0] r_pkt_count;
	reg [IW - 1:0] r_pkt_tid;
	reg [DESTW - 1:0] r_pkt_tdest;
	reg r_paused;
	wire [31:0] w_pkt_beats_now = (r_in_pkt ? r_pkt_beats + 32'd1 : 32'd1);
	reg r_valid_pend;
	reg [31:0] r_stall_cycles;
	reg [AGE_WIDTH - 1:0] r_stall_stamp;
	reg [AGE_WIDTH - 1:0] r_beat_stamp;
	reg r_tmo_hs_fired;
	reg r_tmo_pkt_fired;
	reg r_credit_fired;
	wire [AGE_WIDTH - 1:0] w_stall_age = r_us - r_stall_stamp;
	wire [AGE_WIDTH - 1:0] w_beat_age = r_us - r_beat_stamp;
	wire w_never = cfg_timeout_cnt == 16'hffff;
	function automatic type_allowed;
		input reg [3:0] t;
		type_allowed = !cfg_axis_pkt_mask[t];
	endfunction
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	wire w_en_err = cfg_error_enable && type_allowed(monitor_common_pkg_PktTypeError);
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	wire w_en_tmo = (cfg_timeout_enable && !w_never) && type_allowed(monitor_common_pkg_PktTypeTimeout);
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	wire w_en_compl = cfg_compl_enable && type_allowed(monitor_common_pkg_PktTypeCompletion);
	localparam [3:0] monitor_common_pkg_PktTypeCredit = 4'h5;
	wire w_en_credit = (cfg_credit_enable && (cfg_stall_threshold != 32'd0)) && type_allowed(monitor_common_pkg_PktTypeCredit);
	localparam [3:0] monitor_common_pkg_PktTypeChannel = 4'h6;
	wire w_en_chan = cfg_channel_enable && type_allowed(monitor_common_pkg_PktTypeChannel);
	localparam [3:0] monitor_common_pkg_PktTypeStream = 4'h7;
	wire w_en_stream = cfg_stream_enable && type_allowed(monitor_common_pkg_PktTypeStream);
	wire w_err_valid_drop = (w_en_err && r_valid_pend) && !axis_tvalid;
	wire w_err_strb0 = ((w_en_err && cfg_strb_check_enable) && w_hs) && (axis_tstrb == {SW {1'sb0}});
	wire w_tmo_hs = ((((w_en_tmo && axis_tvalid) && !axis_tready) && r_valid_pend) && (w_stall_age >= cfg_timeout_cnt[AGE_WIDTH - 1:0])) && !r_tmo_hs_fired;
	wire w_tmo_pkt = (((w_en_tmo && r_in_pkt) && !w_hs) && (w_beat_age >= cfg_timeout_cnt[AGE_WIDTH - 1:0])) && !r_tmo_pkt_fired;
	wire w_compl = (w_en_compl && w_hs) && axis_tlast;
	wire w_credit = (((w_en_credit && axis_tvalid) && !axis_tready) && (r_stall_cycles >= cfg_stall_threshold)) && !r_credit_fired;
	wire w_chan_id = ((w_en_chan && w_hs) && r_in_pkt) && (axis_tid != r_pkt_tid);
	wire w_chan_dest = ((w_en_chan && w_hs) && r_in_pkt) && (axis_tdest != r_pkt_tdest);
	wire w_strm_start = (w_en_stream && w_hs) && !r_in_pkt;
	wire w_strm_pause = ((w_en_stream && r_in_pkt) && !axis_tvalid) && !r_paused;
	wire w_strm_resume = (w_en_stream && r_paused) && axis_tvalid;
	localparam signed [31:0] NC = 11;
	wire [10:0] w_cand;
	assign w_cand = {w_err_valid_drop, w_err_strb0, w_tmo_hs, w_tmo_pkt, w_compl, w_credit, w_chan_id, w_chan_dest, w_strm_start, w_strm_pause, w_strm_resume};
	function automatic signed [3:0] sv2v_cast_4_signed;
		input reg signed [3:0] inp;
		sv2v_cast_4_signed = inp;
	endfunction
	function automatic [3:0] first_idx;
		input reg [10:0] c;
		reg [3:0] r;
		begin
			r = 1'sb0;
			begin : sv2v_autoblock_1
				reg signed [31:0] i;
				for (i = 0; i < NC; i = i + 1)
					if (c[i])
						r = sv2v_cast_4_signed(i);
			end
			first_idx = r;
		end
	endfunction
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	function automatic [84:0] cand_entry;
		input reg [3:0] idx;
		reg [84:0] e;
		begin
			e = {monitor_common_pkg_PktTypeError, 8'h00, sv2v_cast_9(axis_tid), 64'h0000000000000000};
			case (idx)
				4'd10: begin
					e[84-:4] = monitor_common_pkg_PktTypeError;
					e[80-:8] = 8'h02;
					e[63-:64] = {r_stall_cycles, r_pkt_count};
				end
				4'd9: begin
					e[84-:4] = monitor_common_pkg_PktTypeError;
					e[80-:8] = 8'h05;
					e[63-:64] = {w_pkt_beats_now, r_pkt_count};
				end
				4'd8: begin
					e[84-:4] = monitor_common_pkg_PktTypeTimeout;
					e[80-:8] = 8'h00;
					e[63-:64] = {r_stall_cycles, sv2v_cast_16(w_stall_age), cfg_timeout_cnt};
				end
				4'd7: begin
					e[84-:4] = monitor_common_pkg_PktTypeTimeout;
					e[80-:8] = 8'h02;
					e[63-:64] = {r_pkt_beats, sv2v_cast_16(w_beat_age), cfg_timeout_cnt};
				end
				4'd6: begin
					e[84-:4] = monitor_common_pkg_PktTypeCompletion;
					e[80-:8] = 8'h00;
					e[63-:64] = {sv2v_cast_16(axis_tid), sv2v_cast_16(axis_tdest), w_pkt_beats_now};
				end
				4'd5: begin
					e[84-:4] = monitor_common_pkg_PktTypeCredit;
					e[80-:8] = 8'h05;
					e[63-:64] = {r_stall_cycles, cfg_stall_threshold};
				end
				4'd4: begin
					e[84-:4] = monitor_common_pkg_PktTypeChannel;
					e[80-:8] = 8'h05;
					e[63-:64] = {sv2v_cast_16(r_pkt_tid), sv2v_cast_16(axis_tid), w_pkt_beats_now};
				end
				4'd3: begin
					e[84-:4] = monitor_common_pkg_PktTypeChannel;
					e[80-:8] = 8'h06;
					e[63-:64] = {sv2v_cast_16(r_pkt_tdest), sv2v_cast_16(axis_tdest), w_pkt_beats_now};
				end
				4'd2: begin
					e[84-:4] = monitor_common_pkg_PktTypeStream;
					e[80-:8] = 8'h00;
					e[63-:64] = {sv2v_cast_16(axis_tid), sv2v_cast_16(axis_tdest), r_pkt_count};
				end
				4'd1: begin
					e[84-:4] = monitor_common_pkg_PktTypeStream;
					e[80-:8] = 8'h02;
					e[63-:64] = {r_pkt_beats, r_pkt_count};
				end
				default: begin
					e[84-:4] = monitor_common_pkg_PktTypeStream;
					e[80-:8] = 8'h03;
					e[63-:64] = {r_pkt_beats, r_pkt_count};
				end
			endcase
			cand_entry = e;
		end
	endfunction
	wire [10:0] w_cand2;
	wire [3:0] w_i1;
	wire [3:0] w_i2;
	wire w_fire1;
	wire w_fire2;
	wire [3:0] w_ev_n;
	assign w_i1 = first_idx(w_cand);
	assign w_cand2 = w_cand & ~(11'sd1 << w_i1);
	assign w_i2 = first_idx(w_cand2);
	assign w_fire1 = |w_cand && !clear;
	assign w_fire2 = |w_cand2 && !clear;
	assign w_ev_n = (clear ? 4'd0 : 4'($countones(w_cand)));
	wire [84:0] w_e1;
	wire [84:0] w_e2;
	assign w_e1 = cand_entry(w_i1);
	assign w_e2 = cand_entry(w_i2);
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_in_pkt <= 1'b0;
			r_pkt_beats <= 1'sb0;
			r_pkt_count <= 1'sb0;
			r_pkt_tid <= 1'sb0;
			r_pkt_tdest <= 1'sb0;
			r_paused <= 1'b0;
			r_valid_pend <= 1'b0;
			r_stall_cycles <= 1'sb0;
			r_stall_stamp <= 1'sb0;
			r_beat_stamp <= 1'sb0;
			r_tmo_hs_fired <= 1'b0;
			r_tmo_pkt_fired <= 1'b0;
			r_credit_fired <= 1'b0;
		end
		else if (clear) begin
			r_in_pkt <= 1'b0;
			r_pkt_beats <= 1'sb0;
			r_pkt_count <= 1'sb0;
			r_paused <= 1'b0;
			r_valid_pend <= 1'b0;
			r_stall_cycles <= 1'sb0;
			r_tmo_hs_fired <= 1'b0;
			r_tmo_pkt_fired <= 1'b0;
			r_credit_fired <= 1'b0;
		end
		else begin
			if (w_hs) begin
				r_beat_stamp <= r_us;
				r_tmo_pkt_fired <= 1'b0;
				r_pkt_tid <= axis_tid;
				r_pkt_tdest <= axis_tdest;
				if (axis_tlast) begin
					r_in_pkt <= 1'b0;
					r_pkt_beats <= 1'sb0;
					r_pkt_count <= r_pkt_count + 32'd1;
				end
				else begin
					r_in_pkt <= 1'b1;
					r_pkt_beats <= w_pkt_beats_now;
				end
			end
			else if (w_tmo_pkt)
				r_tmo_pkt_fired <= 1'b1;
			if (w_strm_pause)
				r_paused <= 1'b1;
			else if (axis_tvalid || !r_in_pkt)
				r_paused <= 1'b0;
			if (axis_tvalid && !axis_tready) begin
				r_valid_pend <= 1'b1;
				r_stall_cycles <= r_stall_cycles + 32'd1;
				if (!r_valid_pend)
					r_stall_stamp <= r_us;
				if (w_tmo_hs)
					r_tmo_hs_fired <= 1'b1;
				if (w_credit)
					r_credit_fired <= 1'b1;
			end
			else begin
				r_valid_pend <= 1'b0;
				r_stall_cycles <= 1'sb0;
				r_tmo_hs_fired <= 1'b0;
				r_credit_fired <= 1'b0;
			end
		end
	localparam signed [31:0] OQW = (OUT_DEPTH > 1 ? $clog2(OUT_DEPTH) : 1);
	reg [84:0] r_q [0:OUT_DEPTH - 1];
	reg [OQW:0] r_q_wp;
	reg [OQW:0] r_q_rp;
	wire [OQW:0] w_q_count = r_q_wp - r_q_rp;
	wire w_q_empty = w_q_count == {(OQW >= 0 ? OQW + 1 : 1 - OQW) {1'sb0}};
	function automatic signed [((OQW + 0) >= 0 ? OQW + 1 : 1 - (OQW + 0)) - 1:0] sv2v_cast_B7197_signed;
		input reg signed [((OQW + 0) >= 0 ? OQW + 1 : 1 - (OQW + 0)) - 1:0] inp;
		sv2v_cast_B7197_signed = inp;
	endfunction
	wire w_room1 = w_q_count <= sv2v_cast_B7197_signed(OUT_DEPTH - 1);
	wire w_room2 = w_q_count <= sv2v_cast_B7197_signed(OUT_DEPTH - 2);
	wire w_take1 = w_fire1 && w_room1;
	wire w_take2 = w_fire2 && w_room2;
	function automatic [3:0] sv2v_cast_4;
		input reg [3:0] inp;
		sv2v_cast_4 = inp;
	endfunction
	wire [3:0] w_lost = (w_ev_n - sv2v_cast_4(w_take1)) - sv2v_cast_4(w_take2);
	reg [15:0] r_dropped;
	reg [15:0] r_errors;
	wire w_drop_rpt = ((((r_dropped != 16'd0) && !w_fire1) && w_q_empty) && w_en_err) && !clear;
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	wire [1:0] w_err_take = sv2v_cast_2(w_take1 && (w_e1[84-:4] == monitor_common_pkg_PktTypeError)) + sv2v_cast_2(w_take2 && (w_e2[84-:4] == monitor_common_pkg_PktTypeError));
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_dropped <= 1'sb0;
			r_errors <= 1'sb0;
		end
		else if (clear) begin
			r_dropped <= 1'sb0;
			r_errors <= 1'sb0;
		end
		else begin
			if (w_drop_rpt)
				r_dropped <= 1'sb0;
			else if (&r_dropped[15:4])
				r_dropped <= 16'hffff;
			else
				r_dropped <= r_dropped + sv2v_cast_16(w_lost);
			if ((w_err_take != 2'd0) && (r_errors < 16'hfffe))
				r_errors <= r_errors + sv2v_cast_16(w_err_take);
		end
	wire [84:0] w_slot1;
	wire [84:0] w_entry_out;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	assign w_slot1 = (w_fire1 ? w_e1 : {monitor_common_pkg_PktTypeError, 17'h01c00, sv2v_cast_64(r_dropped)});
	wire w_push1 = w_take1 || w_drop_rpt;
	wire w_push2 = w_take2;
	wire w_q_pop = monbus_valid && monbus_ready;
	assign w_entry_out = r_q[r_q_rp[OQW - 1:0]];
	always @(posedge aclk) begin
		if (w_push1)
			r_q[r_q_wp[OQW - 1:0]] <= w_slot1;
		if (w_push2)
			r_q[r_q_wp[OQW - 1:0] + 1'b1] <= w_e2;
	end
	function automatic [((OQW + 0) >= 0 ? OQW + 1 : 1 - (OQW + 0)) - 1:0] sv2v_cast_B7197;
		input reg [((OQW + 0) >= 0 ? OQW + 1 : 1 - (OQW + 0)) - 1:0] inp;
		sv2v_cast_B7197 = inp;
	endfunction
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_q_wp <= 1'sb0;
			r_q_rp <= 1'sb0;
		end
		else begin
			r_q_wp <= (r_q_wp + sv2v_cast_B7197(w_push1)) + sv2v_cast_B7197(w_push2);
			if (w_q_pop)
				r_q_rp <= r_q_rp + 1'b1;
		end
	assign monbus_valid = !w_q_empty;
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
	assign monbus_packet = monitor_common_pkg_create_monitor_packet(w_entry_out[84-:4], 4'h1, w_entry_out[80-:8], w_entry_out[72-:9], UNIT_ID, AGENT_ID, w_entry_out[63-:64]);
	assign monbus_timestamp = i_mon_time;
	assign busy = (r_in_pkt || r_valid_pend) || monbus_valid;
	assign in_packet = r_in_pkt;
	assign packet_count = r_pkt_count;
	assign error_count = r_errors;
	assign dropped_count = r_dropped;
	initial _sv2v_0 = 0;
endmodule
