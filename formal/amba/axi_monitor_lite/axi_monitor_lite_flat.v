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
	cfg_axi_pkt_mask,
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
	input wire [15:0] cfg_axi_pkt_mask;
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
	wire w_last_early = ((data_hs && w_dhit) && data_last) && !w_dbeats_zero;
	wire w_last_late = ((data_hs && w_dhit) && !data_last) && w_dbeats_zero;
	wire w_data_done = (data_hs && w_dhit) && data_last;
	wire w_early_w = (data_hs && !w_dhit) && !IS_READ;
	wire w_early_ovf = w_early_w && r_early_last;
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
	wire [7:0] w_alloc_beats = (!IS_READ && r_early_any ? (cmd_len - r_early_beats) + 8'd1 : cmd_len);
	wire w_alloc_done = (!IS_READ && r_early_any) && r_early_last;
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
				r_err[w_free_idx] <= 1'b0;
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
				r_early_beats <= r_early_beats + 8'd1;
				if (data_last)
					r_early_last <= 1'b1;
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
			r_e_scan_phase <= r_phase[r_scan];
			r_e_data_decerr <= data_resp[0];
			r_e_resp_decerr <= resp_code[0];
			r_e_dslot <= w_dslot;
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
	wire w_tmo_v = (r_e_scan_hit || r_e_cmd_tmo) && w_tmo_en;
	wire [7:0] w_tmo_code = (r_e_scan_hit ? (r_e_scan_phase ? 8'h02 : 8'h01) : 8'h00);
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	wire [1:0] w_tmo_fired = (w_tmo_en ? sv2v_cast_2(r_e_scan_hit) + sv2v_cast_2(r_e_cmd_tmo) : 2'd0);
	wire w_cmp_v = r_e_compl && w_cmp_en;
	wire w_thr_v = r_e_thresh && w_thr_en;
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
			w_evt_from_slot = r_e_scan_hit;
			w_evt_slot = r_e_tslot;
			w_evt_id_alt = r_e_cmd_id;
			w_evt_addr_alt = r_e_cmd_addr;
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
			w_evt_code = 8'h00;
			w_evt_addr_alt = sv2v_cast_DE851(r_e_occupancy);
		end
	end
	wire [IW - 1:0] w_evt_id = (w_evt_from_slot ? r_id[w_evt_slot * IW+:IW] : w_evt_id_alt);
	wire [AW - 1:0] w_evt_addr = (w_evt_from_slot ? r_addr[w_evt_slot * AW+:AW] : w_evt_addr_alt);
	wire w_wr_ready;
	wire [3:0] w_offered = ((w_err_fired + sv2v_cast_4(w_tmo_fired)) + sv2v_cast_4(w_cmp_v)) + sv2v_cast_4(w_thr_v);
	wire w_take = w_evt_v && w_wr_ready;
	wire [3:0] w_lost = w_offered - sv2v_cast_4(w_take);
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
	wire w_q_pop = monbus_valid && monbus_ready;
	assign w_wr_ready = !w_q_full;
	assign monbus_valid = !w_q_empty;
	assign w_entry_out = r_q[r_q_rp[OQW - 1:0]];
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
	assign monbus_packet = monitor_common_pkg_create_monitor_packet(w_entry_out[12 + (AW + 21)-:((12 + (AW + 21)) >= (30 + (AW + 0)) ? ((12 + (AW + 21)) - (30 + (AW + 0))) + 1 : ((30 + (AW + 0)) - (12 + (AW + 21))) + 1)], 4'h0, w_entry_out[14 + (AW + 15)-:((14 + (AW + 15)) >= (22 + (AW + 0)) ? ((14 + (AW + 15)) - (22 + (AW + 0))) + 1 : ((22 + (AW + 0)) - (14 + (AW + 15))) + 1)], {3'b000, w_entry_out[AW + 21-:((AW + 21) >= (16 + (AW + 0)) ? ((AW + 21) - (16 + (AW + 0))) + 1 : ((16 + (AW + 0)) - (AW + 21)) + 1)]}, UNIT_ID, AGENT_ID, w_out_data);
	assign monbus_timestamp = i_mon_time;
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign active_count = sv2v_cast_8(w_occupancy);
	assign busy = |r_valid || monbus_valid;
	assign perf_completed_count = r_completed;
	assign perf_error_count = r_errors;
	assign dropped_count = r_dropped;
	assign refused_count = r_refused;
	initial _sv2v_0 = 0;
endmodule
