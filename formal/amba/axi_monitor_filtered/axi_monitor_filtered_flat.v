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
			$display("Error [%0t] /tmp/formal_axi_monitor_filtered/counter_freq_invariant.sv:128:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MIN_FREQ_MHZ must be >= 1 (got %0d)", MIN_FREQ_MHZ);
		if (MAX_FREQ_MHZ < MIN_FREQ_MHZ)
			$display("Error [%0t] /tmp/formal_axi_monitor_filtered/counter_freq_invariant.sv:130:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MAX_FREQ_MHZ (%0d) < MIN_FREQ_MHZ (%0d)", MAX_FREQ_MHZ, MIN_FREQ_MHZ);
		if (NUM_FREQ_ENTRIES < 1)
			$display("Error [%0t] /tmp/formal_axi_monitor_filtered/counter_freq_invariant.sv:133:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: NUM_FREQ_ENTRIES must be >= 1 (got %0d)", NUM_FREQ_ENTRIES);
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
	output wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	output wire [7:0] active_count;
	output wire [MAX_TRANSACTIONS - 1:0] state_change;
	localparam signed [31:0] N = MAX_TRANSACTIONS;
	reg [(N * 285) - 1:0] r_trans_table;
	reg [(N * 285) - 1:0] r_trans_table_prev;
	reg [7:0] r_active_count;
	reg [N - 1:0] r_state_change;
	assign trans_table = r_trans_table;
	assign active_count = r_active_count;
	assign state_change = r_state_change;
	(* keep = "true" *) reg [N - 1:0] addr_match_oh;
	(* keep = "true" *) reg [N - 1:0] data_match_oh;
	(* keep = "true" *) reg [N - 1:0] resp_match_oh;
	(* keep = "true" *) reg [N - 1:0] free_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin
					addr_match_oh[i] = r_trans_table[(((N - 1) - i) * 285) + 284] && (r_trans_table[(((N - 1) - i) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))] == cmd_id);
					resp_match_oh[i] = r_trans_table[(((N - 1) - i) * 285) + 284] && (r_trans_table[(((N - 1) - i) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))] == resp_id);
					free_oh[i] = !r_trans_table[(((N - 1) - i) * 285) + 284];
					if (IS_READ)
						data_match_oh[i] = r_trans_table[(((N - 1) - i) * 285) + 284] && (r_trans_table[(((N - 1) - i) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))] == data_id);
					else
						data_match_oh[i] = ((r_trans_table[(((N - 1) - i) * 285) + 284] && ((r_trans_table[(((N - 1) - i) * 285) + 277-:3] == 3'h1) || (r_trans_table[(((N - 1) - i) * 285) + 277-:3] == 3'h2))) && r_trans_table[(((N - 1) - i) * 285) + 283]) && !r_trans_table[(((N - 1) - i) * 285) + 281];
				end
		end
	end
	reg [N - 1:0] data_match_first_oh;
	reg addr_hit_any;
	reg data_hit_any;
	reg resp_hit_any;
	always @(*) begin
		if (_sv2v_0)
			;
		addr_hit_any = |addr_match_oh;
		resp_hit_any = |resp_match_oh;
		data_hit_any = |data_match_oh;
		data_match_first_oh = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (data_match_oh[i] && (data_match_first_oh == {N {1'sb0}}))
					data_match_first_oh[i] = 1'b1;
		end
	end
	wire [N - 1:0] addr_update_oh;
	wire [N - 1:0] data_update_oh;
	wire [N - 1:0] resp_update_oh;
	assign addr_update_oh = addr_match_oh;
	assign data_update_oh = (IS_READ ? data_match_oh : data_match_first_oh);
	assign resp_update_oh = resp_match_oh;
	reg [N - 1:0] addr_alloc_oh;
	reg [N - 1:0] data_alloc_oh;
	reg [N - 1:0] resp_alloc_oh;
	wire addr_wants_alloc;
	reg data_wants_alloc;
	reg resp_wants_alloc;
	assign addr_wants_alloc = cmd_valid && !addr_hit_any;
	always @(*) begin
		if (_sv2v_0)
			;
		if (IS_READ)
			data_wants_alloc = (data_valid && data_ready) && !data_hit_any;
		else
			data_wants_alloc = ((data_valid && data_ready) && !IS_AXI) && !data_hit_any;
		resp_wants_alloc = ((!IS_READ && resp_valid) && resp_ready) && !resp_hit_any;
	end
	always @(*) begin : sv2v_autoblock_3
		reg [N - 1:0] remaining;
		reg taken;
		if (_sv2v_0)
			;
		addr_alloc_oh = 1'sb0;
		data_alloc_oh = 1'sb0;
		resp_alloc_oh = 1'sb0;
		taken = 1'b0;
		remaining = free_oh;
		if (addr_wants_alloc) begin
			taken = 1'b0;
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					if (!taken && remaining[i]) begin
						addr_alloc_oh[i] = 1'b1;
						remaining[i] = 1'b0;
						taken = 1'b1;
					end
			end
		end
		if (data_wants_alloc) begin
			taken = 1'b0;
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					if (!taken && remaining[i]) begin
						data_alloc_oh[i] = 1'b1;
						remaining[i] = 1'b0;
						taken = 1'b1;
					end
			end
		end
		if (resp_wants_alloc) begin
			taken = 1'b0;
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					if (!taken && remaining[i]) begin
						resp_alloc_oh[i] = 1'b1;
						remaining[i] = 1'b0;
						taken = 1'b1;
					end
			end
		end
	end
	reg [N - 1:0] w_can_cleanup;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (r_trans_table[(((N - 1) - i) * 285) + 284])
					(* full_case, parallel_case *)
					case (r_trans_table[(((N - 1) - i) * 285) + 277-:3])
						3'h3, 3'h4, 3'h5: w_can_cleanup[i] = r_trans_table[(((N - 1) - i) * 285) + 279];
						default: w_can_cleanup[i] = 1'b0;
					endcase
				else
					w_can_cleanup[i] = 1'b0;
		end
	end
	reg [5:0] w_addr_chan_idx;
	always @(*) begin
		if (_sv2v_0)
			;
		w_addr_chan_idx = (IS_AXI ? {24'h000000, cmd_id} % 64 : 0);
	end
	genvar _gv_gi_2;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_ORPHAN = 8'h02;
	localparam [7:0] monitor_amba4_pkg_EVT_PROTOCOL = 8'h04;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_DECERR = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_ORPHAN = 8'h03;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_SLVERR = 8'h00;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		for (_gv_gi_2 = 0; _gv_gi_2 < N; _gv_gi_2 = _gv_gi_2 + 1) begin : g_entry
			localparam gi = _gv_gi_2;
			wire cmd_handshake;
			assign cmd_handshake = cmd_valid && cmd_ready;
			always @(posedge aclk)
				if (!aresetn)
					r_trans_table[((N - 1) - gi) * 285+:285] <= 1'sb0;
				else begin
					if (addr_alloc_oh[gi]) begin
						r_trans_table[(((N - 1) - gi) * 285) + 284] <= 1'b1;
						r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h1;
						r_trans_table[(((N - 1) - gi) * 285) + 242-:8] <= 1'sb0;
						r_trans_table[(((N - 1) - gi) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))] <= cmd_id;
						r_trans_table[(((N - 1) - gi) * 285) + 274-:32] <= sv2v_cast_32(cmd_addr);
						r_trans_table[(((N - 1) - gi) * 285) + 234-:8] <= cmd_len;
						r_trans_table[(((N - 1) - gi) * 285) + 226-:3] <= cmd_size;
						r_trans_table[(((N - 1) - gi) * 285) + 223-:2] <= cmd_burst;
						r_trans_table[(((N - 1) - gi) * 285) + 283] <= cmd_ready;
						r_trans_table[(((N - 1) - gi) * 285) + 215-:32] <= 1'sb0;
						r_trans_table[(((N - 1) - gi) * 285) + 282] <= 1'b0;
						r_trans_table[(((N - 1) - gi) * 285) + 281] <= 1'b0;
						r_trans_table[(((N - 1) - gi) * 285) + 280] <= 1'b0;
						r_trans_table[(((N - 1) - gi) * 285) + 7-:8] <= 4'h0;
						r_trans_table[(((N - 1) - gi) * 285) + 279] <= 1'b0;
						r_trans_table[(((N - 1) - gi) * 285) + 183-:32] <= 1'sb0;
						r_trans_table[(((N - 1) - gi) * 285) + 151-:32] <= 1'sb0;
						r_trans_table[(((N - 1) - gi) * 285) + 119-:32] <= timestamp;
						r_trans_table[(((N - 1) - gi) * 285) + 23-:8] <= (IS_AXI ? cmd_len + 8'h01 : 8'h01);
						r_trans_table[(((N - 1) - gi) * 285) + 15-:8] <= 1'sb0;
						r_trans_table[(((N - 1) - gi) * 285) + 221-:6] <= w_addr_chan_idx;
						r_trans_table[(((N - 1) - gi) * 285) + 278] <= 1'b0;
					end
					if (addr_update_oh[gi] && cmd_handshake) begin
						r_trans_table[(((N - 1) - gi) * 285) + 283] <= 1'b1;
						r_trans_table[(((N - 1) - gi) * 285) + 215-:32] <= 1'sb0;
						r_trans_table[(((N - 1) - gi) * 285) + 119-:32] <= timestamp;
					end
					if (data_valid && data_ready) begin
						if (data_update_oh[gi]) begin
							r_trans_table[(((N - 1) - gi) * 285) + 282] <= 1'b1;
							r_trans_table[(((N - 1) - gi) * 285) + 15-:8] <= r_trans_table[(((N - 1) - gi) * 285) + 15-:8] + 1'b1;
							r_trans_table[(((N - 1) - gi) * 285) + 183-:32] <= 1'sb0;
							if (r_trans_table[(((N - 1) - gi) * 285) + 277-:3] != 3'h4)
								r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h2;
							if (IS_READ) begin
								if (data_last) begin
									r_trans_table[(((N - 1) - gi) * 285) + 281] <= 1'b1;
									r_trans_table[(((N - 1) - gi) * 285) + 87-:32] <= timestamp;
								end
								if (data_resp[1]) begin
									r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h4;
									r_trans_table[(((N - 1) - gi) * 285) + 7-:8] <= (data_resp[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
								end
								else if (data_last)
									r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h3;
							end
							else if (data_last || ((r_trans_table[(((N - 1) - gi) * 285) + 15-:8] + 1) == r_trans_table[(((N - 1) - gi) * 285) + 23-:8])) begin
								r_trans_table[(((N - 1) - gi) * 285) + 281] <= 1'b1;
								r_trans_table[(((N - 1) - gi) * 285) + 87-:32] <= timestamp;
							end
						end
						else if (data_alloc_oh[gi]) begin
							r_trans_table[(((N - 1) - gi) * 285) + 284] <= 1'b1;
							r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h5;
							r_trans_table[(((N - 1) - gi) * 285) + 242-:8] <= 1'sb0;
							if (IS_AXI) begin
								r_trans_table[(((N - 1) - gi) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))] <= data_id;
								r_trans_table[(((N - 1) - gi) * 285) + 221-:6] <= {24'h000000, data_id} % 64;
								r_trans_table[(((N - 1) - gi) * 285) + 23-:8] <= (IS_READ ? 8'h00 : 8'h01);
							end
							else begin
								r_trans_table[(((N - 1) - gi) * 285) + 23-:8] <= 8'h01;
								r_trans_table[(((N - 1) - gi) * 285) + 221-:6] <= 6'h00;
							end
							r_trans_table[(((N - 1) - gi) * 285) + 282] <= 1'b1;
							r_trans_table[(((N - 1) - gi) * 285) + 281] <= data_last;
							r_trans_table[(((N - 1) - gi) * 285) + 15-:8] <= 8'h01;
							r_trans_table[(((N - 1) - gi) * 285) + 87-:32] <= timestamp;
							r_trans_table[(((N - 1) - gi) * 285) + 7-:8] <= monitor_amba4_pkg_EVT_DATA_ORPHAN;
						end
					end
					if ((!IS_READ && resp_valid) && resp_ready) begin
						if (resp_update_oh[gi]) begin
							r_trans_table[(((N - 1) - gi) * 285) + 280] <= 1'b1;
							r_trans_table[(((N - 1) - gi) * 285) + 55-:32] <= timestamp;
							r_trans_table[(((N - 1) - gi) * 285) + 151-:32] <= 1'sb0;
							if (resp_code[1]) begin
								r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h4;
								r_trans_table[(((N - 1) - gi) * 285) + 7-:8] <= (resp_code[0] ? monitor_amba4_pkg_EVT_RESP_DECERR : monitor_amba4_pkg_EVT_RESP_SLVERR);
							end
							else if (r_trans_table[(((N - 1) - gi) * 285) + 281]) begin
								if (r_trans_table[(((N - 1) - gi) * 285) + 277-:3] != 3'h4)
									r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h3;
							end
							else begin
								r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h4;
								r_trans_table[(((N - 1) - gi) * 285) + 7-:8] <= monitor_amba4_pkg_EVT_PROTOCOL;
							end
						end
						else if (resp_alloc_oh[gi]) begin
							r_trans_table[(((N - 1) - gi) * 285) + 284] <= 1'b1;
							r_trans_table[(((N - 1) - gi) * 285) + 277-:3] <= 3'h5;
							r_trans_table[(((N - 1) - gi) * 285) + 242-:8] <= 1'sb0;
							if (IS_AXI) begin
								r_trans_table[(((N - 1) - gi) * 285) + ((234 + IW) >= 235 ? 234 + IW : ((234 + IW) + ((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))) - 1)-:((234 + IW) >= 235 ? (234 + IW) - 234 : 236 - (234 + IW))] <= resp_id;
								r_trans_table[(((N - 1) - gi) * 285) + 221-:6] <= resp_id % 64;
							end
							else
								r_trans_table[(((N - 1) - gi) * 285) + 221-:6] <= 6'h00;
							r_trans_table[(((N - 1) - gi) * 285) + 280] <= 1'b1;
							r_trans_table[(((N - 1) - gi) * 285) + 55-:32] <= timestamp;
							r_trans_table[(((N - 1) - gi) * 285) + 7-:8] <= monitor_amba4_pkg_EVT_RESP_ORPHAN;
						end
					end
					if (r_trans_table[(((N - 1) - gi) * 285) + 284] && w_can_cleanup[gi])
						r_trans_table[(((N - 1) - gi) * 285) + 284] <= 1'b0;
					if (i_event_reported_flags[gi] && !r_trans_table[(((N - 1) - gi) * 285) + 279])
						r_trans_table[(((N - 1) - gi) * 285) + 279] <= 1'b1;
				end
		end
	endgenerate
	reg [$clog2(N + 1) - 1:0] w_alloc_cnt;
	reg [$clog2(N + 1) - 1:0] w_cleanup_cnt;
	always @(*) begin
		if (_sv2v_0)
			;
		w_alloc_cnt = 1'sb0;
		begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_alloc_cnt = ((w_alloc_cnt + {{$clog2(N + 1) - 1 {1'b0}}, addr_alloc_oh[i]}) + {{$clog2(N + 1) - 1 {1'b0}}, data_alloc_oh[i]}) + {{$clog2(N + 1) - 1 {1'b0}}, resp_alloc_oh[i]};
		end
		w_cleanup_cnt = 1'sb0;
		begin : sv2v_autoblock_9
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_cleanup_cnt = w_cleanup_cnt + {{$clog2(N + 1) - 1 {1'b0}}, r_trans_table[(((N - 1) - i) * 285) + 284] && w_can_cleanup[i]};
		end
	end
	always @(posedge aclk)
		if (!aresetn)
			r_active_count <= 1'sb0;
		else
			r_active_count <= (r_active_count + {{8 - $clog2(N + 1) {1'b0}}, w_alloc_cnt}) - {{8 - $clog2(N + 1) {1'b0}}, w_cleanup_cnt};
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_10
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_trans_table_prev[((N - 1) - i) * 285+:285] <= 1'sb0;
			end
			r_state_change <= 1'sb0;
		end
		else begin
			r_trans_table_prev <= r_trans_table;
			begin : sv2v_autoblock_11
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_state_change[i] <= (r_trans_table[(((N - 1) - i) * 285) + 284] && r_trans_table_prev[(((N - 1) - i) * 285) + 284]) && (r_trans_table[(((N - 1) - i) * 285) + 277-:3] != r_trans_table_prev[(((N - 1) - i) * 285) + 277-:3]);
			end
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
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire timer_tick;
	input wire [3:0] cfg_addr_cnt;
	input wire [3:0] cfg_data_cnt;
	input wire [3:0] cfg_resp_cnt;
	input wire cfg_timeout_enable;
	output wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	reg [284:0] r_trans_table_local [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] r_timeout_detected;
	assign timeout_detected = r_timeout_detected;
	localparam [7:0] monitor_amba4_pkg_EVT_CMD_TIMEOUT = 8'h00;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_TIMEOUT = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_TIMEOUT = 8'h02;
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
						r_trans_table_local[idx] <= trans_table[((MAX_TRANSACTIONS - 1) - idx) * 285+:285];
						if (((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4)) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h0))
							r_timeout_detected[idx] <= 1'b0;
					end
			end
			if (timer_tick) begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (r_trans_table_local[idx][284] && !r_timeout_detected[idx]) begin
						if ((r_trans_table_local[idx][277-:3] == 3'h1) && !r_trans_table_local[idx][283]) begin
							r_trans_table_local[idx][215-:32] <= r_trans_table_local[idx][215-:32] + 1'b1;
							if (r_trans_table_local[idx][215-:32] >= {12'h000, cfg_addr_cnt}) begin
								r_trans_table_local[idx][277-:3] <= 3'h4;
								r_trans_table_local[idx][7-:8] <= monitor_amba4_pkg_EVT_CMD_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
						if (((((r_trans_table_local[idx][277-:3] == 3'h1) || (r_trans_table_local[idx][277-:3] == 3'h2)) && r_trans_table_local[idx][283]) && r_trans_table_local[idx][282]) && !r_trans_table_local[idx][281]) begin
							r_trans_table_local[idx][183-:32] <= r_trans_table_local[idx][183-:32] + 1'b1;
							if (r_trans_table_local[idx][183-:32] >= {12'h000, cfg_data_cnt}) begin
								r_trans_table_local[idx][277-:3] <= 3'h4;
								r_trans_table_local[idx][7-:8] <= monitor_amba4_pkg_EVT_DATA_TIMEOUT;
								r_timeout_detected[idx] <= 1'b1;
							end
						end
						if (((!IS_READ && (r_trans_table_local[idx][277-:3] == 3'h2)) && r_trans_table_local[idx][281]) && !r_trans_table_local[idx][280]) begin
							r_trans_table_local[idx][151-:32] <= r_trans_table_local[idx][151-:32] + 1'b1;
							if (r_trans_table_local[idx][151-:32] >= {12'h000, cfg_resp_cnt}) begin
								r_trans_table_local[idx][277-:3] <= 3'h4;
								r_trans_table_local[idx][7-:8] <= monitor_amba4_pkg_EVT_RESP_TIMEOUT;
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
	parameter [7:0] UNIT_ID = 8'h09;
	parameter [15:0] AGENT_ID = 16'h0063;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b0;
	parameter signed [31:0] INTR_FIFO_DEPTH = 8;
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
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
	reg [(MAX_TRANSACTIONS * 285) - 1:0] r_trans_table_local;
	reg [MAX_TRANSACTIONS - 1:0] r_event_reported;
	assign event_reported_flags = r_event_reported;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	function automatic [63:0] pad_address;
		input reg [31:0] addr;
		pad_address = sv2v_cast_64(addr);
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
	reg [3:0] r_packet_type;
	reg [7:0] r_event_code;
	reg [63:0] r_event_data;
	reg [8:0] r_event_channel;
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
	reg [31:0] r_latency [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] r_latency_over_thresh;
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
				if (((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && !r_event_reported[idx]) && cfg_error_enable) && (((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4) && !timeout_detected[idx]) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h5)))
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
				if ((((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && !r_event_reported[idx]) && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4)) && cfg_timeout_enable) && timeout_detected[idx])
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
				if (((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && !r_event_reported[idx]) && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) && cfg_compl_enable)
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
	localparam [7:0] monitor_amba4_pkg_EVT_TRANS_COMPLETE = 8'h00;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	always @(*) begin
		if (_sv2v_0)
			;
		w_fifo_wr_valid = 1'b0;
		w_fifo_wr_data = 85'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
		if (w_has_error_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = monitor_common_pkg_PktTypeError;
			w_fifo_wr_data[80-:8] = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_error_idx) * 285) + 7-:8];
			w_fifo_wr_data[72-:9] = {3'b000, r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_error_idx) * 285) + 221-:6]};
			w_fifo_wr_data[63-:64] = pad_address(r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_error_idx) * 285) + 274-:32]);
		end
		else if (w_has_timeout_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = monitor_common_pkg_PktTypeTimeout;
			w_fifo_wr_data[80-:8] = r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_timeout_idx) * 285) + 7-:8];
			w_fifo_wr_data[72-:9] = {3'b000, r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_timeout_idx) * 285) + 221-:6]};
			w_fifo_wr_data[63-:64] = pad_address(r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_timeout_idx) * 285) + 274-:32]);
		end
		else if (w_has_completion_event) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = monitor_common_pkg_PktTypeCompletion;
			w_fifo_wr_data[80-:8] = monitor_amba4_pkg_EVT_TRANS_COMPLETE;
			w_fifo_wr_data[72-:9] = {3'b000, r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_completion_idx) * 285) + 221-:6]};
			w_fifo_wr_data[63-:64] = pad_address(r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_completion_idx) * 285) + 274-:32]);
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
				if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284]) begin
					if ((((((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h5)) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) && !r_event_reported[idx]) && w_fifo_wr_valid) && w_fifo_wr_ready) begin
						w_events_to_mark[idx] = 1'b1;
						if ((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h5))
							w_error_events[idx] = 1'b1;
						else if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)
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
				if ((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] != 3'h3)) && (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] != 3'h4))
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
			w_latency_threshold_events = r_latency_over_thresh;
			begin : sv2v_autoblock_9
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
		if (w_has_latency_event)
			w_selected_latency_value = r_latency[w_selected_latency_idx];
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
	localparam [7:0] monitor_amba4_pkg_EVT_NONE = 8'h00;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	always @(posedge aclk)
		if (!aresetn) begin
			r_trans_table_local <= {MAX_TRANSACTIONS {285'b0}};
			monbus_valid <= 1'b0;
			r_event_count <= 1'sb0;
			r_event_reported <= 1'sb0;
			r_perf_completed_count <= 1'sb0;
			r_perf_error_count <= 1'sb0;
			r_active_threshold_crossed <= 1'b0;
			r_latency_threshold_crossed <= 1'b0;
			begin : sv2v_autoblock_10
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_latency[idx] <= 1'sb0;
			end
			r_latency_over_thresh <= 1'sb0;
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
					r_trans_table_local[((MAX_TRANSACTIONS - 1) - idx) * 285+:285] <= trans_table[((MAX_TRANSACTIONS - 1) - idx) * 285+:285];
			end
			begin : sv2v_autoblock_12
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin : g_lat
						reg [31:0] lat;
						if (IS_READ)
							lat = trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 87-:32] - trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 119-:32];
						else
							lat = trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 55-:32] - trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 119-:32];
						r_latency[idx] <= lat;
						r_latency_over_thresh[idx] <= ((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) && (lat > latency_threshold)) && !r_latency_threshold_crossed;
					end
			end
			if (monbus_valid && monbus_ready)
				monbus_valid <= 1'b0;
			if (!monbus_valid && w_fifo_rd_valid) begin
				monbus_valid <= 1'b1;
				r_packet_type <= w_fifo_rd_data[84-:4];
				r_event_code <= w_fifo_rd_data[80-:8];
				r_event_data <= w_fifo_rd_data[63-:64];
				r_event_channel <= w_fifo_rd_data[72-:9];
			end
			begin : sv2v_autoblock_13
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						if (!r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284])
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
					r_event_code <= 8'h00;
					r_event_data <= sv2v_cast_64(w_active_count_current);
					r_event_channel <= 1'sb0;
					r_active_threshold_crossed <= 1'b1;
					r_event_count <= r_event_count + 1'b1;
				end
				else if ({8'h00, w_active_count_current} <= active_trans_threshold)
					r_active_threshold_crossed <= 1'b0;
				if ((w_has_latency_event && !monbus_valid) && (w_fifo_rd_valid == 0)) begin
					monbus_valid <= 1'b1;
					r_packet_type <= monitor_common_pkg_PktTypeThreshold;
					r_event_code <= 8'h01;
					r_event_data <= pad_address(w_selected_latency_value);
					r_event_channel <= {3'b000, r_trans_table_local[(((MAX_TRANSACTIONS - 1) - w_selected_latency_idx) * 285) + 221-:6]};
					r_latency_threshold_crossed <= 1'b1;
					r_event_count <= r_event_count + 1'b1;
				end
			end
			if (w_generate_perf_packet_completed) begin
				monbus_valid <= 1'b1;
				r_packet_type <= monitor_common_pkg_PktTypePerf;
				r_event_code <= 8'h07;
				r_event_data <= sv2v_cast_64(r_perf_completed_count);
				r_event_channel <= 1'sb0;
			end
			if (w_generate_perf_packet_errors) begin
				monbus_valid <= 1'b1;
				r_packet_type <= monitor_common_pkg_PktTypePerf;
				r_event_code <= 8'h08;
				r_event_data <= sv2v_cast_64(r_perf_error_count);
				r_event_channel <= 1'sb0;
			end
			r_perf_report_state <= w_next_perf_report_state;
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
	always @(*) begin
		if (_sv2v_0)
			;
		monbus_packet = monitor_common_pkg_create_monitor_packet(r_packet_type, 4'h0, r_event_code, r_event_channel, UNIT_ID, AGENT_ID, r_event_data);
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
	cfg_addr_check_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	block_ready,
	busy,
	active_count
);
	reg _sv2v_0;
	parameter [7:0] UNIT_ID = 8'h09;
	parameter [15:0] AGENT_ID = 16'h0063;
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
	parameter signed [31:0] N_ADDR_RANGES = 0;
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
	input wire cfg_addr_check_enable;
	input wire [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] cfg_addr_range_enable;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_low;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * AW) - 1:0] cfg_addr_range_high;
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
	wire [(MAX_TRANSACTIONS * 285) - 1:0] w_trans_table;
	wire [MAX_TRANSACTIONS - 1:0] w_event_reported_flags;
	wire [7:0] w_active_count;
	wire [15:0] w_event_count;
	wire [15:0] w_debug_count;
	wire w_timer_tick;
	wire [31:0] r_timestamp;
	wire [MAX_TRANSACTIONS - 1:0] w_state_change_detected;
	wire [MAX_TRANSACTIONS - 1:0] w_timeout_detected;
	wire w_reporter_monbus_valid;
	wire [127:0] w_reporter_monbus_packet;
	wire w_debug_monbus_valid;
	wire [127:0] w_debug_monbus_packet;
	wire w_addr_pkt_valid;
	wire [127:0] w_addr_pkt_data;
	wire [63:0] w_addr_pkt_timestamp;
	wire w_addr_pkt_ready;
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
	generate
		if (N_ADDR_RANGES > 0) begin : gen_addr_check
			axi_monitor_addr_check #(
				.N_ADDR_RANGES(N_ADDR_RANGES),
				.ADDR_WIDTH(ADDR_WIDTH),
				.ID_WIDTH((ID_WIDTH > 0 ? ID_WIDTH : 1)),
				.UNIT_ID(UNIT_ID),
				.AGENT_ID(AGENT_ID),
				.IS_READ(IS_READ)
			) addr_check(
				.clk(aclk),
				.aresetn(aresetn),
				.i_mon_time(i_mon_time),
				.cmd_addr(cmd_addr),
				.cmd_id(cmd_id),
				.cmd_valid(cmd_valid),
				.cmd_ready(cmd_ready),
				.cfg_addr_check_enable(cfg_addr_check_enable),
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
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_reporter_monbus_valid) begin
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
	assign w_addr_pkt_ready = (monbus_ready && !w_reporter_monbus_valid) && !w_debug_monbus_valid;
	assign block_ready = (MAX_TRANSACTIONS > 2 ? {24'h000000, w_active_count} < (MAX_TRANSACTIONS - 2) : 1'b1);
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
	cfg_addr_check_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	block_ready,
	busy,
	active_count,
	cfg_conflict_error
);
	reg _sv2v_0;
	parameter [7:0] UNIT_ID = 8'h01;
	parameter [15:0] AGENT_ID = 16'h000a;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter [0:0] IS_READ = 1'b1;
	parameter [0:0] IS_AXI = 1'b1;
	parameter [0:0] ENABLE_PERF_PACKETS = 1'b1;
	parameter [0:0] ENABLE_DEBUG_MODULE = 1'b0;
	parameter [0:0] ENABLE_FILTERING = 1;
	parameter [0:0] ADD_PIPELINE_STAGE = 0;
	parameter signed [31:0] N_ADDR_RANGES = 0;
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
	input wire cfg_addr_check_enable;
	input wire [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) - 1:0] cfg_addr_range_enable;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * ADDR_WIDTH) - 1:0] cfg_addr_range_low;
	input wire [((N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1) * ADDR_WIDTH) - 1:0] cfg_addr_range_high;
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
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
		.ADDR_WIDTH(ADDR_WIDTH),
		.ID_WIDTH(ID_WIDTH),
		.IS_READ(IS_READ),
		.IS_AXI(IS_AXI),
		.ENABLE_PERF_PACKETS(ENABLE_PERF_PACKETS),
		.ENABLE_DEBUG_MODULE(ENABLE_DEBUG_MODULE),
		.N_ADDR_RANGES(N_ADDR_RANGES)
	) u_axi_monitor_base(
		.aclk(aclk),
		.aresetn(aresetn),
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
		.monbus_valid(base_monbus_valid),
		.monbus_ready(base_monbus_ready),
		.monbus_packet(base_monbus_packet),
		.monbus_timestamp(base_monbus_timestamp),
		.block_ready(block_ready),
		.busy(busy),
		.active_count(active_count)
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
