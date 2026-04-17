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
