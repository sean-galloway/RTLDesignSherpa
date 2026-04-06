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
