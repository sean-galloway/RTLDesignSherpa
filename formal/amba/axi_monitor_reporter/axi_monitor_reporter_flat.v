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
	localparam signed [31:0] ADDR_PAD_WIDTH = (ADDR_WIDTH <= 38 ? 38 - ADDR_WIDTH : 0);
	localparam [0:0] ADDR_NEEDS_TRUNCATE = ADDR_WIDTH > 38;
	function automatic [37:0] pad_address;
		input reg [ADDR_WIDTH - 1:0] addr;
		if (ADDR_NEEDS_TRUNCATE)
			pad_address = addr[37:0];
		else
			pad_address = {{ADDR_PAD_WIDTH {1'b0}}, addr};
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
