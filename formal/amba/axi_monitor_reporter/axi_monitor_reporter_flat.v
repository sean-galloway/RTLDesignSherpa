module axi_monitor_reporter_compl (
	trans_table,
	event_reported,
	cfg_compl_enable,
	pkt_valid,
	pkt_type,
	pkt_event_code,
	pkt_channel,
	pkt_data,
	sel_idx
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] IDX_W = $clog2(MAX_TRANSACTIONS);
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire [MAX_TRANSACTIONS - 1:0] event_reported;
	input wire cfg_compl_enable;
	output wire pkt_valid;
	output wire [3:0] pkt_type;
	output wire [7:0] pkt_event_code;
	output wire [8:0] pkt_channel;
	output wire [63:0] pkt_data;
	output wire [IDX_W - 1:0] sel_idx;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	function automatic [63:0] pad_address;
		input reg [31:0] addr;
		pad_address = sv2v_cast_64(addr);
	endfunction
	reg [MAX_TRANSACTIONS - 1:0] w_events;
	reg [IDX_W - 1:0] w_sel;
	reg w_has_event;
	always @(*) begin
		if (_sv2v_0)
			;
		w_events = 1'sb0;
		w_sel = 1'sb0;
		w_has_event = 1'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && !event_reported[idx]) && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) && cfg_compl_enable)
					w_events[idx] = 1'b1;
		end
		begin : sv2v_autoblock_2
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (w_events[idx] && !w_has_event) begin
					w_sel = idx[IDX_W - 1:0];
					w_has_event = 1'b1;
				end
		end
	end
	assign pkt_valid = w_has_event;
	assign sel_idx = w_sel;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	assign pkt_type = monitor_common_pkg_PktTypeCompletion;
	localparam [7:0] monitor_amba4_pkg_EVT_TRANS_COMPLETE = 8'h00;
	assign pkt_event_code = monitor_amba4_pkg_EVT_TRANS_COMPLETE;
	assign pkt_channel = {3'b000, trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 221-:6]};
	assign pkt_data = pad_address(trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 274-:32]);
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_reporter_debug (
	aclk,
	aresetn,
	trans_table,
	cfg_debug_enable,
	output_busy,
	pkt_taken,
	pkt_valid,
	pkt_type,
	pkt_event_code,
	pkt_channel,
	pkt_data
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] IDX_W = $clog2(MAX_TRANSACTIONS);
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire cfg_debug_enable;
	input wire output_busy;
	input wire pkt_taken;
	output reg pkt_valid;
	output reg [3:0] pkt_type;
	output reg [7:0] pkt_event_code;
	output reg [8:0] pkt_channel;
	output reg [63:0] pkt_data;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	function automatic [63:0] pad_address;
		input reg [31:0] addr;
		pad_address = sv2v_cast_64(addr);
	endfunction
	reg [2:0] r_prev_state [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] w_changed;
	reg [IDX_W - 1:0] w_sel;
	reg w_has_event;
	always @(*) begin
		if (_sv2v_0)
			;
		w_changed = 1'sb0;
		w_sel = 1'sb0;
		w_has_event = 1'b0;
		if (cfg_debug_enable) begin
			begin : sv2v_autoblock_1
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] != r_prev_state[idx]))
						w_changed[idx] = 1'b1;
			end
			begin : sv2v_autoblock_2
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					if (w_changed[idx] && !w_has_event) begin
						w_sel = idx[IDX_W - 1:0];
						w_has_event = 1'b1;
					end
			end
		end
	end
	always @(posedge aclk)
		if (!aresetn) begin : sv2v_autoblock_3
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				r_prev_state[idx] <= 3'h0;
		end
		else begin : sv2v_autoblock_4
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (!trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284])
					r_prev_state[idx] <= 3'h0;
				else
					r_prev_state[idx] <= trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3];
		end
	localparam [3:0] monitor_common_pkg_PktTypeDebug = 4'hf;
	always @(*) begin
		if (_sv2v_0)
			;
		pkt_valid = 1'b0;
		pkt_type = monitor_common_pkg_PktTypeDebug;
		pkt_event_code = 8'h00;
		pkt_channel = 1'sb0;
		pkt_data = 1'sb0;
		if (w_has_event && !output_busy) begin
			pkt_valid = 1'b1;
			pkt_event_code = 8'h00;
			pkt_channel = {3'b000, trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 221-:6]};
			pkt_data = {r_prev_state[w_sel], trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 277-:3], 26'h0000000, trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 274-:32]};
		end
	end
	wire unused_pkt_taken;
	assign unused_pkt_taken = pkt_taken;
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_reporter_error (
	trans_table,
	event_reported,
	timeout_detected,
	cfg_error_enable,
	pkt_valid,
	pkt_type,
	pkt_event_code,
	pkt_channel,
	pkt_data,
	sel_idx
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] IDX_W = $clog2(MAX_TRANSACTIONS);
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire [MAX_TRANSACTIONS - 1:0] event_reported;
	input wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	input wire cfg_error_enable;
	output wire pkt_valid;
	output wire [3:0] pkt_type;
	output wire [7:0] pkt_event_code;
	output wire [8:0] pkt_channel;
	output wire [63:0] pkt_data;
	output wire [IDX_W - 1:0] sel_idx;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	function automatic [63:0] pad_address;
		input reg [31:0] addr;
		pad_address = sv2v_cast_64(addr);
	endfunction
	reg [MAX_TRANSACTIONS - 1:0] w_events;
	reg [IDX_W - 1:0] w_sel;
	reg w_has_event;
	always @(*) begin
		if (_sv2v_0)
			;
		w_events = 1'sb0;
		w_sel = 1'sb0;
		w_has_event = 1'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && !event_reported[idx]) && cfg_error_enable) && (((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4) && !timeout_detected[idx]) || (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h5)))
					w_events[idx] = 1'b1;
		end
		begin : sv2v_autoblock_2
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (w_events[idx] && !w_has_event) begin
					w_sel = idx[IDX_W - 1:0];
					w_has_event = 1'b1;
				end
		end
	end
	assign pkt_valid = w_has_event;
	assign sel_idx = w_sel;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	assign pkt_type = monitor_common_pkg_PktTypeError;
	assign pkt_event_code = trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 7-:8];
	assign pkt_channel = {3'b000, trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 221-:6]};
	assign pkt_data = pad_address(trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 274-:32]);
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_reporter_perf (
	aclk,
	aresetn,
	cfg_perf_enable,
	output_busy,
	pkt_taken,
	error_marked_mask,
	compl_marked_mask,
	pkt_valid,
	pkt_type,
	pkt_event_code,
	pkt_channel,
	pkt_data,
	perf_completed_count,
	perf_error_count
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	input wire aclk;
	input wire aresetn;
	input wire cfg_perf_enable;
	input wire output_busy;
	input wire pkt_taken;
	input wire [MAX_TRANSACTIONS - 1:0] error_marked_mask;
	input wire [MAX_TRANSACTIONS - 1:0] compl_marked_mask;
	output reg pkt_valid;
	output reg [3:0] pkt_type;
	output reg [7:0] pkt_event_code;
	output reg [8:0] pkt_channel;
	output reg [63:0] pkt_data;
	output wire [15:0] perf_completed_count;
	output wire [15:0] perf_error_count;
	reg [15:0] r_completed_count;
	reg [15:0] r_error_count;
	assign perf_completed_count = r_completed_count;
	assign perf_error_count = r_error_count;
	reg [2:0] r_state;
	reg [2:0] w_next_state;
	reg w_gen_completed;
	reg w_gen_errors;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_state;
		w_gen_completed = 1'b0;
		w_gen_errors = 1'b0;
		if (cfg_perf_enable && !output_busy)
			case (r_state)
				3'h0: w_next_state = 3'h1;
				3'h1: w_next_state = 3'h2;
				3'h2: w_next_state = 3'h3;
				3'h3: begin
					w_next_state = 3'h4;
					if (r_completed_count > 0)
						w_gen_completed = 1'b1;
				end
				3'h4: begin
					w_next_state = 3'h0;
					if (r_error_count > 0)
						w_gen_errors = 1'b1;
				end
				default: w_next_state = 3'h0;
			endcase
	end
	always @(posedge aclk)
		if (!aresetn) begin
			r_completed_count <= 1'sb0;
			r_error_count <= 1'sb0;
			r_state <= 3'h0;
		end
		else begin
			begin : sv2v_autoblock_1
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin
						if (error_marked_mask[idx])
							r_error_count <= r_error_count + 1'b1;
						if (compl_marked_mask[idx])
							r_completed_count <= r_completed_count + 1'b1;
					end
			end
			r_state <= w_next_state;
		end
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		pkt_valid = 1'b0;
		pkt_type = monitor_common_pkg_PktTypePerf;
		pkt_event_code = 8'h07;
		pkt_channel = 1'sb0;
		pkt_data = 1'sb0;
		if (w_gen_completed) begin
			pkt_valid = 1'b1;
			pkt_event_code = 8'h07;
			pkt_data = sv2v_cast_64(r_completed_count);
		end
		else if (w_gen_errors) begin
			pkt_valid = 1'b1;
			pkt_event_code = 8'h08;
			pkt_data = sv2v_cast_64(r_error_count);
		end
	end
	wire unused_pkt_taken;
	assign unused_pkt_taken = pkt_taken;
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_reporter_threshold (
	aclk,
	aresetn,
	trans_table,
	cfg_threshold_enable,
	active_trans_threshold,
	latency_threshold,
	output_busy,
	pkt_taken,
	pkt_valid,
	pkt_type,
	pkt_event_code,
	pkt_channel,
	pkt_data
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter [0:0] IS_READ = 1'b1;
	parameter signed [31:0] IDX_W = $clog2(MAX_TRANSACTIONS);
	input wire aclk;
	input wire aresetn;
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire cfg_threshold_enable;
	input wire [15:0] active_trans_threshold;
	input wire [31:0] latency_threshold;
	input wire output_busy;
	input wire pkt_taken;
	output reg pkt_valid;
	output reg [3:0] pkt_type;
	output reg [7:0] pkt_event_code;
	output reg [8:0] pkt_channel;
	output reg [63:0] pkt_data;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	function automatic [63:0] pad_address;
		input reg [31:0] v;
		pad_address = sv2v_cast_64(v);
	endfunction
	reg r_active_crossed;
	reg r_latency_crossed;
	reg [31:0] r_latency [0:MAX_TRANSACTIONS - 1];
	reg [MAX_TRANSACTIONS - 1:0] r_latency_over_thresh;
	reg [7:0] w_active_count;
	reg w_active_detect;
	always @(*) begin
		if (_sv2v_0)
			;
		w_active_count = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] != 3'h3)) && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] != 3'h4))
					w_active_count = w_active_count + 1'b1;
		end
		w_active_detect = ((cfg_threshold_enable && ({8'h00, w_active_count} > active_trans_threshold)) && !r_active_crossed) && !output_busy;
	end
	reg [IDX_W - 1:0] w_lat_sel;
	reg w_has_lat;
	always @(*) begin
		if (_sv2v_0)
			;
		w_lat_sel = 1'sb0;
		w_has_lat = 1'b0;
		if (cfg_threshold_enable) begin : sv2v_autoblock_2
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (r_latency_over_thresh[idx] && !w_has_lat) begin
					w_lat_sel = idx[IDX_W - 1:0];
					w_has_lat = 1'b1;
				end
		end
	end
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_3
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					r_latency[idx] <= 1'sb0;
			end
			r_latency_over_thresh <= 1'sb0;
			r_active_crossed <= 1'b0;
			r_latency_crossed <= 1'b0;
		end
		else begin
			begin : sv2v_autoblock_4
				reg signed [31:0] idx;
				for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
					begin : sv2v_autoblock_5
						reg [31:0] lat;
						if (IS_READ)
							lat = trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 87-:32] - trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 119-:32];
						else
							lat = trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 55-:32] - trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 119-:32];
						r_latency[idx] <= lat;
						r_latency_over_thresh[idx] <= ((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) && (lat > latency_threshold)) && !r_latency_crossed;
					end
			end
			if (((w_active_detect && pkt_taken) && (pkt_type == monitor_common_pkg_PktTypeThreshold)) && (pkt_event_code == 8'h00))
				r_active_crossed <= 1'b1;
			else if ({8'h00, w_active_count} <= active_trans_threshold)
				r_active_crossed <= 1'b0;
			if (((w_has_lat && pkt_taken) && (pkt_type == monitor_common_pkg_PktTypeThreshold)) && (pkt_event_code == 8'h01))
				r_latency_crossed <= 1'b1;
		end
	always @(*) begin
		if (_sv2v_0)
			;
		pkt_valid = 1'b0;
		pkt_type = monitor_common_pkg_PktTypeThreshold;
		pkt_event_code = 8'h00;
		pkt_channel = 1'sb0;
		pkt_data = 1'sb0;
		if (w_active_detect) begin
			pkt_valid = 1'b1;
			pkt_event_code = 8'h00;
			pkt_data = sv2v_cast_64(w_active_count);
			pkt_channel = 1'sb0;
		end
		else if (w_has_lat && !output_busy) begin
			pkt_valid = 1'b1;
			pkt_event_code = 8'h01;
			pkt_data = pad_address(r_latency[w_lat_sel]);
			pkt_channel = {3'b000, trans_table[(((MAX_TRANSACTIONS - 1) - w_lat_sel) * 285) + 221-:6]};
		end
	end
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_reporter_timeout (
	trans_table,
	event_reported,
	timeout_detected,
	cfg_timeout_enable,
	pkt_valid,
	pkt_type,
	pkt_event_code,
	pkt_channel,
	pkt_data,
	sel_idx
);
	reg _sv2v_0;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
	parameter signed [31:0] IDX_W = $clog2(MAX_TRANSACTIONS);
	input wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	input wire [MAX_TRANSACTIONS - 1:0] event_reported;
	input wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	input wire cfg_timeout_enable;
	output wire pkt_valid;
	output wire [3:0] pkt_type;
	output wire [7:0] pkt_event_code;
	output wire [8:0] pkt_channel;
	output wire [63:0] pkt_data;
	output wire [IDX_W - 1:0] sel_idx;
	function automatic [63:0] sv2v_cast_64;
		input reg [63:0] inp;
		sv2v_cast_64 = inp;
	endfunction
	function automatic [63:0] pad_address;
		input reg [31:0] addr;
		pad_address = sv2v_cast_64(addr);
	endfunction
	reg [MAX_TRANSACTIONS - 1:0] w_events;
	reg [IDX_W - 1:0] w_sel;
	reg w_has_event;
	always @(*) begin
		if (_sv2v_0)
			;
		w_events = 1'sb0;
		w_sel = 1'sb0;
		w_has_event = 1'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((((trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && !event_reported[idx]) && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4)) && cfg_timeout_enable) && timeout_detected[idx])
					w_events[idx] = 1'b1;
		end
		begin : sv2v_autoblock_2
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if (w_events[idx] && !w_has_event) begin
					w_sel = idx[IDX_W - 1:0];
					w_has_event = 1'b1;
				end
		end
	end
	assign pkt_valid = w_has_event;
	assign sel_idx = w_sel;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	assign pkt_type = monitor_common_pkg_PktTypeTimeout;
	assign pkt_event_code = trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 7-:8];
	assign pkt_channel = {3'b000, trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 221-:6]};
	assign pkt_data = pad_address(trans_table[(((MAX_TRANSACTIONS - 1) - w_sel) * 285) + 274-:32]);
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
	always @(*) begin
		if (_sv2v_0)
			;
		w_fifo_wr_valid = 1'b0;
		w_fifo_wr_data = 85'b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000;
		if (err_valid) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = err_type;
			w_fifo_wr_data[80-:8] = err_code;
			w_fifo_wr_data[72-:9] = err_chan;
			w_fifo_wr_data[63-:64] = err_data;
		end
		else if (to_valid) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = to_type;
			w_fifo_wr_data[80-:8] = to_code;
			w_fifo_wr_data[72-:9] = to_chan;
			w_fifo_wr_data[63-:64] = to_data;
		end
		else if (compl_valid) begin
			w_fifo_wr_valid = 1'b1;
			w_fifo_wr_data[84-:4] = compl_type;
			w_fifo_wr_data[80-:8] = compl_code;
			w_fifo_wr_data[72-:9] = compl_chan;
			w_fifo_wr_data[63-:64] = compl_data;
		end
	end
	assign w_fifo_rd_ready = monbus_ready && monbus_valid;
	reg [MAX_TRANSACTIONS - 1:0] w_events_to_mark;
	reg [MAX_TRANSACTIONS - 1:0] w_error_events;
	reg [MAX_TRANSACTIONS - 1:0] w_completion_events;
	always @(*) begin
		if (_sv2v_0)
			;
		w_events_to_mark = 1'sb0;
		w_error_events = 1'sb0;
		w_completion_events = 1'sb0;
		begin : sv2v_autoblock_1
			reg signed [31:0] idx;
			for (idx = 0; idx < MAX_TRANSACTIONS; idx = idx + 1)
				if ((((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h5)) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3))) && !r_event_reported[idx]) && w_fifo_wr_valid) && w_fifo_wr_ready) begin
					w_events_to_mark[idx] = 1'b1;
					if ((r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h4) || (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h5))
						w_error_events[idx] = 1'b1;
					else if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)
						w_completion_events[idx] = 1'b1;
				end
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
					else if (w_events_to_mark[idx]) begin
						r_event_reported[idx] <= 1'b1;
						r_event_count <= r_event_count + 1'b1;
					end
			end
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
				r_event_count <= r_event_count + 1'b1;
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
