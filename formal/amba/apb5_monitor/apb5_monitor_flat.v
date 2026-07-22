module apb_monitor_addr_check (
	clk,
	aresetn,
	i_mon_time,
	cmd_paddr,
	cmd_pwrite,
	cmd_valid,
	cmd_ready,
	cfg_addr_check_enable,
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
	parameter [7:0] UNIT_ID = 8'h00;
	parameter [15:0] AGENT_ID = 16'h0000;
	parameter signed [31:0] M = ADDR_WIDTH;
	input wire clk;
	input wire aresetn;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	input wire [M - 1:0] cmd_paddr;
	input wire cmd_pwrite;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire cfg_addr_check_enable;
	input wire [N_ADDR_RANGES - 1:0] cfg_addr_range_enable;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_low;
	input wire [(N_ADDR_RANGES * M) - 1:0] cfg_addr_range_high;
	output wire addr_pkt_valid;
	input wire addr_pkt_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] addr_pkt_data;
	output wire [63:0] addr_pkt_timestamp;
	wire cmd_fire;
	reg [N_ADDR_RANGES - 1:0] hit_oh;
	assign cmd_fire = (cmd_valid && cmd_ready) && cfg_addr_check_enable;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				hit_oh[i] = ((cfg_addr_range_enable[i] && cmd_fire) && (cmd_paddr >= cfg_addr_range_low[i * M+:M])) && (cmd_paddr <= cfg_addr_range_high[i * M+:M]);
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_pending;
	reg [(N_ADDR_RANGES * M) - 1:0] r_lat_addr;
	reg [N_ADDR_RANGES - 1:0] r_lat_is_read;
	reg [N_ADDR_RANGES - 1:0] emit_oh;
	wire emit_any;
	reg [3:0] emit_idx;
	assign emit_any = |r_pending;
	function automatic signed [3:0] sv2v_cast_4_signed;
		input reg signed [3:0] inp;
		sv2v_cast_4_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		emit_oh = 1'sb0;
		emit_idx = 4'h0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (r_pending[i] && (emit_oh == {N_ADDR_RANGES {1'sb0}})) begin
					emit_oh[i] = 1'b1;
					emit_idx = sv2v_cast_4_signed(i);
				end
		end
	end
	assign addr_pkt_valid = emit_any && cfg_addr_check_enable;
	wire accept;
	assign accept = addr_pkt_valid && addr_pkt_ready;
	always @(posedge clk)
		if (!aresetn) begin
			r_pending <= 1'sb0;
			r_lat_addr <= 1'sb0;
			r_lat_is_read <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (hit_oh[i]) begin
						r_lat_addr[i * M+:M] <= cmd_paddr;
						r_lat_is_read[i] <= !cmd_pwrite;
					end
			end
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (hit_oh[i])
						r_pending[i] <= 1'b1;
					else if (accept && emit_oh[i])
						r_pending[i] <= 1'b0;
			end
		end
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] PKT_TYPE_FIELD = monitor_common_pkg_PktTypeError;
	localparam [3:0] PROTOCOL_FIELD = 4'h2;
	localparam [7:0] EVENT_CODE = 8'h08;
	reg [M - 1:0] emit_addr;
	reg emit_is_read;
	wire [63:0] event_data_field;
	wire [58:0] addr_payload;
	always @(*) begin
		if (_sv2v_0)
			;
		emit_addr = 1'sb0;
		emit_is_read = 1'b0;
		begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (emit_oh[i]) begin
					emit_addr = r_lat_addr[i * M+:M];
					emit_is_read = r_lat_is_read[i];
				end
		end
	end
	generate
		if (M >= 59) begin : g_addr_wide
			assign addr_payload = emit_addr[58:0];
		end
		else begin : g_addr_narrow
			assign addr_payload = {{59 - M {1'b0}}, emit_addr};
		end
	endgenerate
	assign event_data_field = {emit_idx[3:0], emit_is_read, addr_payload};
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
	assign addr_pkt_data = monitor_common_pkg_create_monitor_packet(PKT_TYPE_FIELD, PROTOCOL_FIELD, EVENT_CODE, 9'h000, UNIT_ID, AGENT_ID, event_data_field);
	assign addr_pkt_timestamp = i_mon_time;
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
	genvar _gv_gi_1;
	generate
		for (_gv_gi_1 = 0; _gv_gi_1 < DEPTH; _gv_gi_1 = _gv_gi_1 + 1) begin : g_slot
			localparam gi = _gv_gi_1;
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
module apb5_monitor (
	aclk,
	aresetn,
	cmd_valid,
	cmd_ready,
	cmd_pwrite,
	cmd_paddr,
	cmd_pwdata,
	cmd_pstrb,
	cmd_pprot,
	cmd_pauser,
	cmd_pwuser,
	rsp_valid,
	rsp_ready,
	rsp_prdata,
	rsp_pslverr,
	rsp_pruser,
	rsp_pbuser,
	apb5_pwakeup,
	parity_error_wdata,
	parity_error_rdata,
	parity_error_ctrl,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_protocol_enable,
	cfg_slverr_enable,
	cfg_parity_enable,
	cfg_wakeup_enable,
	cfg_user_enable,
	cfg_perf_enable,
	cfg_latency_enable,
	cfg_cmd_timeout_cnt,
	cfg_rsp_timeout_cnt,
	cfg_latency_threshold,
	cfg_wakeup_timeout_cnt,
	cfg_addr_check_enable,
	cfg_addr_range_enable,
	cfg_addr_range_low,
	cfg_addr_range_high,
	i_mon_time,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	active_count,
	error_count,
	transaction_count,
	wakeup_active
);
	reg _sv2v_0;
	parameter [0:0] USE_MONITOR = 1'b1;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] AUSER_WIDTH = 4;
	parameter signed [31:0] WUSER_WIDTH = 4;
	parameter signed [31:0] RUSER_WIDTH = 4;
	parameter signed [31:0] BUSER_WIDTH = 4;
	parameter [7:0] UNIT_ID = 8'h01;
	parameter [15:0] AGENT_ID = 16'h000a;
	parameter signed [31:0] MAX_TRANSACTIONS = 4;
	parameter signed [31:0] MONITOR_FIFO_DEPTH = 8;
	parameter [0:0] ENABLE_PARITY_MON = 0;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = DW / 8;
	parameter signed [31:0] AUW = AUSER_WIDTH;
	parameter signed [31:0] WUW = WUSER_WIDTH;
	parameter signed [31:0] RUW = RUSER_WIDTH;
	parameter signed [31:0] BUW = BUSER_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire cmd_valid;
	input wire cmd_ready;
	input wire cmd_pwrite;
	input wire [AW - 1:0] cmd_paddr;
	input wire [DW - 1:0] cmd_pwdata;
	input wire [SW - 1:0] cmd_pstrb;
	input wire [2:0] cmd_pprot;
	input wire [AUW - 1:0] cmd_pauser;
	input wire [WUW - 1:0] cmd_pwuser;
	input wire rsp_valid;
	input wire rsp_ready;
	input wire [DW - 1:0] rsp_prdata;
	input wire rsp_pslverr;
	input wire [RUW - 1:0] rsp_pruser;
	input wire [BUW - 1:0] rsp_pbuser;
	input wire apb5_pwakeup;
	input wire parity_error_wdata;
	input wire parity_error_rdata;
	input wire parity_error_ctrl;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_protocol_enable;
	input wire cfg_slverr_enable;
	input wire cfg_parity_enable;
	input wire cfg_wakeup_enable;
	input wire cfg_user_enable;
	input wire cfg_perf_enable;
	input wire cfg_latency_enable;
	input wire [15:0] cfg_cmd_timeout_cnt;
	input wire [15:0] cfg_rsp_timeout_cnt;
	input wire [31:0] cfg_latency_threshold;
	input wire [15:0] cfg_wakeup_timeout_cnt;
	input wire cfg_addr_check_enable;
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
	output wire [7:0] active_count;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
	output wire wakeup_active;
	localparam [3:0] monitor_common_pkg_PktTypeAPB = 4'h9;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
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
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		if (USE_MONITOR) begin : gen_monitor
			reg [284:0] r_trans_table [0:MAX_TRANSACTIONS - 1];
			reg [7:0] r_active_count;
			reg [15:0] r_error_count;
			reg [31:0] r_transaction_count;
			reg [1:0] r_trans_state;
			reg [1:0] w_next_trans_state;
			wire w_state_change;
			reg [31:0] r_timestamp;
			reg [31:0] r_cmd_start_time;
			reg [15:0] r_cmd_timeout_timer;
			reg [15:0] r_rsp_timeout_timer;
			reg r_pwakeup_prev;
			reg r_wakeup_active;
			reg [15:0] r_wakeup_timer;
			wire w_wakeup_rising;
			wire w_wakeup_falling;
			wire w_wakeup_timeout;
			reg [MAX_TRANSACTIONS - 1:0] w_free_slot;
			reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_free_idx;
			reg w_has_free_slot;
			reg [MAX_TRANSACTIONS - 1:0] w_active_trans;
			reg [$clog2(MAX_TRANSACTIONS) - 1:0] w_active_idx;
			reg w_has_active_trans;
			reg [MAX_TRANSACTIONS - 1:0] w_completed_trans;
			wire w_cmd_handshake;
			wire w_rsp_handshake;
			wire w_cmd_timeout;
			wire w_rsp_timeout;
			reg w_protocol_violation;
			reg w_parity_error;
			reg w_latency_threshold_exceeded;
			reg r_cmd_timeout_d;
			reg r_rsp_timeout_d;
			reg r_wakeup_timeout_d;
			reg r_protocol_violation_d;
			reg r_parity_error_d;
			reg r_latency_exceeded_d;
			wire w_cmd_timeout_pulse;
			wire w_rsp_timeout_pulse;
			wire w_wakeup_timeout_pulse;
			wire w_protocol_violation_pulse;
			wire w_parity_error_pulse;
			wire w_latency_exceeded_pulse;
			reg [31:0] w_current_latency;
			reg w_generate_error_event;
			reg w_generate_timeout_event;
			reg w_generate_perf_event;
			reg w_generate_wakeup_event;
			reg w_generate_parity_event;
			reg w_generate_completion_event;
			reg [7:0] w_error_event_code;
			reg [7:0] w_timeout_event_code;
			reg [7:0] w_wakeup_event_code;
			reg [7:0] w_parity_event_code;
			reg w_fifo_wr_valid;
			wire w_fifo_wr_ready;
			reg [51:0] w_fifo_wr_data;
			wire w_fifo_rd_valid;
			wire w_fifo_rd_ready;
			wire [51:0] w_fifo_rd_data;
			assign active_count = r_active_count;
			assign error_count = r_error_count;
			assign transaction_count = r_transaction_count;
			assign wakeup_active = r_wakeup_active;
			assign w_cmd_handshake = cmd_valid && cmd_ready;
			assign w_rsp_handshake = rsp_valid && rsp_ready;
			always @(posedge aclk)
				if (!aresetn)
					r_timestamp <= 1'sb0;
				else
					r_timestamp <= r_timestamp + 1'b1;
			assign w_wakeup_rising = apb5_pwakeup && !r_pwakeup_prev;
			assign w_wakeup_falling = !apb5_pwakeup && r_pwakeup_prev;
			always @(posedge aclk)
				if (!aresetn) begin
					r_pwakeup_prev <= 1'b0;
					r_wakeup_active <= 1'b0;
					r_wakeup_timer <= 1'sb0;
				end
				else begin
					r_pwakeup_prev <= apb5_pwakeup;
					if (w_wakeup_rising) begin
						r_wakeup_active <= 1'b1;
						r_wakeup_timer <= 1'sb0;
					end
					else if (w_wakeup_falling) begin
						r_wakeup_active <= 1'b0;
						r_wakeup_timer <= 1'sb0;
					end
					else if (r_wakeup_active)
						r_wakeup_timer <= r_wakeup_timer + 1'b1;
				end
			assign w_wakeup_timeout = (r_wakeup_active && (r_wakeup_timer >= cfg_wakeup_timeout_cnt)) && cfg_wakeup_enable;
			always @(*) begin
				if (_sv2v_0)
					;
				w_next_trans_state = r_trans_state;
				case (r_trans_state)
					2'b00:
						if (w_cmd_handshake)
							w_next_trans_state = 2'b01;
					2'b01:
						if (w_rsp_handshake)
							w_next_trans_state = 2'b10;
					2'b10: w_next_trans_state = 2'b00;
					default: w_next_trans_state = 2'b00;
				endcase
			end
			assign w_state_change = w_next_trans_state != r_trans_state;
			always @(posedge aclk)
				if (!aresetn)
					r_trans_state <= 2'b00;
				else
					r_trans_state <= w_next_trans_state;
			always @(*) begin
				if (_sv2v_0)
					;
				w_free_slot = 1'sb0;
				w_free_idx = 1'sb0;
				w_has_free_slot = 1'b0;
				begin : sv2v_autoblock_1
					reg signed [31:0] i;
					for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
						if (!r_trans_table[i][284] && !w_has_free_slot) begin
							w_free_slot[i] = 1'b1;
							w_free_idx = i[$clog2(MAX_TRANSACTIONS) - 1:0];
							w_has_free_slot = 1'b1;
						end
				end
			end
			always @(*) begin
				if (_sv2v_0)
					;
				w_active_trans = 1'sb0;
				w_active_idx = 1'sb0;
				w_has_active_trans = 1'b0;
				begin : sv2v_autoblock_2
					reg signed [31:0] i;
					for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
						if ((r_trans_table[i][284] && ((r_trans_table[i][277-:3] == 3'h1) || (r_trans_table[i][277-:3] == 3'h2))) && !w_has_active_trans) begin
							w_active_trans[i] = 1'b1;
							w_active_idx = i[$clog2(MAX_TRANSACTIONS) - 1:0];
							w_has_active_trans = 1'b1;
						end
				end
			end
			always @(*) begin
				if (_sv2v_0)
					;
				w_completed_trans = 1'sb0;
				begin : sv2v_autoblock_3
					reg signed [31:0] i;
					for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
						if ((r_trans_table[i][284] && ((r_trans_table[i][277-:3] == 3'h3) || (r_trans_table[i][277-:3] == 3'h4))) && r_trans_table[i][279])
							w_completed_trans[i] = 1'b1;
				end
			end
			always @(posedge aclk)
				if (!aresetn) begin
					begin : sv2v_autoblock_4
						reg signed [31:0] i;
						for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
							r_trans_table[i] <= 1'sb0;
					end
					r_active_count <= 1'sb0;
					r_error_count <= 1'sb0;
					r_transaction_count <= 1'sb0;
					r_cmd_start_time <= 1'sb0;
				end
				else begin
					if (w_cmd_handshake && w_has_free_slot) begin
						r_trans_table[w_free_idx][284] <= 1'b1;
						r_trans_table[w_free_idx][277-:3] <= 3'h2;
						r_trans_table[w_free_idx][274-:32] <= sv2v_cast_32(cmd_paddr);
						r_trans_table[w_free_idx][223-:2] <= {1'b0, cmd_pwrite};
						r_trans_table[w_free_idx][221-:6] <= {cmd_pprot, cmd_pstrb[2:0]};
						r_trans_table[w_free_idx][283] <= 1'b1;
						r_trans_table[w_free_idx][282] <= cmd_pwrite;
						r_trans_table[w_free_idx][119-:32] <= r_timestamp;
						r_trans_table[w_free_idx][87-:32] <= r_timestamp;
						r_trans_table[w_free_idx][7-:8] <= 1'sb0;
						r_trans_table[w_free_idx][279] <= 1'b0;
						r_trans_table[w_free_idx][215-:32] <= 1'sb0;
						r_trans_table[w_free_idx][151-:32] <= 1'sb0;
						r_active_count <= r_active_count + 1'b1;
						r_cmd_start_time <= r_timestamp;
					end
					if (w_rsp_handshake && w_has_active_trans) begin
						r_trans_table[w_active_idx][281] <= 1'b1;
						r_trans_table[w_active_idx][280] <= 1'b1;
						r_trans_table[w_active_idx][55-:32] <= r_timestamp;
						if (rsp_pslverr && cfg_slverr_enable) begin
							r_trans_table[w_active_idx][277-:3] <= 3'h4;
							r_trans_table[w_active_idx][7-:8] <= 8'h00;
							r_error_count <= r_error_count + 1'b1;
						end
						else begin
							r_trans_table[w_active_idx][277-:3] <= 3'h3;
							r_trans_table[w_active_idx][7-:8] <= 8'h00;
						end
						r_transaction_count <= r_transaction_count + 1'b1;
					end
					begin : sv2v_autoblock_5
						reg signed [31:0] i;
						for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
							if (w_completed_trans[i]) begin
								r_trans_table[i][284] <= 1'b0;
								r_active_count <= r_active_count - 1'b1;
							end
					end
				end
			always @(posedge aclk)
				if (!aresetn) begin
					r_cmd_timeout_timer <= 1'sb0;
					r_rsp_timeout_timer <= 1'sb0;
				end
				else begin
					if (((r_trans_state == 2'b00) && cmd_valid) && !cmd_ready)
						r_cmd_timeout_timer <= r_cmd_timeout_timer + 1'b1;
					else
						r_cmd_timeout_timer <= 1'sb0;
					if ((r_trans_state == 2'b01) && (!rsp_valid || !rsp_ready))
						r_rsp_timeout_timer <= r_rsp_timeout_timer + 1'b1;
					else
						r_rsp_timeout_timer <= 1'sb0;
				end
			assign w_cmd_timeout = (cfg_timeout_enable && (r_cmd_timeout_timer >= cfg_cmd_timeout_cnt)) && (r_cmd_timeout_timer != {16 {1'sb0}});
			assign w_rsp_timeout = (cfg_timeout_enable && (r_rsp_timeout_timer >= cfg_rsp_timeout_cnt)) && (r_rsp_timeout_timer != {16 {1'sb0}});
			always @(*) begin
				if (_sv2v_0)
					;
				w_protocol_violation = 1'b0;
				w_parity_error = 1'b0;
				if (cfg_protocol_enable) begin
					if (rsp_valid && (r_trans_state == 2'b00))
						w_protocol_violation = 1'b1;
					if (cmd_valid && (r_trans_state == 2'b01))
						w_protocol_violation = 1'b1;
				end
				if (cfg_parity_enable && ENABLE_PARITY_MON)
					w_parity_error = (parity_error_wdata || parity_error_rdata) || parity_error_ctrl;
			end
			always @(posedge aclk)
				if (!aresetn) begin
					r_cmd_timeout_d <= 1'b0;
					r_rsp_timeout_d <= 1'b0;
					r_wakeup_timeout_d <= 1'b0;
					r_protocol_violation_d <= 1'b0;
					r_parity_error_d <= 1'b0;
					r_latency_exceeded_d <= 1'b0;
				end
				else begin
					r_cmd_timeout_d <= w_cmd_timeout;
					r_rsp_timeout_d <= w_rsp_timeout;
					r_wakeup_timeout_d <= w_wakeup_timeout;
					r_protocol_violation_d <= w_protocol_violation;
					r_parity_error_d <= w_parity_error;
					r_latency_exceeded_d <= w_latency_threshold_exceeded;
				end
			assign w_cmd_timeout_pulse = w_cmd_timeout && !r_cmd_timeout_d;
			assign w_rsp_timeout_pulse = w_rsp_timeout && !r_rsp_timeout_d;
			assign w_wakeup_timeout_pulse = w_wakeup_timeout && !r_wakeup_timeout_d;
			assign w_protocol_violation_pulse = w_protocol_violation && !r_protocol_violation_d;
			assign w_parity_error_pulse = w_parity_error && !r_parity_error_d;
			assign w_latency_exceeded_pulse = w_latency_threshold_exceeded && !r_latency_exceeded_d;
			always @(*) begin
				if (_sv2v_0)
					;
				w_current_latency = 1'sb0;
				w_latency_threshold_exceeded = 1'b0;
				if (w_has_active_trans && r_trans_table[w_active_idx][284]) begin
					w_current_latency = r_timestamp - r_trans_table[w_active_idx][119-:32];
					w_latency_threshold_exceeded = (cfg_perf_enable && cfg_latency_enable) && (w_current_latency > cfg_latency_threshold);
				end
			end
			always @(*) begin
				if (_sv2v_0)
					;
				w_generate_error_event = 1'b0;
				w_generate_timeout_event = 1'b0;
				w_generate_perf_event = 1'b0;
				w_generate_wakeup_event = 1'b0;
				w_generate_parity_event = 1'b0;
				w_generate_completion_event = 1'b0;
				w_error_event_code = 8'h00;
				w_timeout_event_code = 8'h00;
				w_wakeup_event_code = 8'h00;
				w_parity_event_code = 8'h00;
				if (cfg_error_enable) begin
					if (w_protocol_violation_pulse) begin
						w_generate_error_event = 1'b1;
						w_error_event_code = 8'h01;
					end
					else if ((rsp_pslverr && w_rsp_handshake) && cfg_slverr_enable) begin
						w_generate_error_event = 1'b1;
						w_error_event_code = 8'h00;
					end
				end
				if (cfg_timeout_enable) begin
					if (w_cmd_timeout_pulse) begin
						w_generate_timeout_event = 1'b1;
						w_timeout_event_code = 8'h00;
					end
					else if (w_rsp_timeout_pulse) begin
						w_generate_timeout_event = 1'b1;
						w_timeout_event_code = 8'h01;
					end
					else if (w_wakeup_timeout_pulse) begin
						w_generate_timeout_event = 1'b1;
						w_timeout_event_code = 8'h01;
					end
				end
				if (cfg_wakeup_enable) begin
					if (w_wakeup_rising) begin
						w_generate_wakeup_event = 1'b1;
						w_wakeup_event_code = 8'h00;
					end
					else if (w_wakeup_falling) begin
						w_generate_wakeup_event = 1'b1;
						w_wakeup_event_code = 8'h01;
					end
				end
				if (cfg_parity_enable && w_parity_error_pulse) begin
					w_generate_parity_event = 1'b1;
					if (parity_error_wdata)
						w_parity_event_code = 8'h00;
					else if (parity_error_rdata)
						w_parity_event_code = 8'h01;
					else
						w_parity_event_code = 8'h02;
				end
				if (cfg_perf_enable && w_latency_exceeded_pulse)
					w_generate_perf_event = 1'b1;
				if (w_rsp_handshake && !rsp_pslverr)
					w_generate_completion_event = 1'b1;
			end
			gaxi_fifo_sync #(
				.REGISTERED(1),
				.DATA_WIDTH(52),
				.DEPTH(MONITOR_FIFO_DEPTH),
				.ALMOST_WR_MARGIN(1),
				.ALMOST_RD_MARGIN(1)
			) monitor_fifo(
				.axi_aclk(aclk),
				.axi_aresetn(aresetn),
				.wr_valid(w_fifo_wr_valid),
				.wr_ready(w_fifo_wr_ready),
				.wr_data(w_fifo_wr_data),
				.rd_ready(w_fifo_rd_ready),
				.count(),
				.rd_valid(w_fifo_rd_valid),
				.rd_data(w_fifo_rd_data)
			);
			always @(*) begin
				if (_sv2v_0)
					;
				w_fifo_wr_valid = 1'b0;
				w_fifo_wr_data = 1'sb0;
				if (w_generate_error_event) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeError;
					w_fifo_wr_data[47-:8] = w_error_event_code;
					w_fifo_wr_data[39-:32] = sv2v_cast_32(cmd_paddr);
					w_fifo_wr_data[7-:8] = {4'h0, cmd_pprot, cmd_pwrite};
				end
				else if (w_generate_parity_event) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeError;
					w_fifo_wr_data[47-:8] = w_parity_event_code;
					w_fifo_wr_data[39-:32] = sv2v_cast_32(cmd_paddr);
					w_fifo_wr_data[7-:8] = {5'h00, parity_error_wdata, parity_error_rdata, parity_error_ctrl};
				end
				else if (w_generate_timeout_event) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeTimeout;
					w_fifo_wr_data[47-:8] = w_timeout_event_code;
					w_fifo_wr_data[39-:32] = (w_has_active_trans ? r_trans_table[w_active_idx][274:243] : sv2v_cast_32(cmd_paddr));
					w_fifo_wr_data[7-:8] = r_cmd_timeout_timer[7:0];
				end
				else if (w_generate_wakeup_event) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeAPB;
					w_fifo_wr_data[47-:8] = w_wakeup_event_code;
					w_fifo_wr_data[39-:32] = {16'h0000, r_wakeup_timer};
					w_fifo_wr_data[7-:8] = {7'h00, r_wakeup_active};
				end
				else if (w_generate_perf_event) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypePerf;
					w_fifo_wr_data[47-:8] = (cmd_pwrite ? 8'h01 : 8'h00);
					w_fifo_wr_data[39-:32] = w_current_latency;
					w_fifo_wr_data[7-:8] = {4'h0, cmd_pprot, cmd_pwrite};
				end
				else if (w_generate_completion_event) begin
					w_fifo_wr_valid = 1'b1;
					w_fifo_wr_data[51-:4] = monitor_common_pkg_PktTypeCompletion;
					w_fifo_wr_data[47-:8] = 8'h00;
					w_fifo_wr_data[39-:32] = sv2v_cast_32(cmd_paddr);
					w_fifo_wr_data[7-:8] = {4'h0, cmd_pprot, cmd_pwrite};
				end
			end
			always @(posedge aclk)
				if (!aresetn)
					;
				else begin : sv2v_autoblock_6
					reg signed [31:0] i;
					for (i = 0; i < MAX_TRANSACTIONS; i = i + 1)
						if ((((r_trans_table[i][284] && ((r_trans_table[i][277-:3] == 3'h3) || (r_trans_table[i][277-:3] == 3'h4))) && !r_trans_table[i][279]) && w_fifo_wr_valid) && w_fifo_wr_ready)
							r_trans_table[i][279] <= 1'b1;
				end
			reg w_monbus_pkt_valid;
			wire w_monbus_pkt_ready;
			reg [127:0] w_monbus_pkt_data;
			reg [63:0] w_monbus_pkt_ts;
			wire [127:0] w_fifo_pkt_data;
			assign w_fifo_pkt_data = monitor_common_pkg_create_monitor_packet(w_fifo_rd_data[51-:4], 4'h2, w_fifo_rd_data[47-:8], 9'h000, UNIT_ID, AGENT_ID, {24'h000000, w_fifo_rd_data[7-:8], w_fifo_rd_data[39-:32]});
			wire w_addr_pkt_valid;
			wire [127:0] w_addr_pkt_data;
			wire [63:0] w_addr_pkt_timestamp;
			wire w_addr_pkt_ready;
			if (N_ADDR_RANGES > 0) begin : gen_addr_check
				apb_monitor_addr_check #(
					.N_ADDR_RANGES(N_ADDR_RANGES),
					.ADDR_WIDTH(ADDR_WIDTH),
					.UNIT_ID(UNIT_ID),
					.AGENT_ID(AGENT_ID)
				) addr_check(
					.clk(aclk),
					.aresetn(aresetn),
					.i_mon_time(i_mon_time),
					.cmd_paddr(cmd_paddr),
					.cmd_pwrite(cmd_pwrite),
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
			always @(*) begin
				if (_sv2v_0)
					;
				if (w_fifo_rd_valid) begin
					w_monbus_pkt_valid = 1'b1;
					w_monbus_pkt_data = w_fifo_pkt_data;
					w_monbus_pkt_ts = i_mon_time;
				end
				else if (w_addr_pkt_valid) begin
					w_monbus_pkt_valid = 1'b1;
					w_monbus_pkt_data = w_addr_pkt_data;
					w_monbus_pkt_ts = w_addr_pkt_timestamp;
				end
				else begin
					w_monbus_pkt_valid = 1'b0;
					w_monbus_pkt_data = 1'sb0;
					w_monbus_pkt_ts = 1'sb0;
				end
			end
			assign w_fifo_rd_ready = w_monbus_pkt_ready && w_fifo_rd_valid;
			assign w_addr_pkt_ready = w_monbus_pkt_ready && !w_fifo_rd_valid;
			localparam signed [31:0] MONBUS_TOTAL_W = monitor_common_pkg_MONBUS_PKT_WIDTH + monitor_common_pkg_MONBUS_TS_WIDTH;
			wire [MONBUS_TOTAL_W - 1:0] w_skid_wr_data;
			wire [MONBUS_TOTAL_W - 1:0] w_skid_rd_data;
			assign w_skid_wr_data = {w_monbus_pkt_data, w_monbus_pkt_ts};
			gaxi_skid_buffer #(
				.DATA_WIDTH(MONBUS_TOTAL_W),
				.DEPTH(2)
			) monbus_skid_buffer(
				.axi_aclk(aclk),
				.axi_aresetn(aresetn),
				.wr_valid(w_monbus_pkt_valid),
				.wr_ready(w_monbus_pkt_ready),
				.wr_data(w_skid_wr_data),
				.rd_valid(monbus_valid),
				.rd_ready(monbus_ready),
				.rd_data(w_skid_rd_data),
				.count(),
				.rd_count()
			);
			assign monbus_packet = w_skid_rd_data[MONBUS_TOTAL_W - 1-:monitor_common_pkg_MONBUS_PKT_WIDTH];
			assign monbus_timestamp = w_skid_rd_data[63:0];
		end
		else begin : gen_no_monitor
			assign monbus_valid = 1'b0;
			assign monbus_packet = 1'sb0;
			assign monbus_timestamp = 1'sb0;
			assign active_count = 8'h00;
			assign error_count = 16'h0000;
			assign transaction_count = 32'h00000000;
			assign wakeup_active = 1'b0;
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
