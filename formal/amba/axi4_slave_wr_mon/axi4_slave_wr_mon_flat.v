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
module axi4_slave_wr (
	aclk,
	aresetn,
	s_axi_awid,
	s_axi_awaddr,
	s_axi_awlen,
	s_axi_awsize,
	s_axi_awburst,
	s_axi_awlock,
	s_axi_awcache,
	s_axi_awprot,
	s_axi_awqos,
	s_axi_awregion,
	s_axi_awuser,
	s_axi_awvalid,
	s_axi_awready,
	s_axi_wdata,
	s_axi_wstrb,
	s_axi_wlast,
	s_axi_wuser,
	s_axi_wvalid,
	s_axi_wready,
	s_axi_bid,
	s_axi_bresp,
	s_axi_buser,
	s_axi_bvalid,
	s_axi_bready,
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
	input wire [IW - 1:0] s_axi_awid;
	input wire [AW - 1:0] s_axi_awaddr;
	input wire [7:0] s_axi_awlen;
	input wire [2:0] s_axi_awsize;
	input wire [1:0] s_axi_awburst;
	input wire s_axi_awlock;
	input wire [3:0] s_axi_awcache;
	input wire [2:0] s_axi_awprot;
	input wire [3:0] s_axi_awqos;
	input wire [3:0] s_axi_awregion;
	input wire [UW - 1:0] s_axi_awuser;
	input wire s_axi_awvalid;
	output wire s_axi_awready;
	input wire [DW - 1:0] s_axi_wdata;
	input wire [SW - 1:0] s_axi_wstrb;
	input wire s_axi_wlast;
	input wire [UW - 1:0] s_axi_wuser;
	input wire s_axi_wvalid;
	output wire s_axi_wready;
	output wire [IW - 1:0] s_axi_bid;
	output wire [1:0] s_axi_bresp;
	output wire [UW - 1:0] s_axi_buser;
	output wire s_axi_bvalid;
	input wire s_axi_bready;
	output wire [IW - 1:0] fub_axi_awid;
	output wire [AW - 1:0] fub_axi_awaddr;
	output wire [7:0] fub_axi_awlen;
	output wire [2:0] fub_axi_awsize;
	output wire [1:0] fub_axi_awburst;
	output wire fub_axi_awlock;
	output wire [3:0] fub_axi_awcache;
	output wire [2:0] fub_axi_awprot;
	output wire [3:0] fub_axi_awqos;
	output wire [3:0] fub_axi_awregion;
	output wire [UW - 1:0] fub_axi_awuser;
	output wire fub_axi_awvalid;
	input wire fub_axi_awready;
	output wire [DW - 1:0] fub_axi_wdata;
	output wire [SW - 1:0] fub_axi_wstrb;
	output wire fub_axi_wlast;
	output wire [UW - 1:0] fub_axi_wuser;
	output wire fub_axi_wvalid;
	input wire fub_axi_wready;
	input wire [IW - 1:0] fub_axi_bid;
	input wire [1:0] fub_axi_bresp;
	input wire [UW - 1:0] fub_axi_buser;
	input wire fub_axi_bvalid;
	output wire fub_axi_bready;
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
	assign busy = (((((int_aw_count > 0) || (int_w_count > 0)) || (int_b_count > 0)) || s_axi_awvalid) || s_axi_wvalid) || fub_axi_bvalid;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AW),
		.DATA_WIDTH(AWSize)
	) i_aw_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_awvalid),
		.wr_ready(s_axi_awready),
		.wr_data({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos, s_axi_awregion, s_axi_awuser}),
		.rd_valid(int_skid_awvalid),
		.rd_ready(int_skid_awready),
		.rd_count(int_aw_count),
		.rd_data(int_aw_pkt),
		.count()
	);
	assign {fub_axi_awid, fub_axi_awaddr, fub_axi_awlen, fub_axi_awsize, fub_axi_awburst, fub_axi_awlock, fub_axi_awcache, fub_axi_awprot, fub_axi_awqos, fub_axi_awregion, fub_axi_awuser} = int_aw_pkt;
	assign fub_axi_awvalid = int_skid_awvalid;
	assign int_skid_awready = fub_axi_awready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_W),
		.DATA_WIDTH(WSize)
	) i_w_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_wvalid),
		.wr_ready(s_axi_wready),
		.wr_data({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
		.rd_valid(int_skid_wvalid),
		.rd_ready(int_skid_wready),
		.rd_count(int_w_count),
		.rd_data(int_w_pkt),
		.count()
	);
	assign {fub_axi_wdata, fub_axi_wstrb, fub_axi_wlast, fub_axi_wuser} = int_w_pkt;
	assign fub_axi_wvalid = int_skid_wvalid;
	assign int_skid_wready = fub_axi_wready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_B),
		.DATA_WIDTH(BSize)
	) i_b_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_axi_bvalid),
		.wr_ready(fub_axi_bready),
		.wr_data({fub_axi_bid, fub_axi_bresp, fub_axi_buser}),
		.rd_valid(int_skid_bvalid),
		.rd_ready(int_skid_bready),
		.rd_count(int_b_count),
		.rd_data({s_axi_bid, s_axi_bresp, s_axi_buser}),
		.count()
	);
	assign s_axi_bvalid = int_skid_bvalid;
	assign int_skid_bready = s_axi_bready;
endmodule
module axi_monitor_addr_check (
	clk,
	aresetn,
	i_mon_time,
	cmd_addr,
	cmd_id,
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
	parameter signed [31:0] ID_WIDTH = 6;
	parameter [7:0] UNIT_ID = 8'h00;
	parameter [15:0] AGENT_ID = 16'h0000;
	parameter [0:0] IS_READ = 1'b1;
	parameter signed [31:0] M = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	input wire clk;
	input wire aresetn;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	input wire [M - 1:0] cmd_addr;
	input wire [IW - 1:0] cmd_id;
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
				hit_oh[i] = ((cfg_addr_range_enable[i] && cmd_fire) && (cmd_addr >= cfg_addr_range_low[i * M+:M])) && (cmd_addr <= cfg_addr_range_high[i * M+:M]);
		end
	end
	reg [N_ADDR_RANGES - 1:0] r_pending;
	reg [(N_ADDR_RANGES * M) - 1:0] r_lat_addr;
	reg [(N_ADDR_RANGES * IW) - 1:0] r_lat_id;
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
			r_lat_id <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < N_ADDR_RANGES; i = i + 1)
					if (hit_oh[i]) begin
						r_lat_addr[i * M+:M] <= cmd_addr;
						r_lat_id[i * IW+:IW] <= cmd_id;
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
	localparam [3:0] PROTOCOL_FIELD = 4'h0;
	localparam [7:0] EVENT_CODE = 8'h0d;
	reg [M - 1:0] emit_addr;
	reg [IW - 1:0] emit_id;
	wire [8:0] channel_id_field;
	wire [63:0] event_data_field;
	wire [59:0] addr_payload;
	always @(*) begin
		if (_sv2v_0)
			;
		emit_addr = 1'sb0;
		emit_id = 1'sb0;
		begin : sv2v_autoblock_5
			reg signed [31:0] i;
			for (i = 0; i < N_ADDR_RANGES; i = i + 1)
				if (emit_oh[i]) begin
					emit_addr = r_lat_addr[i * M+:M];
					emit_id = r_lat_id[i * IW+:IW];
				end
		end
	end
	generate
		if (IW >= 9) begin : g_chan_id_wide
			assign channel_id_field = emit_id[8:0];
		end
		else begin : g_chan_id_narrow
			assign channel_id_field = {{9 - IW {1'b0}}, emit_id};
		end
		if (M >= 60) begin : g_addr_wide
			assign addr_payload = emit_addr[59:0];
		end
		else begin : g_addr_narrow
			assign addr_payload = {{60 - M {1'b0}}, emit_addr};
		end
	endgenerate
	assign event_data_field = {emit_idx[3:0], addr_payload};
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
	assign addr_pkt_data = monitor_common_pkg_create_monitor_packet(PKT_TYPE_FIELD, PROTOCOL_FIELD, EVENT_CODE, channel_id_field, UNIT_ID, AGENT_ID, event_data_field);
	assign addr_pkt_timestamp = i_mon_time;
	initial _sv2v_0 = 0;
endmodule
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
			if (!(pkt_valid && !pkt_taken))
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
						r_latency_over_thresh[idx] <= (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284] && (trans_table[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 277-:3] == 3'h3)) && (lat > latency_threshold);
					end
			end
			if (((w_active_detect && pkt_taken) && (pkt_type == monitor_common_pkg_PktTypeThreshold)) && (pkt_event_code == 8'h00))
				r_active_crossed <= 1'b1;
			else if ({8'h00, w_active_count} <= active_trans_threshold)
				r_active_crossed <= 1'b0;
			if (((w_has_lat && pkt_taken) && (pkt_type == monitor_common_pkg_PktTypeThreshold)) && (pkt_event_code == 8'h01))
				r_latency_crossed <= 1'b1;
			else if (!w_has_lat)
				r_latency_crossed <= 1'b0;
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
		else if ((w_has_lat && !r_latency_crossed) && !output_busy) begin
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
		if (err_valid) begin
			w_mark_idx = err_idx;
			w_mark_is_error = 1'b1;
		end
		else if (to_valid) begin
			w_mark_idx = to_idx;
			w_mark_is_error = 1'b1;
		end
		else if (compl_valid) begin
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
				if (r_trans_table_local[(((MAX_TRANSACTIONS - 1) - idx) * 285) + 284])
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
	input wire [3:0] cfg_addr_cnt;
	input wire [3:0] cfg_data_cnt;
	input wire [3:0] cfg_resp_cnt;
	input wire cfg_timeout_enable;
	output wire [MAX_TRANSACTIONS - 1:0] timeout_detected;
	localparam signed [31:0] TIMER_W = 8;
	reg [7:0] r_addr_timer [0:MAX_TRANSACTIONS - 1];
	reg [7:0] r_data_timer [0:MAX_TRANSACTIONS - 1];
	reg [7:0] r_resp_timer [0:MAX_TRANSACTIONS - 1];
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
							if (r_addr_timer[idx] >= {4'h0, cfg_addr_cnt})
								r_timeout_detected[idx] <= 1'b1;
							else
								r_addr_timer[idx] <= r_addr_timer[idx] + 1'b1;
						end
						if (w_data_pending[idx]) begin
							if (r_data_timer[idx] >= {4'h0, cfg_data_cnt})
								r_timeout_detected[idx] <= 1'b1;
							else
								r_data_timer[idx] <= r_data_timer[idx] + 1'b1;
						end
						if (w_resp_pending[idx]) begin
							if (r_resp_timer[idx] >= {4'h0, cfg_resp_cnt})
								r_timeout_detected[idx] <= 1'b1;
							else
								r_resp_timer[idx] <= r_resp_timer[idx] + 1'b1;
						end
					end
				end
		end
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
			$display("Error [%0t] /tmp/formal_axi4_slave_wr_mon/counter_freq_invariant.sv:128:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MIN_FREQ_MHZ must be >= 1 (got %0d)", MIN_FREQ_MHZ);
		if (MAX_FREQ_MHZ < MIN_FREQ_MHZ)
			$display("Error [%0t] /tmp/formal_axi4_slave_wr_mon/counter_freq_invariant.sv:130:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: MAX_FREQ_MHZ (%0d) < MIN_FREQ_MHZ (%0d)", MAX_FREQ_MHZ, MIN_FREQ_MHZ);
		if (NUM_FREQ_ENTRIES < 1)
			$display("Error [%0t] /tmp/formal_axi4_slave_wr_mon/counter_freq_invariant.sv:133:13 - counter_freq_invariant.param_check.<unnamed_block>\n msg: ", $time, "counter_freq_invariant: NUM_FREQ_ENTRIES must be >= 1 (got %0d)", NUM_FREQ_ENTRIES);
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
	genvar _gv_gi_2;
	function automatic signed [DIV_WIDTH - 1:0] sv2v_cast_DC41E_signed;
		input reg signed [DIV_WIDTH - 1:0] inp;
		sv2v_cast_DC41E_signed = inp;
	endfunction
	generate
		for (_gv_gi_2 = 0; _gv_gi_2 < NUM_FREQ_ENTRIES; _gv_gi_2 = _gv_gi_2 + 1) begin : gen_div_entry
			localparam gi = _gv_gi_2;
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
module monitor_trans_cam (
	clk,
	rst_n,
	clear,
	lookup_addr_id,
	lookup_data_id,
	lookup_resp_id,
	addr_match_oh,
	data_match_oh,
	resp_match_oh,
	data_match_first_oh,
	free_oh,
	addr_wants_alloc,
	data_wants_alloc,
	resp_wants_alloc,
	addr_alloc_oh,
	data_alloc_oh,
	resp_alloc_oh,
	entry_we,
	entry_valid_next,
	entry_id_next,
	entry_payload_next,
	entry_valid,
	entry_id,
	entry_payload
);
	reg _sv2v_0;
	parameter signed [31:0] DEPTH = 16;
	parameter signed [31:0] ID_WIDTH = 8;
	parameter signed [31:0] PAYLOAD_WIDTH = 128;
	input wire clk;
	input wire rst_n;
	input wire clear;
	input wire [ID_WIDTH - 1:0] lookup_addr_id;
	input wire [ID_WIDTH - 1:0] lookup_data_id;
	input wire [ID_WIDTH - 1:0] lookup_resp_id;
	output wire [DEPTH - 1:0] addr_match_oh;
	output wire [DEPTH - 1:0] data_match_oh;
	output wire [DEPTH - 1:0] resp_match_oh;
	output reg [DEPTH - 1:0] data_match_first_oh;
	output wire [DEPTH - 1:0] free_oh;
	input wire addr_wants_alloc;
	input wire data_wants_alloc;
	input wire resp_wants_alloc;
	output reg [DEPTH - 1:0] addr_alloc_oh;
	output reg [DEPTH - 1:0] data_alloc_oh;
	output reg [DEPTH - 1:0] resp_alloc_oh;
	input wire [DEPTH - 1:0] entry_we;
	input wire [DEPTH - 1:0] entry_valid_next;
	input wire [(DEPTH * ID_WIDTH) - 1:0] entry_id_next;
	input wire [(DEPTH * PAYLOAD_WIDTH) - 1:0] entry_payload_next;
	output wire [DEPTH - 1:0] entry_valid;
	output wire [(DEPTH * ID_WIDTH) - 1:0] entry_id;
	output wire [(DEPTH * PAYLOAD_WIDTH) - 1:0] entry_payload;
	reg r_valid [0:DEPTH - 1];
	reg [ID_WIDTH - 1:0] r_id [0:DEPTH - 1];
	reg [PAYLOAD_WIDTH - 1:0] r_payload [0:DEPTH - 1];
	(* keep = "true" *) reg [DEPTH - 1:0] w_addr_match_oh;
	(* keep = "true" *) reg [DEPTH - 1:0] w_data_match_oh;
	(* keep = "true" *) reg [DEPTH - 1:0] w_resp_match_oh;
	(* keep = "true" *) reg [DEPTH - 1:0] w_free_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				begin
					w_addr_match_oh[i] = r_valid[i] && (r_id[i] == lookup_addr_id);
					w_data_match_oh[i] = r_valid[i] && (r_id[i] == lookup_data_id);
					w_resp_match_oh[i] = r_valid[i] && (r_id[i] == lookup_resp_id);
					w_free_oh[i] = !r_valid[i];
				end
		end
	end
	assign addr_match_oh = w_addr_match_oh;
	assign data_match_oh = w_data_match_oh;
	assign resp_match_oh = w_resp_match_oh;
	assign free_oh = w_free_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		data_match_first_oh = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				if (w_data_match_oh[i] && (data_match_first_oh == {DEPTH {1'sb0}}))
					data_match_first_oh[i] = 1'b1;
		end
	end
	always @(*) begin : sv2v_autoblock_3
		reg [DEPTH - 1:0] remaining;
		reg taken;
		if (_sv2v_0)
			;
		addr_alloc_oh = 1'sb0;
		data_alloc_oh = 1'sb0;
		resp_alloc_oh = 1'sb0;
		taken = 1'b0;
		remaining = w_free_oh;
		if (addr_wants_alloc) begin
			taken = 1'b0;
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
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
				for (i = 0; i < DEPTH; i = i + 1)
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
				for (i = 0; i < DEPTH; i = i + 1)
					if (!taken && remaining[i]) begin
						resp_alloc_oh[i] = 1'b1;
						remaining[i] = 1'b0;
						taken = 1'b1;
					end
			end
		end
	end
	genvar _gv_gi_3;
	generate
		for (_gv_gi_3 = 0; _gv_gi_3 < DEPTH; _gv_gi_3 = _gv_gi_3 + 1) begin : g_slot
			localparam gi = _gv_gi_3;
			always @(posedge clk)
				if (!rst_n) begin
					r_valid[gi] <= 1'b0;
					r_id[gi] <= 1'sb0;
					r_payload[gi] <= 1'sb0;
				end
				else if (clear)
					r_valid[gi] <= 1'b0;
				else if (entry_we[gi]) begin
					r_valid[gi] <= entry_valid_next[gi];
					r_id[gi] <= entry_id_next[((DEPTH - 1) - gi) * ID_WIDTH+:ID_WIDTH];
					r_payload[gi] <= entry_payload_next[((DEPTH - 1) - gi) * PAYLOAD_WIDTH+:PAYLOAD_WIDTH];
				end
			assign entry_valid[gi] = r_valid[gi];
			assign entry_id[((DEPTH - 1) - gi) * ID_WIDTH+:ID_WIDTH] = r_id[gi];
			assign entry_payload[((DEPTH - 1) - gi) * PAYLOAD_WIDTH+:PAYLOAD_WIDTH] = r_payload[gi];
		end
	endgenerate
	initial _sv2v_0 = 0;
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
	output wire [(MAX_TRANSACTIONS * 285) - 1:0] trans_table;
	output wire [7:0] active_count;
	output wire [MAX_TRANSACTIONS - 1:0] state_change;
	localparam signed [31:0] N = MAX_TRANSACTIONS;
	localparam signed [31:0] PAYLOAD_W = 285;
	generate
		if (ID_WIDTH > 8) begin : gen_id_width_unsupported
			initial $display("Error [elaboration] /tmp/formal_axi4_slave_wr_mon/axi_monitor_trans_mgr.sv:163:9 - axi_monitor_trans_mgr.gen_id_width_unsupported\n msg: ", "axi_monitor_trans_mgr: ID_WIDTH=%0d exceeds the 8-bit id field in bus_transaction_t; the table and the CAM key would disagree. Widen bus_transaction_t.id or reduce ID_WIDTH.", ID_WIDTH);
		end
	endgenerate
	wire [N - 1:0] addr_match_oh;
	wire [N - 1:0] data_match_oh;
	wire [N - 1:0] resp_match_oh;
	wire [N - 1:0] cam_data_match_first_oh;
	wire [N - 1:0] free_oh;
	wire [N - 1:0] addr_alloc_oh;
	wire [N - 1:0] data_alloc_oh;
	wire [N - 1:0] resp_alloc_oh;
	wire [N - 1:0] cam_entry_valid;
	wire [(N * 285) - 1:0] cam_entry_payload;
	wire [N - 1:0] cam_entry_we;
	wire [N - 1:0] cam_entry_valid_next;
	wire [(N * IW) - 1:0] cam_entry_id_next;
	wire [(N * 285) - 1:0] cam_entry_payload_next;
	wire addr_wants_alloc;
	reg data_wants_alloc;
	reg resp_wants_alloc;
	monitor_trans_cam #(
		.DEPTH(N),
		.ID_WIDTH(IW),
		.PAYLOAD_WIDTH(PAYLOAD_W)
	) u_cam(
		.clk(aclk),
		.rst_n(aresetn),
		.clear(clear),
		.lookup_addr_id(cmd_id),
		.lookup_data_id(data_id),
		.lookup_resp_id(resp_id),
		.addr_match_oh(addr_match_oh),
		.data_match_oh(data_match_oh),
		.resp_match_oh(resp_match_oh),
		.data_match_first_oh(cam_data_match_first_oh),
		.free_oh(free_oh),
		.addr_wants_alloc(addr_wants_alloc),
		.data_wants_alloc(data_wants_alloc),
		.resp_wants_alloc(resp_wants_alloc),
		.addr_alloc_oh(addr_alloc_oh),
		.data_alloc_oh(data_alloc_oh),
		.resp_alloc_oh(resp_alloc_oh),
		.entry_we(cam_entry_we),
		.entry_valid_next(cam_entry_valid_next),
		.entry_id_next(cam_entry_id_next),
		.entry_payload_next(cam_entry_payload_next),
		.entry_valid(cam_entry_valid),
		.entry_id(),
		.entry_payload(cam_entry_payload)
	);
	localparam signed [31:0] AGEW = (N > 1 ? $clog2(N) : 1);
	reg [AGEW - 1:0] r_age [0:N - 1];
	reg [(N * AGEW) - 1:0] w_age_flat;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_age_flat[i * AGEW+:AGEW] = r_age[i];
		end
	end
	function automatic signed [AGEW - 1:0] sv2v_cast_D1065_signed;
		input reg signed [AGEW - 1:0] inp;
		sv2v_cast_D1065_signed = inp;
	endfunction
	function automatic [N - 1:0] pick_oldest;
		input reg [N - 1:0] cand;
		input reg [(N * AGEW) - 1:0] ages;
		reg [N - 1:0] res;
		reg found;
		begin
			res = 1'sb0;
			found = 1'b0;
			begin : sv2v_autoblock_2
				reg signed [31:0] r;
				for (r = 0; r < N; r = r + 1)
					begin : sv2v_autoblock_3
						reg signed [31:0] i;
						for (i = 0; i < N; i = i + 1)
							if ((!found && cand[i]) && (ages[i * AGEW+:AGEW] == sv2v_cast_D1065_signed(r))) begin
								res[i] = 1'b1;
								found = 1'b1;
							end
					end
			end
			pick_oldest = res;
		end
	endfunction
	(* keep = "true" *) reg [N - 1:0] w_data_state_pred_oh;
	reg [N - 1:0] w_data_state_first_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_data_state_first_oh = 1'sb0;
		begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_data_state_pred_oh[i] = ((cam_entry_valid[i] && ((cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h1) || (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] == 3'h2))) && cam_entry_payload[(((N - 1) - i) * 285) + 283]) && !cam_entry_payload[(((N - 1) - i) * 285) + 281];
		end
		w_data_state_first_oh = pick_oldest(w_data_state_pred_oh, w_age_flat);
	end
	reg [N - 1:0] w_can_cleanup;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_5
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
	reg [N - 1:0] w_freeing_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_6
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				w_freeing_oh[i] = cam_entry_valid[i] && w_can_cleanup[i];
		end
	end
	reg [N - 1:0] w_addr_pend_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_7
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
		if (addr_wants_alloc) begin : sv2v_autoblock_8
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if ((w_addr_alloc_mirror_oh == {N {1'sb0}}) && free_oh[i])
					w_addr_alloc_mirror_oh[i] = 1'b1;
		end
	end
	reg [N - 1:0] w_data_cmd_bypass_oh;
	wire [N - 1:0] addr_update_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		w_data_cmd_bypass_oh = 1'sb0;
		if (((!IS_READ && data_valid) && data_ready) && !(|w_data_state_pred_oh)) begin : sv2v_autoblock_9
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
		monitor_common_pkg_cmd_entry_reserve = (max_transactions >= 16 ? 2 : 0);
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
		begin : sv2v_autoblock_10
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
	wire [N - 1:0] data_update_oh;
	wire [N - 1:0] resp_update_oh;
	reg [N - 1:0] w_data_cand_open;
	reg [N - 1:0] w_data_cand_any;
	reg [N - 1:0] w_resp_cand_open;
	reg [N - 1:0] w_resp_cand_any;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_11
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
		else begin : sv2v_autoblock_12
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
	always @(*) begin : sv2v_autoblock_13
		reg signed [31:0] surv;
		if (_sv2v_0)
			;
		surv = 0;
		begin : sv2v_autoblock_14
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				if (cam_entry_valid[i] && !w_freeing_oh[i])
					surv = surv + 1;
		end
		w_age_addr_new = sv2v_cast_D1065_signed(surv);
		w_age_data_new = sv2v_cast_D1065_signed(surv + (w_addr_alloc_fire ? 1 : 0));
		w_age_resp_new = sv2v_cast_D1065_signed((surv + (w_addr_alloc_fire ? 1 : 0)) + (w_data_alloc_fire ? 1 : 0));
	end
	reg [AGEW - 1:0] w_age_next [0:N - 1];
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_15
			reg signed [31:0] i;
			for (i = 0; i < N; i = i + 1)
				begin : sv2v_autoblock_16
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
						begin : sv2v_autoblock_17
							reg signed [31:0] j;
							for (j = 0; j < N; j = j + 1)
								if (w_freeing_oh[j] && (r_age[j] < r_age[i]))
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
	genvar _gv_gi_4;
	localparam [7:0] monitor_amba4_pkg_EVT_CMD_TIMEOUT = 8'h00;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_ORPHAN = 8'h02;
	localparam [7:0] monitor_amba4_pkg_EVT_DATA_TIMEOUT = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_PROTOCOL = 8'h04;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_DECERR = 8'h01;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_ORPHAN = 8'h03;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_SLVERR = 8'h00;
	localparam [7:0] monitor_amba4_pkg_EVT_RESP_TIMEOUT = 8'h02;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		for (_gv_gi_4 = 0; _gv_gi_4 < N; _gv_gi_4 = _gv_gi_4 + 1) begin : g_entry_next
			localparam gi = _gv_gi_4;
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
			assign cam_entry_id_next[((N - 1) - gi) * IW+:IW] = next_id;
			assign cam_entry_payload_next[((N - 1) - gi) * 285+:285] = next;
		end
	endgenerate
	assign trans_table = cam_entry_payload;
	reg [7:0] r_active_count;
	reg [$clog2(N + 1) - 1:0] w_occupancy;
	always @(*) begin
		if (_sv2v_0)
			;
		w_occupancy = 1'sb0;
		begin : sv2v_autoblock_18
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
	reg [(N * 285) - 1:0] r_trans_table_prev;
	reg [N - 1:0] r_state_change;
	always @(posedge aclk)
		if (!aresetn) begin
			begin : sv2v_autoblock_19
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_trans_table_prev[((N - 1) - i) * 285+:285] <= 1'sb0;
			end
			r_state_change <= 1'sb0;
		end
		else begin
			r_trans_table_prev <= cam_entry_payload;
			begin : sv2v_autoblock_20
				reg signed [31:0] i;
				for (i = 0; i < N; i = i + 1)
					r_state_change[i] <= (cam_entry_payload[(((N - 1) - i) * 285) + 284] && r_trans_table_prev[(((N - 1) - i) * 285) + 284]) && (cam_entry_payload[(((N - 1) - i) * 285) + 277-:3] != r_trans_table_prev[(((N - 1) - i) * 285) + 277-:3]);
			end
		end
	assign state_change = r_state_change;
	reg f_past_ok;
	initial f_past_ok = 1'b0;
	always @(posedge aclk) f_past_ok <= aresetn;
	always @(posedge aclk)
		if ((IS_READ && aresetn) && f_past_ok) begin : sv2v_autoblock_21
			reg signed [31:0] fi;
			for (fi = 0; fi < N; fi = fi + 1)
				if (cam_entry_valid[fi]) begin : ap_no_reopened_complete
					assert (!((cam_entry_payload[(((N - 1) - fi) * 285) + 277-:3] == 3'h2) && cam_entry_payload[(((N - 1) - fi) * 285) + 281])) ;
				end
		end
	always @(posedge aclk)
		if ((!IS_READ && aresetn) && f_past_ok) begin : sv2v_autoblock_22
			reg signed [31:0] fi;
			for (fi = 0; fi < N; fi = fi + 1)
				if (cam_entry_valid[fi]) begin : ap_wr_data_phase_has_cmd
					assert (!((cam_entry_payload[(((N - 1) - fi) * 285) + 277-:3] == 3'h2) && !cam_entry_payload[(((N - 1) - fi) * 285) + 283])) ;
				end
		end
	always @(posedge aclk)
		if (aresetn && f_past_ok) begin : ap_bypass_alloc_mirror
			assert (w_addr_alloc_mirror_oh == addr_alloc_oh) ;
		end
	always @(posedge aclk)
		if ((aresetn && f_past_ok) && (CMD_ENTRY_RESERVE > 0)) begin : ap_cmd_entry_cap
			assert (w_cmd_entry_count <= sv2v_cast_54CAC_signed(N - CMD_ENTRY_RESERVE)) ;
		end
	initial _sv2v_0 = 0;
endmodule
module axi_monitor_base (
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
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] IW = ID_WIDTH;
	parameter signed [31:0] ADDR_BITS = (ADDR_BITS_IN_PKT > AW ? AW : ADDR_BITS_IN_PKT);
	input wire aclk;
	input wire aresetn;
	input wire clear;
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
		.clear(clear),
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
		.i_timeout_detected(w_timeout_detected),
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
	function automatic signed [31:0] monitor_common_pkg_cmd_entry_reserve;
		input reg signed [31:0] max_transactions;
		monitor_common_pkg_cmd_entry_reserve = (max_transactions >= 16 ? 2 : 0);
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
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
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
		.UNIT_ID(UNIT_ID),
		.AGENT_ID(AGENT_ID),
		.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
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
		.N_ADDR_RANGES(N_ADDR_RANGES)
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
module axi4_slave_wr_mon (
	aclk,
	aresetn,
	cam_clear,
	s_axi_awid,
	s_axi_awaddr,
	s_axi_awlen,
	s_axi_awsize,
	s_axi_awburst,
	s_axi_awlock,
	s_axi_awcache,
	s_axi_awprot,
	s_axi_awqos,
	s_axi_awregion,
	s_axi_awuser,
	s_axi_awvalid,
	s_axi_awready,
	s_axi_wdata,
	s_axi_wstrb,
	s_axi_wlast,
	s_axi_wuser,
	s_axi_wvalid,
	s_axi_wready,
	s_axi_bid,
	s_axi_bresp,
	s_axi_buser,
	s_axi_bvalid,
	s_axi_bready,
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
	cfg_monitor_enable,
	cfg_error_enable,
	cfg_timeout_enable,
	cfg_perf_enable,
	cfg_compl_enable,
	cfg_threshold_enable,
	cfg_debug_enable,
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
	busy,
	active_transactions,
	error_count,
	transaction_count,
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
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter [0:0] USE_MONITOR = 1'b1;
	parameter signed [31:0] N_ADDR_RANGES = 0;
	parameter [7:0] UNIT_ID = 8'h02;
	parameter [15:0] AGENT_ID = 16'h0015;
	parameter signed [31:0] MAX_TRANSACTIONS = 16;
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
	input wire [IW - 1:0] s_axi_awid;
	input wire [AW - 1:0] s_axi_awaddr;
	input wire [7:0] s_axi_awlen;
	input wire [2:0] s_axi_awsize;
	input wire [1:0] s_axi_awburst;
	input wire s_axi_awlock;
	input wire [3:0] s_axi_awcache;
	input wire [2:0] s_axi_awprot;
	input wire [3:0] s_axi_awqos;
	input wire [3:0] s_axi_awregion;
	input wire [UW - 1:0] s_axi_awuser;
	input wire s_axi_awvalid;
	output wire s_axi_awready;
	input wire [DW - 1:0] s_axi_wdata;
	input wire [SW - 1:0] s_axi_wstrb;
	input wire s_axi_wlast;
	input wire [UW - 1:0] s_axi_wuser;
	input wire s_axi_wvalid;
	output wire s_axi_wready;
	output wire [IW - 1:0] s_axi_bid;
	output wire [1:0] s_axi_bresp;
	output wire [UW - 1:0] s_axi_buser;
	output wire s_axi_bvalid;
	input wire s_axi_bready;
	output wire [IW - 1:0] fub_axi_awid;
	output wire [AW - 1:0] fub_axi_awaddr;
	output wire [7:0] fub_axi_awlen;
	output wire [2:0] fub_axi_awsize;
	output wire [1:0] fub_axi_awburst;
	output wire fub_axi_awlock;
	output wire [3:0] fub_axi_awcache;
	output wire [2:0] fub_axi_awprot;
	output wire [3:0] fub_axi_awqos;
	output wire [3:0] fub_axi_awregion;
	output wire [UW - 1:0] fub_axi_awuser;
	output wire fub_axi_awvalid;
	input wire fub_axi_awready;
	output wire [DW - 1:0] fub_axi_wdata;
	output wire [SW - 1:0] fub_axi_wstrb;
	output wire fub_axi_wlast;
	output wire [UW - 1:0] fub_axi_wuser;
	output wire fub_axi_wvalid;
	input wire fub_axi_wready;
	input wire [IW - 1:0] fub_axi_bid;
	input wire [1:0] fub_axi_bresp;
	input wire [UW - 1:0] fub_axi_buser;
	input wire fub_axi_bvalid;
	output wire fub_axi_bready;
	input wire cfg_monitor_enable;
	input wire cfg_error_enable;
	input wire cfg_timeout_enable;
	input wire cfg_perf_enable;
	input wire cfg_compl_enable;
	input wire cfg_threshold_enable;
	input wire cfg_debug_enable;
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
	output wire monbus_valid;
	input wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] monbus_packet;
	output wire [63:0] monbus_timestamp;
	output wire busy;
	output wire [7:0] active_transactions;
	output wire [15:0] error_count;
	output wire [31:0] transaction_count;
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
	wire w_core_s_axi_awready;
	wire w_block_ready;
	axi4_slave_wr #(
		.SKID_DEPTH_AW(SKID_DEPTH_AW),
		.SKID_DEPTH_W(SKID_DEPTH_W),
		.SKID_DEPTH_B(SKID_DEPTH_B),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH),
		.AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH)
	) axi4_slave_wr_inst(
		.aclk(aclk),
		.aresetn(aresetn),
		.s_axi_awid(s_axi_awid),
		.s_axi_awaddr(s_axi_awaddr),
		.s_axi_awlen(s_axi_awlen),
		.s_axi_awsize(s_axi_awsize),
		.s_axi_awburst(s_axi_awburst),
		.s_axi_awlock(s_axi_awlock),
		.s_axi_awcache(s_axi_awcache),
		.s_axi_awprot(s_axi_awprot),
		.s_axi_awqos(s_axi_awqos),
		.s_axi_awregion(s_axi_awregion),
		.s_axi_awuser(s_axi_awuser),
		.s_axi_awvalid(s_axi_awvalid),
		.s_axi_awready(w_core_s_axi_awready),
		.s_axi_wdata(s_axi_wdata),
		.s_axi_wstrb(s_axi_wstrb),
		.s_axi_wlast(s_axi_wlast),
		.s_axi_wuser(s_axi_wuser),
		.s_axi_wvalid(s_axi_wvalid),
		.s_axi_wready(s_axi_wready),
		.s_axi_bid(s_axi_bid),
		.s_axi_bresp(s_axi_bresp),
		.s_axi_buser(s_axi_buser),
		.s_axi_bvalid(s_axi_bvalid),
		.s_axi_bready(s_axi_bready),
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
		.busy(busy)
	);
	wire w_mon_cmd_valid;
	wire w_mon_data_valid;
	wire w_mon_resp_valid;
	wire [3:0] w_timeout_cnt;
	wire [15:0] w_perf_completed_count;
	wire [15:0] w_perf_error_count;
	assign w_mon_cmd_valid = s_axi_awvalid & cfg_monitor_enable;
	assign w_mon_data_valid = s_axi_wvalid & cfg_monitor_enable;
	assign w_mon_resp_valid = s_axi_bvalid & cfg_monitor_enable;
	assign w_timeout_cnt = (cfg_timeout_cycles == 16'h0000 ? 4'hf : (|cfg_timeout_cycles[15:4] ? 4'hf : cfg_timeout_cycles[3:0]));
	function automatic signed [15:0] sv2v_cast_16_signed;
		input reg signed [15:0] inp;
		sv2v_cast_16_signed = inp;
	endfunction
	generate
		if (USE_MONITOR) begin : gen_monitor
			axi_monitor_filtered #(
				.UNIT_ID(UNIT_ID),
				.AGENT_ID(AGENT_ID),
				.MAX_TRANSACTIONS(MAX_TRANSACTIONS),
				.ADDR_WIDTH(AW),
				.ID_WIDTH(IW),
				.IS_READ(1'b0),
				.IS_AXI(1'b1),
				.ENABLE_PERF_PACKETS(1'b1),
				.ENABLE_ERROR_LOGIC(ENABLE_ERROR_LOGIC),
				.ENABLE_TIMEOUT_LOGIC(ENABLE_TIMEOUT_LOGIC),
				.ENABLE_COMPL_LOGIC(ENABLE_COMPL_LOGIC),
				.ENABLE_THRESHOLD_LOGIC(ENABLE_THRESHOLD_LOGIC),
				.ENABLE_PERF_LOGIC(ENABLE_PERF_LOGIC),
				.ENABLE_DEBUG_LOGIC(ENABLE_DEBUG_LOGIC),
				.ENABLE_DEBUG_MODULE(1'b0),
				.ENABLE_FILTERING(ENABLE_FILTERING),
				.ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE),
				.N_ADDR_RANGES(N_ADDR_RANGES)
			) axi_monitor_inst(
				.aclk(aclk),
				.aresetn(aresetn),
				.clear(cam_clear | ~cfg_monitor_enable),
				.i_mon_time(i_mon_time),
				.cmd_addr(s_axi_awaddr),
				.cmd_id(s_axi_awid),
				.cmd_len(s_axi_awlen),
				.cmd_size(s_axi_awsize),
				.cmd_burst(s_axi_awburst),
				.cmd_valid(w_mon_cmd_valid),
				.cmd_ready(s_axi_awready),
				.data_id(s_axi_awid),
				.data_last(s_axi_wlast),
				.data_resp(2'b00),
				.data_valid(w_mon_data_valid),
				.data_ready(s_axi_wready),
				.resp_id(s_axi_bid),
				.resp_code(s_axi_bresp),
				.resp_valid(w_mon_resp_valid),
				.resp_ready(s_axi_bready),
				.cfg_freq_sel(4'b0001),
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
	assign s_axi_awready = w_core_s_axi_awready & (w_block_ready | ~cfg_monitor_enable);
	assign error_count = w_perf_error_count;
	assign transaction_count = {16'h0000, w_perf_completed_count};
	always @(*) begin
		if ((aresetn && cfg_monitor_enable) && !w_block_ready) begin : ap_block_ready_gating
			assert (!s_axi_awready) ;
		end
		if (aresetn && !cfg_monitor_enable) begin : ap_disabled_never_stalls
			assert (s_axi_awready == w_core_s_axi_awready) ;
		end
	end
endmodule
