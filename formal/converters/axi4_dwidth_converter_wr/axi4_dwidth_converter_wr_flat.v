module reset_sync (
	clk,
	rst_n,
	sync_rst_n
);
	reg _sv2v_0;
	parameter signed [31:0] N = 3;
	parameter [0:0] KEEP_ATTRS = 1'b1;
	parameter [0:0] IN_ACTIVE_LOW = 1'b1;
	parameter [0:0] OUT_ACTIVE_LOW = 1'b1;
	parameter [0:0] ASYNC_ASSERT = 1'b1;
	input wire clk;
	input wire rst_n;
	output reg sync_rst_n;
	generate
		if (N < 2) begin : g_illegal
			initial $display("Error [%0t] /tmp/rds-canonical-repo-root/rtl/cdc/reset_sync.sv:248:17 - reset_sync.g_illegal.<unnamed_block>\n msg: ", $time, "reset_sync: N must be >= 2 (got %0d)", N);
		end
	endgenerate
	wire rst_in_h = (IN_ACTIVE_LOW ? ~rst_n : rst_n);
	generate
		if (ASYNC_ASSERT) begin : g_async_assert
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk or posedge rst_in_h)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
		end
		else begin : g_sync_only
			if (KEEP_ATTRS) begin : g_attrd
				(* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *) (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *) reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
			else begin : g_plain
				reg [N - 1:0] r_sync_reg = 1'sb0;
				always @(posedge clk)
					if (rst_in_h)
						r_sync_reg <= 1'sb1;
					else
						r_sync_reg <= {r_sync_reg[N - 2:0], 1'b0};
				wire sync_rst_h = r_sync_reg[N - 1];
				always @(*) begin
					if (_sv2v_0)
						;
					sync_rst_n = (OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h);
				end
			end
		end
	endgenerate
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
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			counter_bin_curr <= 'b0;
		else
			counter_bin_curr <= counter_bin_next;
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
	localparam signed [31:0] SLOTS = (DEPTH == 0 ? 1 : DEPTH);
	reg [DW - 1:0] r_data [0:SLOTS - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH != 0) && ((DEPTH < 2) || (DEPTH > 8))) begin : gen_depth_guard
			initial $display("Error [elaboration] /tmp/rds-canonical-repo-root/rtl/amba/gaxi/gaxi_skid_buffer.sv:107:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive, or 0 (pass-through)", DEPTH);
		end
	endgenerate
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		if (DEPTH == 0) begin : g_bypass
			wire [1:1] sv2v_tmp_B1958;
			assign sv2v_tmp_B1958 = rd_ready;
			always @(*) wr_ready = sv2v_tmp_B1958;
			wire [1:1] sv2v_tmp_00E98;
			assign sv2v_tmp_00E98 = wr_valid;
			always @(*) rd_valid = sv2v_tmp_00E98;
			assign rd_data = wr_data;
			wire [4:1] sv2v_tmp_953DA;
			assign sv2v_tmp_953DA = 1'sb0;
			always @(*) r_data_count = sv2v_tmp_953DA;
			wire [DW:1] sv2v_tmp_D35D5;
			assign sv2v_tmp_D35D5 = 1'sb0;
			always @(*) r_data[0] = sv2v_tmp_D35D5;
			assign rd_count = 1'sb0;
			assign count = 1'sb0;
			wire w_bypass_unused;
			assign w_bypass_unused = &{1'b0, axi_aclk, axi_aresetn, r_data[0], r_data_count, w_wr_xfer, w_rd_xfer};
		end
		else begin : g_skid
			genvar _gv_gi_1;
			for (_gv_gi_1 = 0; _gv_gi_1 < DEPTH; _gv_gi_1 = _gv_gi_1 + 1) begin : g_slot
				localparam gi = _gv_gi_1;
				always @(posedge axi_aclk or negedge axi_aresetn)
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
			always @(posedge axi_aclk or negedge axi_aresetn)
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
			always @(posedge axi_aclk or negedge axi_aresetn)
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
		end
	endgenerate
endmodule
module axi_data_upsize (
	aclk,
	aresetn,
	narrow_valid,
	narrow_ready,
	narrow_data,
	narrow_sideband,
	narrow_last,
	start_lane,
	wide_valid,
	wide_ready,
	wide_data,
	wide_sideband,
	wide_last
);
	parameter signed [31:0] NARROW_WIDTH = 32;
	parameter signed [31:0] WIDE_WIDTH = 128;
	parameter signed [31:0] NARROW_SB_WIDTH = 0;
	parameter signed [31:0] WIDE_SB_WIDTH = 0;
	parameter signed [31:0] SB_OR_MODE = 0;
	localparam signed [31:0] WIDTH_RATIO = WIDE_WIDTH / NARROW_WIDTH;
	localparam signed [31:0] PTR_WIDTH = $clog2(WIDTH_RATIO);
	localparam signed [31:0] NARROW_SB_PORT_WIDTH = (NARROW_SB_WIDTH > 0 ? NARROW_SB_WIDTH : 1);
	localparam signed [31:0] WIDE_SB_PORT_WIDTH = (WIDE_SB_WIDTH > 0 ? WIDE_SB_WIDTH : 1);
	input wire aclk;
	input wire aresetn;
	input wire narrow_valid;
	output wire narrow_ready;
	input wire [NARROW_WIDTH - 1:0] narrow_data;
	input wire [NARROW_SB_PORT_WIDTH - 1:0] narrow_sideband;
	input wire narrow_last;
	input wire [PTR_WIDTH - 1:0] start_lane;
	output wire wide_valid;
	input wire wide_ready;
	output wire [WIDE_WIDTH - 1:0] wide_data;
	output wire [WIDE_SB_PORT_WIDTH - 1:0] wide_sideband;
	output wire wide_last;
	initial begin
		if (WIDE_WIDTH <= NARROW_WIDTH)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi_data_upsize.sv:87:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be > NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if ((WIDE_WIDTH % NARROW_WIDTH) != 0)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi_data_upsize.sv:89:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDE_WIDTH (%0d) must be integer multiple of NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi_data_upsize.sv:91:13 - axi_data_upsize.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
	end
	reg [WIDE_WIDTH - 1:0] r_data_accumulator;
	reg [WIDE_SB_PORT_WIDTH - 1:0] r_sideband_accumulator;
	reg [PTR_WIDTH - 1:0] r_beat_ptr;
	reg r_wide_valid;
	reg r_last_buffered;
	reg r_burst_fresh;
	wire [PTR_WIDTH - 1:0] w_lane;
	assign w_lane = (r_beat_ptr == {PTR_WIDTH {1'sb0}} ? (r_burst_fresh ? start_lane : {PTR_WIDTH {1'sb0}}) : r_beat_ptr);
	wire narrow_completes_group;
	function automatic signed [PTR_WIDTH - 1:0] sv2v_cast_62A53_signed;
		input reg signed [PTR_WIDTH - 1:0] inp;
		sv2v_cast_62A53_signed = inp;
	endfunction
	assign narrow_completes_group = (narrow_valid && narrow_ready) && ((w_lane == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) || narrow_last);
	wire wide_accept;
	assign wide_accept = r_wide_valid && wide_ready;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_data_accumulator <= 1'sb0;
			r_beat_ptr <= 1'sb0;
			r_wide_valid <= 1'b0;
			r_last_buffered <= 1'b0;
			r_burst_fresh <= 1'b1;
		end
		else begin
			if (narrow_valid && narrow_ready) begin
				if (r_beat_ptr == {PTR_WIDTH {1'sb0}})
					r_data_accumulator <= {{WIDE_WIDTH - NARROW_WIDTH {1'b0}}, narrow_data} << (w_lane * NARROW_WIDTH);
				else
					r_data_accumulator[w_lane * NARROW_WIDTH+:NARROW_WIDTH] <= narrow_data;
				if (narrow_completes_group)
					r_beat_ptr <= 1'sb0;
				else
					r_beat_ptr <= w_lane + 1'b1;
				r_burst_fresh <= narrow_last;
			end
			if (narrow_completes_group) begin
				r_wide_valid <= 1'b1;
				r_last_buffered <= narrow_last;
			end
			else if (wide_accept) begin
				r_wide_valid <= 1'b0;
				r_last_buffered <= 1'b0;
			end
		end
	function automatic [WIDE_SB_PORT_WIDTH - 1:0] sv2v_cast_5BF29;
		input reg [WIDE_SB_PORT_WIDTH - 1:0] inp;
		sv2v_cast_5BF29 = inp;
	endfunction
	generate
		if (NARROW_SB_WIDTH > 0) begin : gen_sideband_accumulation
			if (SB_OR_MODE != 0) begin : gen_or_mode
				always @(posedge aclk or negedge aresetn)
					if (!aresetn)
						r_sideband_accumulator <= 1'sb0;
					else if (narrow_valid && narrow_ready) begin
						if (r_beat_ptr == {PTR_WIDTH {1'sb0}})
							r_sideband_accumulator <= sv2v_cast_5BF29(narrow_sideband);
						else if (sv2v_cast_5BF29(narrow_sideband) > r_sideband_accumulator)
							r_sideband_accumulator <= sv2v_cast_5BF29(narrow_sideband);
					end
			end
			else begin : gen_concat_mode
				always @(posedge aclk or negedge aresetn)
					if (!aresetn)
						r_sideband_accumulator <= 1'sb0;
					else if (narrow_valid && narrow_ready) begin
						if (r_beat_ptr == {PTR_WIDTH {1'sb0}})
							r_sideband_accumulator <= {{WIDE_SB_PORT_WIDTH - NARROW_SB_WIDTH {1'b0}}, narrow_sideband[NARROW_SB_WIDTH - 1:0]} << (w_lane * NARROW_SB_WIDTH);
						else
							r_sideband_accumulator[w_lane * NARROW_SB_WIDTH+:NARROW_SB_WIDTH] <= narrow_sideband[NARROW_SB_WIDTH - 1:0];
					end
			end
		end
	endgenerate
	assign narrow_ready = !r_wide_valid || wide_ready;
	assign wide_valid = r_wide_valid;
	assign wide_data = r_data_accumulator;
	assign wide_sideband = r_sideband_accumulator;
	assign wide_last = r_last_buffered && r_wide_valid;
endmodule
module axi4_dwidth_converter_wr (
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
	m_axi_bready
);
	reg _sv2v_0;
	parameter signed [31:0] S_AXI_DATA_WIDTH = 32;
	parameter signed [31:0] M_AXI_DATA_WIDTH = 128;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	localparam signed [31:0] S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] WIDTH_RATIO = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH : S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH);
	localparam [0:0] UPSIZE = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam [0:0] DOWNSIZE = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam signed [31:0] LANE_W = $clog2(WIDTH_RATIO);
	localparam signed [31:0] AW_WIDTH = ((AXI_ID_WIDTH + AXI_ADDR_WIDTH) + 29) + AXI_USER_WIDTH;
	localparam signed [31:0] W_WIDTH = ((S_AXI_DATA_WIDTH + S_STRB_WIDTH) + 1) + AXI_USER_WIDTH;
	localparam signed [31:0] B_WIDTH = (AXI_ID_WIDTH + 2) + AXI_USER_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire [AXI_ID_WIDTH - 1:0] s_axi_awid;
	input wire [AXI_ADDR_WIDTH - 1:0] s_axi_awaddr;
	input wire [7:0] s_axi_awlen;
	input wire [2:0] s_axi_awsize;
	input wire [1:0] s_axi_awburst;
	input wire s_axi_awlock;
	input wire [3:0] s_axi_awcache;
	input wire [2:0] s_axi_awprot;
	input wire [3:0] s_axi_awqos;
	input wire [3:0] s_axi_awregion;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_awuser;
	input wire s_axi_awvalid;
	output wire s_axi_awready;
	input wire [S_AXI_DATA_WIDTH - 1:0] s_axi_wdata;
	input wire [S_STRB_WIDTH - 1:0] s_axi_wstrb;
	input wire s_axi_wlast;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_wuser;
	input wire s_axi_wvalid;
	output wire s_axi_wready;
	output wire [AXI_ID_WIDTH - 1:0] s_axi_bid;
	output wire [1:0] s_axi_bresp;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_buser;
	output wire s_axi_bvalid;
	input wire s_axi_bready;
	output wire [AXI_ID_WIDTH - 1:0] m_axi_awid;
	output wire [AXI_ADDR_WIDTH - 1:0] m_axi_awaddr;
	output wire [7:0] m_axi_awlen;
	output wire [2:0] m_axi_awsize;
	output wire [1:0] m_axi_awburst;
	output wire m_axi_awlock;
	output wire [3:0] m_axi_awcache;
	output wire [2:0] m_axi_awprot;
	output wire [3:0] m_axi_awqos;
	output wire [3:0] m_axi_awregion;
	output wire [AXI_USER_WIDTH - 1:0] m_axi_awuser;
	output wire m_axi_awvalid;
	input wire m_axi_awready;
	output wire [M_AXI_DATA_WIDTH - 1:0] m_axi_wdata;
	output reg [M_STRB_WIDTH - 1:0] m_axi_wstrb;
	output wire m_axi_wlast;
	output wire [AXI_USER_WIDTH - 1:0] m_axi_wuser;
	output wire m_axi_wvalid;
	input wire m_axi_wready;
	input wire [AXI_ID_WIDTH - 1:0] m_axi_bid;
	input wire [1:0] m_axi_bresp;
	input wire [AXI_USER_WIDTH - 1:0] m_axi_buser;
	input wire m_axi_bvalid;
	output wire m_axi_bready;
	wire w_aresetn;
	reset_sync #(
		.N(3),
		.KEEP_ATTRS(1'b1),
		.IN_ACTIVE_LOW(1'b1),
		.OUT_ACTIVE_LOW(1'b1),
		.ASYNC_ASSERT(1'b1)
	) u_reset_sync(
		.clk(aclk),
		.rst_n(aresetn),
		.sync_rst_n(w_aresetn)
	);
	initial begin
		if (S_AXI_DATA_WIDTH != (2 ** $clog2(S_AXI_DATA_WIDTH)))
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:165:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "S_AXI_DATA_WIDTH must be power of 2");
		if (M_AXI_DATA_WIDTH != (2 ** $clog2(M_AXI_DATA_WIDTH)))
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:167:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "M_AXI_DATA_WIDTH must be power of 2");
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:169:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
		if (!UPSIZE && !DOWNSIZE)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_wr.sv:171:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "Must be either UPSIZE or DOWNSIZE mode");
	end
	wire [AW_WIDTH - 1:0] int_aw_data;
	wire int_aw_valid;
	wire int_aw_ready;
	wire [AXI_ID_WIDTH - 1:0] int_awid;
	wire [AXI_ADDR_WIDTH - 1:0] int_awaddr;
	wire [7:0] int_awlen;
	wire [2:0] int_awsize;
	wire [1:0] int_awburst;
	wire int_awlock;
	wire [3:0] int_awcache;
	wire [2:0] int_awprot;
	wire [3:0] int_awqos;
	wire [3:0] int_awregion;
	wire [AXI_USER_WIDTH - 1:0] int_awuser;
	wire [W_WIDTH - 1:0] int_w_data;
	wire int_w_valid;
	wire int_w_ready;
	wire [S_AXI_DATA_WIDTH - 1:0] int_wdata;
	wire [S_STRB_WIDTH - 1:0] int_wstrb;
	wire int_wlast;
	wire [AXI_USER_WIDTH - 1:0] int_wuser;
	wire [B_WIDTH - 1:0] int_b_data;
	wire int_b_valid;
	wire w_aw_issue;
	reg w_this_last;
	wire w_this_first;
	reg [8:0] w_this_parts;
	wire w_b_cam_slot_free;
	localparam signed [31:0] SPLITQ_DEPTH = 16;
	wire split_w_avail;
	wire [8:0] split_w_beats;
	wire split_w_pop;
	wire [1:0] split_w_mode;
	wire [LANE_W - 1:0] split_w_lane;
	wire [LANE_W - 1:0] split_w_rmask;
	localparam [1:0] CM_PACK = 2'd0;
	localparam [1:0] CM_PASS = 2'd1;
	localparam [1:0] CM_EXPAND = 2'd2;
	wire [7:0] w_upsize_start_lane;
	wire w_upsize_w_gate;
	wire [1:0] w_upsize_mode;
	wire [$clog2(M_STRB_WIDTH) - 1:0] w_upsize_pa;
	wire [2:0] w_upsize_size;
	wire [1:0] w_upsize_burst;
	wire [7:0] w_upsize_len;
	wire int_b_ready;
	wire [AXI_ID_WIDTH - 1:0] int_bid;
	wire [1:0] int_bresp;
	wire [AXI_USER_WIDTH - 1:0] int_buser;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AW),
		.DATA_WIDTH(AW_WIDTH)
	) aw_skid(
		.axi_aclk(aclk),
		.axi_aresetn(w_aresetn),
		.wr_valid(s_axi_awvalid),
		.wr_ready(s_axi_awready),
		.wr_data({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos, s_axi_awregion, s_axi_awuser}),
		.rd_valid(int_aw_valid),
		.rd_ready(int_aw_ready),
		.rd_data(int_aw_data),
		.count(),
		.rd_count()
	);
	assign {int_awid, int_awaddr, int_awlen, int_awsize, int_awburst, int_awlock, int_awcache, int_awprot, int_awqos, int_awregion, int_awuser} = int_aw_data;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_W),
		.DATA_WIDTH(W_WIDTH)
	) w_skid(
		.axi_aclk(aclk),
		.axi_aresetn(w_aresetn),
		.wr_valid(s_axi_wvalid),
		.wr_ready(s_axi_wready),
		.wr_data({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
		.rd_valid(int_w_valid),
		.rd_ready(int_w_ready),
		.rd_data(int_w_data),
		.count(),
		.rd_count()
	);
	assign {int_wdata, int_wstrb, int_wlast, int_wuser} = int_w_data;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_B),
		.DATA_WIDTH(B_WIDTH)
	) b_skid(
		.axi_aclk(aclk),
		.axi_aresetn(w_aresetn),
		.wr_valid(int_b_valid),
		.wr_ready(int_b_ready),
		.wr_data(int_b_data),
		.rd_valid(s_axi_bvalid),
		.rd_ready(s_axi_bready),
		.rd_data({s_axi_bid, s_axi_bresp, s_axi_buser}),
		.count(),
		.rd_count()
	);
	assign int_b_data = {int_bid, int_bresp, int_buser};
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	function automatic [LANE_W - 1:0] sv2v_cast_3FA0D;
		input reg [LANE_W - 1:0] inp;
		sv2v_cast_3FA0D = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic [9:0] sv2v_cast_10;
		input reg [9:0] inp;
		sv2v_cast_10 = inp;
	endfunction
	function automatic signed [9:0] sv2v_cast_10_signed;
		input reg signed [9:0] inp;
		sv2v_cast_10_signed = inp;
	endfunction
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	function automatic signed [8:0] sv2v_cast_9_signed;
		input reg signed [8:0] inp;
		sv2v_cast_9_signed = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_aw_downsize
			assign w_upsize_start_lane = 8'd0;
			assign w_upsize_w_gate = 1'b1;
			assign w_upsize_mode = CM_PACK;
			assign w_upsize_pa = 1'sb0;
			assign w_upsize_size = 1'sb0;
			assign w_upsize_burst = 1'sb0;
			assign w_upsize_len = 1'sb0;
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] MAX_BEATS = 256;
			localparam signed [31:0] CNTW = 9 + $clog2(WIDTH_RATIO);
			localparam signed [31:0] CNTP = CNTW + 1;
			localparam signed [31:0] SPLITQ_AW = 4;
			localparam signed [31:0] AW = AXI_ADDR_WIDTH;
			reg [CNTW - 1:0] r_split_remaining;
			reg [AW - 1:0] r_split_addr;
			reg [8:0] r_beats_left;
			reg r_split_active;
			reg r_split_issued;
			wire [1:0] w_mode;
			wire [2:0] w_rlog;
			wire [AW - 1:0] w_bmask;
			wire [AW - 1:0] w_wmask;
			wire [AW - 1:0] w_next_beat;
			wire [8:0] w_lane_in_beat;
			wire [8:0] w_cap;
			reg [8:0] w_this_beats;
			wire [LANE_W - 1:0] w_this_lane;
			wire [LANE_W - 1:0] w_this_rmask;
			assign w_mode = (int_awsize <= sv2v_cast_3_signed(MASTER_SIZE) ? CM_PASS : (int_awburst == 2'b01 ? CM_PACK : CM_EXPAND));
			assign w_rlog = int_awsize - sv2v_cast_3_signed(MASTER_SIZE);
			function automatic signed [AW - 1:0] sv2v_cast_DE851_signed;
				input reg signed [AW - 1:0] inp;
				sv2v_cast_DE851_signed = inp;
			endfunction
			assign w_bmask = (sv2v_cast_DE851_signed(1) << int_awsize) - sv2v_cast_DE851_signed(1);
			function automatic [AW - 1:0] sv2v_cast_DE851;
				input reg [AW - 1:0] inp;
				sv2v_cast_DE851 = inp;
			endfunction
			assign w_wmask = ((sv2v_cast_DE851(int_awlen) + sv2v_cast_DE851_signed(1)) << int_awsize) - sv2v_cast_DE851_signed(1);
			assign w_lane_in_beat = sv2v_cast_9((r_split_addr & w_bmask) >> MASTER_SIZE);
			assign w_cap = sv2v_cast_9_signed(MAX_BEATS) - w_lane_in_beat;
			assign w_next_beat = (int_awburst == 2'b10 ? (r_split_addr & ~w_wmask) | ((((r_split_addr & ~w_bmask) + w_bmask) + sv2v_cast_DE851_signed(1)) & w_wmask) : r_split_addr);
			assign w_this_lane = sv2v_cast_3FA0D(r_split_addr[$clog2(S_STRB_WIDTH) - 1:0] >> MASTER_SIZE);
			assign w_this_rmask = (w_mode == CM_PASS ? {LANE_W {1'sb0}} : sv2v_cast_3FA0D((9'd1 << w_rlog) - 9'd1));
			always @(*) begin
				if (_sv2v_0)
					;
				case (w_mode)
					CM_PASS: begin
						w_this_beats = sv2v_cast_9(int_awlen) + 9'd1;
						w_this_last = 1'b1;
						w_this_parts = 9'd1;
					end
					CM_EXPAND: begin
						w_this_beats = (9'd1 << w_rlog) - w_lane_in_beat;
						w_this_last = r_beats_left == 9'd1;
						w_this_parts = sv2v_cast_9(int_awlen) + 9'd1;
					end
					default: begin
						begin : sv2v_autoblock_1
							reg [CNTW - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = w_cap;
							w_this_beats = (r_split_remaining > sv2v_tmp_cast ? w_cap : sv2v_cast_9(r_split_remaining));
						end
						begin : sv2v_autoblock_2
							reg [CNTW - 1:0] sv2v_tmp_cast_1;
							sv2v_tmp_cast_1 = w_cap;
							w_this_last = r_split_remaining <= sv2v_tmp_cast_1;
						end
						begin : sv2v_autoblock_3
							reg [CNTP - 1:0] sv2v_tmp_cast_2;
							reg signed [CNTP - 1:0] sv2v_tmp_cast_3;
							reg signed [CNTP - 1:0] sv2v_tmp_cast_4;
							sv2v_tmp_cast_2 = int_awlen;
							sv2v_tmp_cast_3 = 1;
							sv2v_tmp_cast_4 = 255;
							w_this_parts = sv2v_cast_9((((sv2v_tmp_cast_2 + sv2v_tmp_cast_3) << w_rlog) + sv2v_tmp_cast_4) >> 8);
						end
					end
				endcase
			end
			assign w_this_first = !r_split_issued;
			assign w_aw_issue = m_axi_awvalid && m_axi_awready;
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin
					r_split_remaining <= 1'sb0;
					r_split_addr <= 1'sb0;
					r_beats_left <= 1'sb0;
					r_split_active <= 1'b0;
					r_split_issued <= 1'b0;
				end
				else if (!r_split_active) begin
					r_split_issued <= 1'b0;
					if (int_aw_valid) begin
						begin : sv2v_autoblock_4
							reg [CNTW - 1:0] sv2v_tmp_cast;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_1;
							reg [CNTW - 1:0] sv2v_tmp_cast_2;
							sv2v_tmp_cast = int_awlen;
							sv2v_tmp_cast_1 = 1;
							sv2v_tmp_cast_2 = (int_awaddr & w_bmask) >> MASTER_SIZE;
							r_split_remaining <= ((sv2v_tmp_cast + sv2v_tmp_cast_1) << w_rlog) - sv2v_tmp_cast_2;
						end
						r_split_addr <= int_awaddr;
						r_beats_left <= sv2v_cast_9(int_awlen) + 9'd1;
						r_split_active <= 1'b1;
					end
				end
				else if (w_aw_issue) begin
					r_split_issued <= !w_this_last;
					if (w_this_last) begin
						r_split_remaining <= 1'sb0;
						r_split_active <= 1'b0;
					end
					else begin
						begin : sv2v_autoblock_5
							reg [CNTW - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = w_this_beats;
							r_split_remaining <= r_split_remaining - sv2v_tmp_cast;
						end
						r_beats_left <= r_beats_left - 9'd1;
						begin : sv2v_autoblock_6
							reg signed [AW - 1:0] sv2v_tmp_cast_1;
							sv2v_tmp_cast_1 = MAX_BEATS * M_STRB_WIDTH;
							r_split_addr <= (w_mode == CM_EXPAND ? w_next_beat : (r_split_addr & ~w_bmask) + sv2v_tmp_cast_1);
						end
					end
				end
			localparam signed [31:0] SQ_W = (2 + (2 * LANE_W)) + 9;
			reg [SQ_W - 1:0] splitq_mem [0:15];
			reg [SPLITQ_AW:0] splitq_wptr;
			reg [SPLITQ_AW:0] splitq_rptr_w;
			wire w_splitq_full;
			assign w_splitq_full = (splitq_wptr[3:0] == splitq_rptr_w[3:0]) && (splitq_wptr[SPLITQ_AW] != splitq_rptr_w[SPLITQ_AW]);
			assign split_w_avail = splitq_wptr != splitq_rptr_w;
			assign {split_w_mode, split_w_lane, split_w_rmask, split_w_beats} = splitq_mem[splitq_rptr_w[3:0]];
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin
					splitq_wptr <= 1'sb0;
					splitq_rptr_w <= 1'sb0;
				end
				else begin
					if (w_aw_issue) begin
						splitq_mem[splitq_wptr[3:0]] <= {w_mode, w_this_lane, w_this_rmask, w_this_beats};
						splitq_wptr <= splitq_wptr + 1'b1;
					end
					if (split_w_pop)
						splitq_rptr_w <= splitq_rptr_w + 1'b1;
				end
			assign m_axi_awid = int_awid;
			assign m_axi_awaddr = r_split_addr;
			assign m_axi_awlen = sv2v_cast_8(w_this_beats - 9'd1);
			assign m_axi_awsize = (w_mode == CM_PASS ? int_awsize : MASTER_SIZE[2:0]);
			assign m_axi_awburst = (w_mode == CM_PASS ? int_awburst : 2'b01);
			assign m_axi_awlock = int_awlock;
			assign m_axi_awcache = int_awcache;
			assign m_axi_awprot = int_awprot;
			assign m_axi_awqos = int_awqos;
			assign m_axi_awregion = int_awregion;
			assign m_axi_awuser = int_awuser;
			assign m_axi_awvalid = (r_split_active && !w_splitq_full) && (!w_this_first || w_b_cam_slot_free);
			assign int_aw_ready = w_aw_issue && w_this_last;
		end
		else begin : gen_aw_upsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] PAW = $clog2(M_STRB_WIDTH);
			assign split_w_avail = 1'b0;
			assign split_w_beats = 9'd0;
			assign split_w_mode = CM_PACK;
			assign split_w_lane = 1'sb0;
			assign split_w_rmask = 1'sb0;
			wire [1:1] sv2v_tmp_18A94;
			assign sv2v_tmp_18A94 = 1'b1;
			always @(*) w_this_last = sv2v_tmp_18A94;
			assign w_this_first = 1'b1;
			wire [9:1] sv2v_tmp_01E75;
			assign sv2v_tmp_01E75 = 9'd1;
			always @(*) w_this_parts = sv2v_tmp_01E75;
			assign w_aw_issue = m_axi_awvalid && m_axi_awready;
			wire [1:0] w_mode;
			assign w_mode = ((int_awburst == 2'b01) && (int_awsize == sv2v_cast_3_signed($clog2(S_STRB_WIDTH))) ? CM_PACK : CM_PASS);
			wire [LANE_W - 1:0] w_aw_lane;
			assign w_aw_lane = sv2v_cast_3FA0D(int_awaddr[$clog2(M_STRB_WIDTH) - 1:0] >> $clog2(S_STRB_WIDTH));
			localparam signed [31:0] WLANE_DEPTH = 16;
			localparam signed [31:0] WLANE_AW = 4;
			localparam signed [31:0] WQ_W = ((2 + LANE_W) + PAW) + 13;
			reg [WQ_W - 1:0] wlane_mem [0:15];
			reg [WLANE_AW:0] wlane_wptr;
			reg [WLANE_AW:0] wlane_rptr;
			wire w_wlane_full;
			wire w_wlane_avail;
			wire [LANE_W - 1:0] w_head_lane;
			assign w_wlane_full = (wlane_wptr[WLANE_AW] != wlane_rptr[WLANE_AW]) && (wlane_wptr[3:0] == wlane_rptr[3:0]);
			assign w_wlane_avail = wlane_wptr != wlane_rptr;
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin
					wlane_wptr <= 1'sb0;
					wlane_rptr <= 1'sb0;
				end
				else begin
					if (int_aw_valid && int_aw_ready) begin
						begin : sv2v_autoblock_7
							reg [PAW - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = int_awaddr;
							wlane_mem[wlane_wptr[3:0]] <= {w_mode, w_aw_lane, sv2v_tmp_cast, int_awsize, int_awburst, int_awlen};
						end
						wlane_wptr <= wlane_wptr + 1'b1;
					end
					if ((int_w_valid && int_w_ready) && int_wlast)
						wlane_rptr <= wlane_rptr + 1'b1;
				end
			assign {w_upsize_mode, w_head_lane, w_upsize_pa, w_upsize_size, w_upsize_burst, w_upsize_len} = wlane_mem[wlane_rptr[3:0]];
			assign w_upsize_start_lane = sv2v_cast_8(w_head_lane);
			assign w_upsize_w_gate = w_wlane_avail;
			assign m_axi_awid = int_awid;
			assign m_axi_awaddr = int_awaddr;
			assign m_axi_awlen = (w_mode == CM_PASS ? int_awlen : sv2v_cast_8((((sv2v_cast_10(w_aw_lane) + sv2v_cast_10(int_awlen)) + sv2v_cast_10_signed(WIDTH_RATIO)) / sv2v_cast_10_signed(WIDTH_RATIO)) - 10'd1));
			assign m_axi_awsize = (w_mode == CM_PASS ? int_awsize : MASTER_SIZE[2:0]);
			assign m_axi_awburst = int_awburst;
			assign m_axi_awlock = int_awlock;
			assign m_axi_awcache = int_awcache;
			assign m_axi_awprot = int_awprot;
			assign m_axi_awqos = int_awqos;
			assign m_axi_awregion = int_awregion;
			assign m_axi_awuser = int_awuser;
			assign m_axi_awvalid = int_aw_valid && !w_wlane_full;
			assign int_aw_ready = m_axi_awready && !w_wlane_full;
		end
	endgenerate
	reg [AXI_USER_WIDTH - 1:0] r_wuser_held;
	always @(posedge aclk or negedge w_aresetn)
		if (!w_aresetn)
			r_wuser_held <= 1'sb0;
		else if (int_w_valid && int_w_ready)
			r_wuser_held <= int_wuser;
	assign m_axi_wuser = r_wuser_held;
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	function automatic signed [LANE_W - 1:0] sv2v_cast_3FA0D_signed;
		input reg signed [LANE_W - 1:0] inp;
		sv2v_cast_3FA0D_signed = inp;
	endfunction
	function automatic [2:0] sv2v_cast_3;
		input reg [2:0] inp;
		sv2v_cast_3 = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_w_downsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			reg [8:0] r_w_beats_left;
			reg [LANE_W - 1:0] r_w_chunk;
			reg [LANE_W - 1:0] r_w_rmask;
			reg [1:0] r_w_mode;
			reg [LANE_W - 1:0] w_pass_chunk;
			wire [LANE_W - 1:0] w_chunk;
			wire w_last_hs;
			wire w_hs;
			wire w_take_wide;
			always @(*) begin
				if (_sv2v_0)
					;
				w_pass_chunk = 1'sb0;
				begin : sv2v_autoblock_8
					reg signed [31:0] k;
					for (k = WIDTH_RATIO - 1; k >= 0; k = k - 1)
						if (|int_wstrb[k * M_STRB_WIDTH+:M_STRB_WIDTH])
							w_pass_chunk = sv2v_cast_3FA0D_signed(k);
				end
			end
			assign w_chunk = (r_w_mode == CM_PASS ? w_pass_chunk : r_w_chunk);
			assign m_axi_wvalid = int_w_valid && (r_w_beats_left != 9'd0);
			assign m_axi_wdata = int_wdata[w_chunk * M_AXI_DATA_WIDTH+:M_AXI_DATA_WIDTH];
			wire [M_STRB_WIDTH:1] sv2v_tmp_4EAEA;
			assign sv2v_tmp_4EAEA = int_wstrb[w_chunk * M_STRB_WIDTH+:M_STRB_WIDTH];
			always @(*) m_axi_wstrb = sv2v_tmp_4EAEA;
			assign m_axi_wlast = r_w_beats_left == 9'd1;
			assign w_hs = m_axi_wvalid && m_axi_wready;
			assign w_last_hs = w_hs && (r_w_beats_left == 9'd1);
			assign w_take_wide = (r_w_mode == CM_PASS) || ((r_w_chunk & r_w_rmask) == r_w_rmask);
			assign int_w_ready = (m_axi_wready && (r_w_beats_left != 9'd0)) && w_take_wide;
			assign split_w_pop = split_w_avail && ((r_w_beats_left == 9'd0) || w_last_hs);
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin
					r_w_beats_left <= 9'd0;
					r_w_chunk <= 1'sb0;
					r_w_rmask <= 1'sb0;
					r_w_mode <= CM_PACK;
				end
				else if (split_w_pop) begin
					r_w_beats_left <= split_w_beats;
					r_w_chunk <= split_w_lane;
					r_w_rmask <= split_w_rmask;
					r_w_mode <= split_w_mode;
				end
				else if (w_hs) begin
					r_w_beats_left <= r_w_beats_left - 9'd1;
					r_w_chunk <= r_w_chunk + sv2v_cast_3FA0D_signed(1);
				end
		end
		else begin : gen_w_upsize
			assign split_w_pop = 1'b0;
			localparam signed [31:0] PAW = $clog2(M_STRB_WIDTH);
			wire w_upz_nready;
			wire w_upz_wvalid;
			wire w_upz_wlast;
			wire [M_AXI_DATA_WIDTH - 1:0] w_upz_wdata;
			wire [M_STRB_WIDTH - 1:0] w_upz_wstrb;
			wire w_pass;
			wire w_pass_go;
			wire w_sel_prim;
			reg [2:0] r_prim_bursts;
			wire w_prim_busy;
			reg r_pa_live;
			reg [PAW - 1:0] r_pa;
			wire [PAW - 1:0] w_pa;
			wire [PAW - 1:0] w_pa_bm;
			wire [PAW - 1:0] w_pa_wm;
			wire [PAW - 1:0] w_pa_step;
			wire [PAW - 1:0] w_pa_next;
			wire [15:0] w_pa_span;
			wire [LANE_W - 1:0] w_pa_chunk;
			assign w_pass = w_upsize_mode == CM_PASS;
			assign w_prim_busy = r_prim_bursts != 3'd0;
			assign w_sel_prim = w_prim_busy || !w_pass;
			assign w_pass_go = (w_upsize_w_gate && w_pass) && !w_prim_busy;
			assign w_pa = (r_pa_live ? r_pa : w_upsize_pa);
			function automatic [PAW - 1:0] sv2v_cast_B30D0;
				input reg [PAW - 1:0] inp;
				sv2v_cast_B30D0 = inp;
			endfunction
			assign w_pa_bm = sv2v_cast_B30D0((16'd1 << w_upsize_size) - 16'd1);
			assign w_pa_span = (sv2v_cast_16(w_upsize_len) + 16'd1) << w_upsize_size;
			assign w_pa_wm = sv2v_cast_B30D0(w_pa_span - 16'd1);
			function automatic signed [PAW - 1:0] sv2v_cast_B30D0_signed;
				input reg signed [PAW - 1:0] inp;
				sv2v_cast_B30D0_signed = inp;
			endfunction
			assign w_pa_step = ((w_pa & ~w_pa_bm) + w_pa_bm) + sv2v_cast_B30D0_signed(1);
			assign w_pa_next = (w_upsize_burst == 2'b00 ? w_pa : (w_upsize_burst == 2'b10 ? (w_pa & ~w_pa_wm) | (w_pa_step & w_pa_wm) : w_pa_step));
			assign w_pa_chunk = sv2v_cast_3FA0D(w_pa >> $clog2(S_STRB_WIDTH));
			assign int_w_ready = (w_pass ? w_pass_go && m_axi_wready : w_upz_nready && w_upsize_w_gate);
			always @(*) begin
				if (_sv2v_0)
					;
				m_axi_wstrb = 1'sb0;
				begin : sv2v_autoblock_9
					reg signed [31:0] k;
					for (k = 0; k < WIDTH_RATIO; k = k + 1)
						if (sv2v_cast_3FA0D_signed(k) == w_pa_chunk)
							m_axi_wstrb[k * S_STRB_WIDTH+:S_STRB_WIDTH] = int_wstrb;
				end
				if (w_sel_prim)
					m_axi_wstrb = w_upz_wstrb;
			end
			assign m_axi_wvalid = (w_sel_prim ? w_upz_wvalid : int_w_valid && w_pass_go);
			assign m_axi_wdata = (w_sel_prim ? w_upz_wdata : {WIDTH_RATIO {int_wdata}});
			assign m_axi_wlast = (w_sel_prim ? w_upz_wlast : int_wlast);
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin
					r_prim_bursts <= 3'd0;
					r_pa_live <= 1'b0;
					r_pa <= 1'sb0;
				end
				else begin
					r_prim_bursts <= (r_prim_bursts + sv2v_cast_3(((!w_pass && int_w_valid) && int_w_ready) && int_wlast)) - sv2v_cast_3(((w_sel_prim && w_upz_wvalid) && m_axi_wready) && w_upz_wlast);
					if ((w_pass && int_w_valid) && int_w_ready) begin
						r_pa <= w_pa_next;
						r_pa_live <= !int_wlast;
					end
				end
			axi_data_upsize #(
				.NARROW_WIDTH(S_AXI_DATA_WIDTH),
				.WIDE_WIDTH(M_AXI_DATA_WIDTH),
				.NARROW_SB_WIDTH(S_STRB_WIDTH),
				.WIDE_SB_WIDTH(M_STRB_WIDTH),
				.SB_OR_MODE(0)
			) u_w_upsize(
				.aclk(aclk),
				.aresetn(w_aresetn),
				.narrow_valid((int_w_valid && w_upsize_w_gate) && !w_pass),
				.narrow_ready(w_upz_nready),
				.narrow_data(int_wdata),
				.narrow_sideband(int_wstrb),
				.narrow_last(int_wlast),
				.start_lane(w_upsize_start_lane[$clog2(WIDTH_RATIO) - 1:0]),
				.wide_valid(w_upz_wvalid),
				.wide_ready(m_axi_wready && w_sel_prim),
				.wide_data(w_upz_wdata),
				.wide_sideband(w_upz_wstrb),
				.wide_last(w_upz_wlast)
			);
		end
		if (DOWNSIZE) begin : gen_b_fold
			localparam signed [31:0] BQ_W = (AXI_ID_WIDTH + 2) + AXI_USER_WIDTH;
			wire q_bvalid;
			wire q_bready;
			wire [AXI_ID_WIDTH - 1:0] q_bid;
			wire [1:0] q_bresp;
			wire [AXI_USER_WIDTH - 1:0] q_buser;
			wire [BQ_W - 1:0] q_bpkt;
			gaxi_skid_buffer #(
				.DEPTH(2),
				.DATA_WIDTH(BQ_W)
			) b_in_skid(
				.axi_aclk(aclk),
				.axi_aresetn(w_aresetn),
				.wr_valid(m_axi_bvalid),
				.wr_ready(m_axi_bready),
				.wr_data({m_axi_bid, m_axi_bresp, m_axi_buser}),
				.rd_valid(q_bvalid),
				.rd_ready(q_bready),
				.rd_data(q_bpkt),
				.count(),
				.rd_count()
			);
			assign {q_bid, q_bresp, q_buser} = q_bpkt;
			localparam signed [31:0] B_CAM_DEPTH = SPLITQ_DEPTH;
			localparam signed [31:0] B_CAM_AW = 4;
			reg [AXI_ID_WIDTH + 10:0] b_cam [0:15];
			reg [15:0] b_cam_valid;
			reg [15:0] b_cam_older [0:15];
			reg [15:0] b_cam_last;
			wire [8:0] w_b_cam_push_count;
			assign w_b_cam_push_count = w_this_parts;
			reg [3:0] w_b_cam_free_idx;
			reg w_b_cam_free_found;
			always @(*) begin
				if (_sv2v_0)
					;
				w_b_cam_free_found = 1'b0;
				w_b_cam_free_idx = 1'sb0;
				begin : sv2v_autoblock_10
					reg signed [31:0] i;
					for (i = 0; i < B_CAM_DEPTH; i = i + 1)
						if (!b_cam_valid[i] && !w_b_cam_free_found) begin
							w_b_cam_free_found = 1'b1;
							begin : sv2v_autoblock_11
								reg signed [3:0] sv2v_tmp_cast;
								sv2v_tmp_cast = i;
								w_b_cam_free_idx = sv2v_tmp_cast;
							end
						end
				end
			end
			assign w_b_cam_slot_free = w_b_cam_free_found;
			reg [15:0] w_b_cam_hit;
			wire w_b_cam_match;
			wire w_b_cam_last;
			reg [1:0] w_b_cam_worst;
			reg [15:0] w_b_cam_same_id;
			always @(*) begin
				if (_sv2v_0)
					;
				w_b_cam_worst = 1'sb0;
				begin : sv2v_autoblock_12
					reg signed [31:0] i;
					for (i = 0; i < B_CAM_DEPTH; i = i + 1)
						begin
							w_b_cam_hit[i] = (b_cam_valid[i] && (b_cam[i][AXI_ID_WIDTH + 10-:((AXI_ID_WIDTH + 10) >= 11 ? AXI_ID_WIDTH + 0 : 12 - (AXI_ID_WIDTH + 10))] == q_bid)) && ((b_cam_older[i] & b_cam_valid) == {16 {1'sb0}});
							w_b_cam_same_id[i] = b_cam_valid[i] && (b_cam[i][AXI_ID_WIDTH + 10-:((AXI_ID_WIDTH + 10) >= 11 ? AXI_ID_WIDTH + 0 : 12 - (AXI_ID_WIDTH + 10))] == int_awid);
							if (w_b_cam_hit[i])
								w_b_cam_worst = w_b_cam_worst | b_cam[i][1-:2];
						end
				end
			end
			assign w_b_cam_match = |w_b_cam_hit;
			assign w_b_cam_last = |(w_b_cam_hit & b_cam_last);
			assign int_bid = q_bid;
			assign int_buser = q_buser;
			assign int_b_valid = q_bvalid && w_b_cam_last;
			assign int_bresp = (q_bresp > w_b_cam_worst ? q_bresp : w_b_cam_worst);
			assign q_bready = (q_bvalid && w_b_cam_last ? int_b_ready : 1'b1);
			always @(posedge aclk or negedge w_aresetn)
				if (!w_aresetn) begin : sv2v_autoblock_13
					reg signed [31:0] i;
					for (i = 0; i < B_CAM_DEPTH; i = i + 1)
						begin
							b_cam_valid[i] <= 1'b0;
							b_cam[i] <= 1'sb0;
							b_cam_older[i] <= 1'sb0;
							b_cam_last[i] <= 1'b0;
						end
				end
				else begin
					if (w_aw_issue && w_this_first) begin
						if (w_b_cam_free_found) begin
							b_cam_valid[w_b_cam_free_idx] <= 1'b1;
							b_cam[w_b_cam_free_idx][AXI_ID_WIDTH + 10-:((AXI_ID_WIDTH + 10) >= 11 ? AXI_ID_WIDTH + 0 : 12 - (AXI_ID_WIDTH + 10))] <= int_awid;
							b_cam[w_b_cam_free_idx][10-:9] <= w_b_cam_push_count;
							b_cam_last[w_b_cam_free_idx] <= w_b_cam_push_count == 9'd1;
							b_cam[w_b_cam_free_idx][1-:2] <= 2'b00;
							begin : sv2v_autoblock_14
								reg signed [31:0] i;
								for (i = 0; i < B_CAM_DEPTH; i = i + 1)
									b_cam_older[i][w_b_cam_free_idx] <= 1'b0;
							end
							b_cam_older[w_b_cam_free_idx] <= w_b_cam_same_id;
						end
					end
					begin : sv2v_autoblock_15
						reg signed [31:0] i;
						for (i = 0; i < B_CAM_DEPTH; i = i + 1)
							if ((q_bvalid && q_bready) && w_b_cam_hit[i]) begin
								if (b_cam_last[i])
									b_cam_valid[i] <= 1'b0;
								else begin
									b_cam[i][10-:9] <= b_cam[i][10-:9] - 9'd1;
									b_cam_last[i] <= b_cam[i][10-:9] == 9'd2;
									if (q_bresp > b_cam[i][1-:2])
										b_cam[i][1-:2] <= q_bresp;
								end
							end
					end
				end
		end
		else begin : gen_b_pass
			assign w_b_cam_slot_free = 1'b1;
			assign int_bid = m_axi_bid;
			assign int_bresp = m_axi_bresp;
			assign int_buser = m_axi_buser;
			assign int_b_valid = m_axi_bvalid;
			assign m_axi_bready = int_b_ready;
		end
	endgenerate
	initial _sv2v_0 = 0;
endmodule
