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
	reg [DW - 1:0] r_data [0:DEPTH - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH < 2) || (DEPTH > 8)) begin : gen_depth_guard
			initial $display("Error [elaboration] /tmp/rds-canonical-repo-root/rtl/amba/gaxi/gaxi_skid_buffer.sv:101:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
		end
	endgenerate
	genvar _gv_gi_1;
	generate
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
	endgenerate
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
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
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
endmodule
module axi4_dwidth_converter_rd (
	aclk,
	aresetn,
	s_axi_arid,
	s_axi_araddr,
	s_axi_arlen,
	s_axi_arsize,
	s_axi_arburst,
	s_axi_arlock,
	s_axi_arcache,
	s_axi_arprot,
	s_axi_arqos,
	s_axi_arregion,
	s_axi_aruser,
	s_axi_arvalid,
	s_axi_arready,
	s_axi_rid,
	s_axi_rdata,
	s_axi_rresp,
	s_axi_rlast,
	s_axi_ruser,
	s_axi_rvalid,
	s_axi_rready,
	m_axi_arid,
	m_axi_araddr,
	m_axi_arlen,
	m_axi_arsize,
	m_axi_arburst,
	m_axi_arlock,
	m_axi_arcache,
	m_axi_arprot,
	m_axi_arqos,
	m_axi_arregion,
	m_axi_aruser,
	m_axi_arvalid,
	m_axi_arready,
	m_axi_rid,
	m_axi_rdata,
	m_axi_rresp,
	m_axi_rlast,
	m_axi_ruser,
	m_axi_rvalid,
	m_axi_rready
);
	parameter signed [31:0] S_AXI_DATA_WIDTH = 32;
	parameter signed [31:0] M_AXI_DATA_WIDTH = 128;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	localparam signed [31:0] S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8;
	localparam signed [31:0] WIDTH_RATIO = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH : S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH);
	localparam [0:0] UPSIZE = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam [0:0] DOWNSIZE = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH ? 1'b1 : 1'b0);
	localparam signed [31:0] AR_WIDTH = ((AXI_ID_WIDTH + AXI_ADDR_WIDTH) + 29) + AXI_USER_WIDTH;
	localparam signed [31:0] R_WIDTH = (((S_AXI_DATA_WIDTH + 2) + AXI_USER_WIDTH) + 1) + AXI_ID_WIDTH;
	input wire aclk;
	input wire aresetn;
	input wire [AXI_ID_WIDTH - 1:0] s_axi_arid;
	input wire [AXI_ADDR_WIDTH - 1:0] s_axi_araddr;
	input wire [7:0] s_axi_arlen;
	input wire [2:0] s_axi_arsize;
	input wire [1:0] s_axi_arburst;
	input wire s_axi_arlock;
	input wire [3:0] s_axi_arcache;
	input wire [2:0] s_axi_arprot;
	input wire [3:0] s_axi_arqos;
	input wire [3:0] s_axi_arregion;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_aruser;
	input wire s_axi_arvalid;
	output wire s_axi_arready;
	output wire [AXI_ID_WIDTH - 1:0] s_axi_rid;
	output wire [S_AXI_DATA_WIDTH - 1:0] s_axi_rdata;
	output wire [1:0] s_axi_rresp;
	output wire s_axi_rlast;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_ruser;
	output wire s_axi_rvalid;
	input wire s_axi_rready;
	output wire [AXI_ID_WIDTH - 1:0] m_axi_arid;
	output wire [AXI_ADDR_WIDTH - 1:0] m_axi_araddr;
	output wire [7:0] m_axi_arlen;
	output wire [2:0] m_axi_arsize;
	output wire [1:0] m_axi_arburst;
	output wire m_axi_arlock;
	output wire [3:0] m_axi_arcache;
	output wire [2:0] m_axi_arprot;
	output wire [3:0] m_axi_arqos;
	output wire [3:0] m_axi_arregion;
	output wire [AXI_USER_WIDTH - 1:0] m_axi_aruser;
	output wire m_axi_arvalid;
	input wire m_axi_arready;
	input wire [AXI_ID_WIDTH - 1:0] m_axi_rid;
	input wire [M_AXI_DATA_WIDTH - 1:0] m_axi_rdata;
	input wire [1:0] m_axi_rresp;
	input wire m_axi_rlast;
	input wire [AXI_USER_WIDTH - 1:0] m_axi_ruser;
	input wire m_axi_rvalid;
	output wire m_axi_rready;
	initial begin
		if (S_AXI_DATA_WIDTH != (2 ** $clog2(S_AXI_DATA_WIDTH)))
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:127:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "S_AXI_DATA_WIDTH must be power of 2");
		if (M_AXI_DATA_WIDTH != (2 ** $clog2(M_AXI_DATA_WIDTH)))
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:129:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "M_AXI_DATA_WIDTH must be power of 2");
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:131:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
		if (!UPSIZE && !DOWNSIZE)
			$display("Error [%0t] /tmp/rds-canonical-repo-root/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv:133:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "Must be either UPSIZE or DOWNSIZE mode");
	end
	wire [AR_WIDTH - 1:0] int_ar_data;
	wire int_ar_valid;
	wire int_ar_ready;
	wire [AXI_ID_WIDTH - 1:0] int_arid;
	wire [AXI_ADDR_WIDTH - 1:0] int_araddr;
	wire [7:0] int_arlen;
	wire [2:0] int_arsize;
	wire [1:0] int_arburst;
	wire int_arlock;
	wire [3:0] int_arcache;
	wire [2:0] int_arprot;
	wire [3:0] int_arqos;
	wire [3:0] int_arregion;
	wire [AXI_USER_WIDTH - 1:0] int_aruser;
	wire [R_WIDTH - 1:0] int_r_data;
	wire int_r_valid;
	wire int_r_ready;
	wire [AXI_ID_WIDTH - 1:0] int_rid;
	wire [S_AXI_DATA_WIDTH - 1:0] int_rdata;
	wire [1:0] int_rresp;
	wire int_rlast;
	wire arsplit_final;
	wire arsplit_pop;
	wire [AXI_USER_WIDTH - 1:0] int_ruser;
	wire w_blen_wr_ready;
	wire w_blen_rd_valid;
	wire [7:0] w_blen_rd_data;
	wire [7:0] w_blen_rd_lane;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AR),
		.DATA_WIDTH(AR_WIDTH)
	) ar_skid(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_arvalid),
		.wr_ready(s_axi_arready),
		.wr_data({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst, s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos, s_axi_arregion, s_axi_aruser}),
		.rd_valid(int_ar_valid),
		.rd_ready(int_ar_ready),
		.rd_data(int_ar_data),
		.count(),
		.rd_count()
	);
	assign {int_arid, int_araddr, int_arlen, int_arsize, int_arburst, int_arlock, int_arcache, int_arprot, int_arqos, int_arregion, int_aruser} = int_ar_data;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_R),
		.DATA_WIDTH(R_WIDTH)
	) r_skid(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(int_r_valid),
		.wr_ready(int_r_ready),
		.wr_data(int_r_data),
		.rd_valid(s_axi_rvalid),
		.rd_ready(s_axi_rready),
		.rd_data({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser}),
		.count(),
		.rd_count()
	);
	assign int_r_data = {int_rid, int_rdata, int_rresp, int_rlast, int_ruser};
	function automatic [9:0] sv2v_cast_10;
		input reg [9:0] inp;
		sv2v_cast_10 = inp;
	endfunction
	function automatic signed [9:0] sv2v_cast_10_signed;
		input reg signed [9:0] inp;
		sv2v_cast_10_signed = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic signed [8:0] sv2v_cast_9_signed;
		input reg signed [8:0] inp;
		sv2v_cast_9_signed = inp;
	endfunction
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	function automatic signed [AXI_ADDR_WIDTH - 1:0] sv2v_cast_6D0DE_signed;
		input reg signed [AXI_ADDR_WIDTH - 1:0] inp;
		sv2v_cast_6D0DE_signed = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_ar_downsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] MAX_BEATS = 256;
			localparam signed [31:0] CNTW = 9 + $clog2(WIDTH_RATIO);
			localparam signed [31:0] ARQ_DEPTH = 16;
			localparam signed [31:0] ARQ_AW = 4;
			reg [CNTW - 1:0] r_split_remaining;
			reg [AXI_ADDR_WIDTH - 1:0] r_split_addr;
			reg r_split_active;
			wire [8:0] w_this_beats;
			wire w_this_last;
			wire w_ar_issue;
			function automatic signed [CNTW - 1:0] sv2v_cast_1954F_signed;
				input reg signed [CNTW - 1:0] inp;
				sv2v_cast_1954F_signed = inp;
			endfunction
			assign w_this_beats = (r_split_remaining > sv2v_cast_1954F_signed(MAX_BEATS) ? sv2v_cast_9_signed(MAX_BEATS) : sv2v_cast_9(r_split_remaining));
			assign w_this_last = r_split_remaining <= sv2v_cast_1954F_signed(MAX_BEATS);
			assign w_ar_issue = m_axi_arvalid && m_axi_arready;
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					r_split_remaining <= 1'sb0;
					r_split_addr <= 1'sb0;
					r_split_active <= 1'b0;
				end
				else if (!r_split_active) begin
					if (int_ar_valid) begin
						begin : sv2v_autoblock_1
							reg [CNTW - 1:0] sv2v_tmp_cast;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_1;
							reg signed [CNTW - 1:0] sv2v_tmp_cast_2;
							sv2v_tmp_cast = int_arlen;
							sv2v_tmp_cast_1 = 1;
							sv2v_tmp_cast_2 = WIDTH_RATIO;
							r_split_remaining <= (sv2v_tmp_cast + sv2v_tmp_cast_1) * sv2v_tmp_cast_2;
						end
						r_split_addr <= int_araddr;
						r_split_active <= 1'b1;
					end
				end
				else if (w_ar_issue) begin
					if (w_this_last) begin
						r_split_remaining <= 1'sb0;
						r_split_active <= 1'b0;
					end
					else begin
						begin : sv2v_autoblock_2
							reg signed [CNTW - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = MAX_BEATS;
							r_split_remaining <= r_split_remaining - sv2v_tmp_cast;
						end
						if (int_arburst != 2'b00)
							r_split_addr <= r_split_addr + sv2v_cast_6D0DE_signed(MAX_BEATS * M_STRB_WIDTH);
					end
				end
			reg [ARQ_AW:0] arq_wptr;
			reg [ARQ_AW:0] arq_rptr;
			reg arq_mem [0:15];
			wire w_arq_full;
			assign w_arq_full = (arq_wptr[3:0] == arq_rptr[3:0]) && (arq_wptr[ARQ_AW] != arq_rptr[ARQ_AW]);
			assign arsplit_final = arq_mem[arq_rptr[3:0]];
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					arq_wptr <= 1'sb0;
					arq_rptr <= 1'sb0;
				end
				else begin
					if (w_ar_issue) begin
						arq_mem[arq_wptr[3:0]] <= w_this_last;
						arq_wptr <= arq_wptr + 1'b1;
					end
					if (arsplit_pop)
						arq_rptr <= arq_rptr + 1'b1;
				end
			assign m_axi_arid = int_arid;
			assign m_axi_araddr = r_split_addr;
			assign m_axi_arlen = sv2v_cast_8(w_this_beats - 9'd1);
			assign m_axi_arsize = MASTER_SIZE[2:0];
			assign m_axi_arburst = int_arburst;
			assign m_axi_arlock = int_arlock;
			assign m_axi_arcache = int_arcache;
			assign m_axi_arprot = int_arprot;
			assign m_axi_arqos = int_arqos;
			assign m_axi_arregion = int_arregion;
			assign m_axi_aruser = int_aruser;
			assign m_axi_arvalid = r_split_active && !w_arq_full;
			assign int_ar_ready = w_ar_issue && w_this_last;
		end
		else begin : gen_ar_upsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			assign arsplit_final = 1'b1;
			localparam signed [31:0] ALIGN_BITS = $clog2(M_STRB_WIDTH);
			wire [7:0] master_arlen;
			wire [AXI_ADDR_WIDTH - 1:0] aligned_araddr;
			wire [9:0] w_ar_lane;
			assign w_ar_lane = sv2v_cast_10(int_araddr[ALIGN_BITS - 1:0]) >> $clog2(S_STRB_WIDTH);
			assign master_arlen = sv2v_cast_8((((w_ar_lane + sv2v_cast_10(int_arlen)) + sv2v_cast_10_signed(WIDTH_RATIO)) / sv2v_cast_10_signed(WIDTH_RATIO)) - 10'd1);
			assign aligned_araddr = {int_araddr[AXI_ADDR_WIDTH - 1:ALIGN_BITS], {ALIGN_BITS {1'b0}}};
			assign m_axi_arid = int_arid;
			assign m_axi_araddr = aligned_araddr;
			assign m_axi_arlen = master_arlen;
			assign m_axi_arsize = MASTER_SIZE[2:0];
			assign m_axi_arburst = int_arburst;
			assign m_axi_arlock = int_arlock;
			assign m_axi_arcache = int_arcache;
			assign m_axi_arprot = int_arprot;
			assign m_axi_arqos = int_arqos;
			assign m_axi_arregion = int_arregion;
			assign m_axi_aruser = int_aruser;
			assign m_axi_arvalid = int_ar_valid && w_blen_wr_ready;
			assign int_ar_ready = m_axi_arready && w_blen_wr_ready;
		end
	endgenerate
	reg [AXI_ID_WIDTH - 1:0] r_rid_held;
	reg [AXI_USER_WIDTH - 1:0] r_ruser_held;
	always @(posedge aclk or negedge aresetn)
		if (!aresetn) begin
			r_rid_held <= 1'sb0;
			r_ruser_held <= 1'sb0;
		end
		else if (m_axi_rvalid && m_axi_rready) begin
			r_rid_held <= m_axi_rid;
			r_ruser_held <= m_axi_ruser;
		end
	assign int_rid = r_rid_held;
	assign int_ruser = r_ruser_held;
	generate
		if (DOWNSIZE) begin : gen_r_downsize
			axi_data_upsize #(
				.NARROW_WIDTH(M_AXI_DATA_WIDTH),
				.WIDE_WIDTH(S_AXI_DATA_WIDTH),
				.NARROW_SB_WIDTH(2),
				.WIDE_SB_WIDTH(2),
				.SB_OR_MODE(1)
			) u_r_upsize(
				.aclk(aclk),
				.aresetn(aresetn),
				.narrow_valid(m_axi_rvalid),
				.narrow_ready(m_axi_rready),
				.narrow_data(m_axi_rdata),
				.narrow_sideband(m_axi_rresp),
				.narrow_last(m_axi_rlast && arsplit_final),
				.start_lane(1'sb0),
				.wide_valid(int_r_valid),
				.wide_ready(int_r_ready),
				.wide_data(int_rdata),
				.wide_sideband(int_rresp),
				.wide_last(int_rlast)
			);
			assign arsplit_pop = (m_axi_rvalid && m_axi_rready) && m_axi_rlast;
			assign w_blen_wr_ready = 1'b1;
			assign w_blen_rd_valid = 1'b0;
			assign w_blen_rd_data = 1'sb0;
			assign w_blen_rd_lane = 1'sb0;
		end
		else begin : gen_r_upsize
			assign arsplit_pop = 1'b0;
			localparam signed [31:0] BLEN_FIFO_DEPTH = 16;
			localparam signed [31:0] BLEN_AW = 4;
			localparam signed [31:0] R_LANE_W = $clog2(WIDTH_RATIO);
			reg [7:0] blen_mem [0:15];
			reg [R_LANE_W - 1:0] blen_lane_mem [0:15];
			reg [BLEN_AW:0] blen_wptr;
			reg [BLEN_AW:0] blen_rptr;
			wire w_blen_push;
			wire w_blen_pop;
			assign w_blen_push = int_ar_valid && int_ar_ready;
			assign w_blen_pop = (int_r_valid && int_r_ready) && int_rlast;
			assign w_blen_wr_ready = !((blen_wptr[3:0] == blen_rptr[3:0]) && (blen_wptr[BLEN_AW] != blen_rptr[BLEN_AW]));
			assign w_blen_rd_valid = blen_wptr != blen_rptr;
			assign w_blen_rd_data = blen_mem[blen_rptr[3:0]];
			assign w_blen_rd_lane = sv2v_cast_8(blen_lane_mem[blen_rptr[3:0]]);
			always @(posedge aclk or negedge aresetn)
				if (!aresetn) begin
					blen_wptr <= 1'sb0;
					blen_rptr <= 1'sb0;
				end
				else begin
					if (w_blen_push) begin
						blen_mem[blen_wptr[3:0]] <= int_arlen;
						begin : sv2v_autoblock_3
							reg [R_LANE_W - 1:0] sv2v_tmp_cast;
							sv2v_tmp_cast = int_araddr[$clog2(M_STRB_WIDTH) - 1:0] >> $clog2(S_STRB_WIDTH);
							blen_lane_mem[blen_wptr[3:0]] <= sv2v_tmp_cast;
						end
						blen_wptr <= blen_wptr + 1'b1;
					end
					if (w_blen_pop)
						blen_rptr <= blen_rptr + 1'b1;
				end
			axi_data_dnsize #(
				.WIDE_WIDTH(M_AXI_DATA_WIDTH),
				.NARROW_WIDTH(S_AXI_DATA_WIDTH),
				.WIDE_SB_WIDTH(2),
				.NARROW_SB_WIDTH(2),
				.SB_BROADCAST(1),
				.TRACK_BURSTS(1),
				.BURST_LEN_WIDTH(8)
			) u_r_dnsize(
				.aclk(aclk),
				.aresetn(aresetn),
				.burst_len(w_blen_rd_data),
				.burst_start(w_blen_rd_valid),
				.start_lane(w_blen_rd_lane[$clog2(WIDTH_RATIO) - 1:0]),
				.wide_valid(m_axi_rvalid),
				.wide_ready(m_axi_rready),
				.wide_data(m_axi_rdata),
				.wide_sideband(m_axi_rresp),
				.wide_last(m_axi_rlast),
				.narrow_valid(int_r_valid),
				.narrow_ready(int_r_ready),
				.narrow_data(int_rdata),
				.narrow_sideband(int_rresp),
				.narrow_last(int_rlast)
			);
		end
	endgenerate
endmodule
