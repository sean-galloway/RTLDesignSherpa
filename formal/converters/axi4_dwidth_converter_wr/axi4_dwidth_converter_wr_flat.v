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
	reg [BW - 1:0] r_data;
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	wire [DW - 1:0] zeros;
	assign zeros = 'b0;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(posedge axi_aclk)
		if (!axi_aresetn) begin
			r_data <= 'b0;
			r_data_count <= 'b0;
		end
		else
			case ({w_wr_xfer, w_rd_xfer})
				2'b10: begin
					r_data[DW * r_data_count+:DW] <= wr_data;
					r_data_count <= r_data_count + 1;
				end
				2'b01: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data_count <= r_data_count - 1;
				end
				2'b11: begin
					r_data <= {zeros, r_data[BUF_WIDTH - 1:DW]};
					r_data[DW * (sv2v_cast_32(r_data_count) - 1)+:DW] <= wr_data;
				end
				default:
					;
			endcase
	always @(posedge axi_aclk)
		if (!axi_aresetn) begin
			wr_ready <= 1'b0;
			rd_valid <= 1'b0;
		end
		else begin
			wr_ready <= ((sv2v_cast_32(r_data_count) <= (DEPTH - 2)) || ((sv2v_cast_32(r_data_count) == (DEPTH - 1)) && (~w_wr_xfer || w_rd_xfer))) || ((sv2v_cast_32(r_data_count) == DEPTH) && w_rd_xfer);
			rd_valid <= ((r_data_count >= 2) || ((r_data_count == 4'b0001) && (~w_rd_xfer || w_wr_xfer))) || ((r_data_count == 4'b0000) && w_wr_xfer);
		end
	assign rd_data = r_data[DW - 1:0];
	assign rd_count = r_data_count;
	assign count = r_data_count;
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
	localparam signed [31:0] PTR_WIDTH = $clog2(WIDTH_RATIO);
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
	output wire [M_STRB_WIDTH - 1:0] m_axi_wstrb;
	output wire m_axi_wlast;
	output wire [AXI_USER_WIDTH - 1:0] m_axi_wuser;
	output wire m_axi_wvalid;
	input wire m_axi_wready;
	input wire [AXI_ID_WIDTH - 1:0] m_axi_bid;
	input wire [1:0] m_axi_bresp;
	input wire [AXI_USER_WIDTH - 1:0] m_axi_buser;
	input wire m_axi_bvalid;
	output wire m_axi_bready;
	initial begin
		if (S_AXI_DATA_WIDTH != (2 ** $clog2(S_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv:145:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "S_AXI_DATA_WIDTH must be power of 2");
		if (M_AXI_DATA_WIDTH != (2 ** $clog2(M_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv:147:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "M_AXI_DATA_WIDTH must be power of 2");
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv:149:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
		if (!UPSIZE && !DOWNSIZE)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_wr.sv:151:13 - axi4_dwidth_converter_wr.<unnamed_block>.<unnamed_block>\n msg: ", $time, "Must be either UPSIZE or DOWNSIZE mode");
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
	wire int_b_ready;
	wire [AXI_ID_WIDTH - 1:0] int_bid;
	wire [1:0] int_bresp;
	wire [AXI_USER_WIDTH - 1:0] int_buser;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AW),
		.DATA_WIDTH(AW_WIDTH)
	) aw_skid(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
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
		.axi_aresetn(aresetn),
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
		.axi_aresetn(aresetn),
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
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_aw_downsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			assign m_axi_awid = int_awid;
			assign m_axi_awaddr = int_awaddr;
			assign m_axi_awlen = ((int_awlen + 8'd1) * sv2v_cast_8_signed(WIDTH_RATIO)) - 8'd1;
			assign m_axi_awsize = MASTER_SIZE[2:0];
			assign m_axi_awburst = int_awburst;
			assign m_axi_awlock = int_awlock;
			assign m_axi_awcache = int_awcache;
			assign m_axi_awprot = int_awprot;
			assign m_axi_awqos = int_awqos;
			assign m_axi_awregion = int_awregion;
			assign m_axi_awuser = int_awuser;
			assign m_axi_awvalid = int_aw_valid;
			assign int_aw_ready = m_axi_awready;
		end
		else begin : gen_aw_upsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			assign m_axi_awid = int_awid;
			assign m_axi_awaddr = int_awaddr;
			assign m_axi_awlen = ((int_awlen + sv2v_cast_8_signed(WIDTH_RATIO)) / sv2v_cast_8_signed(WIDTH_RATIO)) - 8'd1;
			assign m_axi_awsize = MASTER_SIZE[2:0];
			assign m_axi_awburst = int_awburst;
			assign m_axi_awlock = int_awlock;
			assign m_axi_awcache = int_awcache;
			assign m_axi_awprot = int_awprot;
			assign m_axi_awqos = int_awqos;
			assign m_axi_awregion = int_awregion;
			assign m_axi_awuser = int_awuser;
			assign m_axi_awvalid = int_aw_valid;
			assign int_aw_ready = m_axi_awready;
		end
	endgenerate
	function automatic signed [PTR_WIDTH - 1:0] sv2v_cast_62A53_signed;
		input reg signed [PTR_WIDTH - 1:0] inp;
		sv2v_cast_62A53_signed = inp;
	endfunction
	function automatic signed [((PTR_WIDTH + 0) >= 0 ? PTR_WIDTH + 1 : 1 - (PTR_WIDTH + 0)) - 1:0] sv2v_cast_56CB7_signed;
		input reg signed [((PTR_WIDTH + 0) >= 0 ? PTR_WIDTH + 1 : 1 - (PTR_WIDTH + 0)) - 1:0] inp;
		sv2v_cast_56CB7_signed = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_w_downsize
			reg [S_AXI_DATA_WIDTH - 1:0] r_wdata_buffer;
			reg [S_STRB_WIDTH - 1:0] r_wstrb_buffer;
			reg [AXI_USER_WIDTH - 1:0] r_wuser_buffer;
			reg r_wlast_buffered;
			reg [PTR_WIDTH:0] r_beat_index;
			always @(posedge aclk)
				if (!aresetn) begin
					r_wdata_buffer <= 1'sb0;
					r_wstrb_buffer <= 1'sb0;
					r_wuser_buffer <= 1'sb0;
					r_wlast_buffered <= 1'b0;
					r_beat_index <= sv2v_cast_56CB7_signed(WIDTH_RATIO);
				end
				else begin : sv2v_autoblock_1
					reg accepting_wide_beat;
					reg sending_narrow_beat;
					accepting_wide_beat = int_w_valid && int_w_ready;
					sending_narrow_beat = m_axi_wvalid && m_axi_wready;
					if (accepting_wide_beat) begin
						r_wdata_buffer <= int_wdata;
						r_wstrb_buffer <= int_wstrb;
						r_wuser_buffer <= int_wuser;
						r_wlast_buffered <= int_wlast;
						r_beat_index <= 1'sb0;
					end
					else if (sending_narrow_beat)
						r_beat_index <= r_beat_index + 1'b1;
				end
			wire buffer_valid = r_beat_index < sv2v_cast_56CB7_signed(WIDTH_RATIO);
			wire last_beat = r_beat_index == sv2v_cast_56CB7_signed(WIDTH_RATIO - 1);
			assign int_w_ready = !buffer_valid || (m_axi_wready && last_beat);
			assign m_axi_wvalid = buffer_valid;
			assign m_axi_wdata = r_wdata_buffer[r_beat_index[PTR_WIDTH - 1:0] * M_AXI_DATA_WIDTH+:M_AXI_DATA_WIDTH];
			assign m_axi_wstrb = r_wstrb_buffer[r_beat_index[PTR_WIDTH - 1:0] * M_STRB_WIDTH+:M_STRB_WIDTH];
			assign m_axi_wlast = r_wlast_buffered && last_beat;
			assign m_axi_wuser = r_wuser_buffer;
		end
		else begin : gen_w_upsize
			reg [M_AXI_DATA_WIDTH - 1:0] r_wdata_buffer;
			reg [M_STRB_WIDTH - 1:0] r_wstrb_buffer;
			reg [AXI_USER_WIDTH - 1:0] r_wuser_buffer;
			reg [PTR_WIDTH - 1:0] r_write_beat_ptr;
			reg r_wlast_buffered;
			reg r_buffer_full;
			always @(posedge aclk)
				if (!aresetn) begin
					r_wdata_buffer <= 1'sb0;
					r_wstrb_buffer <= 1'sb0;
					r_wuser_buffer <= 1'sb0;
					r_write_beat_ptr <= 1'sb0;
					r_wlast_buffered <= 1'b0;
					r_buffer_full <= 1'b0;
				end
				else begin : sv2v_autoblock_2
					reg accepting_new_beat;
					reg sending_master_beat;
					reg buffer_completing;
					accepting_new_beat = int_w_valid && int_w_ready;
					sending_master_beat = m_axi_wvalid && m_axi_wready;
					buffer_completing = accepting_new_beat && ((r_write_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) || int_wlast);
					if (accepting_new_beat) begin
						r_wdata_buffer[r_write_beat_ptr * S_AXI_DATA_WIDTH+:S_AXI_DATA_WIDTH] <= int_wdata;
						r_wstrb_buffer[r_write_beat_ptr * S_STRB_WIDTH+:S_STRB_WIDTH] <= int_wstrb;
						r_wuser_buffer <= int_wuser;
						r_wlast_buffered <= int_wlast;
						if ((r_write_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) || int_wlast) begin
							r_write_beat_ptr <= 1'sb0;
							r_buffer_full <= 1'b1;
						end
						else begin
							r_write_beat_ptr <= r_write_beat_ptr + 1'b1;
							if (sending_master_beat)
								r_buffer_full <= 1'b0;
						end
					end
					else if (sending_master_beat && !buffer_completing)
						r_buffer_full <= 1'b0;
				end
			assign int_w_ready = !r_buffer_full || (m_axi_wvalid && m_axi_wready);
			assign m_axi_wvalid = r_buffer_full;
			assign m_axi_wdata = r_wdata_buffer;
			assign m_axi_wstrb = r_wstrb_buffer;
			assign m_axi_wuser = r_wuser_buffer;
			assign m_axi_wlast = r_wlast_buffered;
		end
	endgenerate
	assign int_bid = m_axi_bid;
	assign int_bresp = m_axi_bresp;
	assign int_buser = m_axi_buser;
	assign int_b_valid = m_axi_bvalid;
	assign m_axi_bready = int_b_ready;
endmodule
