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
	localparam signed [31:0] PTR_WIDTH = $clog2(WIDTH_RATIO);
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
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv:130:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "S_AXI_DATA_WIDTH must be power of 2");
		if (M_AXI_DATA_WIDTH != (2 ** $clog2(M_AXI_DATA_WIDTH)))
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv:132:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "M_AXI_DATA_WIDTH must be power of 2");
		if (WIDTH_RATIO < 2)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv:134:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "WIDTH_RATIO must be >= 2");
		if (!UPSIZE && !DOWNSIZE)
			$display("Error [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv:136:13 - axi4_dwidth_converter_rd.<unnamed_block>.<unnamed_block>\n msg: ", $time, "Must be either UPSIZE or DOWNSIZE mode");
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
	wire [AXI_USER_WIDTH - 1:0] int_ruser;
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
	function automatic signed [7:0] sv2v_cast_8_signed;
		input reg signed [7:0] inp;
		sv2v_cast_8_signed = inp;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_ar_downsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			assign m_axi_arid = int_arid;
			assign m_axi_araddr = int_araddr;
			assign m_axi_arlen = ((int_arlen + 8'd1) * sv2v_cast_8_signed(WIDTH_RATIO)) - 8'd1;
			assign m_axi_arsize = MASTER_SIZE[2:0];
			assign m_axi_arburst = int_arburst;
			assign m_axi_arlock = int_arlock;
			assign m_axi_arcache = int_arcache;
			assign m_axi_arprot = int_arprot;
			assign m_axi_arqos = int_arqos;
			assign m_axi_arregion = int_arregion;
			assign m_axi_aruser = int_aruser;
			assign m_axi_arvalid = int_ar_valid;
			assign int_ar_ready = m_axi_arready;
		end
		else begin : gen_ar_upsize
			localparam signed [31:0] MASTER_SIZE = $clog2(M_STRB_WIDTH);
			localparam signed [31:0] ALIGN_BITS = $clog2(M_STRB_WIDTH);
			wire [7:0] master_arlen;
			wire [AXI_ADDR_WIDTH - 1:0] aligned_araddr;
			assign master_arlen = sv2v_cast_8((int_arlen + sv2v_cast_8_signed(WIDTH_RATIO)) / sv2v_cast_8_signed(WIDTH_RATIO)) - 8'd1;
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
			assign m_axi_arvalid = int_ar_valid;
			assign int_ar_ready = m_axi_arready;
		end
	endgenerate
	function automatic signed [PTR_WIDTH - 1:0] sv2v_cast_62A53_signed;
		input reg signed [PTR_WIDTH - 1:0] inp;
		sv2v_cast_62A53_signed = inp;
	endfunction
	generate
		if (DOWNSIZE) begin : gen_r_downsize
			reg [S_AXI_DATA_WIDTH - 1:0] r_rdata_accumulator;
			reg [PTR_WIDTH - 1:0] r_accum_ptr;
			reg r_wide_beat_valid;
			reg r_rlast_buffered;
			reg [1:0] r_rresp_buffered;
			reg [AXI_ID_WIDTH - 1:0] r_rid_buffered;
			reg [AXI_USER_WIDTH - 1:0] r_ruser_buffered;
			always @(posedge aclk)
				if (!aresetn) begin
					r_rdata_accumulator <= 1'sb0;
					r_accum_ptr <= 1'sb0;
					r_wide_beat_valid <= 1'b0;
					r_rlast_buffered <= 1'b0;
					r_rresp_buffered <= 2'b00;
					r_rid_buffered <= 1'sb0;
					r_ruser_buffered <= 1'sb0;
				end
				else begin
					if (m_axi_rvalid && m_axi_rready) begin
						r_rdata_accumulator[r_accum_ptr * M_AXI_DATA_WIDTH+:M_AXI_DATA_WIDTH] <= m_axi_rdata;
						if (r_accum_ptr == {PTR_WIDTH {1'sb0}}) begin
							r_rid_buffered <= m_axi_rid;
							r_rresp_buffered <= m_axi_rresp;
							r_ruser_buffered <= m_axi_ruser;
						end
						else
							r_rresp_buffered <= r_rresp_buffered | m_axi_rresp;
						if ((r_accum_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) || m_axi_rlast) begin
							r_wide_beat_valid <= 1'b1;
							r_accum_ptr <= 1'sb0;
							r_rlast_buffered <= m_axi_rlast;
						end
						else
							r_accum_ptr <= r_accum_ptr + 1'b1;
					end
					if (r_wide_beat_valid && int_r_ready) begin
						r_wide_beat_valid <= 1'b0;
						r_rlast_buffered <= 1'b0;
					end
				end
			assign int_rdata = r_rdata_accumulator;
			assign int_rid = r_rid_buffered;
			assign int_rresp = r_rresp_buffered;
			assign int_rlast = r_rlast_buffered && r_wide_beat_valid;
			assign int_ruser = r_ruser_buffered;
			assign int_r_valid = r_wide_beat_valid;
			assign m_axi_rready = !r_wide_beat_valid || int_r_ready;
		end
		else begin : gen_r_upsize
			reg [M_AXI_DATA_WIDTH - 1:0] r_rdata_buffer;
			reg [1:0] r_rresp_buffer;
			reg [AXI_USER_WIDTH - 1:0] r_ruser_buffer;
			reg [AXI_ID_WIDTH - 1:0] r_rid_buffer;
			reg [PTR_WIDTH - 1:0] r_beat_ptr;
			reg r_wide_buffered;
			reg r_rlast_buffered;
			reg [7:0] r_slave_beat_count;
			reg [7:0] r_slave_total_beats;
			reg r_burst_active;
			always @(posedge aclk)
				if (!aresetn) begin
					r_rdata_buffer <= 1'sb0;
					r_rresp_buffer <= 1'sb0;
					r_ruser_buffer <= 1'sb0;
					r_rid_buffer <= 1'sb0;
					r_beat_ptr <= 1'sb0;
					r_wide_buffered <= 1'b0;
					r_rlast_buffered <= 1'b0;
					r_slave_beat_count <= 1'sb0;
					r_slave_total_beats <= 1'sb0;
					r_burst_active <= 1'b0;
				end
				else begin
					if ((int_ar_valid && int_ar_ready) && !r_burst_active) begin
						r_slave_total_beats <= int_arlen + 8'd1;
						r_slave_beat_count <= 1'sb0;
						r_burst_active <= 1'b1;
					end
					if ((m_axi_rvalid && m_axi_rready) && !r_wide_buffered) begin
						r_rdata_buffer <= m_axi_rdata;
						r_rresp_buffer <= m_axi_rresp;
						r_ruser_buffer <= m_axi_ruser;
						r_rid_buffer <= m_axi_rid;
						r_rlast_buffered <= m_axi_rlast;
						r_wide_buffered <= 1'b1;
						r_beat_ptr <= 1'sb0;
					end
					if ((r_wide_buffered && int_r_ready) && r_burst_active) begin
						if ((r_slave_beat_count + 8'd1) >= r_slave_total_beats) begin
							r_wide_buffered <= 1'b0;
							r_beat_ptr <= 1'sb0;
							r_slave_beat_count <= 1'sb0;
							r_burst_active <= 1'b0;
						end
						else if (r_beat_ptr == sv2v_cast_62A53_signed(WIDTH_RATIO - 1)) begin
							r_wide_buffered <= 1'b0;
							r_beat_ptr <= 1'sb0;
							r_slave_beat_count <= r_slave_beat_count + 8'd1;
						end
						else begin
							r_beat_ptr <= r_beat_ptr + 1'b1;
							r_slave_beat_count <= r_slave_beat_count + 8'd1;
						end
					end
				end
			wire w_last_slave_beat;
			assign w_last_slave_beat = (r_slave_beat_count + 8'd1) >= r_slave_total_beats;
			assign m_axi_rready = !r_wide_buffered || (int_r_ready && w_last_slave_beat);
			assign int_r_valid = r_wide_buffered && r_burst_active;
			assign int_rdata = r_rdata_buffer[r_beat_ptr * S_AXI_DATA_WIDTH+:S_AXI_DATA_WIDTH];
			assign int_rresp = r_rresp_buffer;
			assign int_ruser = r_ruser_buffer;
			assign int_rid = r_rid_buffer;
			assign int_rlast = r_wide_buffered && w_last_slave_beat;
		end
	endgenerate
endmodule
