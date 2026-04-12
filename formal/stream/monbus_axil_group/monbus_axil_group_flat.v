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
module axil4_slave_rd (
	aclk,
	aresetn,
	s_axil_araddr,
	s_axil_arprot,
	s_axil_arvalid,
	s_axil_arready,
	s_axil_rdata,
	s_axil_rresp,
	s_axil_rvalid,
	s_axil_rready,
	fub_araddr,
	fub_arprot,
	fub_arvalid,
	fub_arready,
	fub_rdata,
	fub_rresp,
	fub_rvalid,
	fub_rready,
	busy
);
	parameter signed [31:0] AXIL_ADDR_WIDTH = 32;
	parameter signed [31:0] AXIL_DATA_WIDTH = 32;
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] AW = AXIL_ADDR_WIDTH;
	parameter signed [31:0] DW = AXIL_DATA_WIDTH;
	parameter signed [31:0] ARSize = AW + 3;
	parameter signed [31:0] RSize = DW + 2;
	input wire aclk;
	input wire aresetn;
	input wire [AW - 1:0] s_axil_araddr;
	input wire [2:0] s_axil_arprot;
	input wire s_axil_arvalid;
	output wire s_axil_arready;
	output wire [DW - 1:0] s_axil_rdata;
	output wire [1:0] s_axil_rresp;
	output wire s_axil_rvalid;
	input wire s_axil_rready;
	output wire [AW - 1:0] fub_araddr;
	output wire [2:0] fub_arprot;
	output wire fub_arvalid;
	input wire fub_arready;
	input wire [DW - 1:0] fub_rdata;
	input wire [1:0] fub_rresp;
	input wire fub_rvalid;
	output wire fub_rready;
	output wire busy;
	wire [3:0] int_ar_count;
	wire [ARSize - 1:0] int_ar_pkt;
	wire int_skid_arvalid;
	wire int_skid_arready;
	wire [3:0] int_r_count;
	wire [RSize - 1:0] int_r_pkt;
	wire int_skid_rvalid;
	wire int_skid_rready;
	assign busy = (((int_ar_count > 0) || (int_r_count > 0)) || s_axil_arvalid) || fub_rvalid;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AR),
		.DATA_WIDTH(ARSize)
	) i_ar_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axil_arvalid),
		.wr_ready(s_axil_arready),
		.wr_data({s_axil_araddr, s_axil_arprot}),
		.rd_valid(int_skid_arvalid),
		.rd_ready(int_skid_arready),
		.rd_count(int_ar_count),
		.rd_data(int_ar_pkt),
		.count()
	);
	assign {fub_araddr, fub_arprot} = int_ar_pkt;
	assign fub_arvalid = int_skid_arvalid;
	assign int_skid_arready = fub_arready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_R),
		.DATA_WIDTH(RSize)
	) i_r_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_rvalid),
		.wr_ready(fub_rready),
		.wr_data({fub_rdata, fub_rresp}),
		.rd_valid(int_skid_rvalid),
		.rd_ready(int_skid_rready),
		.rd_count(int_r_count),
		.rd_data({s_axil_rdata, s_axil_rresp}),
		.count()
	);
	assign s_axil_rvalid = int_skid_rvalid;
	assign int_skid_rready = s_axil_rready;
endmodule
module axil4_master_wr (
	aclk,
	aresetn,
	fub_awaddr,
	fub_awprot,
	fub_awvalid,
	fub_awready,
	fub_wdata,
	fub_wstrb,
	fub_wvalid,
	fub_wready,
	fub_bresp,
	fub_bvalid,
	fub_bready,
	m_axil_awaddr,
	m_axil_awprot,
	m_axil_awvalid,
	m_axil_awready,
	m_axil_wdata,
	m_axil_wstrb,
	m_axil_wvalid,
	m_axil_wready,
	m_axil_bresp,
	m_axil_bvalid,
	m_axil_bready,
	busy
);
	parameter signed [31:0] AXIL_ADDR_WIDTH = 32;
	parameter signed [31:0] AXIL_DATA_WIDTH = 32;
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 2;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	parameter signed [31:0] AW = AXIL_ADDR_WIDTH;
	parameter signed [31:0] DW = AXIL_DATA_WIDTH;
	parameter signed [31:0] AWSize = AW + 3;
	parameter signed [31:0] WSize = DW + (DW / 8);
	parameter signed [31:0] BSize = 2;
	input wire aclk;
	input wire aresetn;
	input wire [AW - 1:0] fub_awaddr;
	input wire [2:0] fub_awprot;
	input wire fub_awvalid;
	output wire fub_awready;
	input wire [DW - 1:0] fub_wdata;
	input wire [(DW / 8) - 1:0] fub_wstrb;
	input wire fub_wvalid;
	output wire fub_wready;
	output wire [1:0] fub_bresp;
	output wire fub_bvalid;
	input wire fub_bready;
	output wire [AW - 1:0] m_axil_awaddr;
	output wire [2:0] m_axil_awprot;
	output wire m_axil_awvalid;
	input wire m_axil_awready;
	output wire [DW - 1:0] m_axil_wdata;
	output wire [(DW / 8) - 1:0] m_axil_wstrb;
	output wire m_axil_wvalid;
	input wire m_axil_wready;
	input wire [1:0] m_axil_bresp;
	input wire m_axil_bvalid;
	output wire m_axil_bready;
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
	assign busy = (((((int_aw_count > 0) || (int_w_count > 0)) || (int_b_count > 0)) || fub_awvalid) || fub_wvalid) || m_axil_bvalid;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AW),
		.DATA_WIDTH(AWSize)
	) aw_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_awvalid),
		.wr_ready(fub_awready),
		.wr_data({fub_awaddr, fub_awprot}),
		.rd_valid(int_skid_awvalid),
		.rd_ready(int_skid_awready),
		.rd_count(int_aw_count),
		.rd_data(int_aw_pkt),
		.count()
	);
	assign {m_axil_awaddr, m_axil_awprot} = int_aw_pkt;
	assign m_axil_awvalid = int_skid_awvalid;
	assign int_skid_awready = m_axil_awready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_W),
		.DATA_WIDTH(WSize)
	) w_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_wvalid),
		.wr_ready(fub_wready),
		.wr_data({fub_wdata, fub_wstrb}),
		.rd_valid(int_skid_wvalid),
		.rd_ready(int_skid_wready),
		.rd_count(int_w_count),
		.rd_data(int_w_pkt),
		.count()
	);
	assign {m_axil_wdata, m_axil_wstrb} = int_w_pkt;
	assign m_axil_wvalid = int_skid_wvalid;
	assign int_skid_wready = m_axil_wready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_B),
		.DATA_WIDTH(BSize)
	) b_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(m_axil_bvalid),
		.wr_ready(m_axil_bready),
		.wr_data(m_axil_bresp),
		.rd_valid(int_skid_bvalid),
		.rd_ready(int_skid_bready),
		.rd_count(int_b_count),
		.rd_data(fub_bresp),
		.count()
	);
	assign fub_bvalid = int_skid_bvalid;
	assign int_skid_bready = fub_bready;
endmodule
module monbus_axil_group (
	axi_aclk,
	axi_aresetn,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	s_axil_arvalid,
	s_axil_arready,
	s_axil_araddr,
	s_axil_arprot,
	s_axil_rvalid,
	s_axil_rready,
	s_axil_rdata,
	s_axil_rresp,
	m_axil_awvalid,
	m_axil_awready,
	m_axil_awaddr,
	m_axil_awprot,
	m_axil_wvalid,
	m_axil_wready,
	m_axil_wdata,
	m_axil_wstrb,
	m_axil_bvalid,
	m_axil_bready,
	m_axil_bresp,
	irq_out,
	cfg_base_addr,
	cfg_limit_addr,
	cfg_axi_pkt_mask,
	cfg_axi_err_select,
	cfg_axi_error_mask,
	cfg_axi_timeout_mask,
	cfg_axi_compl_mask,
	cfg_axi_thresh_mask,
	cfg_axi_perf_mask,
	cfg_axi_addr_mask,
	cfg_axi_debug_mask,
	cfg_axis_pkt_mask,
	cfg_axis_err_select,
	cfg_axis_error_mask,
	cfg_axis_timeout_mask,
	cfg_axis_compl_mask,
	cfg_axis_credit_mask,
	cfg_axis_channel_mask,
	cfg_axis_stream_mask,
	cfg_core_pkt_mask,
	cfg_core_err_select,
	cfg_core_error_mask,
	cfg_core_timeout_mask,
	cfg_core_compl_mask,
	cfg_core_thresh_mask,
	cfg_core_perf_mask,
	cfg_core_debug_mask,
	err_fifo_full,
	write_fifo_full,
	err_fifo_count,
	write_fifo_count
);
	reg _sv2v_0;
	parameter signed [31:0] FIFO_DEPTH_ERR = 64;
	parameter signed [31:0] FIFO_DEPTH_WRITE = 32;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] NUM_PROTOCOLS = 3;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire monbus_valid;
	output wire monbus_ready;
	input wire [63:0] monbus_packet;
	input wire s_axil_arvalid;
	output wire s_axil_arready;
	input wire [ADDR_WIDTH - 1:0] s_axil_araddr;
	input wire [2:0] s_axil_arprot;
	output wire s_axil_rvalid;
	input wire s_axil_rready;
	output wire [DATA_WIDTH - 1:0] s_axil_rdata;
	output wire [1:0] s_axil_rresp;
	output wire m_axil_awvalid;
	input wire m_axil_awready;
	output wire [ADDR_WIDTH - 1:0] m_axil_awaddr;
	output wire [2:0] m_axil_awprot;
	output wire m_axil_wvalid;
	input wire m_axil_wready;
	output wire [DATA_WIDTH - 1:0] m_axil_wdata;
	output wire [(DATA_WIDTH / 8) - 1:0] m_axil_wstrb;
	input wire m_axil_bvalid;
	output wire m_axil_bready;
	input wire [1:0] m_axil_bresp;
	output wire irq_out;
	input wire [ADDR_WIDTH - 1:0] cfg_base_addr;
	input wire [ADDR_WIDTH - 1:0] cfg_limit_addr;
	input wire [15:0] cfg_axi_pkt_mask;
	input wire [15:0] cfg_axi_err_select;
	input wire [15:0] cfg_axi_error_mask;
	input wire [15:0] cfg_axi_timeout_mask;
	input wire [15:0] cfg_axi_compl_mask;
	input wire [15:0] cfg_axi_thresh_mask;
	input wire [15:0] cfg_axi_perf_mask;
	input wire [15:0] cfg_axi_addr_mask;
	input wire [15:0] cfg_axi_debug_mask;
	input wire [15:0] cfg_axis_pkt_mask;
	input wire [15:0] cfg_axis_err_select;
	input wire [15:0] cfg_axis_error_mask;
	input wire [15:0] cfg_axis_timeout_mask;
	input wire [15:0] cfg_axis_compl_mask;
	input wire [15:0] cfg_axis_credit_mask;
	input wire [15:0] cfg_axis_channel_mask;
	input wire [15:0] cfg_axis_stream_mask;
	input wire [15:0] cfg_core_pkt_mask;
	input wire [15:0] cfg_core_err_select;
	input wire [15:0] cfg_core_error_mask;
	input wire [15:0] cfg_core_timeout_mask;
	input wire [15:0] cfg_core_compl_mask;
	input wire [15:0] cfg_core_thresh_mask;
	input wire [15:0] cfg_core_perf_mask;
	input wire [15:0] cfg_core_debug_mask;
	output wire err_fifo_full;
	output wire write_fifo_full;
	output wire [7:0] err_fifo_count;
	output wire [7:0] write_fifo_count;
	localparam signed [31:0] ERR_FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH_ERR);
	localparam signed [31:0] WRITE_FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH_WRITE);
	wire input_monbus_valid;
	wire input_monbus_ready;
	wire [63:0] input_monbus_packet;
	wire [3:0] pkt_type;
	wire [2:0] pkt_protocol;
	wire [3:0] pkt_event_code;
	wire [35:0] pkt_event_data;
	reg pkt_drop;
	reg pkt_to_err_fifo;
	reg pkt_to_write_fifo;
	reg pkt_event_masked;
	wire err_fifo_wr_valid;
	wire err_fifo_wr_ready;
	wire [63:0] err_fifo_wr_data;
	wire err_fifo_rd_valid;
	wire err_fifo_rd_ready;
	wire [63:0] err_fifo_rd_data;
	wire err_fifo_empty;
	wire [ERR_FIFO_ADDR_WIDTH:0] err_fifo_count_full;
	wire write_fifo_wr_valid;
	wire write_fifo_wr_ready;
	wire [63:0] write_fifo_wr_data;
	wire write_fifo_rd_valid;
	wire write_fifo_rd_ready;
	wire [63:0] write_fifo_rd_data;
	wire write_fifo_empty;
	wire [WRITE_FIFO_ADDR_WIDTH:0] write_fifo_count_full;
	wire [ADDR_WIDTH - 1:0] fub_rd_araddr;
	wire [2:0] fub_rd_arprot;
	wire fub_rd_arvalid;
	wire fub_rd_arready;
	reg [DATA_WIDTH - 1:0] fub_rd_rdata;
	wire [1:0] fub_rd_rresp;
	wire fub_rd_rvalid;
	wire fub_rd_rready;
	wire [ADDR_WIDTH - 1:0] fub_wr_awaddr;
	wire [2:0] fub_wr_awprot;
	wire fub_wr_awvalid;
	wire fub_wr_awready;
	reg [DATA_WIDTH - 1:0] fub_wr_wdata;
	wire [(DATA_WIDTH / 8) - 1:0] fub_wr_wstrb;
	wire fub_wr_wvalid;
	wire fub_wr_wready;
	wire [1:0] fub_wr_bresp;
	wire fub_wr_bvalid;
	wire fub_wr_bready;
	reg [ADDR_WIDTH - 1:0] current_write_addr;
	reg [ADDR_WIDTH - 1:0] next_write_addr;
	wire addr_counter_enable;
	assign input_monbus_valid = monbus_valid;
	assign monbus_ready = input_monbus_ready;
	assign input_monbus_packet = monbus_packet;
	function automatic [3:0] monitor_common_pkg_get_packet_type;
		input reg [63:0] pkt;
		monitor_common_pkg_get_packet_type = pkt[63:60];
	endfunction
	assign pkt_type = monitor_common_pkg_get_packet_type(input_monbus_packet);
	assign pkt_protocol = input_monbus_packet[59:57];
	function automatic [3:0] monitor_common_pkg_get_event_code;
		input reg [63:0] pkt;
		monitor_common_pkg_get_event_code = pkt[56:53];
	endfunction
	assign pkt_event_code = monitor_common_pkg_get_event_code(input_monbus_packet);
	function automatic [34:0] monitor_common_pkg_get_event_data;
		input reg [63:0] pkt;
		monitor_common_pkg_get_event_data = pkt[34:0];
	endfunction
	assign pkt_event_data = monitor_common_pkg_get_event_data(input_monbus_packet);
	localparam [3:0] monitor_common_pkg_PktTypeAddrMatch = 4'h8;
	localparam [3:0] monitor_common_pkg_PktTypeChannel = 4'h6;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeCredit = 4'h5;
	localparam [3:0] monitor_common_pkg_PktTypeDebug = 4'hf;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeStream = 4'h7;
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	always @(*) begin
		if (_sv2v_0)
			;
		pkt_drop = 1'b0;
		pkt_to_err_fifo = 1'b0;
		pkt_to_write_fifo = 1'b0;
		pkt_event_masked = 1'b0;
		if (({29'b00000000000000000000000000000, pkt_protocol} < NUM_PROTOCOLS) && input_monbus_valid) begin
			case (pkt_protocol)
				3'b000: begin
					pkt_drop = cfg_axi_pkt_mask[pkt_type];
					pkt_to_err_fifo = cfg_axi_err_select[pkt_type] && !pkt_drop;
					case (pkt_type)
						monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_axi_error_mask[pkt_event_code];
						monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_axi_timeout_mask[pkt_event_code];
						monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask[pkt_event_code];
						monitor_common_pkg_PktTypeThreshold: pkt_event_masked = cfg_axi_thresh_mask[pkt_event_code];
						monitor_common_pkg_PktTypePerf: pkt_event_masked = cfg_axi_perf_mask[pkt_event_code];
						monitor_common_pkg_PktTypeAddrMatch: pkt_event_masked = cfg_axi_addr_mask[pkt_event_code];
						monitor_common_pkg_PktTypeDebug: pkt_event_masked = cfg_axi_debug_mask[pkt_event_code];
						default: pkt_event_masked = 1'b0;
					endcase
				end
				3'b001: begin
					pkt_drop = cfg_axis_pkt_mask[pkt_type];
					pkt_to_err_fifo = cfg_axis_err_select[pkt_type] && !pkt_drop;
					case (pkt_type)
						monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_axis_error_mask[pkt_event_code];
						monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_axis_timeout_mask[pkt_event_code];
						monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_axis_compl_mask[pkt_event_code];
						monitor_common_pkg_PktTypeCredit: pkt_event_masked = cfg_axis_credit_mask[pkt_event_code];
						monitor_common_pkg_PktTypeChannel: pkt_event_masked = cfg_axis_channel_mask[pkt_event_code];
						monitor_common_pkg_PktTypeStream: pkt_event_masked = cfg_axis_stream_mask[pkt_event_code];
						default: pkt_event_masked = 1'b0;
					endcase
				end
				3'b010: begin
					pkt_drop = cfg_core_pkt_mask[pkt_type];
					pkt_to_err_fifo = cfg_core_err_select[pkt_type] && !pkt_drop;
					case (pkt_type)
						monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_core_error_mask[pkt_event_code];
						monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_core_timeout_mask[pkt_event_code];
						monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_core_compl_mask[pkt_event_code];
						monitor_common_pkg_PktTypeThreshold: pkt_event_masked = cfg_core_thresh_mask[pkt_event_code];
						monitor_common_pkg_PktTypePerf: pkt_event_masked = cfg_core_perf_mask[pkt_event_code];
						monitor_common_pkg_PktTypeDebug: pkt_event_masked = cfg_core_debug_mask[pkt_event_code];
						default: pkt_event_masked = 1'b0;
					endcase
				end
				default: pkt_drop = 1'b1;
			endcase
			if (pkt_event_masked) begin
				pkt_drop = 1'b1;
				pkt_to_err_fifo = 1'b0;
			end
			pkt_to_write_fifo = !pkt_drop && !pkt_to_err_fifo;
		end
	end
	assign input_monbus_ready = (pkt_drop || (pkt_to_err_fifo && err_fifo_wr_ready)) || (pkt_to_write_fifo && write_fifo_wr_ready);
	assign err_fifo_wr_valid = (input_monbus_valid && pkt_to_err_fifo) && !pkt_drop;
	assign err_fifo_wr_data = input_monbus_packet;
	gaxi_fifo_sync #(
		.REGISTERED(0),
		.DATA_WIDTH(64),
		.DEPTH(FIFO_DEPTH_ERR)
	) u_err_fifo(
		.axi_aclk(axi_aclk),
		.axi_aresetn(axi_aresetn),
		.wr_valid(err_fifo_wr_valid),
		.wr_ready(err_fifo_wr_ready),
		.wr_data(err_fifo_wr_data),
		.rd_valid(err_fifo_rd_valid),
		.rd_ready(err_fifo_rd_ready),
		.rd_data(err_fifo_rd_data),
		.count(err_fifo_count_full)
	);
	assign err_fifo_empty = !err_fifo_rd_valid;
	assign err_fifo_full = !err_fifo_wr_ready;
	assign irq_out = !err_fifo_empty;
	assign err_fifo_count = {{(8 - ERR_FIFO_ADDR_WIDTH) - 1 {1'b0}}, err_fifo_count_full};
	assign write_fifo_wr_valid = (input_monbus_valid && pkt_to_write_fifo) && !pkt_drop;
	assign write_fifo_wr_data = input_monbus_packet;
	gaxi_fifo_sync #(
		.REGISTERED(0),
		.DATA_WIDTH(64),
		.DEPTH(FIFO_DEPTH_WRITE)
	) u_write_fifo(
		.axi_aclk(axi_aclk),
		.axi_aresetn(axi_aresetn),
		.wr_valid(write_fifo_wr_valid),
		.wr_ready(write_fifo_wr_ready),
		.wr_data(write_fifo_wr_data),
		.rd_valid(write_fifo_rd_valid),
		.rd_ready(write_fifo_rd_ready),
		.rd_data(write_fifo_rd_data),
		.count(write_fifo_count_full)
	);
	assign write_fifo_empty = !write_fifo_rd_valid;
	assign write_fifo_full = !write_fifo_wr_ready;
	assign write_fifo_count = {{(8 - WRITE_FIFO_ADDR_WIDTH) - 1 {1'b0}}, write_fifo_count_full};
	axil4_slave_rd #(
		.AXIL_ADDR_WIDTH(ADDR_WIDTH),
		.AXIL_DATA_WIDTH(DATA_WIDTH),
		.SKID_DEPTH_AR(2),
		.SKID_DEPTH_R(4)
	) u_slave_rd(
		.aclk(axi_aclk),
		.aresetn(axi_aresetn),
		.s_axil_araddr(s_axil_araddr),
		.s_axil_arprot(s_axil_arprot),
		.s_axil_arvalid(s_axil_arvalid),
		.s_axil_arready(s_axil_arready),
		.s_axil_rdata(s_axil_rdata),
		.s_axil_rresp(s_axil_rresp),
		.s_axil_rvalid(s_axil_rvalid),
		.s_axil_rready(s_axil_rready),
		.fub_araddr(fub_rd_araddr),
		.fub_arprot(fub_rd_arprot),
		.fub_arvalid(fub_rd_arvalid),
		.fub_arready(fub_rd_arready),
		.fub_rdata(fub_rd_rdata),
		.fub_rresp(fub_rd_rresp),
		.fub_rvalid(fub_rd_rvalid),
		.fub_rready(fub_rd_rready),
		.busy()
	);
	assign fub_rd_arready = !err_fifo_empty;
	assign fub_rd_rvalid = fub_rd_arvalid && fub_rd_arready;
	assign err_fifo_rd_ready = fub_rd_rvalid && fub_rd_rready;
	always @(*) begin
		if (_sv2v_0)
			;
		fub_rd_rdata = {DATA_WIDTH {1'b0}};
		if (!err_fifo_empty) begin
			if (DATA_WIDTH == 64)
				fub_rd_rdata = err_fifo_rd_data[DATA_WIDTH - 1:0];
			else
				fub_rd_rdata = (fub_rd_araddr[2] ? err_fifo_rd_data[63:32] : err_fifo_rd_data[31:0]);
		end
	end
	assign fub_rd_rresp = 2'b00;
	always @(*) begin
		if (_sv2v_0)
			;
		if (DATA_WIDTH == 64)
			next_write_addr = current_write_addr + 8;
		else
			next_write_addr = current_write_addr + 4;
		if (next_write_addr > cfg_limit_addr)
			next_write_addr = cfg_base_addr;
	end
	always @(posedge axi_aclk)
		if (!axi_aresetn)
			current_write_addr <= cfg_base_addr;
		else if (addr_counter_enable)
			current_write_addr <= next_write_addr;
	axil4_master_wr #(
		.AXIL_ADDR_WIDTH(ADDR_WIDTH),
		.AXIL_DATA_WIDTH(DATA_WIDTH),
		.SKID_DEPTH_AW(2),
		.SKID_DEPTH_W(2),
		.SKID_DEPTH_B(2)
	) u_master_wr(
		.aclk(axi_aclk),
		.aresetn(axi_aresetn),
		.fub_awaddr(fub_wr_awaddr),
		.fub_awprot(fub_wr_awprot),
		.fub_awvalid(fub_wr_awvalid),
		.fub_awready(fub_wr_awready),
		.fub_wdata(fub_wr_wdata),
		.fub_wstrb(fub_wr_wstrb),
		.fub_wvalid(fub_wr_wvalid),
		.fub_wready(fub_wr_wready),
		.fub_bresp(fub_wr_bresp),
		.fub_bvalid(fub_wr_bvalid),
		.fub_bready(fub_wr_bready),
		.m_axil_awaddr(m_axil_awaddr),
		.m_axil_awprot(m_axil_awprot),
		.m_axil_awvalid(m_axil_awvalid),
		.m_axil_awready(m_axil_awready),
		.m_axil_wdata(m_axil_wdata),
		.m_axil_wstrb(m_axil_wstrb),
		.m_axil_wvalid(m_axil_wvalid),
		.m_axil_wready(m_axil_wready),
		.m_axil_bresp(m_axil_bresp),
		.m_axil_bvalid(m_axil_bvalid),
		.m_axil_bready(m_axil_bready),
		.busy()
	);
	reg [2:0] write_state;
	reg [63:0] current_packet;
	reg upper_word_pending;
	always @(posedge axi_aclk)
		if (!axi_aresetn) begin
			write_state <= 3'b000;
			current_packet <= 1'sb0;
			upper_word_pending <= 1'b0;
		end
		else
			case (write_state)
				3'b000:
					if (write_fifo_rd_valid) begin
						current_packet <= write_fifo_rd_data;
						write_state <= 3'b001;
						upper_word_pending <= DATA_WIDTH == 32;
					end
				3'b001:
					if (fub_wr_awvalid && fub_wr_awready)
						write_state <= 3'b010;
				3'b010:
					if (fub_wr_wvalid && fub_wr_wready)
						write_state <= 3'b100;
				3'b100:
					if (fub_wr_bvalid && fub_wr_bready) begin
						if (upper_word_pending && (DATA_WIDTH == 32)) begin
							write_state <= 3'b001;
							upper_word_pending <= 1'b0;
						end
						else
							write_state <= 3'b000;
					end
				default: write_state <= 3'b000;
			endcase
	assign fub_wr_awvalid = write_state == 3'b001;
	assign fub_wr_awaddr = current_write_addr;
	assign fub_wr_awprot = 3'b000;
	assign fub_wr_wvalid = write_state == 3'b010;
	always @(*) begin
		if (_sv2v_0)
			;
		if (DATA_WIDTH == 64)
			fub_wr_wdata = current_packet[DATA_WIDTH - 1:0];
		else
			fub_wr_wdata = (upper_word_pending ? current_packet[31:0] : current_packet[63:32]);
	end
	assign fub_wr_wstrb = {DATA_WIDTH / 8 {1'b1}};
	assign fub_wr_bready = write_state == 3'b100;
	assign write_fifo_rd_ready = (write_state == 3'b000) && write_fifo_rd_valid;
	assign addr_counter_enable = (((write_state == 3'b100) && fub_wr_bvalid) && fub_wr_bready) && (!upper_word_pending || (DATA_WIDTH == 64));
	initial _sv2v_0 = 0;
endmodule
