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
module axil4_master_rd (
	aclk,
	aresetn,
	fub_araddr,
	fub_arprot,
	fub_arvalid,
	fub_arready,
	fub_rdata,
	fub_rresp,
	fub_rvalid,
	fub_rready,
	m_axil_araddr,
	m_axil_arprot,
	m_axil_arvalid,
	m_axil_arready,
	m_axil_rdata,
	m_axil_rresp,
	m_axil_rvalid,
	m_axil_rready,
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
	input wire [AW - 1:0] fub_araddr;
	input wire [2:0] fub_arprot;
	input wire fub_arvalid;
	output wire fub_arready;
	output wire [DW - 1:0] fub_rdata;
	output wire [1:0] fub_rresp;
	output wire fub_rvalid;
	input wire fub_rready;
	output wire [AW - 1:0] m_axil_araddr;
	output wire [2:0] m_axil_arprot;
	output wire m_axil_arvalid;
	input wire m_axil_arready;
	input wire [DW - 1:0] m_axil_rdata;
	input wire [1:0] m_axil_rresp;
	input wire m_axil_rvalid;
	output wire m_axil_rready;
	output wire busy;
	wire [3:0] int_ar_count;
	wire [ARSize - 1:0] int_ar_pkt;
	wire int_skid_arvalid;
	wire int_skid_arready;
	wire [3:0] int_r_count;
	wire [RSize - 1:0] int_r_pkt;
	wire int_skid_rvalid;
	wire int_skid_rready;
	assign busy = (((int_ar_count > 0) || (int_r_count > 0)) || fub_arvalid) || m_axil_rvalid;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AR),
		.DATA_WIDTH(ARSize)
	) ar_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_arvalid),
		.wr_ready(fub_arready),
		.wr_data({fub_araddr, fub_arprot}),
		.rd_valid(int_skid_arvalid),
		.rd_ready(int_skid_arready),
		.rd_count(int_ar_count),
		.rd_data(int_ar_pkt),
		.count()
	);
	assign {m_axil_araddr, m_axil_arprot} = int_ar_pkt;
	assign m_axil_arvalid = int_skid_arvalid;
	assign int_skid_arready = m_axil_arready;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_R),
		.DATA_WIDTH(RSize)
	) r_channel(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(m_axil_rvalid),
		.wr_ready(m_axil_rready),
		.wr_data({m_axil_rdata, m_axil_rresp}),
		.rd_valid(int_skid_rvalid),
		.rd_ready(int_skid_rready),
		.rd_count(int_r_count),
		.rd_data({fub_rdata, fub_rresp}),
		.count()
	);
	assign fub_rvalid = int_skid_rvalid;
	assign int_skid_rready = fub_rready;
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
module uart_rx (
	i_clk,
	i_rst_n,
	i_rx,
	o_rx_data,
	o_rx_valid,
	i_rx_ready
);
	reg _sv2v_0;
	parameter signed [31:0] CLKS_PER_BIT = 868;
	input wire i_clk;
	input wire i_rst_n;
	input wire i_rx;
	output wire [7:0] o_rx_data;
	output wire o_rx_valid;
	input wire i_rx_ready;
	localparam signed [31:0] COUNT_WIDTH = $clog2(CLKS_PER_BIT);
	reg [2:0] r_state;
	reg [2:0] w_next_state;
	reg [COUNT_WIDTH - 1:0] r_clk_count;
	reg [COUNT_WIDTH - 1:0] w_clk_count_next;
	reg [2:0] r_bit_index;
	reg [2:0] w_bit_index_next;
	reg [7:0] r_rx_data_reg;
	reg [7:0] w_rx_data_next;
	reg r_rx_valid_reg;
	reg r_rx_sync1;
	reg r_rx_sync2;
	always @(posedge i_clk)
		if (!i_rst_n) begin
			r_rx_sync1 <= 1'b1;
			r_rx_sync2 <= 1'b1;
		end
		else begin
			r_rx_sync1 <= i_rx;
			r_rx_sync2 <= r_rx_sync1;
		end
	always @(posedge i_clk)
		if (!i_rst_n) begin
			r_state <= 3'd0;
			r_clk_count <= 1'sb0;
			r_bit_index <= 1'sb0;
			r_rx_data_reg <= 1'sb0;
			r_rx_valid_reg <= 1'b0;
		end
		else begin
			r_state <= w_next_state;
			r_clk_count <= w_clk_count_next;
			r_bit_index <= w_bit_index_next;
			r_rx_data_reg <= w_rx_data_next;
			r_rx_valid_reg <= w_next_state == 3'd4;
		end
	function automatic signed [COUNT_WIDTH - 1:0] sv2v_cast_C1BE4_signed;
		input reg signed [COUNT_WIDTH - 1:0] inp;
		sv2v_cast_C1BE4_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_state;
		w_clk_count_next = r_clk_count;
		w_bit_index_next = r_bit_index;
		w_rx_data_next = r_rx_data_reg;
		case (r_state)
			3'd0: begin
				w_clk_count_next = 1'sb0;
				w_bit_index_next = 1'sb0;
				if (r_rx_sync2 == 1'b0)
					w_next_state = 3'd1;
			end
			3'd1:
				if (r_clk_count == sv2v_cast_C1BE4_signed((CLKS_PER_BIT - 1) / 2)) begin
					if (r_rx_sync2 == 1'b0) begin
						w_clk_count_next = 1'sb0;
						w_next_state = 3'd2;
					end
					else
						w_next_state = 3'd0;
				end
				else
					w_clk_count_next = r_clk_count + 1'b1;
			3'd2:
				if (r_clk_count == sv2v_cast_C1BE4_signed(CLKS_PER_BIT - 1)) begin
					w_clk_count_next = 1'sb0;
					w_rx_data_next[r_bit_index] = r_rx_sync2;
					if (r_bit_index == 3'd7)
						w_next_state = 3'd3;
					else
						w_bit_index_next = r_bit_index + 1'b1;
				end
				else
					w_clk_count_next = r_clk_count + 1'b1;
			3'd3:
				if (r_clk_count == sv2v_cast_C1BE4_signed(CLKS_PER_BIT - 1)) begin
					w_clk_count_next = 1'sb0;
					w_next_state = 3'd4;
				end
				else
					w_clk_count_next = r_clk_count + 1'b1;
			3'd4:
				if (i_rx_ready)
					w_next_state = 3'd0;
			default: w_next_state = 3'd0;
		endcase
	end
	assign o_rx_data = r_rx_data_reg;
	assign o_rx_valid = r_rx_valid_reg;
	initial _sv2v_0 = 0;
endmodule
module uart_tx (
	i_clk,
	i_rst_n,
	o_tx,
	i_tx_data,
	i_tx_valid,
	o_tx_ready
);
	reg _sv2v_0;
	parameter signed [31:0] CLKS_PER_BIT = 868;
	input wire i_clk;
	input wire i_rst_n;
	output wire o_tx;
	input wire [7:0] i_tx_data;
	input wire i_tx_valid;
	output wire o_tx_ready;
	localparam signed [31:0] COUNT_WIDTH = $clog2(CLKS_PER_BIT);
	reg [2:0] r_state;
	reg [2:0] w_next_state;
	reg [COUNT_WIDTH - 1:0] r_clk_count;
	reg [COUNT_WIDTH - 1:0] w_clk_count_next;
	reg [2:0] r_bit_index;
	reg [2:0] w_bit_index_next;
	reg [7:0] r_tx_data_reg;
	reg [7:0] w_tx_data_next;
	reg r_tx_reg;
	always @(posedge i_clk)
		if (!i_rst_n) begin
			r_state <= 3'd0;
			r_clk_count <= 1'sb0;
			r_bit_index <= 1'sb0;
			r_tx_data_reg <= 1'sb0;
			r_tx_reg <= 1'b1;
		end
		else begin
			r_state <= w_next_state;
			r_clk_count <= w_clk_count_next;
			r_bit_index <= w_bit_index_next;
			r_tx_data_reg <= w_tx_data_next;
			case (w_next_state)
				3'd0: r_tx_reg <= 1'b1;
				3'd1: r_tx_reg <= 1'b0;
				3'd2: r_tx_reg <= r_tx_data_reg[r_bit_index];
				3'd3: r_tx_reg <= 1'b1;
				default: r_tx_reg <= 1'b1;
			endcase
		end
	function automatic signed [COUNT_WIDTH - 1:0] sv2v_cast_C1BE4_signed;
		input reg signed [COUNT_WIDTH - 1:0] inp;
		sv2v_cast_C1BE4_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_state;
		w_clk_count_next = r_clk_count;
		w_bit_index_next = r_bit_index;
		w_tx_data_next = r_tx_data_reg;
		case (r_state)
			3'd0: begin
				w_clk_count_next = 1'sb0;
				w_bit_index_next = 1'sb0;
				if (i_tx_valid) begin
					w_tx_data_next = i_tx_data;
					w_next_state = 3'd1;
				end
			end
			3'd1:
				if (r_clk_count == sv2v_cast_C1BE4_signed(CLKS_PER_BIT - 1)) begin
					w_clk_count_next = 1'sb0;
					w_next_state = 3'd2;
				end
				else
					w_clk_count_next = r_clk_count + 1'b1;
			3'd2:
				if (r_clk_count == sv2v_cast_C1BE4_signed(CLKS_PER_BIT - 1)) begin
					w_clk_count_next = 1'sb0;
					if (r_bit_index == 3'd7)
						w_next_state = 3'd3;
					else
						w_bit_index_next = r_bit_index + 1'b1;
				end
				else
					w_clk_count_next = r_clk_count + 1'b1;
			3'd3:
				if (r_clk_count == sv2v_cast_C1BE4_signed(CLKS_PER_BIT - 1)) begin
					w_clk_count_next = 1'sb0;
					w_next_state = 3'd0;
				end
				else
					w_clk_count_next = r_clk_count + 1'b1;
			default: w_next_state = 3'd0;
		endcase
	end
	assign o_tx = r_tx_reg;
	assign o_tx_ready = r_state == 3'd0;
	initial _sv2v_0 = 0;
endmodule
module uart_axil_bridge (
	aclk,
	aresetn,
	i_uart_rx,
	o_uart_tx,
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
	m_axil_araddr,
	m_axil_arprot,
	m_axil_arvalid,
	m_axil_arready,
	m_axil_rdata,
	m_axil_rresp,
	m_axil_rvalid,
	m_axil_rready
);
	reg _sv2v_0;
	parameter signed [31:0] AXIL_ADDR_WIDTH = 32;
	parameter signed [31:0] AXIL_DATA_WIDTH = 32;
	parameter signed [31:0] CLKS_PER_BIT = 868;
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	input wire aclk;
	input wire aresetn;
	input wire i_uart_rx;
	output wire o_uart_tx;
	output wire [AXIL_ADDR_WIDTH - 1:0] m_axil_awaddr;
	output wire [2:0] m_axil_awprot;
	output wire m_axil_awvalid;
	input wire m_axil_awready;
	output wire [AXIL_DATA_WIDTH - 1:0] m_axil_wdata;
	output wire [(AXIL_DATA_WIDTH / 8) - 1:0] m_axil_wstrb;
	output wire m_axil_wvalid;
	input wire m_axil_wready;
	input wire [1:0] m_axil_bresp;
	input wire m_axil_bvalid;
	output wire m_axil_bready;
	output wire [AXIL_ADDR_WIDTH - 1:0] m_axil_araddr;
	output wire [2:0] m_axil_arprot;
	output wire m_axil_arvalid;
	input wire m_axil_arready;
	input wire [AXIL_DATA_WIDTH - 1:0] m_axil_rdata;
	input wire [1:0] m_axil_rresp;
	input wire m_axil_rvalid;
	output wire m_axil_rready;
	wire [7:0] w_rx_data;
	wire [7:0] w_tx_data;
	wire w_rx_valid;
	wire w_rx_ready;
	wire w_tx_valid;
	wire w_tx_ready;
	wire [AXIL_ADDR_WIDTH - 1:0] w_fub_awaddr;
	wire [2:0] w_fub_awprot;
	wire w_fub_awvalid;
	wire w_fub_awready;
	wire [AXIL_DATA_WIDTH - 1:0] w_fub_wdata;
	wire [(AXIL_DATA_WIDTH / 8) - 1:0] w_fub_wstrb;
	wire w_fub_wvalid;
	wire w_fub_wready;
	wire [1:0] w_fub_bresp;
	wire w_fub_bvalid;
	wire w_fub_bready;
	wire [AXIL_ADDR_WIDTH - 1:0] w_fub_araddr;
	wire [2:0] w_fub_arprot;
	wire w_fub_arvalid;
	wire w_fub_arready;
	wire [AXIL_DATA_WIDTH - 1:0] w_fub_rdata;
	wire [1:0] w_fub_rresp;
	wire w_fub_rvalid;
	wire w_fub_rready;
	uart_rx #(.CLKS_PER_BIT(CLKS_PER_BIT)) u_uart_rx(
		.i_clk(aclk),
		.i_rst_n(aresetn),
		.i_rx(i_uart_rx),
		.o_rx_data(w_rx_data),
		.o_rx_valid(w_rx_valid),
		.i_rx_ready(w_rx_ready)
	);
	uart_tx #(.CLKS_PER_BIT(CLKS_PER_BIT)) u_uart_tx(
		.i_clk(aclk),
		.i_rst_n(aresetn),
		.o_tx(o_uart_tx),
		.i_tx_data(w_tx_data),
		.i_tx_valid(w_tx_valid),
		.o_tx_ready(w_tx_ready)
	);
	reg [3:0] r_cmd_state;
	reg [3:0] w_cmd_state_next;
	localparam signed [31:0] ADDR_HEX_DIGITS = (AXIL_ADDR_WIDTH + 3) / 4;
	localparam signed [31:0] DATA_HEX_DIGITS = (AXIL_DATA_WIDTH + 3) / 4;
	localparam signed [31:0] MAX_RESPONSE_LEN = (2 + DATA_HEX_DIGITS) + 1;
	localparam signed [31:0] RESPONSE_INDEX_WIDTH = $clog2(MAX_RESPONSE_LEN + 1);
	reg [7:0] r_cmd_type;
	reg [31:0] r_cmd_addr;
	reg [AXIL_DATA_WIDTH - 1:0] r_cmd_data;
	reg [AXIL_DATA_WIDTH - 1:0] r_resp_data;
	reg [4:0] r_nibble_count;
	reg [7:0] r_response_buffer [MAX_RESPONSE_LEN - 1:0];
	reg [RESPONSE_INDEX_WIDTH - 1:0] r_response_index;
	reg [RESPONSE_INDEX_WIDTH - 1:0] r_response_length;
	function automatic [3:0] hex_to_val;
		input reg [7:0] c;
		reg [7:0] temp;
		if ((c >= "0") && (c <= "9")) begin
			temp = c - 8'd48;
			hex_to_val = temp[3:0];
		end
		else if ((c >= "a") && (c <= "f")) begin
			temp = c - 8'd87;
			hex_to_val = temp[3:0];
		end
		else if ((c >= "A") && (c <= "F")) begin
			temp = c - 8'd55;
			hex_to_val = temp[3:0];
		end
		else
			hex_to_val = 4'h0;
	endfunction
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	function automatic [7:0] val_to_hex;
		input reg [3:0] v;
		reg [7:0] v_extended;
		begin
			v_extended = sv2v_cast_8(v);
			if (v < 4'd10)
				val_to_hex = 8'd48 + v_extended;
			else
				val_to_hex = 8'd55 + v_extended;
		end
	endfunction
	function automatic [AXIL_DATA_WIDTH - 1:0] sv2v_cast_A77A0;
		input reg [AXIL_DATA_WIDTH - 1:0] inp;
		sv2v_cast_A77A0 = inp;
	endfunction
	function automatic signed [RESPONSE_INDEX_WIDTH - 1:0] sv2v_cast_1E9FA_signed;
		input reg signed [RESPONSE_INDEX_WIDTH - 1:0] inp;
		sv2v_cast_1E9FA_signed = inp;
	endfunction
	always @(posedge aclk)
		if (!aresetn) begin
			r_cmd_state <= 4'd0;
			r_cmd_type <= 1'sb0;
			r_cmd_addr <= 1'sb0;
			r_cmd_data <= sv2v_cast_A77A0(1'sb0);
			r_resp_data <= sv2v_cast_A77A0(1'sb0);
			r_nibble_count <= 1'sb0;
			r_response_index <= 1'sb0;
			r_response_length <= 1'sb0;
		end
		else begin
			r_cmd_state <= w_cmd_state_next;
			case (r_cmd_state)
				4'd0:
					if (w_rx_valid && w_rx_ready) begin
						r_cmd_type <= w_rx_data;
						r_nibble_count <= 1'sb0;
						r_cmd_addr <= 1'sb0;
						r_cmd_data <= sv2v_cast_A77A0(1'sb0);
					end
				4'd2:
					if (w_rx_valid && w_rx_ready) begin
						if (((w_rx_data != " ") && (w_rx_data != "\n")) && (w_rx_data != "\r")) begin
							r_cmd_addr <= {r_cmd_addr[AXIL_ADDR_WIDTH - 5:0], hex_to_val(w_rx_data)};
							r_nibble_count <= r_nibble_count + 1'b1;
						end
					end
				4'd3:
					if (w_rx_valid && w_rx_ready) begin
						if (((w_rx_data != " ") && (w_rx_data != "\n")) && (w_rx_data != "\r")) begin
							r_cmd_data <= {r_cmd_data[AXIL_DATA_WIDTH - 5:0], hex_to_val(w_rx_data)};
							r_nibble_count <= r_nibble_count + 1'b1;
						end
					end
				4'd9:
					if (w_fub_rvalid && w_fub_rready) begin
						r_resp_data <= w_fub_rdata;
						r_response_buffer[0] <= "0";
						r_response_buffer[1] <= "x";
						begin : sv2v_autoblock_1
							reg signed [31:0] i;
							for (i = 0; i < DATA_HEX_DIGITS; i = i + 1)
								r_response_buffer[2 + i] <= val_to_hex(w_fub_rdata[(AXIL_DATA_WIDTH - 1) - (i * 4)-:4]);
						end
						r_response_buffer[2 + DATA_HEX_DIGITS] <= "\n";
						r_response_index <= 1'sb0;
						r_response_length <= sv2v_cast_1E9FA_signed((2 + DATA_HEX_DIGITS) + 1);
					end
				4'd7:
					if (w_fub_bvalid && w_fub_bready) begin
						r_response_buffer[0] <= "O";
						r_response_buffer[1] <= "K";
						r_response_buffer[2] <= "\n";
						r_response_index <= 1'sb0;
						r_response_length <= sv2v_cast_1E9FA_signed(3);
					end
				4'd10:
					if (w_tx_valid && w_tx_ready)
						r_response_index <= r_response_index + 1'b1;
				default:
					;
			endcase
		end
	always @(*) begin
		if (_sv2v_0)
			;
		w_cmd_state_next = r_cmd_state;
		case (r_cmd_state)
			4'd0:
				if (w_rx_valid && w_rx_ready) begin
					if ((w_rx_data == "W") || (w_rx_data == "w"))
						w_cmd_state_next = 4'd2;
					else if ((w_rx_data == "R") || (w_rx_data == "r"))
						w_cmd_state_next = 4'd2;
				end
			4'd2:
				if (w_rx_valid && w_rx_ready) begin
					if (w_rx_data == " ") begin
						if (r_nibble_count > 0) begin
							if ((r_cmd_type == "W") || (r_cmd_type == "w"))
								w_cmd_state_next = 4'd3;
							else
								w_cmd_state_next = 4'd4;
						end
					end
					else if ((w_rx_data == "\n") || (w_rx_data == "\r"))
						w_cmd_state_next = 4'd4;
				end
			4'd3:
				if (w_rx_valid && w_rx_ready) begin
					if (w_rx_data == " ")
						;
					else if ((w_rx_data == "\n") || (w_rx_data == "\r"))
						w_cmd_state_next = 4'd4;
				end
			4'd4:
				if ((r_cmd_type == "W") || (r_cmd_type == "w"))
					w_cmd_state_next = 4'd5;
				else if ((r_cmd_type == "R") || (r_cmd_type == "r"))
					w_cmd_state_next = 4'd8;
				else
					w_cmd_state_next = 4'd0;
			4'd5:
				if (w_fub_awvalid && w_fub_awready)
					w_cmd_state_next = 4'd6;
			4'd6:
				if (w_fub_wvalid && w_fub_wready)
					w_cmd_state_next = 4'd7;
			4'd7:
				if (w_fub_bvalid && w_fub_bready)
					w_cmd_state_next = 4'd10;
			4'd8:
				if (w_fub_arvalid && w_fub_arready)
					w_cmd_state_next = 4'd9;
			4'd9:
				if (w_fub_rvalid && w_fub_rready)
					w_cmd_state_next = 4'd10;
			4'd10:
				if (w_tx_valid && w_tx_ready) begin
					if (r_response_index >= (r_response_length - 1))
						w_cmd_state_next = 4'd0;
				end
			default: w_cmd_state_next = 4'd0;
		endcase
	end
	assign w_rx_ready = ((r_cmd_state == 4'd0) || (r_cmd_state == 4'd2)) || (r_cmd_state == 4'd3);
	assign w_tx_valid = r_cmd_state == 4'd10;
	assign w_tx_data = r_response_buffer[r_response_index];
	assign w_fub_awaddr = r_cmd_addr[AXIL_ADDR_WIDTH - 1:0];
	assign w_fub_awprot = 3'b000;
	assign w_fub_awvalid = r_cmd_state == 4'd5;
	assign w_fub_wdata = r_cmd_data[AXIL_DATA_WIDTH - 1:0];
	assign w_fub_wstrb = {AXIL_DATA_WIDTH / 8 {1'b1}};
	assign w_fub_wvalid = r_cmd_state == 4'd6;
	assign w_fub_bready = r_cmd_state == 4'd7;
	assign w_fub_araddr = r_cmd_addr[AXIL_ADDR_WIDTH - 1:0];
	assign w_fub_arprot = 3'b000;
	assign w_fub_arvalid = r_cmd_state == 4'd8;
	assign w_fub_rready = r_cmd_state == 4'd9;
	axil4_master_wr #(
		.AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
		.AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
		.SKID_DEPTH_AW(SKID_DEPTH_AW),
		.SKID_DEPTH_W(SKID_DEPTH_W),
		.SKID_DEPTH_B(SKID_DEPTH_B)
	) u_axil_wr_timing(
		.aclk(aclk),
		.aresetn(aresetn),
		.fub_awaddr(w_fub_awaddr),
		.fub_awprot(w_fub_awprot),
		.fub_awvalid(w_fub_awvalid),
		.fub_awready(w_fub_awready),
		.fub_wdata(w_fub_wdata),
		.fub_wstrb(w_fub_wstrb),
		.fub_wvalid(w_fub_wvalid),
		.fub_wready(w_fub_wready),
		.fub_bresp(w_fub_bresp),
		.fub_bvalid(w_fub_bvalid),
		.fub_bready(w_fub_bready),
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
	axil4_master_rd #(
		.AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
		.AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
		.SKID_DEPTH_AR(SKID_DEPTH_AR),
		.SKID_DEPTH_R(SKID_DEPTH_R)
	) u_axil_rd_timing(
		.aclk(aclk),
		.aresetn(aresetn),
		.fub_araddr(w_fub_araddr),
		.fub_arprot(w_fub_arprot),
		.fub_arvalid(w_fub_arvalid),
		.fub_arready(w_fub_arready),
		.fub_rdata(w_fub_rdata),
		.fub_rresp(w_fub_rresp),
		.fub_rvalid(w_fub_rvalid),
		.fub_rready(w_fub_rready),
		.m_axil_araddr(m_axil_araddr),
		.m_axil_arprot(m_axil_arprot),
		.m_axil_arvalid(m_axil_arvalid),
		.m_axil_arready(m_axil_arready),
		.m_axil_rdata(m_axil_rdata),
		.m_axil_rresp(m_axil_rresp),
		.m_axil_rvalid(m_axil_rvalid),
		.m_axil_rready(m_axil_rready),
		.busy()
	);
	initial _sv2v_0 = 0;
endmodule
