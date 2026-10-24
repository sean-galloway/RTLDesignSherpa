module monbus_wr_mux2 (
	axi_aclk,
	axi_aresetn,
	s0_awid,
	s0_awaddr,
	s0_awlen,
	s0_awsize,
	s0_awburst,
	s0_awvalid,
	s0_awready,
	s0_wdata,
	s0_wstrb,
	s0_wlast,
	s0_wvalid,
	s0_wready,
	s0_bid,
	s0_bresp,
	s0_bvalid,
	s0_bready,
	s1_awid,
	s1_awaddr,
	s1_awlen,
	s1_awsize,
	s1_awburst,
	s1_awvalid,
	s1_awready,
	s1_wdata,
	s1_wstrb,
	s1_wlast,
	s1_wvalid,
	s1_wready,
	s1_bid,
	s1_bresp,
	s1_bvalid,
	s1_bready,
	m_awid,
	m_awaddr,
	m_awlen,
	m_awsize,
	m_awburst,
	m_awvalid,
	m_awready,
	m_wdata,
	m_wstrb,
	m_wlast,
	m_wvalid,
	m_wready,
	m_bid,
	m_bresp,
	m_bvalid,
	m_bready
);
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_ID_WIDTH = 1;
	parameter signed [31:0] ORDER_DEPTH = 8;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire [AXI_ID_WIDTH - 1:0] s0_awid;
	input wire [ADDR_WIDTH - 1:0] s0_awaddr;
	input wire [7:0] s0_awlen;
	input wire [2:0] s0_awsize;
	input wire [1:0] s0_awburst;
	input wire s0_awvalid;
	output wire s0_awready;
	input wire [63:0] s0_wdata;
	input wire [7:0] s0_wstrb;
	input wire s0_wlast;
	input wire s0_wvalid;
	output wire s0_wready;
	output wire [AXI_ID_WIDTH - 1:0] s0_bid;
	output wire [1:0] s0_bresp;
	output wire s0_bvalid;
	input wire s0_bready;
	input wire [AXI_ID_WIDTH - 1:0] s1_awid;
	input wire [ADDR_WIDTH - 1:0] s1_awaddr;
	input wire [7:0] s1_awlen;
	input wire [2:0] s1_awsize;
	input wire [1:0] s1_awburst;
	input wire s1_awvalid;
	output wire s1_awready;
	input wire [63:0] s1_wdata;
	input wire [7:0] s1_wstrb;
	input wire s1_wlast;
	input wire s1_wvalid;
	output wire s1_wready;
	output wire [AXI_ID_WIDTH - 1:0] s1_bid;
	output wire [1:0] s1_bresp;
	output wire s1_bvalid;
	input wire s1_bready;
	output wire [AXI_ID_WIDTH - 1:0] m_awid;
	output wire [ADDR_WIDTH - 1:0] m_awaddr;
	output wire [7:0] m_awlen;
	output wire [2:0] m_awsize;
	output wire [1:0] m_awburst;
	output wire m_awvalid;
	input wire m_awready;
	output wire [63:0] m_wdata;
	output wire [7:0] m_wstrb;
	output wire m_wlast;
	output wire m_wvalid;
	input wire m_wready;
	input wire [AXI_ID_WIDTH - 1:0] m_bid;
	input wire [1:0] m_bresp;
	input wire m_bvalid;
	output wire m_bready;
	localparam signed [31:0] QAW = $clog2(ORDER_DEPTH);
	initial begin : param_check
		if ((ORDER_DEPTH < 2) || ((ORDER_DEPTH & (ORDER_DEPTH - 1)) != 0)) begin
			$display("Fatal [%0t] /tmp/rds-canonical-repo-root/rtl/amba/ocelus/monbus_wr_mux2.sv:119:13 - monbus_wr_mux2.param_check.<unnamed_block>\n msg: ", $time, "monbus_wr_mux2: ORDER_DEPTH must be a power of 2 >= 2 (got %0d)", ORDER_DEPTH);
			$finish(1);
		end
	end
	reg [ORDER_DEPTH - 1:0] r_wq_tag;
	reg [QAW - 1:0] r_wq_rd;
	reg [QAW - 1:0] r_wq_wr;
	reg [QAW:0] r_wq_count;
	reg [ORDER_DEPTH - 1:0] r_bq_tag;
	reg [QAW - 1:0] r_bq_rd;
	reg [QAW - 1:0] r_bq_wr;
	reg [QAW:0] r_bq_count;
	wire w_q_full;
	wire w_aw_sel;
	reg r_aw_pend;
	reg r_aw_pend_sel;
	wire w_aw_issue;
	wire w_wq_nonempty;
	wire w_bq_nonempty;
	wire w_w_sel;
	wire w_b_sel;
	wire w_w_issue;
	wire w_w_last_issue;
	wire w_b_issue;
	function automatic signed [((QAW + 0) >= 0 ? QAW + 1 : 1 - (QAW + 0)) - 1:0] sv2v_cast_D01D9_signed;
		input reg signed [((QAW + 0) >= 0 ? QAW + 1 : 1 - (QAW + 0)) - 1:0] inp;
		sv2v_cast_D01D9_signed = inp;
	endfunction
	assign w_q_full = (r_wq_count == sv2v_cast_D01D9_signed(ORDER_DEPTH)) || (r_bq_count == sv2v_cast_D01D9_signed(ORDER_DEPTH));
	assign w_aw_sel = (r_aw_pend ? r_aw_pend_sel : !s0_awvalid);
	assign m_awvalid = (w_aw_sel ? s1_awvalid : s0_awvalid) && !w_q_full;
	assign m_awid = (w_aw_sel ? s1_awid : s0_awid);
	assign m_awaddr = (w_aw_sel ? s1_awaddr : s0_awaddr);
	assign m_awlen = (w_aw_sel ? s1_awlen : s0_awlen);
	assign m_awsize = (w_aw_sel ? s1_awsize : s0_awsize);
	assign m_awburst = (w_aw_sel ? s1_awburst : s0_awburst);
	assign s0_awready = (m_awready && !w_q_full) && !w_aw_sel;
	assign s1_awready = (m_awready && !w_q_full) && w_aw_sel;
	assign w_aw_issue = m_awvalid && m_awready;
	assign w_wq_nonempty = r_wq_count != {(QAW >= 0 ? QAW + 1 : 1 - QAW) {1'sb0}};
	assign w_w_sel = r_wq_tag[r_wq_rd];
	assign m_wvalid = w_wq_nonempty && (w_w_sel ? s1_wvalid : s0_wvalid);
	assign m_wdata = (w_w_sel ? s1_wdata : s0_wdata);
	assign m_wstrb = (w_w_sel ? s1_wstrb : s0_wstrb);
	assign m_wlast = (w_w_sel ? s1_wlast : s0_wlast);
	assign s0_wready = (w_wq_nonempty && !w_w_sel) && m_wready;
	assign s1_wready = (w_wq_nonempty && w_w_sel) && m_wready;
	assign w_w_issue = m_wvalid && m_wready;
	assign w_w_last_issue = w_w_issue && m_wlast;
	assign w_bq_nonempty = r_bq_count != {(QAW >= 0 ? QAW + 1 : 1 - QAW) {1'sb0}};
	assign w_b_sel = r_bq_tag[r_bq_rd];
	assign s0_bvalid = (w_bq_nonempty && !w_b_sel) && m_bvalid;
	assign s1_bvalid = (w_bq_nonempty && w_b_sel) && m_bvalid;
	assign s0_bid = m_bid;
	assign s1_bid = m_bid;
	assign s0_bresp = m_bresp;
	assign s1_bresp = m_bresp;
	assign m_bready = w_bq_nonempty && (w_b_sel ? s1_bready : s0_bready);
	assign w_b_issue = m_bvalid && m_bready;
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			r_aw_pend <= 1'b0;
			r_aw_pend_sel <= 1'b0;
			r_wq_tag <= 1'sb0;
			r_wq_rd <= 1'sb0;
			r_wq_wr <= 1'sb0;
			r_wq_count <= 1'sb0;
			r_bq_tag <= 1'sb0;
			r_bq_rd <= 1'sb0;
			r_bq_wr <= 1'sb0;
			r_bq_count <= 1'sb0;
		end
		else begin
			if (m_awvalid && !m_awready) begin
				r_aw_pend <= 1'b1;
				r_aw_pend_sel <= w_aw_sel;
			end
			else
				r_aw_pend <= 1'b0;
			if (w_aw_issue) begin
				r_wq_tag[r_wq_wr] <= w_aw_sel;
				r_wq_wr <= r_wq_wr + 1'b1;
				r_bq_tag[r_bq_wr] <= w_aw_sel;
				r_bq_wr <= r_bq_wr + 1'b1;
			end
			if (w_w_last_issue)
				r_wq_rd <= r_wq_rd + 1'b1;
			if (w_b_issue)
				r_bq_rd <= r_bq_rd + 1'b1;
			case ({w_aw_issue, w_w_last_issue})
				2'b10: r_wq_count <= r_wq_count + 1'b1;
				2'b01: r_wq_count <= r_wq_count - 1'b1;
				default:
					;
			endcase
			case ({w_aw_issue, w_b_issue})
				2'b10: r_bq_count <= r_bq_count + 1'b1;
				2'b01: r_bq_count <= r_bq_count - 1'b1;
				default:
					;
			endcase
		end
endmodule
