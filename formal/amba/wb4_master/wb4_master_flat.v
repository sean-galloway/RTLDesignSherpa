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
			initial $display("Error [elaboration] /mnt/data/github/RTLDesignSherpa/rtl/amba/gaxi/gaxi_skid_buffer.sv:101:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive", DEPTH);
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
module wb4_master (
	clk,
	aresetn,
	m_wb_CYC,
	m_wb_STB,
	m_wb_WE,
	m_wb_ADR,
	m_wb_DAT_W,
	m_wb_SEL,
	m_wb_STALL,
	m_wb_ACK,
	m_wb_ERR,
	m_wb_RTY,
	m_wb_DAT_R,
	cmd_valid,
	cmd_ready,
	cmd_we,
	cmd_adr,
	cmd_dat,
	cmd_sel,
	rsp_valid,
	rsp_ready,
	rsp_status,
	rsp_dat
);
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] CMD_DEPTH = 4;
	parameter signed [31:0] RSP_DEPTH = 4;
	parameter signed [31:0] SEL_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = SEL_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_STATUS_WIDTH = 2;
	parameter signed [31:0] STW = wb4_pkg_WB4_STATUS_WIDTH;
	parameter signed [31:0] CPW = ((1 + AW) + DW) + SW;
	parameter signed [31:0] RPW = STW + DW;
	input wire clk;
	input wire aresetn;
	output wire m_wb_CYC;
	output wire m_wb_STB;
	output wire m_wb_WE;
	output wire [AW - 1:0] m_wb_ADR;
	output wire [DW - 1:0] m_wb_DAT_W;
	output wire [SW - 1:0] m_wb_SEL;
	input wire m_wb_STALL;
	input wire m_wb_ACK;
	input wire m_wb_ERR;
	input wire m_wb_RTY;
	input wire [DW - 1:0] m_wb_DAT_R;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire cmd_we;
	input wire [AW - 1:0] cmd_adr;
	input wire [DW - 1:0] cmd_dat;
	input wire [SW - 1:0] cmd_sel;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [STW - 1:0] rsp_status;
	output wire [DW - 1:0] rsp_dat;
	wire r_cmd_valid;
	wire w_cmd_pop;
	wire [CPW - 1:0] w_cmd_data_in;
	wire [CPW - 1:0] r_cmd_data_out;
	assign w_cmd_data_in = {cmd_we, cmd_adr, cmd_dat, cmd_sel};
	assign {m_wb_WE, m_wb_ADR, m_wb_DAT_W, m_wb_SEL} = r_cmd_data_out;
	gaxi_skid_buffer #(
		.DATA_WIDTH(CPW),
		.DEPTH(CMD_DEPTH)
	) u_cmd_skid(
		.axi_aclk(clk),
		.axi_aresetn(aresetn),
		.wr_valid(cmd_valid),
		.wr_ready(cmd_ready),
		.wr_data(w_cmd_data_in),
		.rd_valid(r_cmd_valid),
		.rd_ready(w_cmd_pop),
		.rd_data(r_cmd_data_out),
		.count(),
		.rd_count()
	);
	wire w_rsp_push;
	wire w_rsp_space;
	wire [STW - 1:0] w_status;
	wire [RPW - 1:0] w_rsp_data_in;
	function automatic [1:0] sv2v_cast_1AA03;
		input reg [1:0] inp;
		sv2v_cast_1AA03 = inp;
	endfunction
	assign w_status = (m_wb_ERR ? sv2v_cast_1AA03(2'b01) : (m_wb_RTY ? sv2v_cast_1AA03(2'b10) : sv2v_cast_1AA03(2'b00)));
	assign w_rsp_data_in = {w_status, m_wb_DAT_R};
	gaxi_skid_buffer #(
		.DATA_WIDTH(RPW),
		.DEPTH(RSP_DEPTH)
	) u_rsp_skid(
		.axi_aclk(clk),
		.axi_aresetn(aresetn),
		.wr_valid(w_rsp_push),
		.wr_ready(w_rsp_space),
		.wr_data(w_rsp_data_in),
		.rd_valid(rsp_valid),
		.rd_ready(rsp_ready),
		.rd_data({rsp_status, rsp_dat}),
		.count(),
		.rd_count()
	);
	localparam signed [31:0] CW = $clog2(RSP_DEPTH + 1);
	reg [CW - 1:0] r_inflight;
	reg [CW - 1:0] r_reserved;
	wire w_issue;
	wire w_term;
	wire w_rsp_pop;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	assign w_issue = r_cmd_valid && (sv2v_cast_32(r_reserved) < RSP_DEPTH);
	assign m_wb_STB = w_issue;
	assign m_wb_CYC = w_issue || (r_inflight != {CW {1'sb0}});
	assign w_cmd_pop = m_wb_STB && !m_wb_STALL;
	assign w_term = m_wb_CYC && ((m_wb_ACK || m_wb_ERR) || m_wb_RTY);
	assign w_rsp_push = w_term;
	assign w_rsp_pop = rsp_valid && rsp_ready;
	function automatic [CW - 1:0] sv2v_cast_3D2D3;
		input reg [CW - 1:0] inp;
		sv2v_cast_3D2D3 = inp;
	endfunction
	always @(posedge clk or negedge aresetn)
		if (!aresetn) begin
			r_inflight <= 1'sb0;
			r_reserved <= 1'sb0;
		end
		else begin
			r_inflight <= (r_inflight + sv2v_cast_3D2D3(w_cmd_pop)) - sv2v_cast_3D2D3(w_term);
			r_reserved <= (r_reserved + sv2v_cast_3D2D3(w_cmd_pop)) - sv2v_cast_3D2D3(w_rsp_pop);
		end
	reg f_past_valid;
	initial f_past_valid = 1'b0;
	always @(posedge clk) f_past_valid <= 1'b1;
	always @(posedge clk)
		if ((f_past_valid && aresetn) && $past(aresetn)) begin
			assert ((r_inflight == {CW {1'sb0}}) || m_wb_CYC) ;
			assert (!m_wb_STB || m_wb_CYC) ;
			if (($past(m_wb_STB) && $past(m_wb_STALL)) && $past(m_wb_CYC)) begin
				assert (m_wb_STB) ;
				assert ((($stable(m_wb_ADR) && $stable(m_wb_DAT_W)) && $stable(m_wb_SEL)) && $stable(m_wb_WE)) ;
			end
			assert (sv2v_cast_32(r_reserved) <= RSP_DEPTH) ;
			assert (r_inflight <= r_reserved) ;
			assert (!w_rsp_push || w_rsp_space) ;
		end
endmodule
