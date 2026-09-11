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
module apb5_master (
	pclk,
	presetn,
	m_apb_PSEL,
	m_apb_PENABLE,
	m_apb_PADDR,
	m_apb_PWRITE,
	m_apb_PWDATA,
	m_apb_PSTRB,
	m_apb_PPROT,
	m_apb_PAUSER,
	m_apb_PWUSER,
	m_apb_PRDATA,
	m_apb_PSLVERR,
	m_apb_PREADY,
	m_apb_PWAKEUP,
	m_apb_PRUSER,
	m_apb_PBUSER,
	m_apb_PWDATAPARITY,
	m_apb_PADDRPARITY,
	m_apb_PCTRLPARITY,
	m_apb_PRDATAPARITY,
	m_apb_PREADYPARITY,
	m_apb_PSLVERRPARITY,
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
	rsp_pwakeup,
	rsp_pruser,
	rsp_pbuser,
	parity_error_rdata,
	parity_error_ctrl,
	wakeup_pending
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] PROT_WIDTH = 3;
	parameter signed [31:0] AUSER_WIDTH = 4;
	parameter signed [31:0] WUSER_WIDTH = 4;
	parameter signed [31:0] RUSER_WIDTH = 4;
	parameter signed [31:0] BUSER_WIDTH = 4;
	parameter signed [31:0] CMD_DEPTH = 6;
	parameter signed [31:0] RSP_DEPTH = 6;
	parameter [0:0] ENABLE_PARITY = 0;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = STRB_WIDTH;
	parameter signed [31:0] PW = PROT_WIDTH;
	parameter signed [31:0] AUW = AUSER_WIDTH;
	parameter signed [31:0] WUW = WUSER_WIDTH;
	parameter signed [31:0] RUW = RUSER_WIDTH;
	parameter signed [31:0] BUW = BUSER_WIDTH;
	parameter signed [31:0] CPW = (((((AW + DW) + SW) + PW) + AUW) + WUW) + 1;
	parameter signed [31:0] RPW = ((DW + RUW) + BUW) + 2;
	input wire pclk;
	input wire presetn;
	output reg m_apb_PSEL;
	output reg m_apb_PENABLE;
	output reg [AW - 1:0] m_apb_PADDR;
	output reg m_apb_PWRITE;
	output reg [DW - 1:0] m_apb_PWDATA;
	output reg [SW - 1:0] m_apb_PSTRB;
	output reg [PW - 1:0] m_apb_PPROT;
	output reg [AUW - 1:0] m_apb_PAUSER;
	output reg [WUW - 1:0] m_apb_PWUSER;
	input wire [DW - 1:0] m_apb_PRDATA;
	input wire m_apb_PSLVERR;
	input wire m_apb_PREADY;
	input wire m_apb_PWAKEUP;
	input wire [RUW - 1:0] m_apb_PRUSER;
	input wire [BUW - 1:0] m_apb_PBUSER;
	output wire [SW - 1:0] m_apb_PWDATAPARITY;
	output wire m_apb_PADDRPARITY;
	output wire m_apb_PCTRLPARITY;
	input wire [SW - 1:0] m_apb_PRDATAPARITY;
	input wire m_apb_PREADYPARITY;
	input wire m_apb_PSLVERRPARITY;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire cmd_pwrite;
	input wire [AW - 1:0] cmd_paddr;
	input wire [DW - 1:0] cmd_pwdata;
	input wire [SW - 1:0] cmd_pstrb;
	input wire [PW - 1:0] cmd_pprot;
	input wire [AUW - 1:0] cmd_pauser;
	input wire [WUW - 1:0] cmd_pwuser;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [DW - 1:0] rsp_prdata;
	output wire rsp_pslverr;
	output wire rsp_pwakeup;
	output wire [RUW - 1:0] rsp_pruser;
	output wire [BUW - 1:0] rsp_pbuser;
	output wire parity_error_rdata;
	output wire parity_error_ctrl;
	output wire wakeup_pending;
	wire r_cmd_valid;
	reg w_cmd_ready;
	wire [CPW - 1:0] r_cmd_data_in;
	wire [CPW - 1:0] r_cmd_data_out;
	wire [3:0] w_cmd_count;
	wire [DW - 1:0] r_cmd_pwdata;
	wire [AW - 1:0] r_cmd_paddr;
	wire [SW - 1:0] r_cmd_pstrb;
	wire [PW - 1:0] r_cmd_pprot;
	wire [AUW - 1:0] r_cmd_pauser;
	wire [WUW - 1:0] r_cmd_pwuser;
	wire r_cmd_pwrite;
	assign r_cmd_data_in = {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata, cmd_pauser, cmd_pwuser};
	assign {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata, r_cmd_pauser, r_cmd_pwuser} = r_cmd_data_out;
	gaxi_skid_buffer #(
		.DATA_WIDTH(CPW),
		.DEPTH(CMD_DEPTH)
	) cmd_fifo_inst(
		.axi_aclk(pclk),
		.axi_aresetn(presetn),
		.wr_valid(cmd_valid),
		.wr_ready(cmd_ready),
		.wr_data(r_cmd_data_in),
		.count(w_cmd_count),
		.rd_valid(r_cmd_valid),
		.rd_ready(w_cmd_ready),
		.rd_data(r_cmd_data_out),
		.rd_count()
	);
	reg w_rsp_valid;
	wire r_rsp_ready;
	wire [3:0] w_rsp_count;
	wire [RPW - 1:0] r_rsp_data_in;
	wire [RPW - 1:0] r_rsp_data_out;
	assign r_rsp_data_in = {m_apb_PSLVERR, m_apb_PWAKEUP, m_apb_PRDATA, m_apb_PRUSER, m_apb_PBUSER};
	gaxi_skid_buffer #(
		.DATA_WIDTH(RPW),
		.DEPTH(RSP_DEPTH)
	) resp_fifo_inst(
		.axi_aclk(pclk),
		.axi_aresetn(presetn),
		.wr_valid(w_rsp_valid),
		.wr_ready(r_rsp_ready),
		.wr_data(r_rsp_data_in),
		.count(w_rsp_count),
		.rd_valid(rsp_valid),
		.rd_ready(rsp_ready),
		.rd_data(r_rsp_data_out),
		.rd_count()
	);
	assign {rsp_pslverr, rsp_pwakeup, rsp_prdata, rsp_pruser, rsp_pbuser} = r_rsp_data_out;
	reg [2:0] r_apb_state;
	reg [2:0] w_apb_next_state;
	always @(posedge pclk or negedge presetn)
		if (!presetn)
			r_apb_state <= 3'b001;
		else
			r_apb_state <= w_apb_next_state;
	reg r_wakeup_pending;
	always @(posedge pclk or negedge presetn)
		if (!presetn)
			r_wakeup_pending <= 1'b0;
		else if (m_apb_PWAKEUP)
			r_wakeup_pending <= 1'b1;
		else if (r_apb_state != 3'b001)
			r_wakeup_pending <= 1'b0;
	assign wakeup_pending = r_wakeup_pending;
	generate
		if (ENABLE_PARITY) begin : gen_parity
			genvar _gv_i_1;
			for (_gv_i_1 = 0; _gv_i_1 < SW; _gv_i_1 = _gv_i_1 + 1) begin : gen_wdata_parity
				localparam i = _gv_i_1;
				assign m_apb_PWDATAPARITY[i] = ^r_cmd_pwdata[i * 8+:8];
			end
			assign m_apb_PADDRPARITY = ^r_cmd_paddr;
			assign m_apb_PCTRLPARITY = ^{r_cmd_pwrite, r_cmd_pstrb, r_cmd_pprot};
			wire [SW - 1:0] w_expected_rdata_parity;
			genvar _gv_i_2;
			for (_gv_i_2 = 0; _gv_i_2 < SW; _gv_i_2 = _gv_i_2 + 1) begin : gen_rdata_parity_check
				localparam i = _gv_i_2;
				assign w_expected_rdata_parity[i] = ^m_apb_PRDATA[i * 8+:8];
			end
			assign parity_error_rdata = ((m_apb_PREADY && m_apb_PSEL) && m_apb_PENABLE ? w_expected_rdata_parity != m_apb_PRDATAPARITY : 1'b0);
			assign parity_error_ctrl = ((m_apb_PREADY && m_apb_PSEL) && m_apb_PENABLE ? (^m_apb_PREADY != m_apb_PREADYPARITY) || (^m_apb_PSLVERR != m_apb_PSLVERRPARITY) : 1'b0);
		end
		else begin : gen_no_parity
			assign m_apb_PWDATAPARITY = 1'sb0;
			assign m_apb_PADDRPARITY = 1'b0;
			assign m_apb_PCTRLPARITY = 1'b0;
			assign parity_error_rdata = 1'b0;
			assign parity_error_ctrl = 1'b0;
		end
	endgenerate
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		w_apb_next_state = r_apb_state;
		m_apb_PSEL = 1'b0;
		m_apb_PENABLE = 1'b0;
		m_apb_PADDR = r_cmd_paddr;
		m_apb_PWRITE = r_cmd_pwrite;
		m_apb_PWDATA = r_cmd_pwdata;
		m_apb_PSTRB = r_cmd_pstrb;
		m_apb_PPROT = r_cmd_pprot;
		m_apb_PAUSER = r_cmd_pauser;
		m_apb_PWUSER = r_cmd_pwuser;
		w_cmd_ready = 1'b0;
		w_rsp_valid = 1'b0;
		casez (r_apb_state)
			3'b001:
				if (r_cmd_valid && r_rsp_ready)
					w_apb_next_state = 3'b010;
			3'b010: begin
				m_apb_PSEL = 1'b1;
				w_apb_next_state = 3'b100;
			end
			3'b100: begin
				m_apb_PSEL = 1'b1;
				m_apb_PENABLE = 1'b1;
				if (m_apb_PREADY) begin
					w_rsp_valid = 1'b1;
					w_cmd_ready = 1'b1;
					if ((w_cmd_count > 1) && (sv2v_cast_32(w_rsp_count) <= (RSP_DEPTH - 2)))
						w_apb_next_state = 3'b010;
					else
						w_apb_next_state = 3'b001;
				end
			end
			default: w_apb_next_state = 3'b001;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module apb5_master_stub (
	pclk,
	presetn,
	m_apb_PSEL,
	m_apb_PENABLE,
	m_apb_PADDR,
	m_apb_PWRITE,
	m_apb_PWDATA,
	m_apb_PSTRB,
	m_apb_PPROT,
	m_apb_PAUSER,
	m_apb_PWUSER,
	m_apb_PRDATA,
	m_apb_PSLVERR,
	m_apb_PREADY,
	m_apb_PWAKEUP,
	m_apb_PRUSER,
	m_apb_PBUSER,
	m_apb_PWDATAPARITY,
	m_apb_PADDRPARITY,
	m_apb_PCTRLPARITY,
	m_apb_PRDATAPARITY,
	m_apb_PREADYPARITY,
	m_apb_PSLVERRPARITY,
	cmd_valid,
	cmd_ready,
	cmd_data,
	rsp_valid,
	rsp_ready,
	rsp_data,
	parity_error_rdata,
	parity_error_ctrl,
	wakeup_pending
);
	parameter signed [31:0] CMD_DEPTH = 6;
	parameter signed [31:0] RSP_DEPTH = 6;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] PROT_WIDTH = 3;
	parameter signed [31:0] AUSER_WIDTH = 4;
	parameter signed [31:0] WUSER_WIDTH = 4;
	parameter signed [31:0] RUSER_WIDTH = 4;
	parameter signed [31:0] BUSER_WIDTH = 4;
	parameter [0:0] ENABLE_PARITY = 0;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] CMD_PACKET_WIDTH = (((((ADDR_WIDTH + DATA_WIDTH) + STRB_WIDTH) + PROT_WIDTH) + AUSER_WIDTH) + WUSER_WIDTH) + 3;
	parameter signed [31:0] RESP_PACKET_WIDTH = ((DATA_WIDTH + RUSER_WIDTH) + BUSER_WIDTH) + 4;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] SW = STRB_WIDTH;
	parameter signed [31:0] PW = PROT_WIDTH;
	parameter signed [31:0] AUW = AUSER_WIDTH;
	parameter signed [31:0] WUW = WUSER_WIDTH;
	parameter signed [31:0] RUW = RUSER_WIDTH;
	parameter signed [31:0] BUW = BUSER_WIDTH;
	parameter signed [31:0] CPW = CMD_PACKET_WIDTH;
	parameter signed [31:0] RPW = RESP_PACKET_WIDTH;
	input wire pclk;
	input wire presetn;
	output wire m_apb_PSEL;
	output wire m_apb_PENABLE;
	output wire [AW - 1:0] m_apb_PADDR;
	output wire m_apb_PWRITE;
	output wire [DW - 1:0] m_apb_PWDATA;
	output wire [SW - 1:0] m_apb_PSTRB;
	output wire [PW - 1:0] m_apb_PPROT;
	output wire [AUW - 1:0] m_apb_PAUSER;
	output wire [WUW - 1:0] m_apb_PWUSER;
	input wire [DW - 1:0] m_apb_PRDATA;
	input wire m_apb_PSLVERR;
	input wire m_apb_PREADY;
	input wire m_apb_PWAKEUP;
	input wire [RUW - 1:0] m_apb_PRUSER;
	input wire [BUW - 1:0] m_apb_PBUSER;
	output wire [SW - 1:0] m_apb_PWDATAPARITY;
	output wire m_apb_PADDRPARITY;
	output wire m_apb_PCTRLPARITY;
	input wire [SW - 1:0] m_apb_PRDATAPARITY;
	input wire m_apb_PREADYPARITY;
	input wire m_apb_PSLVERRPARITY;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire [CPW - 1:0] cmd_data;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [RPW - 1:0] rsp_data;
	output wire parity_error_rdata;
	output wire parity_error_ctrl;
	output wire wakeup_pending;
	wire [DW - 1:0] cmd_pwdata;
	wire [AW - 1:0] cmd_paddr;
	wire [SW - 1:0] cmd_pstrb;
	wire [PW - 1:0] cmd_pprot;
	wire [AUW - 1:0] cmd_pauser;
	wire [WUW - 1:0] cmd_pwuser;
	wire cmd_pwrite;
	wire cmd_first;
	wire cmd_last;
	assign {cmd_last, cmd_first, cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata, cmd_pauser, cmd_pwuser} = cmd_data;
	wire [DW - 1:0] rsp_prdata;
	wire rsp_pslverr;
	wire rsp_pwakeup;
	wire [RUW - 1:0] rsp_pruser;
	wire [BUW - 1:0] rsp_pbuser;
	assign rsp_data = {cmd_last, cmd_first, rsp_pslverr, rsp_pwakeup, rsp_prdata, rsp_pruser, rsp_pbuser};
	apb5_master #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.DATA_WIDTH(DATA_WIDTH),
		.PROT_WIDTH(PROT_WIDTH),
		.AUSER_WIDTH(AUSER_WIDTH),
		.WUSER_WIDTH(WUSER_WIDTH),
		.RUSER_WIDTH(RUSER_WIDTH),
		.BUSER_WIDTH(BUSER_WIDTH),
		.CMD_DEPTH(CMD_DEPTH),
		.RSP_DEPTH(RSP_DEPTH),
		.ENABLE_PARITY(ENABLE_PARITY),
		.STRB_WIDTH(STRB_WIDTH)
	) u_apb5_master(
		.pclk(pclk),
		.presetn(presetn),
		.m_apb_PSEL(m_apb_PSEL),
		.m_apb_PENABLE(m_apb_PENABLE),
		.m_apb_PADDR(m_apb_PADDR),
		.m_apb_PWRITE(m_apb_PWRITE),
		.m_apb_PWDATA(m_apb_PWDATA),
		.m_apb_PSTRB(m_apb_PSTRB),
		.m_apb_PPROT(m_apb_PPROT),
		.m_apb_PAUSER(m_apb_PAUSER),
		.m_apb_PWUSER(m_apb_PWUSER),
		.m_apb_PRDATA(m_apb_PRDATA),
		.m_apb_PSLVERR(m_apb_PSLVERR),
		.m_apb_PREADY(m_apb_PREADY),
		.m_apb_PWAKEUP(m_apb_PWAKEUP),
		.m_apb_PRUSER(m_apb_PRUSER),
		.m_apb_PBUSER(m_apb_PBUSER),
		.m_apb_PWDATAPARITY(m_apb_PWDATAPARITY),
		.m_apb_PADDRPARITY(m_apb_PADDRPARITY),
		.m_apb_PCTRLPARITY(m_apb_PCTRLPARITY),
		.m_apb_PRDATAPARITY(m_apb_PRDATAPARITY),
		.m_apb_PREADYPARITY(m_apb_PREADYPARITY),
		.m_apb_PSLVERRPARITY(m_apb_PSLVERRPARITY),
		.cmd_valid(cmd_valid),
		.cmd_ready(cmd_ready),
		.cmd_pwrite(cmd_pwrite),
		.cmd_paddr(cmd_paddr),
		.cmd_pwdata(cmd_pwdata),
		.cmd_pstrb(cmd_pstrb),
		.cmd_pprot(cmd_pprot),
		.cmd_pauser(cmd_pauser),
		.cmd_pwuser(cmd_pwuser),
		.rsp_valid(rsp_valid),
		.rsp_ready(rsp_ready),
		.rsp_prdata(rsp_prdata),
		.rsp_pslverr(rsp_pslverr),
		.rsp_pwakeup(rsp_pwakeup),
		.rsp_pruser(rsp_pruser),
		.rsp_pbuser(rsp_pbuser),
		.parity_error_rdata(parity_error_rdata),
		.parity_error_ctrl(parity_error_ctrl),
		.wakeup_pending(wakeup_pending)
	);
endmodule
