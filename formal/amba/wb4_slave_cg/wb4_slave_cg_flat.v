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
module clock_gate_ctrl (
	clk_in,
	aresetn,
	cfg_cg_enable,
	cfg_cg_idle_count,
	wakeup,
	clk_out,
	gating
);
	parameter signed [31:0] IDLE_CNTR_WIDTH = 4;
	input wire clk_in;
	input wire aresetn;
	input wire cfg_cg_enable;
	input wire [IDLE_CNTR_WIDTH - 1:0] cfg_cg_idle_count;
	input wire wakeup;
	output wire clk_out;
	output wire gating;
	localparam signed [31:0] N = IDLE_CNTR_WIDTH;
	reg [N - 1:0] r_idle_counter;
	always @(posedge clk_in or negedge aresetn)
		if (!aresetn)
			r_idle_counter <= cfg_cg_idle_count;
		else if (wakeup || !cfg_cg_enable)
			r_idle_counter <= cfg_cg_idle_count;
		else if (r_idle_counter != 'h0)
			r_idle_counter <= r_idle_counter - 1'b1;
	wire w_gate_enable = (cfg_cg_enable && !wakeup) && (r_idle_counter == 'h0);
	icg u_icg(
		.clk(clk_in),
		.en(~w_gate_enable),
		.gclk(clk_out)
	);
	assign gating = w_gate_enable;
endmodule
module amba_clock_gate_ctrl (
	clk_in,
	aresetn,
	cfg_cg_enable,
	cfg_cg_idle_count,
	user_valid,
	axi_valid,
	clk_out,
	gating,
	idle
);
	parameter signed [31:0] CG_IDLE_COUNT_WIDTH = 4;
	parameter signed [31:0] ICW = CG_IDLE_COUNT_WIDTH;
	input wire clk_in;
	input wire aresetn;
	input wire cfg_cg_enable;
	input wire [ICW - 1:0] cfg_cg_idle_count;
	input wire user_valid;
	input wire axi_valid;
	output wire clk_out;
	output wire gating;
	output wire idle;
	reg r_wakeup;
	always @(posedge clk_in or negedge aresetn)
		if (!aresetn)
			r_wakeup <= 'h1;
		else
			r_wakeup <= user_valid || axi_valid;
	assign idle = ~r_wakeup;
	clock_gate_ctrl #(.IDLE_CNTR_WIDTH(ICW)) u_clock_gate_ctrl(
		.clk_in(clk_in),
		.aresetn(aresetn),
		.cfg_cg_enable(cfg_cg_enable),
		.cfg_cg_idle_count(cfg_cg_idle_count),
		.wakeup(r_wakeup),
		.clk_out(clk_out),
		.gating(gating)
	);
endmodule
module wb4_slave (
	clk,
	aresetn,
	s_wb_CYC,
	s_wb_STB,
	s_wb_WE,
	s_wb_ADR,
	s_wb_DAT_W,
	s_wb_SEL,
	s_wb_STALL,
	s_wb_ACK,
	s_wb_ERR,
	s_wb_RTY,
	s_wb_DAT_R,
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
	parameter signed [31:0] CMD_DEPTH = 2;
	parameter signed [31:0] RSP_DEPTH = 2;
	parameter signed [31:0] MAX_OUTSTANDING = 16;
	parameter signed [31:0] CLASSIC = 0;
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
	input wire s_wb_CYC;
	input wire s_wb_STB;
	input wire s_wb_WE;
	input wire [AW - 1:0] s_wb_ADR;
	input wire [DW - 1:0] s_wb_DAT_W;
	input wire [SW - 1:0] s_wb_SEL;
	output wire s_wb_STALL;
	output reg s_wb_ACK;
	output reg s_wb_ERR;
	output reg s_wb_RTY;
	output reg [DW - 1:0] s_wb_DAT_R;
	output wire cmd_valid;
	input wire cmd_ready;
	output wire cmd_we;
	output wire [AW - 1:0] cmd_adr;
	output wire [DW - 1:0] cmd_dat;
	output wire [SW - 1:0] cmd_sel;
	input wire rsp_valid;
	output wire rsp_ready;
	input wire [STW - 1:0] rsp_status;
	input wire [DW - 1:0] rsp_dat;
	localparam signed [31:0] OW = $clog2(MAX_OUTSTANDING + 1);
	localparam signed [31:0] ABW = OW + 1;
	localparam signed [31:0] AB_MAX = (1 << ABW) - 1;
	reg [OW - 1:0] r_outstanding;
	reg [ABW - 1:0] r_abandoned;
	wire w_drop_abandoned;
	wire w_accept;
	wire w_term;
	wire w_orphan;
	wire w_cmd_room;
	wire [CPW - 1:0] w_cmd_data_in;
	wire [CPW - 1:0] r_cmd_data_out;
	assign w_cmd_data_in = {s_wb_WE, s_wb_ADR, s_wb_DAT_W, s_wb_SEL};
	assign {cmd_we, cmd_adr, cmd_dat, cmd_sel} = r_cmd_data_out;
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		if (CLASSIC != 0) begin : g_classic
			assign s_wb_STALL = 1'b0;
			assign w_accept = (((s_wb_CYC && s_wb_STB) && w_cmd_room) && (r_outstanding == {OW {1'sb0}})) && !((s_wb_ACK || s_wb_ERR) || s_wb_RTY);
		end
		else begin : g_pipelined
			assign s_wb_STALL = !w_cmd_room || (sv2v_cast_32(r_outstanding) >= MAX_OUTSTANDING);
			assign w_accept = (s_wb_CYC && s_wb_STB) && !s_wb_STALL;
		end
	endgenerate
	gaxi_skid_buffer #(
		.DATA_WIDTH(CPW),
		.DEPTH(CMD_DEPTH)
	) u_cmd_skid(
		.axi_aclk(clk),
		.axi_aresetn(aresetn),
		.wr_valid(w_accept),
		.wr_ready(w_cmd_room),
		.wr_data(w_cmd_data_in),
		.rd_valid(cmd_valid),
		.rd_ready(cmd_ready),
		.rd_data(r_cmd_data_out),
		.count(),
		.rd_count()
	);
	wire r_rsp_valid;
	wire w_rsp_pop;
	wire [RPW - 1:0] w_rsp_data_in;
	wire [RPW - 1:0] r_rsp_data_out;
	wire [STW - 1:0] r_rsp_status;
	wire [DW - 1:0] r_rsp_dat;
	assign w_rsp_data_in = {rsp_status, rsp_dat};
	assign {r_rsp_status, r_rsp_dat} = r_rsp_data_out;
	gaxi_skid_buffer #(
		.DATA_WIDTH(RPW),
		.DEPTH(RSP_DEPTH)
	) u_rsp_skid(
		.axi_aclk(clk),
		.axi_aresetn(aresetn),
		.wr_valid(rsp_valid),
		.wr_ready(rsp_ready),
		.wr_data(w_rsp_data_in),
		.rd_valid(r_rsp_valid),
		.rd_ready(w_rsp_pop),
		.rd_data(r_rsp_data_out),
		.count(),
		.rd_count()
	);
	assign w_drop_abandoned = r_rsp_valid && (r_abandoned != {ABW {1'sb0}});
	assign w_term = ((r_rsp_valid && (r_outstanding != {OW {1'sb0}})) && s_wb_CYC) && (r_abandoned == {ABW {1'sb0}});
	assign w_orphan = r_rsp_valid && ((r_outstanding == {OW {1'sb0}}) || w_drop_abandoned);
	assign w_rsp_pop = w_term || w_orphan;
	function automatic [1:0] sv2v_cast_1AA03;
		input reg [1:0] inp;
		sv2v_cast_1AA03 = inp;
	endfunction
	function automatic signed [ABW - 1:0] sv2v_cast_5B7D2_signed;
		input reg signed [ABW - 1:0] inp;
		sv2v_cast_5B7D2_signed = inp;
	endfunction
	function automatic [ABW - 1:0] sv2v_cast_5B7D2;
		input reg [ABW - 1:0] inp;
		sv2v_cast_5B7D2 = inp;
	endfunction
	function automatic [OW - 1:0] sv2v_cast_0975F;
		input reg [OW - 1:0] inp;
		sv2v_cast_0975F = inp;
	endfunction
	always @(posedge clk or negedge aresetn)
		if (!aresetn) begin
			r_outstanding <= 1'sb0;
			r_abandoned <= 1'sb0;
			s_wb_ACK <= 1'b0;
			s_wb_ERR <= 1'b0;
			s_wb_RTY <= 1'b0;
			s_wb_DAT_R <= 1'sb0;
		end
		else begin
			s_wb_ACK <= w_term && (r_rsp_status == sv2v_cast_1AA03(2'b00));
			s_wb_ERR <= w_term && (r_rsp_status == sv2v_cast_1AA03(2'b01));
			s_wb_RTY <= w_term && (r_rsp_status == sv2v_cast_1AA03(2'b10));
			if (w_term)
				s_wb_DAT_R <= r_rsp_dat;
			if (!s_wb_CYC) begin
				r_outstanding <= 1'sb0;
				if (((sv2v_cast_32(r_abandoned) + sv2v_cast_32(r_outstanding)) - sv2v_cast_32(w_drop_abandoned)) > AB_MAX)
					r_abandoned <= sv2v_cast_5B7D2_signed(AB_MAX);
				else
					r_abandoned <= (r_abandoned + sv2v_cast_5B7D2(r_outstanding)) - sv2v_cast_5B7D2(w_drop_abandoned);
			end
			else begin
				r_outstanding <= (r_outstanding + sv2v_cast_0975F(w_accept)) - sv2v_cast_0975F(w_term);
				r_abandoned <= r_abandoned - sv2v_cast_5B7D2(w_drop_abandoned);
			end
		end
	reg f_past_valid;
	initial f_past_valid = 1'b0;
	always @(posedge clk) f_past_valid <= 1'b1;
	always @(posedge clk)
		if ((f_past_valid && aresetn) && $past(aresetn)) begin
			assert ($onehot0({s_wb_ACK, s_wb_ERR, s_wb_RTY})) ;
			if ((s_wb_ACK || s_wb_ERR) || s_wb_RTY)
				assert ($past(s_wb_CYC) && ($past(r_outstanding) != 0)) ;
			assert (sv2v_cast_32(r_outstanding) <= MAX_OUTSTANDING) ;
			assert (!w_accept || w_cmd_room) ;
			assert (!w_term || (r_abandoned == 0)) ;
			if ($past(!s_wb_CYC) && ($past(r_outstanding) != 0))
				assert (r_abandoned != 0) ;
			if (CLASSIC != 0) begin
				assert (r_outstanding <= 1) ;
				assert (!s_wb_STALL) ;
			end
		end
endmodule
module wb4_slave_cg (
	clk,
	aresetn,
	cfg_cg_enable,
	cfg_cg_idle_count,
	s_wb_CYC,
	s_wb_STB,
	s_wb_WE,
	s_wb_ADR,
	s_wb_DAT_W,
	s_wb_SEL,
	s_wb_STALL,
	s_wb_ACK,
	s_wb_ERR,
	s_wb_RTY,
	s_wb_DAT_R,
	cmd_valid,
	cmd_ready,
	cmd_we,
	cmd_adr,
	cmd_dat,
	cmd_sel,
	rsp_valid,
	rsp_ready,
	rsp_status,
	rsp_dat,
	cg_gating,
	cg_idle
);
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] CMD_DEPTH = 2;
	parameter signed [31:0] RSP_DEPTH = 2;
	parameter signed [31:0] MAX_OUTSTANDING = 16;
	parameter signed [31:0] CLASSIC = 0;
	parameter signed [31:0] CG_IDLE_COUNT_WIDTH = 4;
	parameter signed [31:0] SEL_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = SEL_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_STATUS_WIDTH = 2;
	parameter signed [31:0] STW = wb4_pkg_WB4_STATUS_WIDTH;
	parameter signed [31:0] ICW = CG_IDLE_COUNT_WIDTH;
	input wire clk;
	input wire aresetn;
	input wire cfg_cg_enable;
	input wire [ICW - 1:0] cfg_cg_idle_count;
	input wire s_wb_CYC;
	input wire s_wb_STB;
	input wire s_wb_WE;
	input wire [AW - 1:0] s_wb_ADR;
	input wire [DW - 1:0] s_wb_DAT_W;
	input wire [SW - 1:0] s_wb_SEL;
	output wire s_wb_STALL;
	output wire s_wb_ACK;
	output wire s_wb_ERR;
	output wire s_wb_RTY;
	output wire [DW - 1:0] s_wb_DAT_R;
	output wire cmd_valid;
	input wire cmd_ready;
	output wire cmd_we;
	output wire [AW - 1:0] cmd_adr;
	output wire [DW - 1:0] cmd_dat;
	output wire [SW - 1:0] cmd_sel;
	input wire rsp_valid;
	output wire rsp_ready;
	input wire [STW - 1:0] rsp_status;
	input wire [DW - 1:0] rsp_dat;
	output wire cg_gating;
	output wire cg_idle;
	wire w_wakeup;
	wire gated_clk;
	wire w_cmd_valid;
	wire w_rsp_ready;
	wire w_stall;
	assign w_wakeup = (s_wb_CYC || rsp_valid) || w_cmd_valid;
	amba_clock_gate_ctrl #(.CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)) u_clock_gate_ctrl(
		.clk_in(clk),
		.aresetn(aresetn),
		.cfg_cg_enable(cfg_cg_enable),
		.cfg_cg_idle_count(cfg_cg_idle_count),
		.user_valid(w_wakeup),
		.axi_valid(1'b0),
		.clk_out(gated_clk),
		.gating(cg_gating),
		.idle(cg_idle)
	);
	wb4_slave #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.DATA_WIDTH(DATA_WIDTH),
		.CMD_DEPTH(CMD_DEPTH),
		.RSP_DEPTH(RSP_DEPTH),
		.MAX_OUTSTANDING(MAX_OUTSTANDING),
		.CLASSIC(CLASSIC),
		.SEL_WIDTH(SEL_WIDTH)
	) u_wb4_slave(
		.clk(gated_clk),
		.aresetn(aresetn),
		.s_wb_CYC(s_wb_CYC),
		.s_wb_STB(s_wb_STB),
		.s_wb_WE(s_wb_WE),
		.s_wb_ADR(s_wb_ADR),
		.s_wb_DAT_W(s_wb_DAT_W),
		.s_wb_SEL(s_wb_SEL),
		.s_wb_STALL(w_stall),
		.s_wb_ACK(s_wb_ACK),
		.s_wb_ERR(s_wb_ERR),
		.s_wb_RTY(s_wb_RTY),
		.s_wb_DAT_R(s_wb_DAT_R),
		.cmd_valid(w_cmd_valid),
		.cmd_ready(cmd_ready),
		.cmd_we(cmd_we),
		.cmd_adr(cmd_adr),
		.cmd_dat(cmd_dat),
		.cmd_sel(cmd_sel),
		.rsp_valid(rsp_valid),
		.rsp_ready(w_rsp_ready),
		.rsp_status(rsp_status),
		.rsp_dat(rsp_dat)
	);
	assign cmd_valid = w_cmd_valid && !cg_gating;
	assign rsp_ready = w_rsp_ready && !cg_gating;
	assign s_wb_STALL = w_stall || cg_gating;
endmodule
