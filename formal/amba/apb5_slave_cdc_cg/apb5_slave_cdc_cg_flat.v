module icg (
	en,
	clk,
	gclk
);
	reg _sv2v_0;
	input wire en;
	input wire clk;
	output wire gclk;
	reg en_out;
	always @(*) begin
		if (_sv2v_0)
			;
		if (!clk)
			en_out = en;
	end
	assign gclk = en_out && clk;
	initial _sv2v_0 = 0;
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
module glitch_free_n_dff_arn (
	clk,
	rst_n,
	d,
	q
);
	parameter signed [31:0] FLOP_COUNT = 3;
	parameter signed [31:0] WIDTH = 4;
	input wire clk;
	input wire rst_n;
	input wire [WIDTH - 1:0] d;
	output reg [WIDTH - 1:0] q;
	localparam signed [31:0] FC = FLOP_COUNT;
	localparam signed [31:0] DW = WIDTH;
	reg [(FC * WIDTH) - 1:0] r_q_array;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_q_array <= {FC {{DW {1'b0}}}};
		else begin
			r_q_array[0+:WIDTH] <= d;
			begin : sv2v_autoblock_1
				reg signed [31:0] i;
				for (i = 1; i < FC; i = i + 1)
					r_q_array[i * WIDTH+:WIDTH] <= r_q_array[(i - 1) * WIDTH+:WIDTH];
			end
		end
	wire [WIDTH:1] sv2v_tmp_60F54;
	assign sv2v_tmp_60F54 = r_q_array[(FC - 1) * WIDTH+:WIDTH];
	always @(*) q = sv2v_tmp_60F54;
	wire [(DW * FC) - 1:0] flat_r_q;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < FC; _gv_i_1 = _gv_i_1 + 1) begin : gen_flatten_memory
			localparam i = _gv_i_1;
			assign flat_r_q[i * DW+:DW] = r_q_array[i * WIDTH+:WIDTH];
		end
	endgenerate
endmodule
module cdc_synchronizer (
	clk,
	rst_n,
	async_in,
	sync_out
);
	parameter signed [31:0] WIDTH = 1;
	parameter signed [31:0] FLOP_COUNT = 3;
	input wire clk;
	input wire rst_n;
	input wire [WIDTH - 1:0] async_in;
	output wire [WIDTH - 1:0] sync_out;
	glitch_free_n_dff_arn #(
		.FLOP_COUNT(FLOP_COUNT),
		.WIDTH(WIDTH)
	) u_sync(
		.clk(clk),
		.rst_n(rst_n),
		.d(async_in),
		.q(sync_out)
	);
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
module apb5_slave (
	pclk,
	presetn,
	s_apb_PSEL,
	s_apb_PENABLE,
	s_apb_PREADY,
	s_apb_PADDR,
	s_apb_PWRITE,
	s_apb_PWDATA,
	s_apb_PSTRB,
	s_apb_PPROT,
	s_apb_PAUSER,
	s_apb_PWUSER,
	s_apb_PRDATA,
	s_apb_PSLVERR,
	s_apb_PWAKEUP,
	s_apb_PRUSER,
	s_apb_PBUSER,
	s_apb_PWDATAPARITY,
	s_apb_PADDRPARITY,
	s_apb_PCTRLPARITY,
	s_apb_PRDATAPARITY,
	s_apb_PREADYPARITY,
	s_apb_PSLVERRPARITY,
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
	rsp_pruser,
	rsp_pbuser,
	wakeup_request,
	parity_error_wdata,
	parity_error_ctrl
);
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] PROT_WIDTH = 3;
	parameter signed [31:0] AUSER_WIDTH = 4;
	parameter signed [31:0] WUSER_WIDTH = 4;
	parameter signed [31:0] RUSER_WIDTH = 4;
	parameter signed [31:0] BUSER_WIDTH = 4;
	parameter signed [31:0] DEPTH = 2;
	parameter [0:0] ENABLE_PARITY = 0;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] SW = STRB_WIDTH;
	parameter signed [31:0] PW = PROT_WIDTH;
	parameter signed [31:0] AUW = AUSER_WIDTH;
	parameter signed [31:0] WUW = WUSER_WIDTH;
	parameter signed [31:0] RUW = RUSER_WIDTH;
	parameter signed [31:0] BUW = BUSER_WIDTH;
	parameter signed [31:0] CPW = (((((AW + DW) + SW) + PW) + AUW) + WUW) + 1;
	parameter signed [31:0] RPW = ((DW + RUW) + BUW) + 1;
	input wire pclk;
	input wire presetn;
	input wire s_apb_PSEL;
	input wire s_apb_PENABLE;
	output reg s_apb_PREADY;
	input wire [AW - 1:0] s_apb_PADDR;
	input wire s_apb_PWRITE;
	input wire [DW - 1:0] s_apb_PWDATA;
	input wire [SW - 1:0] s_apb_PSTRB;
	input wire [PW - 1:0] s_apb_PPROT;
	input wire [AUW - 1:0] s_apb_PAUSER;
	input wire [WUW - 1:0] s_apb_PWUSER;
	output reg [DW - 1:0] s_apb_PRDATA;
	output reg s_apb_PSLVERR;
	output wire s_apb_PWAKEUP;
	output reg [RUW - 1:0] s_apb_PRUSER;
	output reg [BUW - 1:0] s_apb_PBUSER;
	input wire [SW - 1:0] s_apb_PWDATAPARITY;
	input wire s_apb_PADDRPARITY;
	input wire s_apb_PCTRLPARITY;
	output wire [SW - 1:0] s_apb_PRDATAPARITY;
	output wire s_apb_PREADYPARITY;
	output wire s_apb_PSLVERRPARITY;
	output wire cmd_valid;
	input wire cmd_ready;
	output wire cmd_pwrite;
	output wire [AW - 1:0] cmd_paddr;
	output wire [DW - 1:0] cmd_pwdata;
	output wire [SW - 1:0] cmd_pstrb;
	output wire [PW - 1:0] cmd_pprot;
	output wire [AUW - 1:0] cmd_pauser;
	output wire [WUW - 1:0] cmd_pwuser;
	input wire rsp_valid;
	output wire rsp_ready;
	input wire [DW - 1:0] rsp_prdata;
	input wire rsp_pslverr;
	input wire [RUW - 1:0] rsp_pruser;
	input wire [BUW - 1:0] rsp_pbuser;
	input wire wakeup_request;
	output wire parity_error_wdata;
	output wire parity_error_ctrl;
	reg r_cmd_valid;
	wire r_cmd_ready;
	wire [CPW - 1:0] r_cmd_data_in;
	wire [CPW - 1:0] r_cmd_data_out;
	wire [3:0] r_cmd_count;
	assign r_cmd_data_in = {s_apb_PWRITE, s_apb_PPROT, s_apb_PSTRB, s_apb_PADDR, s_apb_PWDATA, s_apb_PAUSER, s_apb_PWUSER};
	assign {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata, cmd_pauser, cmd_pwuser} = r_cmd_data_out;
	gaxi_skid_buffer #(
		.DEPTH(DEPTH),
		.DATA_WIDTH(CPW)
	) cmd_skid_buffer_inst(
		.axi_aclk(pclk),
		.axi_aresetn(presetn),
		.wr_valid(r_cmd_valid),
		.wr_ready(r_cmd_ready),
		.wr_data(r_cmd_data_in),
		.rd_valid(cmd_valid),
		.rd_ready(cmd_ready),
		.rd_data(r_cmd_data_out),
		.count(r_cmd_count),
		.rd_count()
	);
	wire r_rsp_valid;
	reg r_rsp_ready;
	wire [RPW - 1:0] r_rsp_data_in;
	wire [RPW - 1:0] r_rsp_data_out;
	wire [DW - 1:0] r_rsp_prdata;
	wire r_rsp_pslverr;
	wire [RUW - 1:0] r_rsp_pruser;
	wire [BUW - 1:0] r_rsp_pbuser;
	wire [3:0] r_rsp_count;
	assign {r_rsp_pslverr, r_rsp_prdata, r_rsp_pruser, r_rsp_pbuser} = r_rsp_data_out;
	assign r_rsp_data_in = {rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser};
	gaxi_skid_buffer #(
		.DEPTH(DEPTH),
		.DATA_WIDTH(RPW)
	) resp_skid_buffer_inst(
		.axi_aclk(pclk),
		.axi_aresetn(presetn),
		.wr_valid(rsp_valid),
		.wr_ready(rsp_ready),
		.wr_data(r_rsp_data_in),
		.rd_valid(r_rsp_valid),
		.rd_ready(r_rsp_ready),
		.rd_data(r_rsp_data_out),
		.count(r_rsp_count),
		.rd_count()
	);
	reg [2:0] r_apb_state;
	reg r_penable_prev;
	reg r_wakeup;
	always @(posedge pclk or negedge presetn)
		if (!presetn)
			r_wakeup <= 1'b0;
		else
			r_wakeup <= wakeup_request;
	assign s_apb_PWAKEUP = r_wakeup;
	generate
		if (ENABLE_PARITY) begin : gen_parity
			wire [SW - 1:0] w_expected_wdata_parity;
			genvar _gv_i_2;
			for (_gv_i_2 = 0; _gv_i_2 < SW; _gv_i_2 = _gv_i_2 + 1) begin : gen_wdata_parity_check
				localparam i = _gv_i_2;
				assign w_expected_wdata_parity[i] = ^s_apb_PWDATA[i * 8+:8];
			end
			assign parity_error_wdata = (s_apb_PSEL && s_apb_PENABLE ? w_expected_wdata_parity != s_apb_PWDATAPARITY : 1'b0);
			wire w_expected_addr_parity;
			wire w_expected_ctrl_parity;
			assign w_expected_addr_parity = ^s_apb_PADDR;
			assign w_expected_ctrl_parity = ^{s_apb_PWRITE, s_apb_PSTRB, s_apb_PPROT};
			assign parity_error_ctrl = (s_apb_PSEL && s_apb_PENABLE ? (w_expected_addr_parity != s_apb_PADDRPARITY) || (w_expected_ctrl_parity != s_apb_PCTRLPARITY) : 1'b0);
			genvar _gv_i_3;
			for (_gv_i_3 = 0; _gv_i_3 < SW; _gv_i_3 = _gv_i_3 + 1) begin : gen_rdata_parity
				localparam i = _gv_i_3;
				assign s_apb_PRDATAPARITY[i] = ^s_apb_PRDATA[i * 8+:8];
			end
			assign s_apb_PREADYPARITY = ^s_apb_PREADY;
			assign s_apb_PSLVERRPARITY = ^s_apb_PSLVERR;
		end
		else begin : gen_no_parity
			assign parity_error_wdata = 1'b0;
			assign parity_error_ctrl = 1'b0;
			assign s_apb_PRDATAPARITY = 1'sb0;
			assign s_apb_PREADYPARITY = 1'b0;
			assign s_apb_PSLVERRPARITY = 1'b0;
		end
	endgenerate
	always @(posedge pclk or negedge presetn)
		if (!presetn) begin
			r_apb_state <= 3'b001;
			s_apb_PREADY <= 1'b0;
			s_apb_PSLVERR <= 1'b0;
			s_apb_PRDATA <= 1'sb0;
			s_apb_PRUSER <= 1'sb0;
			s_apb_PBUSER <= 1'sb0;
			r_cmd_valid <= 1'b0;
			r_rsp_ready <= 1'b0;
			r_penable_prev <= 1'b0;
		end
		else begin
			r_apb_state <= r_apb_state;
			s_apb_PREADY <= 1'b0;
			s_apb_PSLVERR <= 1'b0;
			r_cmd_valid <= 1'b0;
			r_rsp_ready <= 1'b0;
			r_penable_prev <= s_apb_PENABLE;
			casez (r_apb_state)
				3'b001: begin
					if (r_rsp_valid) begin
						r_rsp_ready <= 1'b1;
						$display("%t %m WARNING: orphan APB response discarded (prdata=0x%0h pslverr=%0b) -- no command outstanding. Check for duplicate backend responses or an independently-reset CDC.", $time, r_rsp_prdata, r_rsp_pslverr);
					end
					if (((s_apb_PSEL && s_apb_PENABLE) && !r_penable_prev) && r_cmd_ready) begin
						r_cmd_valid <= 1'b1;
						r_apb_state <= 3'b010;
					end
				end
				3'b010:
					if (r_rsp_valid) begin
						s_apb_PREADY <= 1'b1;
						s_apb_PRDATA <= r_rsp_prdata;
						s_apb_PSLVERR <= r_rsp_pslverr;
						s_apb_PRUSER <= r_rsp_pruser;
						s_apb_PBUSER <= r_rsp_pbuser;
						r_rsp_ready <= 1'b1;
						r_apb_state <= 3'b100;
					end
				3'b100: r_apb_state <= 3'b001;
				default: r_apb_state <= 3'b001;
			endcase
		end
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
module counter_johnson (
	clk,
	rst_n,
	enable,
	counter_gray
);
	parameter signed [31:0] WIDTH = 4;
	input wire clk;
	input wire rst_n;
	input wire enable;
	output reg [WIDTH - 1:0] counter_gray;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			counter_gray <= {WIDTH {1'b0}};
		else if (enable)
			counter_gray <= {counter_gray[WIDTH - 2:0], ~counter_gray[WIDTH - 1]};
endmodule
module counter_bingray (
	clk,
	rst_n,
	enable,
	counter_bin,
	counter_bin_next,
	counter_gray
);
	parameter signed [31:0] WIDTH = 4;
	input wire clk;
	input wire rst_n;
	input wire enable;
	output reg [WIDTH - 1:0] counter_bin;
	output wire [WIDTH - 1:0] counter_bin_next;
	output reg [WIDTH - 1:0] counter_gray;
	wire [WIDTH - 1:0] w_counter_bin;
	wire [WIDTH - 1:0] w_counter_gray;
	assign w_counter_bin = (enable ? counter_bin + 1 : counter_bin);
	assign w_counter_gray = w_counter_bin ^ (w_counter_bin >> 1);
	assign counter_bin_next = w_counter_bin;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			counter_bin <= 'b0;
			counter_gray <= 'b0;
		end
		else begin
			counter_bin <= w_counter_bin;
			counter_gray <= w_counter_gray;
		end
endmodule
module find_last_set (
	data,
	index
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 32;
	input wire [WIDTH - 1:0] data;
	output reg [$clog2(WIDTH) - 1:0] index;
	localparam signed [31:0] N = $clog2(WIDTH);
	reg w_found;
	always @(*) begin
		if (_sv2v_0)
			;
		index = {N {1'b0}};
		w_found = 1'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = WIDTH - 1; i >= 0; i = i - 1)
				if (data[i] && !w_found) begin
					index = i[N - 1:0];
					w_found = 1'b1;
				end
		end
	end
	initial _sv2v_0 = 0;
endmodule
module find_first_set (
	data,
	index
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 32;
	input wire [WIDTH - 1:0] data;
	output reg [$clog2(WIDTH) - 1:0] index;
	localparam signed [31:0] N = $clog2(WIDTH);
	reg w_found;
	always @(*) begin
		if (_sv2v_0)
			;
		index = {N {1'b0}};
		w_found = 1'b0;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < WIDTH; i = i + 1)
				if (data[i] && !w_found) begin
					index = i[N - 1:0];
					w_found = 1'b1;
				end
		end
	end
	initial _sv2v_0 = 0;
endmodule
module leading_one_trailing_one (
	data,
	leadingone,
	leadingone_vector,
	trailingone,
	trailingone_vector,
	all_zeroes,
	all_ones,
	valid
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 8;
	input wire [WIDTH - 1:0] data;
	output wire [$clog2(WIDTH) - 1:0] leadingone;
	output reg [WIDTH - 1:0] leadingone_vector;
	output wire [$clog2(WIDTH) - 1:0] trailingone;
	output reg [WIDTH - 1:0] trailingone_vector;
	output wire all_zeroes;
	output wire all_ones;
	output wire valid;
	localparam signed [31:0] N = $clog2(WIDTH);
	find_last_set #(.WIDTH(WIDTH)) u_find_last_set(
		.data(data),
		.index(leadingone)
	);
	find_first_set #(.WIDTH(WIDTH)) u_find_first_set(
		.data(data),
		.index(trailingone)
	);
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		leadingone_vector = 1'sb0;
		trailingone_vector = 1'sb0;
		if (|data) begin
			if (sv2v_cast_32_signed(leadingone) < WIDTH)
				leadingone_vector[leadingone] = 1'b1;
			if (sv2v_cast_32_signed(trailingone) < WIDTH)
				trailingone_vector[trailingone] = 1'b1;
		end
	end
	assign all_ones = &data;
	assign all_zeroes = ~(|data);
	assign valid = |data;
	initial _sv2v_0 = 0;
endmodule
module johnson2bin (
	clk,
	rst_n,
	gray,
	binary
);
	reg _sv2v_0;
	parameter signed [31:0] JCW = 10;
	parameter signed [31:0] WIDTH = 4;
	input wire clk;
	input wire rst_n;
	input wire [JCW - 1:0] gray;
	output wire [WIDTH - 1:0] binary;
	localparam signed [31:0] N = $clog2(JCW);
	localparam signed [31:0] PAD_WIDTH = (WIDTH > (N + 1) ? (WIDTH - N) - 1 : 0);
	wire [N - 1:0] w_leading_one;
	wire [N - 1:0] w_trailing_one;
	reg [WIDTH - 1:0] w_binary;
	wire w_all_zeroes;
	wire w_all_ones;
	wire w_valid;
	leading_one_trailing_one #(.WIDTH(JCW)) u_leading_one_trailing_one(
		.data(gray),
		.leadingone(w_leading_one),
		.leadingone_vector(),
		.trailingone(w_trailing_one),
		.trailingone_vector(),
		.all_zeroes(w_all_zeroes),
		.all_ones(w_all_ones),
		.valid(w_valid)
	);
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_all_zeroes || w_all_ones)
			w_binary = {WIDTH {1'b0}};
		else if (gray[JCW - 1])
			w_binary = {{WIDTH - N {1'b0}}, w_trailing_one};
		else
			w_binary = {{WIDTH - N {1'b0}}, w_leading_one + 1'b1};
	end
	assign binary[WIDTH - 1] = gray[JCW - 1];
	assign binary[WIDTH - 2:0] = w_binary[WIDTH - 2:0];
	initial _sv2v_0 = 0;
endmodule
module gray2bin (
	gray,
	binary
);
	parameter signed [31:0] WIDTH = 4;
	input wire [WIDTH - 1:0] gray;
	output wire [WIDTH - 1:0] binary;
	genvar _gv_i_4;
	generate
		for (_gv_i_4 = 0; _gv_i_4 < WIDTH; _gv_i_4 = _gv_i_4 + 1) begin : gen_gray_to_bin
			localparam i = _gv_i_4;
			assign binary[i] = ^(gray >> i);
		end
	endgenerate
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
	parameter signed [31:0] DEPTH = 8;
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
			always @(posedge rd_clk or negedge rd_rst_n)
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
module gaxi_fifo_async (
	axi_wr_aclk,
	axi_wr_aresetn,
	axi_rd_aclk,
	axi_rd_aresetn,
	wr_valid,
	wr_ready,
	wr_data,
	rd_ready,
	rd_valid,
	rd_data
);
	parameter signed [31:0] MEM_STYLE = 32'sd0;
	parameter signed [31:0] REGISTERED = 0;
	parameter signed [31:0] DATA_WIDTH = 8;
	parameter signed [31:0] DEPTH = 16;
	parameter signed [31:0] USE_JOHNSON = 0;
	parameter signed [31:0] N_FLOP_CROSS = 2;
	parameter signed [31:0] ALMOST_WR_MARGIN = 1;
	parameter signed [31:0] ALMOST_RD_MARGIN = 1;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] D = DEPTH;
	parameter signed [31:0] AW = $clog2(DEPTH);
	parameter signed [31:0] JCW = D;
	parameter signed [31:0] N = N_FLOP_CROSS;
	input wire axi_wr_aclk;
	input wire axi_wr_aresetn;
	input wire axi_rd_aclk;
	input wire axi_rd_aresetn;
	input wire wr_valid;
	output wire wr_ready;
	input wire [DW - 1:0] wr_data;
	input wire rd_ready;
	output wire rd_valid;
	output wire [DW - 1:0] rd_data;
	wire [AW - 1:0] r_wr_addr;
	wire [AW - 1:0] r_rd_addr;
	localparam signed [31:0] PTRW = (USE_JOHNSON != 0 ? JCW : AW + 1);
	generate
		if ((USE_JOHNSON == 0) && ((DEPTH & (DEPTH - 1)) != 0)) begin : g_bad_depth
			initial $display("Error [elaboration] /mnt/data/github/RTLDesignSherpa/rtl/cdc/gaxi_fifo_async.sv:83:9 - gaxi_fifo_async.g_bad_depth\n msg: ", "gaxi_fifo_async: USE_JOHNSON=0 (Gray) requires a power-of-2 DEPTH, got %0d. Set USE_JOHNSON=1 for arbitrary depths.", DEPTH);
		end
	endgenerate
	wire [PTRW - 1:0] r_wr_ptr_gray;
	wire [PTRW - 1:0] r_wdom_rd_ptr_gray;
	wire [PTRW - 1:0] r_rd_ptr_gray;
	wire [PTRW - 1:0] r_rdom_wr_ptr_gray;
	wire [AW:0] r_wr_ptr_bin;
	wire [AW:0] w_wdom_rd_ptr_bin;
	wire [AW:0] r_rd_ptr_bin;
	wire [AW:0] w_rdom_wr_ptr_bin;
	wire [AW:0] w_wr_ptr_bin_next;
	wire [AW:0] w_rd_ptr_bin_next;
	wire r_wr_full;
	wire r_wr_almost_full;
	wire r_rd_empty;
	wire r_rd_almost_empty;
	wire w_write;
	wire w_read;
	wire [AW:0] w_count;
	assign w_write = wr_valid && wr_ready;
	assign w_read = rd_valid && rd_ready;
	generate
		if (USE_JOHNSON != 0) begin : g_ptr_johnson
			counter_bin #(
				.MAX(D),
				.WIDTH(AW + 1)
			) wr_ptr_counter_bin(
				.clk(axi_wr_aclk),
				.rst_n(axi_wr_aresetn),
				.enable(w_write && !r_wr_full),
				.counter_bin_next(w_wr_ptr_bin_next),
				.counter_bin_curr(r_wr_ptr_bin)
			);
			counter_bin #(
				.MAX(D),
				.WIDTH(AW + 1)
			) rd_ptr_counter_bin(
				.clk(axi_rd_aclk),
				.rst_n(axi_rd_aresetn),
				.enable(w_read && !r_rd_empty),
				.counter_bin_next(w_rd_ptr_bin_next),
				.counter_bin_curr(r_rd_ptr_bin)
			);
			counter_johnson #(.WIDTH(JCW)) wr_ptr_counter_gray(
				.clk(axi_wr_aclk),
				.rst_n(axi_wr_aresetn),
				.enable(w_write && !r_wr_full),
				.counter_gray(r_wr_ptr_gray)
			);
			counter_johnson #(.WIDTH(JCW)) rd_ptr_counter_gray(
				.clk(axi_rd_aclk),
				.rst_n(axi_rd_aresetn),
				.enable(w_read && !r_rd_empty),
				.counter_gray(r_rd_ptr_gray)
			);
		end
		else begin : g_ptr_gray
			counter_bingray #(.WIDTH(AW + 1)) wr_ptr_counter_bingray(
				.clk(axi_wr_aclk),
				.rst_n(axi_wr_aresetn),
				.enable(w_write && !r_wr_full),
				.counter_bin(r_wr_ptr_bin),
				.counter_bin_next(w_wr_ptr_bin_next),
				.counter_gray(r_wr_ptr_gray)
			);
			counter_bingray #(.WIDTH(AW + 1)) rd_ptr_counter_bingray(
				.clk(axi_rd_aclk),
				.rst_n(axi_rd_aresetn),
				.enable(w_read && !r_rd_empty),
				.counter_bin(r_rd_ptr_bin),
				.counter_bin_next(w_rd_ptr_bin_next),
				.counter_gray(r_rd_ptr_gray)
			);
		end
	endgenerate
	glitch_free_n_dff_arn #(
		.FLOP_COUNT(N),
		.WIDTH(PTRW)
	) rd_ptr_gray_cross_inst(
		.q(r_wdom_rd_ptr_gray),
		.d(r_rd_ptr_gray),
		.clk(axi_wr_aclk),
		.rst_n(axi_wr_aresetn)
	);
	glitch_free_n_dff_arn #(
		.FLOP_COUNT(N),
		.WIDTH(PTRW)
	) wr_ptr_gray_cross_inst(
		.q(r_rdom_wr_ptr_gray),
		.d(r_wr_ptr_gray),
		.clk(axi_rd_aclk),
		.rst_n(axi_rd_aresetn)
	);
	generate
		if (USE_JOHNSON != 0) begin : g_cvt_johnson
			johnson2bin #(
				.JCW(JCW),
				.WIDTH(AW + 1)
			) rd_ptr_gray2bin_inst(
				.binary(w_wdom_rd_ptr_bin),
				.gray(r_wdom_rd_ptr_gray),
				.clk(axi_wr_aclk),
				.rst_n(axi_wr_aresetn)
			);
			johnson2bin #(
				.JCW(JCW),
				.WIDTH(AW + 1)
			) wr_ptr_gray2bin_inst(
				.binary(w_rdom_wr_ptr_bin),
				.gray(r_rdom_wr_ptr_gray),
				.clk(axi_rd_aclk),
				.rst_n(axi_rd_aresetn)
			);
		end
		else begin : g_cvt_gray
			gray2bin #(.WIDTH(AW + 1)) rd_ptr_gray2bin_inst(
				.binary(w_wdom_rd_ptr_bin),
				.gray(r_wdom_rd_ptr_gray)
			);
			gray2bin #(.WIDTH(AW + 1)) wr_ptr_gray2bin_inst(
				.binary(w_rdom_wr_ptr_bin),
				.gray(r_rdom_wr_ptr_gray)
			);
		end
	endgenerate
	assign r_wr_addr = r_wr_ptr_bin[AW - 1:0];
	assign r_rd_addr = r_rd_ptr_bin[AW - 1:0];
	fifo_control #(
		.DEPTH(D),
		.ADDR_WIDTH(AW),
		.ALMOST_RD_MARGIN(ALMOST_RD_MARGIN),
		.ALMOST_WR_MARGIN(ALMOST_WR_MARGIN),
		.REGISTERED(REGISTERED)
	) fifo_control_inst(
		.wr_clk(axi_wr_aclk),
		.wr_rst_n(axi_wr_aresetn),
		.rd_clk(axi_rd_aclk),
		.rd_rst_n(axi_rd_aresetn),
		.wr_ptr_bin(w_wr_ptr_bin_next),
		.wdom_rd_ptr_bin(w_wdom_rd_ptr_bin),
		.rd_ptr_bin(w_rd_ptr_bin_next),
		.rdom_wr_ptr_bin(w_rdom_wr_ptr_bin),
		.wr_full(r_wr_full),
		.wr_almost_full(r_wr_almost_full),
		.rd_empty(r_rd_empty),
		.rd_almost_empty(r_rd_almost_empty),
		.count(w_count)
	);
	assign wr_ready = !r_wr_full;
	assign rd_valid = !r_rd_empty;
	generate
		if (MEM_STYLE == 32'sd1) begin : gen_srl
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_wr_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_rd_aclk or negedge axi_rd_aresetn)
					if (!axi_rd_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
		else if (MEM_STYLE == 32'sd2) begin : gen_bram
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_wr_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			reg [DATA_WIDTH - 1:0] r_rd_data;
			always @(posedge axi_rd_aclk or negedge axi_rd_aresetn)
				if (!axi_rd_aresetn)
					r_rd_data <= 1'sb0;
				else
					r_rd_data <= mem[r_rd_addr];
			assign rd_data = r_rd_data;
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_wr_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_rd_aclk or negedge axi_rd_aresetn)
					if (!axi_rd_aresetn)
						r_rd_data <= 1'sb0;
					else
						r_rd_data <= mem[r_rd_addr];
				assign rd_data = r_rd_data;
			end
			else begin : g_mux
				assign rd_data = mem[r_rd_addr];
			end
		end
	endgenerate
	always @(posedge axi_rd_aclk)
		if (w_read && r_rd_empty)
			;
endmodule
module apb5_slave_cdc (
	pclk,
	presetn,
	aclk,
	aresetn,
	s_apb_PSEL,
	s_apb_PENABLE,
	s_apb_PREADY,
	s_apb_PADDR,
	s_apb_PWRITE,
	s_apb_PWDATA,
	s_apb_PSTRB,
	s_apb_PPROT,
	s_apb_PAUSER,
	s_apb_PWUSER,
	s_apb_PRDATA,
	s_apb_PSLVERR,
	s_apb_PWAKEUP,
	s_apb_PRUSER,
	s_apb_PBUSER,
	s_apb_PWDATAPARITY,
	s_apb_PADDRPARITY,
	s_apb_PCTRLPARITY,
	s_apb_PRDATAPARITY,
	s_apb_PREADYPARITY,
	s_apb_PSLVERRPARITY,
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
	rsp_pruser,
	rsp_pbuser,
	wakeup_request,
	parity_error_wdata,
	parity_error_ctrl
);
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] PROT_WIDTH = 3;
	parameter signed [31:0] AUSER_WIDTH = 4;
	parameter signed [31:0] WUSER_WIDTH = 4;
	parameter signed [31:0] RUSER_WIDTH = 4;
	parameter signed [31:0] BUSER_WIDTH = 4;
	parameter signed [31:0] DEPTH = 2;
	parameter [0:0] ENABLE_PARITY = 0;
	parameter [0:0] USE_2_PHASE_CDC = 1'b1;
	parameter signed [31:0] USE_JOHNSON = 0;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] SW = STRB_WIDTH;
	parameter signed [31:0] PW = PROT_WIDTH;
	parameter signed [31:0] AUW = AUSER_WIDTH;
	parameter signed [31:0] WUW = WUSER_WIDTH;
	parameter signed [31:0] RUW = RUSER_WIDTH;
	parameter signed [31:0] BUW = BUSER_WIDTH;
	parameter signed [31:0] CPW = (((((AW + DW) + SW) + PW) + AUW) + WUW) + 1;
	parameter signed [31:0] RPW = ((DW + RUW) + BUW) + 1;
	input wire pclk;
	input wire presetn;
	input wire aclk;
	input wire aresetn;
	input wire s_apb_PSEL;
	input wire s_apb_PENABLE;
	output wire s_apb_PREADY;
	input wire [AW - 1:0] s_apb_PADDR;
	input wire s_apb_PWRITE;
	input wire [DW - 1:0] s_apb_PWDATA;
	input wire [SW - 1:0] s_apb_PSTRB;
	input wire [PW - 1:0] s_apb_PPROT;
	input wire [AUW - 1:0] s_apb_PAUSER;
	input wire [WUW - 1:0] s_apb_PWUSER;
	output wire [DW - 1:0] s_apb_PRDATA;
	output wire s_apb_PSLVERR;
	output wire s_apb_PWAKEUP;
	output wire [RUW - 1:0] s_apb_PRUSER;
	output wire [BUW - 1:0] s_apb_PBUSER;
	input wire [SW - 1:0] s_apb_PWDATAPARITY;
	input wire s_apb_PADDRPARITY;
	input wire s_apb_PCTRLPARITY;
	output wire [SW - 1:0] s_apb_PRDATAPARITY;
	output wire s_apb_PREADYPARITY;
	output wire s_apb_PSLVERRPARITY;
	output wire cmd_valid;
	input wire cmd_ready;
	output wire cmd_pwrite;
	output wire [AW - 1:0] cmd_paddr;
	output wire [DW - 1:0] cmd_pwdata;
	output wire [SW - 1:0] cmd_pstrb;
	output wire [PW - 1:0] cmd_pprot;
	output wire [AUW - 1:0] cmd_pauser;
	output wire [WUW - 1:0] cmd_pwuser;
	input wire rsp_valid;
	output wire rsp_ready;
	input wire [DW - 1:0] rsp_prdata;
	input wire rsp_pslverr;
	input wire [RUW - 1:0] rsp_pruser;
	input wire [BUW - 1:0] rsp_pbuser;
	input wire wakeup_request;
	output wire parity_error_wdata;
	output wire parity_error_ctrl;
	wire w_cmd_valid;
	wire w_cmd_ready;
	wire w_cmd_pwrite;
	wire [AW - 1:0] w_cmd_paddr;
	wire [DW - 1:0] w_cmd_pwdata;
	wire [SW - 1:0] w_cmd_pstrb;
	wire [PW - 1:0] w_cmd_pprot;
	wire [AUW - 1:0] w_cmd_pauser;
	wire [WUW - 1:0] w_cmd_pwuser;
	wire w_rsp_valid;
	wire w_rsp_ready;
	wire [DW - 1:0] w_rsp_prdata;
	wire w_rsp_pslverr;
	wire [RUW - 1:0] w_rsp_pruser;
	wire [BUW - 1:0] w_rsp_pbuser;
	wire w_wakeup_request_sync;
	cdc_synchronizer #(.WIDTH(1)) u_wakeup_sync(
		.clk(pclk),
		.rst_n(presetn),
		.async_in(wakeup_request),
		.sync_out(w_wakeup_request_sync)
	);
	apb5_slave #(
		.ADDR_WIDTH(AW),
		.DATA_WIDTH(DW),
		.STRB_WIDTH(SW),
		.PROT_WIDTH(PW),
		.AUSER_WIDTH(AUW),
		.WUSER_WIDTH(WUW),
		.RUSER_WIDTH(RUW),
		.BUSER_WIDTH(BUW),
		.DEPTH(DEPTH),
		.ENABLE_PARITY(ENABLE_PARITY)
	) u_apb5_slave(
		.pclk(pclk),
		.presetn(presetn),
		.s_apb_PSEL(s_apb_PSEL),
		.s_apb_PENABLE(s_apb_PENABLE),
		.s_apb_PREADY(s_apb_PREADY),
		.s_apb_PADDR(s_apb_PADDR),
		.s_apb_PWRITE(s_apb_PWRITE),
		.s_apb_PWDATA(s_apb_PWDATA),
		.s_apb_PSTRB(s_apb_PSTRB),
		.s_apb_PPROT(s_apb_PPROT),
		.s_apb_PAUSER(s_apb_PAUSER),
		.s_apb_PWUSER(s_apb_PWUSER),
		.s_apb_PRDATA(s_apb_PRDATA),
		.s_apb_PSLVERR(s_apb_PSLVERR),
		.s_apb_PWAKEUP(s_apb_PWAKEUP),
		.s_apb_PRUSER(s_apb_PRUSER),
		.s_apb_PBUSER(s_apb_PBUSER),
		.s_apb_PWDATAPARITY(s_apb_PWDATAPARITY),
		.s_apb_PADDRPARITY(s_apb_PADDRPARITY),
		.s_apb_PCTRLPARITY(s_apb_PCTRLPARITY),
		.s_apb_PRDATAPARITY(s_apb_PRDATAPARITY),
		.s_apb_PREADYPARITY(s_apb_PREADYPARITY),
		.s_apb_PSLVERRPARITY(s_apb_PSLVERRPARITY),
		.cmd_valid(w_cmd_valid),
		.cmd_ready(w_cmd_ready),
		.cmd_pwrite(w_cmd_pwrite),
		.cmd_paddr(w_cmd_paddr),
		.cmd_pwdata(w_cmd_pwdata),
		.cmd_pstrb(w_cmd_pstrb),
		.cmd_pprot(w_cmd_pprot),
		.cmd_pauser(w_cmd_pauser),
		.cmd_pwuser(w_cmd_pwuser),
		.rsp_valid(w_rsp_valid),
		.rsp_ready(w_rsp_ready),
		.rsp_prdata(w_rsp_prdata),
		.rsp_pslverr(w_rsp_pslverr),
		.rsp_pruser(w_rsp_pruser),
		.rsp_pbuser(w_rsp_pbuser),
		.wakeup_request(w_wakeup_request_sync),
		.parity_error_wdata(parity_error_wdata),
		.parity_error_ctrl(parity_error_ctrl)
	);
	localparam signed [31:0] CDC_FIFO_DEPTH = (DEPTH < 4 ? 4 : DEPTH);
	localparam [0:0] CDC_DEPTH_POW2 = (CDC_FIFO_DEPTH & (CDC_FIFO_DEPTH - 1)) == 0;
	localparam signed [31:0] CDC_USE_JOHNSON = (USE_JOHNSON >= 0 ? USE_JOHNSON : (CDC_DEPTH_POW2 ? 0 : 1));
	gaxi_fifo_async #(
		.DATA_WIDTH(CPW),
		.DEPTH(CDC_FIFO_DEPTH),
		.USE_JOHNSON(CDC_USE_JOHNSON),
		.N_FLOP_CROSS(2)
	) u_cmd_cdc_fifo(
		.axi_wr_aclk(pclk),
		.axi_wr_aresetn(presetn),
		.axi_rd_aclk(aclk),
		.axi_rd_aresetn(aresetn),
		.wr_valid(w_cmd_valid),
		.wr_ready(w_cmd_ready),
		.wr_data({w_cmd_pwrite, w_cmd_pprot, w_cmd_pstrb, w_cmd_paddr, w_cmd_pwdata, w_cmd_pauser, w_cmd_pwuser}),
		.rd_ready(cmd_ready),
		.rd_valid(cmd_valid),
		.rd_data({cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata, cmd_pauser, cmd_pwuser})
	);
	gaxi_fifo_async #(
		.DATA_WIDTH(RPW),
		.DEPTH(CDC_FIFO_DEPTH),
		.USE_JOHNSON(CDC_USE_JOHNSON),
		.N_FLOP_CROSS(2)
	) u_rsp_cdc_fifo(
		.axi_wr_aclk(aclk),
		.axi_wr_aresetn(aresetn),
		.axi_rd_aclk(pclk),
		.axi_rd_aresetn(presetn),
		.wr_valid(rsp_valid),
		.wr_ready(rsp_ready),
		.wr_data({rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser}),
		.rd_ready(w_rsp_ready),
		.rd_valid(w_rsp_valid),
		.rd_data({w_rsp_pslverr, w_rsp_prdata, w_rsp_pruser, w_rsp_pbuser})
	);
endmodule
module apb5_slave_cdc_cg (
	pclk,
	presetn,
	aclk,
	aresetn,
	cfg_cg_enable,
	cfg_cg_idle_count,
	s_apb_PSEL,
	s_apb_PENABLE,
	s_apb_PREADY,
	s_apb_PADDR,
	s_apb_PWRITE,
	s_apb_PWDATA,
	s_apb_PSTRB,
	s_apb_PPROT,
	s_apb_PAUSER,
	s_apb_PWUSER,
	s_apb_PRDATA,
	s_apb_PSLVERR,
	s_apb_PWAKEUP,
	s_apb_PRUSER,
	s_apb_PBUSER,
	s_apb_PWDATAPARITY,
	s_apb_PADDRPARITY,
	s_apb_PCTRLPARITY,
	s_apb_PRDATAPARITY,
	s_apb_PREADYPARITY,
	s_apb_PSLVERRPARITY,
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
	rsp_pruser,
	rsp_pbuser,
	wakeup_request,
	parity_error_wdata,
	parity_error_ctrl,
	cg_gating,
	cg_idle
);
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] PROT_WIDTH = 3;
	parameter signed [31:0] AUSER_WIDTH = 4;
	parameter signed [31:0] WUSER_WIDTH = 4;
	parameter signed [31:0] RUSER_WIDTH = 4;
	parameter signed [31:0] BUSER_WIDTH = 4;
	parameter signed [31:0] DEPTH = 2;
	parameter signed [31:0] USE_JOHNSON = 0;
	parameter [0:0] ENABLE_PARITY = 0;
	parameter signed [31:0] CG_IDLE_COUNT_WIDTH = 4;
	parameter [0:0] USE_2_PHASE_CDC = 1'b1;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] SW = STRB_WIDTH;
	parameter signed [31:0] PW = PROT_WIDTH;
	parameter signed [31:0] AUW = AUSER_WIDTH;
	parameter signed [31:0] WUW = WUSER_WIDTH;
	parameter signed [31:0] RUW = RUSER_WIDTH;
	parameter signed [31:0] BUW = BUSER_WIDTH;
	parameter signed [31:0] ICW = CG_IDLE_COUNT_WIDTH;
	parameter signed [31:0] CPW = (((((AW + DW) + SW) + PW) + AUW) + WUW) + 1;
	parameter signed [31:0] RPW = ((DW + RUW) + BUW) + 1;
	input wire pclk;
	input wire presetn;
	input wire aclk;
	input wire aresetn;
	input wire cfg_cg_enable;
	input wire [ICW - 1:0] cfg_cg_idle_count;
	input wire s_apb_PSEL;
	input wire s_apb_PENABLE;
	output wire s_apb_PREADY;
	input wire [AW - 1:0] s_apb_PADDR;
	input wire s_apb_PWRITE;
	input wire [DW - 1:0] s_apb_PWDATA;
	input wire [SW - 1:0] s_apb_PSTRB;
	input wire [PW - 1:0] s_apb_PPROT;
	input wire [AUW - 1:0] s_apb_PAUSER;
	input wire [WUW - 1:0] s_apb_PWUSER;
	output wire [DW - 1:0] s_apb_PRDATA;
	output wire s_apb_PSLVERR;
	output wire s_apb_PWAKEUP;
	output wire [RUW - 1:0] s_apb_PRUSER;
	output wire [BUW - 1:0] s_apb_PBUSER;
	input wire [SW - 1:0] s_apb_PWDATAPARITY;
	input wire s_apb_PADDRPARITY;
	input wire s_apb_PCTRLPARITY;
	output wire [SW - 1:0] s_apb_PRDATAPARITY;
	output wire s_apb_PREADYPARITY;
	output wire s_apb_PSLVERRPARITY;
	output wire cmd_valid;
	input wire cmd_ready;
	output wire cmd_pwrite;
	output wire [AW - 1:0] cmd_paddr;
	output wire [DW - 1:0] cmd_pwdata;
	output wire [SW - 1:0] cmd_pstrb;
	output wire [PW - 1:0] cmd_pprot;
	output wire [AUW - 1:0] cmd_pauser;
	output wire [WUW - 1:0] cmd_pwuser;
	input wire rsp_valid;
	output wire rsp_ready;
	input wire [DW - 1:0] rsp_prdata;
	input wire rsp_pslverr;
	input wire [RUW - 1:0] rsp_pruser;
	input wire [BUW - 1:0] rsp_pbuser;
	input wire wakeup_request;
	output wire parity_error_wdata;
	output wire parity_error_ctrl;
	output wire cg_gating;
	output wire cg_idle;
	reg r_wakeup;
	wire gated_pclk;
	reg r_aclk_activity_sync1;
	reg r_aclk_activity_sync2;
	always @(posedge pclk or negedge presetn)
		if (!presetn) begin
			r_aclk_activity_sync1 <= 1'b0;
			r_aclk_activity_sync2 <= 1'b0;
		end
		else begin
			r_aclk_activity_sync1 <= (cmd_valid || rsp_valid) || wakeup_request;
			r_aclk_activity_sync2 <= r_aclk_activity_sync1;
		end
	always @(posedge pclk or negedge presetn)
		if (!presetn)
			r_wakeup <= 1'b1;
		else
			r_wakeup <= (s_apb_PSEL || s_apb_PENABLE) || r_aclk_activity_sync2;
	amba_clock_gate_ctrl #(.CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)) amba_clock_gate_ctrl(
		.clk_in(pclk),
		.aresetn(presetn),
		.cfg_cg_enable(cfg_cg_enable),
		.cfg_cg_idle_count(cfg_cg_idle_count),
		.user_valid(r_wakeup),
		.axi_valid('b0),
		.clk_out(gated_pclk),
		.gating(cg_gating),
		.idle(cg_idle)
	);
	apb5_slave_cdc #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.DATA_WIDTH(DATA_WIDTH),
		.STRB_WIDTH(STRB_WIDTH),
		.PROT_WIDTH(PROT_WIDTH),
		.AUSER_WIDTH(AUSER_WIDTH),
		.WUSER_WIDTH(WUSER_WIDTH),
		.RUSER_WIDTH(RUSER_WIDTH),
		.BUSER_WIDTH(BUSER_WIDTH),
		.DEPTH(DEPTH),
		.USE_JOHNSON(USE_JOHNSON),
		.ENABLE_PARITY(ENABLE_PARITY),
		.USE_2_PHASE_CDC(USE_2_PHASE_CDC)
	) u_apb5_slave_cdc(
		.pclk(gated_pclk),
		.presetn(presetn),
		.aclk(aclk),
		.aresetn(aresetn),
		.s_apb_PSEL(s_apb_PSEL),
		.s_apb_PENABLE(s_apb_PENABLE),
		.s_apb_PREADY(s_apb_PREADY),
		.s_apb_PADDR(s_apb_PADDR),
		.s_apb_PWRITE(s_apb_PWRITE),
		.s_apb_PWDATA(s_apb_PWDATA),
		.s_apb_PSTRB(s_apb_PSTRB),
		.s_apb_PPROT(s_apb_PPROT),
		.s_apb_PAUSER(s_apb_PAUSER),
		.s_apb_PWUSER(s_apb_PWUSER),
		.s_apb_PRDATA(s_apb_PRDATA),
		.s_apb_PSLVERR(s_apb_PSLVERR),
		.s_apb_PWAKEUP(s_apb_PWAKEUP),
		.s_apb_PRUSER(s_apb_PRUSER),
		.s_apb_PBUSER(s_apb_PBUSER),
		.s_apb_PWDATAPARITY(s_apb_PWDATAPARITY),
		.s_apb_PADDRPARITY(s_apb_PADDRPARITY),
		.s_apb_PCTRLPARITY(s_apb_PCTRLPARITY),
		.s_apb_PRDATAPARITY(s_apb_PRDATAPARITY),
		.s_apb_PREADYPARITY(s_apb_PREADYPARITY),
		.s_apb_PSLVERRPARITY(s_apb_PSLVERRPARITY),
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
		.rsp_pruser(rsp_pruser),
		.rsp_pbuser(rsp_pbuser),
		.wakeup_request(wakeup_request),
		.parity_error_wdata(parity_error_wdata),
		.parity_error_ctrl(parity_error_ctrl)
	);
endmodule
