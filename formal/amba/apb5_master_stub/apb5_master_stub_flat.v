module dataint_parity (
	data_in,
	parity_in,
	parity_type,
	parity,
	parity_err
);
	parameter signed [31:0] CHUNKS = 4;
	parameter signed [31:0] WIDTH = 32;
	input wire [WIDTH - 1:0] data_in;
	input wire [CHUNKS - 1:0] parity_in;
	input wire parity_type;
	output wire [CHUNKS - 1:0] parity;
	output wire [CHUNKS - 1:0] parity_err;
	localparam signed [31:0] ChunkSize = WIDTH / CHUNKS;
	localparam signed [31:0] ExtraBits = WIDTH % CHUNKS;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < CHUNKS; _gv_i_1 = _gv_i_1 + 1) begin : gen_parity
			localparam i = _gv_i_1;
			localparam signed [31:0] LowerBound = i * ChunkSize;
			localparam signed [31:0] UpperBound = (i < (CHUNKS - 1) ? ((i + 1) * ChunkSize) - 1 : WIDTH - 1);
			wire calculated_parity = (parity_type ? ^data_in[UpperBound:LowerBound] : ~^data_in[UpperBound:LowerBound]);
			assign parity[i] = calculated_parity;
			assign parity_err[i] = calculated_parity != parity_in[i];
		end
	endgenerate
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
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
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
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			reg [DATA_WIDTH - 1:0] r_rd_data;
			always @(posedge axi_aclk or negedge axi_aresetn)
				if (!axi_aresetn)
					r_rd_data <= 1'sb0;
				else
					r_rd_data <= mem[r_rd_addr];
			assign rd_data = r_rd_data;
		end
		else begin : gen_auto
			reg [DATA_WIDTH - 1:0] mem [0:DEPTH - 1];
			always @(posedge axi_aclk)
				if (w_write && !r_wr_full)
					mem[r_wr_addr] <= wr_data;
			if (REGISTERED != 0) begin : g_flop
				reg [DATA_WIDTH - 1:0] r_rd_data;
				always @(posedge axi_aclk or negedge axi_aresetn)
					if (!axi_aresetn)
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
	always @(posedge axi_aclk) begin
		if (w_write && r_wr_full)
			;
		if (w_read && r_rd_empty)
			;
	end
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
	localparam signed [31:0] SLOTS = (DEPTH == 0 ? 1 : DEPTH);
	reg [DW - 1:0] r_data [0:SLOTS - 1];
	reg [3:0] r_data_count;
	wire w_wr_xfer;
	wire w_rd_xfer;
	assign w_wr_xfer = wr_valid & wr_ready;
	assign w_rd_xfer = rd_valid & rd_ready;
	generate
		if ((DEPTH != 0) && ((DEPTH < 2) || (DEPTH > 8))) begin : gen_depth_guard
			initial $display("Error [elaboration] /tmp/rds-canonical-repo-root/rtl/amba/gaxi/gaxi_skid_buffer.sv:107:13 - gaxi_skid_buffer.gen_depth_guard\n msg: ", "gaxi_skid_buffer: DEPTH=%0d unsupported -- must be 2..8 inclusive, or 0 (pass-through)", DEPTH);
		end
	endgenerate
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	generate
		if (DEPTH == 0) begin : g_bypass
			wire [1:1] sv2v_tmp_B1958;
			assign sv2v_tmp_B1958 = rd_ready;
			always @(*) wr_ready = sv2v_tmp_B1958;
			wire [1:1] sv2v_tmp_00E98;
			assign sv2v_tmp_00E98 = wr_valid;
			always @(*) rd_valid = sv2v_tmp_00E98;
			assign rd_data = wr_data;
			wire [4:1] sv2v_tmp_953DA;
			assign sv2v_tmp_953DA = 1'sb0;
			always @(*) r_data_count = sv2v_tmp_953DA;
			wire [DW:1] sv2v_tmp_D35D5;
			assign sv2v_tmp_D35D5 = 1'sb0;
			always @(*) r_data[0] = sv2v_tmp_D35D5;
			assign rd_count = 1'sb0;
			assign count = 1'sb0;
			wire w_bypass_unused;
			assign w_bypass_unused = &{1'b0, axi_aclk, axi_aresetn, r_data[0], r_data_count, w_wr_xfer, w_rd_xfer};
		end
		else begin : g_skid
			genvar _gv_gi_1;
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
		end
	endgenerate
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
	m_apb_PADDRCHK,
	m_apb_PCTRLCHK,
	m_apb_PSELCHK,
	m_apb_PENABLECHK,
	m_apb_PWDATACHK,
	m_apb_PSTRBCHK,
	m_apb_PAUSERCHK,
	m_apb_PWUSERCHK,
	m_apb_PRDATACHK,
	m_apb_PREADYCHK,
	m_apb_PSLVERRCHK,
	m_apb_PWAKEUPCHK,
	m_apb_PRUSERCHK,
	m_apb_PBUSERCHK,
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
	parity_error_rdata,
	parity_error_ctrl
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
	parameter signed [31:0] RPW = ((DW + RUW) + BUW) + 1;
	parameter signed [31:0] ACW = (AW + 7) / 8;
	parameter signed [31:0] DCW = DW / 8;
	parameter signed [31:0] AUCW = (AUW + 7) / 8;
	parameter signed [31:0] WUCW = (WUW + 7) / 8;
	parameter signed [31:0] RUCW = (RUW + 7) / 8;
	parameter signed [31:0] BUCW = (BUW + 7) / 8;
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
	output wire m_apb_PWAKEUP;
	input wire [RUW - 1:0] m_apb_PRUSER;
	input wire [BUW - 1:0] m_apb_PBUSER;
	output wire [ACW - 1:0] m_apb_PADDRCHK;
	output wire m_apb_PCTRLCHK;
	output wire m_apb_PSELCHK;
	output wire m_apb_PENABLECHK;
	output wire [DCW - 1:0] m_apb_PWDATACHK;
	output wire m_apb_PSTRBCHK;
	output wire [AUCW - 1:0] m_apb_PAUSERCHK;
	output wire [WUCW - 1:0] m_apb_PWUSERCHK;
	input wire [DCW - 1:0] m_apb_PRDATACHK;
	input wire m_apb_PREADYCHK;
	input wire m_apb_PSLVERRCHK;
	output wire m_apb_PWAKEUPCHK;
	input wire [RUCW - 1:0] m_apb_PRUSERCHK;
	input wire [BUCW - 1:0] m_apb_PBUSERCHK;
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
	output wire [RUW - 1:0] rsp_pruser;
	output wire [BUW - 1:0] rsp_pbuser;
	output wire parity_error_rdata;
	output wire parity_error_ctrl;
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
	assign r_rsp_data_in = {m_apb_PSLVERR, m_apb_PRDATA, m_apb_PRUSER, m_apb_PBUSER};
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
	assign {rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser} = r_rsp_data_out;
	reg [2:0] r_apb_state;
	reg [2:0] w_apb_next_state;
	always @(posedge pclk or negedge presetn)
		if (!presetn)
			r_apb_state <= 3'b001;
		else
			r_apb_state <= w_apb_next_state;
	reg r_pwakeup;
	always @(posedge pclk or negedge presetn)
		if (!presetn)
			r_pwakeup <= 1'b0;
		else
			r_pwakeup <= (cmd_valid || r_cmd_valid) || (r_apb_state != 3'b001);
	assign m_apb_PWAKEUP = r_pwakeup;
	generate
		if (ENABLE_PARITY) begin : gen_parity
			genvar _gv_n_1;
			for (_gv_n_1 = 0; _gv_n_1 < ACW; _gv_n_1 = _gv_n_1 + 1) begin : gen_paddrchk
				localparam n = _gv_n_1;
				localparam signed [31:0] LO = n * 8;
				localparam signed [31:0] PB = ((AW - LO) < 8 ? AW - LO : 8);
				dataint_parity #(
					.CHUNKS(1),
					.WIDTH(PB)
				) u_paddrchk(
					.data_in(m_apb_PADDR[LO+:PB]),
					.parity_in(1'b0),
					.parity_type(1'b0),
					.parity(m_apb_PADDRCHK[n]),
					.parity_err()
				);
			end
			genvar _gv_n_2;
			for (_gv_n_2 = 0; _gv_n_2 < DCW; _gv_n_2 = _gv_n_2 + 1) begin : gen_pwdatachk
				localparam n = _gv_n_2;
				localparam signed [31:0] LO = n * 8;
				localparam signed [31:0] PB = ((DW - LO) < 8 ? DW - LO : 8);
				dataint_parity #(
					.CHUNKS(1),
					.WIDTH(PB)
				) u_pwdatachk(
					.data_in(m_apb_PWDATA[LO+:PB]),
					.parity_in(1'b0),
					.parity_type(1'b0),
					.parity(m_apb_PWDATACHK[n]),
					.parity_err()
				);
			end
			genvar _gv_n_3;
			for (_gv_n_3 = 0; _gv_n_3 < AUCW; _gv_n_3 = _gv_n_3 + 1) begin : gen_pauserchk
				localparam n = _gv_n_3;
				localparam signed [31:0] LO = n * 8;
				localparam signed [31:0] PB = ((AUW - LO) < 8 ? AUW - LO : 8);
				dataint_parity #(
					.CHUNKS(1),
					.WIDTH(PB)
				) u_pauserchk(
					.data_in(m_apb_PAUSER[LO+:PB]),
					.parity_in(1'b0),
					.parity_type(1'b0),
					.parity(m_apb_PAUSERCHK[n]),
					.parity_err()
				);
			end
			genvar _gv_n_4;
			for (_gv_n_4 = 0; _gv_n_4 < WUCW; _gv_n_4 = _gv_n_4 + 1) begin : gen_pwuserchk
				localparam n = _gv_n_4;
				localparam signed [31:0] LO = n * 8;
				localparam signed [31:0] PB = ((WUW - LO) < 8 ? WUW - LO : 8);
				dataint_parity #(
					.CHUNKS(1),
					.WIDTH(PB)
				) u_pwuserchk(
					.data_in(m_apb_PWUSER[LO+:PB]),
					.parity_in(1'b0),
					.parity_type(1'b0),
					.parity(m_apb_PWUSERCHK[n]),
					.parity_err()
				);
			end
			dataint_parity #(
				.CHUNKS(1),
				.WIDTH(PW + 1)
			) u_pctrlchk(
				.data_in({m_apb_PWRITE, m_apb_PPROT}),
				.parity_in(1'b0),
				.parity_type(1'b0),
				.parity(m_apb_PCTRLCHK),
				.parity_err()
			);
			dataint_parity #(
				.CHUNKS(1),
				.WIDTH(SW)
			) u_pstrbchk(
				.data_in(m_apb_PSTRB),
				.parity_in(1'b0),
				.parity_type(1'b0),
				.parity(m_apb_PSTRBCHK),
				.parity_err()
			);
			dataint_parity #(
				.CHUNKS(1),
				.WIDTH(1)
			) u_pselchk(
				.data_in(m_apb_PSEL),
				.parity_in(1'b0),
				.parity_type(1'b0),
				.parity(m_apb_PSELCHK),
				.parity_err()
			);
			dataint_parity #(
				.CHUNKS(1),
				.WIDTH(1)
			) u_pwakeupchk(
				.data_in(m_apb_PWAKEUP),
				.parity_in(1'b0),
				.parity_type(1'b0),
				.parity(m_apb_PWAKEUPCHK),
				.parity_err()
			);
			dataint_parity #(
				.CHUNKS(1),
				.WIDTH(1)
			) u_penablechk(
				.data_in(m_apb_PENABLE),
				.parity_in(1'b0),
				.parity_type(1'b0),
				.parity(m_apb_PENABLECHK),
				.parity_err()
			);
			wire [DCW - 1:0] w_prdatachk_err;
			genvar _gv_n_5;
			for (_gv_n_5 = 0; _gv_n_5 < DCW; _gv_n_5 = _gv_n_5 + 1) begin : gen_prdatachk
				localparam n = _gv_n_5;
				localparam signed [31:0] LO = n * 8;
				localparam signed [31:0] PB = ((DW - LO) < 8 ? DW - LO : 8);
				dataint_parity #(
					.CHUNKS(1),
					.WIDTH(PB)
				) u_prdatachk(
					.data_in(m_apb_PRDATA[LO+:PB]),
					.parity_in(m_apb_PRDATACHK[n]),
					.parity_type(1'b0),
					.parity(),
					.parity_err(w_prdatachk_err[n])
				);
			end
			wire [RUCW - 1:0] w_pruserchk_err;
			genvar _gv_n_6;
			for (_gv_n_6 = 0; _gv_n_6 < RUCW; _gv_n_6 = _gv_n_6 + 1) begin : gen_pruserchk
				localparam n = _gv_n_6;
				localparam signed [31:0] LO = n * 8;
				localparam signed [31:0] PB = ((RUW - LO) < 8 ? RUW - LO : 8);
				dataint_parity #(
					.CHUNKS(1),
					.WIDTH(PB)
				) u_pruserchk(
					.data_in(m_apb_PRUSER[LO+:PB]),
					.parity_in(m_apb_PRUSERCHK[n]),
					.parity_type(1'b0),
					.parity(),
					.parity_err(w_pruserchk_err[n])
				);
			end
			wire [BUCW - 1:0] w_pbuserchk_err;
			genvar _gv_n_7;
			for (_gv_n_7 = 0; _gv_n_7 < BUCW; _gv_n_7 = _gv_n_7 + 1) begin : gen_pbuserchk
				localparam n = _gv_n_7;
				localparam signed [31:0] LO = n * 8;
				localparam signed [31:0] PB = ((BUW - LO) < 8 ? BUW - LO : 8);
				dataint_parity #(
					.CHUNKS(1),
					.WIDTH(PB)
				) u_pbuserchk(
					.data_in(m_apb_PBUSER[LO+:PB]),
					.parity_in(m_apb_PBUSERCHK[n]),
					.parity_type(1'b0),
					.parity(),
					.parity_err(w_pbuserchk_err[n])
				);
			end
			wire w_preadychk_err;
			dataint_parity #(
				.CHUNKS(1),
				.WIDTH(1)
			) u_preadychk(
				.data_in(m_apb_PREADY),
				.parity_in(m_apb_PREADYCHK),
				.parity_type(1'b0),
				.parity(),
				.parity_err(w_preadychk_err)
			);
			wire w_pslverrchk_err;
			dataint_parity #(
				.CHUNKS(1),
				.WIDTH(1)
			) u_pslverrchk(
				.data_in(m_apb_PSLVERR),
				.parity_in(m_apb_PSLVERRCHK),
				.parity_type(1'b0),
				.parity(),
				.parity_err(w_pslverrchk_err)
			);
			wire w_en_ready;
			wire w_en_rsp;
			wire w_en_rdata;
			assign w_en_ready = m_apb_PSEL && m_apb_PENABLE;
			assign w_en_rsp = w_en_ready && m_apb_PREADY;
			assign w_en_rdata = w_en_rsp && !m_apb_PWRITE;
			assign parity_error_rdata = w_en_rdata && (|w_prdatachk_err || |w_pruserchk_err);
			assign parity_error_ctrl = (w_en_ready && w_preadychk_err) || (w_en_rsp && (w_pslverrchk_err || |w_pbuserchk_err));
		end
		else begin : gen_no_parity
			assign m_apb_PADDRCHK = 1'sb0;
			assign m_apb_PWDATACHK = 1'sb0;
			assign m_apb_PAUSERCHK = 1'sb0;
			assign m_apb_PWUSERCHK = 1'sb0;
			assign m_apb_PCTRLCHK = 1'b0;
			assign m_apb_PSTRBCHK = 1'b0;
			assign m_apb_PSELCHK = 1'b0;
			assign m_apb_PENABLECHK = 1'b0;
			assign m_apb_PWAKEUPCHK = 1'b0;
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
	m_apb_PADDRCHK,
	m_apb_PCTRLCHK,
	m_apb_PSELCHK,
	m_apb_PENABLECHK,
	m_apb_PWDATACHK,
	m_apb_PSTRBCHK,
	m_apb_PAUSERCHK,
	m_apb_PWUSERCHK,
	m_apb_PRDATACHK,
	m_apb_PREADYCHK,
	m_apb_PSLVERRCHK,
	m_apb_PWAKEUPCHK,
	m_apb_PRUSERCHK,
	m_apb_PBUSERCHK,
	cmd_valid,
	cmd_ready,
	cmd_data,
	rsp_valid,
	rsp_ready,
	rsp_data,
	parity_error_rdata,
	parity_error_ctrl
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
	parameter signed [31:0] RESP_PACKET_WIDTH = ((DATA_WIDTH + RUSER_WIDTH) + BUSER_WIDTH) + 3;
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
	parameter signed [31:0] ACW = (AW + 7) / 8;
	parameter signed [31:0] DCW = DW / 8;
	parameter signed [31:0] AUCW = (AUW + 7) / 8;
	parameter signed [31:0] WUCW = (WUW + 7) / 8;
	parameter signed [31:0] RUCW = (RUW + 7) / 8;
	parameter signed [31:0] BUCW = (BUW + 7) / 8;
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
	output wire m_apb_PWAKEUP;
	input wire [RUW - 1:0] m_apb_PRUSER;
	input wire [BUW - 1:0] m_apb_PBUSER;
	output wire [ACW - 1:0] m_apb_PADDRCHK;
	output wire m_apb_PCTRLCHK;
	output wire m_apb_PSELCHK;
	output wire m_apb_PENABLECHK;
	output wire [DCW - 1:0] m_apb_PWDATACHK;
	output wire m_apb_PSTRBCHK;
	output wire [AUCW - 1:0] m_apb_PAUSERCHK;
	output wire [WUCW - 1:0] m_apb_PWUSERCHK;
	input wire [DCW - 1:0] m_apb_PRDATACHK;
	input wire m_apb_PREADYCHK;
	input wire m_apb_PSLVERRCHK;
	output wire m_apb_PWAKEUPCHK;
	input wire [RUCW - 1:0] m_apb_PRUSERCHK;
	input wire [BUCW - 1:0] m_apb_PBUSERCHK;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire [CPW - 1:0] cmd_data;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [RPW - 1:0] rsp_data;
	output wire parity_error_rdata;
	output wire parity_error_ctrl;
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
	wire [RUW - 1:0] rsp_pruser;
	wire [BUW - 1:0] rsp_pbuser;
	wire [1:0] w_fl_in_data;
	wire [1:0] w_fl_out_data;
	wire w_fl_out_cmd_last;
	wire w_fl_out_cmd_first;
	assign w_fl_in_data = {cmd_last, cmd_first};
	assign {w_fl_out_cmd_last, w_fl_out_cmd_first} = w_fl_out_data;
	gaxi_fifo_sync #(
		.DATA_WIDTH(2),
		.DEPTH((CMD_DEPTH + RSP_DEPTH) + 2)
	) u_first_last_fifo(
		.axi_aclk(pclk),
		.axi_aresetn(presetn),
		.wr_valid(cmd_valid && cmd_ready),
		.wr_ready(),
		.wr_data(w_fl_in_data),
		.rd_valid(),
		.rd_ready(rsp_valid && rsp_ready),
		.rd_data(w_fl_out_data),
		.count()
	);
	assign rsp_data = {w_fl_out_cmd_last, w_fl_out_cmd_first, rsp_pslverr, rsp_prdata, rsp_pruser, rsp_pbuser};
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
		.m_apb_PADDRCHK(m_apb_PADDRCHK),
		.m_apb_PCTRLCHK(m_apb_PCTRLCHK),
		.m_apb_PSELCHK(m_apb_PSELCHK),
		.m_apb_PENABLECHK(m_apb_PENABLECHK),
		.m_apb_PWDATACHK(m_apb_PWDATACHK),
		.m_apb_PSTRBCHK(m_apb_PSTRBCHK),
		.m_apb_PAUSERCHK(m_apb_PAUSERCHK),
		.m_apb_PWUSERCHK(m_apb_PWUSERCHK),
		.m_apb_PRDATACHK(m_apb_PRDATACHK),
		.m_apb_PREADYCHK(m_apb_PREADYCHK),
		.m_apb_PSLVERRCHK(m_apb_PSLVERRCHK),
		.m_apb_PWAKEUPCHK(m_apb_PWAKEUPCHK),
		.m_apb_PRUSERCHK(m_apb_PRUSERCHK),
		.m_apb_PBUSERCHK(m_apb_PBUSERCHK),
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
		.parity_error_rdata(parity_error_rdata),
		.parity_error_ctrl(parity_error_ctrl)
	);
endmodule
