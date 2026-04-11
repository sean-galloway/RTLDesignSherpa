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
module axi_gen_addr (
	curr_addr,
	size,
	burst,
	len,
	next_addr,
	next_addr_align
);
	reg _sv2v_0;
	parameter signed [31:0] AW = 32;
	parameter signed [31:0] DW = 32;
	parameter signed [31:0] ODW = 32;
	parameter signed [31:0] LEN = 8;
	input wire [AW - 1:0] curr_addr;
	input wire [2:0] size;
	input wire [1:0] burst;
	input wire [LEN - 1:0] len;
	output reg [AW - 1:0] next_addr;
	output wire [AW - 1:0] next_addr_align;
	localparam signed [31:0] ODWBYTES = ODW / 8;
	reg [AW - 1:0] increment_pre;
	reg [AW - 1:0] increment;
	reg [AW - 1:0] wrap_mask;
	reg [AW - 1:0] aligned_addr;
	reg [AW - 1:0] wrap_addr;
	wire [16:0] len_plus1;
	reg [4:0] len_log2;
	function automatic [16:0] sv2v_cast_17;
		input reg [16:0] inp;
		sv2v_cast_17 = inp;
	endfunction
	assign len_plus1 = sv2v_cast_17({1'b0, len}) + 17'd1;
	always @(*) begin
		if (_sv2v_0)
			;
		casez (len_plus1)
			17'b1zzzzzzzzzzzzzzzz: len_log2 = 5'd16;
			17'b01zzzzzzzzzzzzzzz: len_log2 = 5'd15;
			17'b001zzzzzzzzzzzzzz: len_log2 = 5'd14;
			17'b0001zzzzzzzzzzzzz: len_log2 = 5'd13;
			17'b00001zzzzzzzzzzzz: len_log2 = 5'd12;
			17'b000001zzzzzzzzzzz: len_log2 = 5'd11;
			17'b0000001zzzzzzzzzz: len_log2 = 5'd10;
			17'b00000001zzzzzzzzz: len_log2 = 5'd9;
			17'b000000001zzzzzzzz: len_log2 = 5'd8;
			17'b0000000001zzzzzzz: len_log2 = 5'd7;
			17'b00000000001zzzzzz: len_log2 = 5'd6;
			17'b000000000001zzzzz: len_log2 = 5'd5;
			17'b0000000000001zzzz: len_log2 = 5'd4;
			17'b00000000000001zzz: len_log2 = 5'd3;
			17'b000000000000001zz: len_log2 = 5'd2;
			17'b0000000000000001z: len_log2 = 5'd1;
			17'b00000000000000001: len_log2 = 5'd0;
			default: len_log2 = 5'd0;
		endcase
	end
	function automatic [AW - 1:0] sv2v_cast_DE851;
		input reg [AW - 1:0] inp;
		sv2v_cast_DE851 = inp;
	endfunction
	function automatic signed [AW - 1:0] sv2v_cast_DE851_signed;
		input reg signed [AW - 1:0] inp;
		sv2v_cast_DE851_signed = inp;
	endfunction
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		increment_pre = 1 << size;
		increment = increment_pre;
		if (DW != ODW) begin
			if (sv2v_cast_DE851(increment_pre) > sv2v_cast_DE851_signed(ODWBYTES))
				increment = sv2v_cast_DE851_signed(ODWBYTES);
		end
		wrap_mask = (1 << (sv2v_cast_32(size) + sv2v_cast_32(len_log2))) - 1;
		aligned_addr = (curr_addr + increment) & ~(increment - 1);
		wrap_addr = (curr_addr & ~wrap_mask) | (aligned_addr & wrap_mask);
	end
	always @(*) begin
		if (_sv2v_0)
			;
		casez (burst)
			2'b00: next_addr = curr_addr;
			2'b01: next_addr = curr_addr + increment;
			2'b10: next_addr = wrap_addr;
			default: next_addr = curr_addr + increment;
		endcase
	end
	wire [AW - 1:0] w_alignment_mask = sv2v_cast_DE851_signed(ODWBYTES) - 1;
	assign next_addr_align = next_addr & ~w_alignment_mask;
	initial _sv2v_0 = 0;
endmodule
module axi4_to_apb_convert (
	aclk,
	aresetn,
	r_s_axi_aw_pkt,
	r_s_axi_aw_count,
	r_s_axi_awvalid,
	w_s_axi_awready,
	r_s_axi_w_pkt,
	r_s_axi_wvalid,
	w_s_axi_wready,
	r_s_axi_b_pkt,
	w_s_axi_bvalid,
	r_s_axi_bready,
	r_s_axi_ar_pkt,
	r_s_axi_ar_count,
	r_s_axi_arvalid,
	w_s_axi_arready,
	r_s_axi_r_pkt,
	w_s_axi_rvalid,
	r_s_axi_rready,
	w_cmd_valid,
	r_cmd_ready,
	r_cmd_data,
	r_rsp_valid,
	w_rsp_ready,
	r_rsp_data
);
	reg _sv2v_0;
	parameter signed [31:0] SIDE_DEPTH = 6;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] APB_ADDR_WIDTH = 32;
	parameter signed [31:0] APB_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] APB_WSTRB_WIDTH = APB_DATA_WIDTH / 8;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	parameter signed [31:0] SW = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] APBAW = APB_ADDR_WIDTH;
	parameter signed [31:0] APBDW = APB_DATA_WIDTH;
	parameter signed [31:0] APBSW = APB_DATA_WIDTH / 8;
	parameter signed [31:0] AXI2APBRATIO = DW / APBDW;
	parameter signed [31:0] AWSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] WSize = ((DW + SW) + 1) + UW;
	parameter signed [31:0] BSize = (IW + 2) + UW;
	parameter signed [31:0] ARSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] RSize = ((IW + DW) + 3) + UW;
	parameter signed [31:0] APBCmdWidth = ((APBAW + APBDW) + APBSW) + 6;
	parameter signed [31:0] APBRspWidth = APBDW + 3;
	parameter signed [31:0] SideSize = ((1 + IW) + 1) + UW;
	input wire aclk;
	input wire aresetn;
	input wire [AWSize - 1:0] r_s_axi_aw_pkt;
	input wire [3:0] r_s_axi_aw_count;
	input wire r_s_axi_awvalid;
	output reg w_s_axi_awready;
	input wire [WSize - 1:0] r_s_axi_w_pkt;
	input wire r_s_axi_wvalid;
	output reg w_s_axi_wready;
	output wire [BSize - 1:0] r_s_axi_b_pkt;
	output reg w_s_axi_bvalid;
	input wire r_s_axi_bready;
	input wire [ARSize - 1:0] r_s_axi_ar_pkt;
	input wire [3:0] r_s_axi_ar_count;
	input wire r_s_axi_arvalid;
	output reg w_s_axi_arready;
	output wire [RSize - 1:0] r_s_axi_r_pkt;
	output reg w_s_axi_rvalid;
	input wire r_s_axi_rready;
	output reg w_cmd_valid;
	input wire r_cmd_ready;
	output wire [APBCmdWidth - 1:0] r_cmd_data;
	input wire r_rsp_valid;
	output reg w_rsp_ready;
	input wire [APBRspWidth - 1:0] r_rsp_data;
	wire [IW - 1:0] r_s_axi_awid;
	wire [AW - 1:0] r_s_axi_awaddr;
	wire [7:0] r_s_axi_awlen;
	wire [2:0] r_s_axi_awsize;
	wire [1:0] r_s_axi_awburst;
	wire r_s_axi_awlock;
	wire [3:0] r_s_axi_awcache;
	wire [2:0] r_s_axi_awprot;
	wire [3:0] r_s_axi_awqos;
	wire [3:0] r_s_axi_awregion;
	wire [UW - 1:0] r_s_axi_awuser;
	assign {r_s_axi_awid, r_s_axi_awaddr, r_s_axi_awlen, r_s_axi_awsize, r_s_axi_awburst, r_s_axi_awlock, r_s_axi_awcache, r_s_axi_awprot, r_s_axi_awqos, r_s_axi_awregion, r_s_axi_awuser} = r_s_axi_aw_pkt;
	wire [DW - 1:0] r_s_axi_wdata;
	wire [SW - 1:0] r_s_axi_wstrb;
	wire r_s_axi_wlast;
	wire [UW - 1:0] r_s_axi_wuser;
	assign {r_s_axi_wdata, r_s_axi_wstrb, r_s_axi_wlast, r_s_axi_wuser} = r_s_axi_w_pkt;
	wire [IW - 1:0] r_s_axi_arid;
	wire [AW - 1:0] r_s_axi_araddr;
	wire [7:0] r_s_axi_arlen;
	wire [2:0] r_s_axi_arsize;
	wire [1:0] r_s_axi_arburst;
	wire r_s_axi_arlock;
	wire [3:0] r_s_axi_arcache;
	wire [2:0] r_s_axi_arprot;
	wire [3:0] r_s_axi_arqos;
	wire [3:0] r_s_axi_arregion;
	wire [UW - 1:0] r_s_axi_aruser;
	assign {r_s_axi_arid, r_s_axi_araddr, r_s_axi_arlen, r_s_axi_arsize, r_s_axi_arburst, r_s_axi_arlock, r_s_axi_arcache, r_s_axi_arprot, r_s_axi_arqos, r_s_axi_arregion, r_s_axi_aruser} = r_s_axi_ar_pkt;
	reg w_side_in_valid;
	wire r_side_in_ready;
	wire [SideSize - 1:0] r_side_in_data;
	wire [SideSize - 1:0] r_side_in_data_rd;
	wire [SideSize - 1:0] r_side_in_data_wr;
	wire r_side_out_valid;
	reg w_side_out_ready;
	wire [SideSize - 1:0] r_side_out_data;
	wire [DW - 1:0] w_data_zeros;
	wire [DW - 1:0] w_data_read;
	reg w_pslverr;
	reg r_pslverr;
	wire [1:0] w_resp_rd;
	wire [1:0] w_resp_wr;
	wire r_side_operation;
	wire [IW - 1:0] r_side_id;
	wire [DW - 1:0] r_side_data;
	wire r_side_last;
	wire [UW - 1:0] r_side_user;
	assign w_data_zeros = 'b0;
	reg w_apb_cmd_pkt_last;
	reg w_apb_cmd_pkt_first;
	reg w_apb_cmd_pkt_pwrite;
	reg [2:0] w_apb_cmd_pkt_pprot;
	reg [APB_WSTRB_WIDTH - 1:0] w_apb_cmd_pkt_pstrb;
	reg [APB_ADDR_WIDTH - 1:0] w_apb_cmd_pkt_paddr;
	reg [APB_DATA_WIDTH - 1:0] w_apb_cmd_pkt_pwdata;
	wire [APB_DATA_WIDTH - 1:0] r_apb_rsp_pkt_prdata;
	wire r_apb_rsp_pkt_pslverr;
	wire r_apb_rsp_pkt_first;
	wire r_apb_rsp_pkt_last;
	reg [DW - 1:0] r_axi_data_shift;
	reg [DW - 1:0] w_axi_data_shift;
	localparam signed [31:0] PTR_WIDTH = $clog2((AXI2APBRATIO == 1 ? 2 : AXI2APBRATIO));
	reg [PTR_WIDTH - 1:0] r_axi_rd_data_pointer;
	reg [PTR_WIDTH - 1:0] w_axi_rd_data_pointer;
	reg [PTR_WIDTH - 1:0] r_axi_wr_data_pointer;
	reg [PTR_WIDTH - 1:0] w_axi_wr_data_pointer;
	reg [PTR_WIDTH - 1:0] r_axi_rsp_data_pointer;
	reg [PTR_WIDTH - 1:0] w_axi_rsp_data_pointer;
	reg signed [31:0] axi2abpratio = AXI2APBRATIO;
	reg [APBAW - 1:0] w_next_addr;
	wire [APBAW - 1:0] w_next_addr_gen;
	reg [APBAW - 1:0] r_apb_paddr;
	wire [2:0] r_axi_size;
	wire [1:0] r_axi_burst;
	wire [7:0] r_axi_len;
	function automatic signed [APBAW - 1:0] sv2v_cast_A2C65_signed;
		input reg signed [APBAW - 1:0] inp;
		sv2v_cast_A2C65_signed = inp;
	endfunction
	reg [APBAW - 1:0] w_alignment_mask = sv2v_cast_A2C65_signed(APBSW - 1);
	reg [7:0] r_burst_count;
	reg [7:0] w_burst_count;
	reg [2:0] r_apb_state;
	reg [2:0] r_apb_last_state;
	reg [2:0] w_apb_next_state;
	reg [1:0] r_rsp_state;
	reg [1:0] w_rsp_next_state;
	assign r_side_in_data_rd = {1'b0, r_s_axi_arid, w_apb_cmd_pkt_last, r_s_axi_aruser};
	assign r_side_in_data_wr = {1'b1, r_s_axi_awid, w_apb_cmd_pkt_last, r_s_axi_awuser};
	assign r_side_in_data = (r_apb_state == 3'b010 ? r_side_in_data_rd : r_side_in_data_wr);
	assign {r_side_operation, r_side_id, r_side_last, r_side_user} = r_side_out_data;
	assign w_data_read = (axi2abpratio == 1 ? {{DW - APBDW {1'b0}}, r_apb_rsp_pkt_prdata} : w_axi_data_shift);
	assign w_resp_rd = (w_pslverr ? 2'b10 : 2'b00);
	assign w_resp_wr = (w_pslverr | r_pslverr ? 2'b10 : 2'b00);
	assign r_s_axi_r_pkt = {r_side_id, w_data_read, w_resp_rd, r_side_last, r_side_user};
	assign r_s_axi_b_pkt = {r_side_id, w_resp_wr, r_side_user};
	assign r_cmd_data = {w_apb_cmd_pkt_last, w_apb_cmd_pkt_first, w_apb_cmd_pkt_pwrite, w_apb_cmd_pkt_pprot, w_apb_cmd_pkt_pstrb, w_apb_cmd_pkt_paddr, w_apb_cmd_pkt_pwdata};
	assign {r_apb_rsp_pkt_last, r_apb_rsp_pkt_first, r_apb_rsp_pkt_pslverr, r_apb_rsp_pkt_prdata} = r_rsp_data;
	assign r_axi_size = (r_apb_state == 3'b010 ? r_s_axi_arsize : r_s_axi_awsize);
	assign r_axi_burst = (r_apb_state == 3'b010 ? r_s_axi_arburst : r_s_axi_awburst);
	assign r_axi_len = (r_apb_state == 3'b010 ? r_s_axi_arlen : r_s_axi_awlen);
	axi_gen_addr #(
		.AW(APBAW),
		.DW(DW),
		.ODW(APBDW),
		.LEN(8)
	) axi_gen_addr_common(
		.curr_addr(r_apb_paddr),
		.size(r_axi_size),
		.burst(r_axi_burst),
		.len(r_axi_len),
		.next_addr(w_next_addr_gen),
		.next_addr_align()
	);
	function automatic signed [PTR_WIDTH - 1:0] sv2v_cast_62A53_signed;
		input reg signed [PTR_WIDTH - 1:0] inp;
		sv2v_cast_62A53_signed = inp;
	endfunction
	function automatic [APBAW - 1:0] sv2v_cast_A2C65;
		input reg [APBAW - 1:0] inp;
		sv2v_cast_A2C65 = inp;
	endfunction
	always @(posedge aclk)
		if (!aresetn) begin
			r_apb_state <= 3'b001;
			r_apb_last_state <= 3'b001;
			r_rsp_state <= 2'b01;
			r_apb_paddr <= 'b0;
			r_burst_count <= 'b0;
			r_axi_data_shift <= 'b0;
			r_axi_rd_data_pointer <= 'b0;
			r_axi_rsp_data_pointer <= 'b0;
		end
		else begin
			r_apb_state <= w_apb_next_state;
			r_apb_last_state <= r_apb_state;
			r_rsp_state <= w_rsp_next_state;
			r_axi_rd_data_pointer <= w_axi_rd_data_pointer;
			r_axi_wr_data_pointer <= w_axi_wr_data_pointer;
			r_axi_rsp_data_pointer <= w_axi_rsp_data_pointer;
			if (r_rsp_state == 2'b01) begin
				r_pslverr <= 1'b0;
				r_axi_rsp_data_pointer <= 'b0;
			end
			else
				r_pslverr <= r_pslverr | w_pslverr;
			if (((r_rsp_state == 2'b10) && r_rsp_valid) && w_rsp_ready) begin
				if (axi2abpratio == 1)
					r_axi_data_shift <= {{DW - APBDW {1'b0}}, r_apb_rsp_pkt_prdata};
				else begin
					r_axi_data_shift[r_axi_rsp_data_pointer * APBDW+:APBDW] <= r_apb_rsp_pkt_prdata;
					r_axi_rsp_data_pointer <= r_axi_rsp_data_pointer + 1;
					if (r_axi_rsp_data_pointer == sv2v_cast_62A53_signed(axi2abpratio - 1))
						r_axi_rsp_data_pointer <= 'b0;
				end
			end
			if ((r_apb_state == 3'b001) && (w_apb_next_state == 3'b010)) begin
				r_apb_paddr <= sv2v_cast_A2C65(r_s_axi_araddr & ~{{AW - APBAW {1'b0}}, w_alignment_mask});
				r_burst_count <= r_s_axi_arlen;
				r_axi_rd_data_pointer <= 'b0;
				r_axi_data_shift <= 'b0;
			end
			else if ((r_apb_state == 3'b001) && (w_apb_next_state == 3'b100)) begin
				r_apb_paddr <= sv2v_cast_A2C65(r_s_axi_awaddr & ~{{AW - APBAW {1'b0}}, w_alignment_mask});
				r_burst_count <= r_s_axi_awlen;
				r_axi_wr_data_pointer <= 'b0;
			end
			if (r_cmd_ready && (r_apb_state != 3'b001)) begin
				r_apb_paddr <= w_next_addr;
				r_burst_count <= w_burst_count;
				if ((r_apb_state == 3'b010) && w_cmd_valid) begin
					if (axi2abpratio != 1) begin
						r_axi_rd_data_pointer <= r_axi_rd_data_pointer + 1;
						if (r_axi_rd_data_pointer == sv2v_cast_62A53_signed(axi2abpratio - 1))
							r_axi_rd_data_pointer <= 'b0;
					end
				end
				else if (r_apb_state == 3'b100) begin
					if ((axi2abpratio != 1) && w_cmd_valid) begin
						r_axi_wr_data_pointer <= r_axi_wr_data_pointer + 1;
						if (r_axi_wr_data_pointer == sv2v_cast_62A53_signed(axi2abpratio - 1))
							r_axi_wr_data_pointer <= 'b0;
					end
				end
			end
		end
	always @(*) begin
		if (_sv2v_0)
			;
		w_apb_next_state = r_apb_state;
		w_rsp_next_state = r_rsp_state;
		w_next_addr = r_apb_paddr;
		w_pslverr = (r_rsp_valid ? r_apb_rsp_pkt_pslverr : 1'b0);
		w_cmd_valid = 1'b0;
		w_side_in_valid = 1'b0;
		w_apb_cmd_pkt_pwrite = 1'b0;
		w_apb_cmd_pkt_pwdata = (axi2abpratio == 1 ? r_s_axi_wdata[APBDW - 1:0] : r_s_axi_wdata[r_axi_wr_data_pointer * APBDW+:APBDW]);
		w_apb_cmd_pkt_pstrb = (w_apb_cmd_pkt_pwrite == 1'b0 ? {APBSW {1'b1}} : (axi2abpratio == 1 ? r_s_axi_wstrb[APBSW - 1:0] : r_s_axi_wstrb[r_axi_wr_data_pointer * APBSW+:APBSW]));
		w_apb_cmd_pkt_pprot = (r_apb_state == 3'b010 ? r_s_axi_arprot : r_s_axi_awprot);
		w_apb_cmd_pkt_paddr = r_apb_paddr & ~w_alignment_mask;
		w_apb_cmd_pkt_first = 1'b0;
		w_apb_cmd_pkt_last = 1'b0;
		w_axi_rd_data_pointer = r_axi_rd_data_pointer;
		w_axi_wr_data_pointer = r_axi_wr_data_pointer;
		w_axi_rsp_data_pointer = r_axi_rsp_data_pointer;
		w_axi_data_shift = r_axi_data_shift;
		w_s_axi_awready = 1'b0;
		w_s_axi_wready = 1'b0;
		w_s_axi_bvalid = 1'b0;
		w_s_axi_arready = 1'b0;
		w_s_axi_rvalid = 1'b0;
		w_side_out_ready = 1'b0;
		w_rsp_ready = 1'b0;
		w_burst_count = r_burst_count;
		case (r_rsp_state)
			2'b01:
				if (r_rsp_valid && r_apb_rsp_pkt_first)
					w_rsp_next_state = 2'b10;
			2'b10:
				if (r_rsp_valid && r_side_out_valid) begin
					if (~r_side_operation && r_s_axi_rready) begin
						w_side_out_ready = 1'b1;
						w_rsp_ready = 1'b1;
						w_axi_data_shift[r_axi_rsp_data_pointer * APBDW+:APBDW] = r_apb_rsp_pkt_prdata;
						if (r_axi_rsp_data_pointer == sv2v_cast_62A53_signed(axi2abpratio - 1)) begin
							w_axi_rsp_data_pointer = 'b0;
							w_s_axi_rvalid = 1'b1;
						end
						if (r_side_last)
							w_rsp_next_state = 2'b01;
					end
					else if (r_side_operation && r_s_axi_bready) begin
						w_rsp_ready = 1'b1;
						w_side_out_ready = 1'b1;
						if (r_side_last) begin
							w_s_axi_bvalid = 1'b1;
							w_rsp_next_state = 2'b01;
						end
					end
				end
			default: w_rsp_next_state = 2'b01;
		endcase
		case (r_apb_state)
			3'b001:
				if (~r_side_out_valid) begin
					if (r_s_axi_awvalid && r_s_axi_wvalid) begin
						w_apb_next_state = 3'b100;
						w_apb_cmd_pkt_pwrite = 1'b1;
						w_apb_cmd_pkt_paddr = sv2v_cast_A2C65(r_s_axi_awaddr & ~{{AW - APBAW {1'b0}}, w_alignment_mask});
					end
					else if (r_s_axi_arvalid) begin
						w_apb_next_state = 3'b010;
						w_apb_cmd_pkt_pwrite = 1'b0;
						w_apb_cmd_pkt_paddr = sv2v_cast_A2C65(r_s_axi_araddr & ~{{AW - APBAW {1'b0}}, w_alignment_mask});
					end
				end
			3'b010:
				if (r_cmd_ready && r_side_in_ready) begin
					w_cmd_valid = 'b1;
					w_next_addr = w_next_addr_gen;
					w_side_in_valid = 1'b1;
					if (r_apb_last_state == 3'b001)
						w_apb_cmd_pkt_first = 1'b1;
					if ((r_axi_rd_data_pointer == 0) && (r_burst_count == r_s_axi_arlen))
						w_apb_cmd_pkt_first = 1'b1;
					if (r_axi_rd_data_pointer == sv2v_cast_62A53_signed(axi2abpratio - 1)) begin
						w_axi_rd_data_pointer = 'b0;
						if (r_burst_count == 0) begin
							w_apb_next_state = 3'b001;
							w_s_axi_arready = 1'b1;
							w_apb_cmd_pkt_last = 1'b1;
						end
						else
							w_burst_count = r_burst_count - 1;
					end
					else
						w_axi_rd_data_pointer = r_axi_rd_data_pointer + 1;
				end
			3'b100: begin
				w_apb_cmd_pkt_pwrite = 1'b1;
				if ((r_cmd_ready && r_side_in_ready) && r_s_axi_wvalid) begin
					w_cmd_valid = 'b1;
					w_next_addr = w_next_addr_gen;
					w_side_in_valid = 1'b1;
					if (r_apb_last_state == 3'b001)
						w_apb_cmd_pkt_first = 1'b1;
					if ((r_axi_wr_data_pointer == 0) && (r_burst_count == r_s_axi_awlen))
						w_apb_cmd_pkt_first = 1'b1;
					if (r_axi_wr_data_pointer == sv2v_cast_62A53_signed(axi2abpratio - 1)) begin
						if (r_burst_count == 0) begin
							w_apb_next_state = 3'b001;
							w_s_axi_awready = 1'b1;
							w_s_axi_wready = 1'b1;
							w_axi_wr_data_pointer = 'b0;
							w_apb_cmd_pkt_last = 1'b1;
						end
						else begin
							w_burst_count = r_burst_count - 1;
							w_s_axi_wready = 1'b1;
						end
					end
					else
						w_axi_wr_data_pointer = r_axi_wr_data_pointer + 1;
				end
			end
			default: w_apb_next_state = 3'b001;
		endcase
	end
	gaxi_fifo_sync #(
		.DATA_WIDTH(SideSize),
		.DEPTH(SIDE_DEPTH)
	) side_fifo_inst(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(w_side_in_valid),
		.wr_ready(r_side_in_ready),
		.wr_data(r_side_in_data),
		.rd_valid(r_side_out_valid),
		.rd_ready(w_side_out_ready),
		.rd_data(r_side_out_data),
		.count()
	);
	initial _sv2v_0 = 0;
endmodule
