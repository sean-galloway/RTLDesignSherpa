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
module cdc_handshake (
	clk_src,
	rst_src_n,
	src_valid,
	src_ready,
	src_data,
	clk_dst,
	rst_dst_n,
	dst_valid,
	dst_ready,
	dst_data
);
	parameter signed [31:0] DATA_WIDTH = 8;
	input wire clk_src;
	input wire rst_src_n;
	input wire src_valid;
	output reg src_ready;
	input wire [DATA_WIDTH - 1:0] src_data;
	input wire clk_dst;
	input wire rst_dst_n;
	output reg dst_valid;
	input wire dst_ready;
	output wire [DATA_WIDTH - 1:0] dst_data;
	reg r_req_src;
	reg r_ack_dst;
	reg [DATA_WIDTH - 1:0] r_async_data;
	reg [DATA_WIDTH - 1:0] r_dst_data;
	reg [2:0] r_req_sync;
	reg [2:0] r_ack_sync;
	wire w_req_sync;
	wire w_ack_sync;
	reg [1:0] r_src_state;
	reg [1:0] r_dst_state;
	always @(posedge clk_src)
		if (!rst_src_n)
			r_ack_sync <= 3'b000;
		else
			r_ack_sync <= {r_ack_sync[1:0], r_ack_dst};
	assign w_ack_sync = r_ack_sync[2];
	always @(posedge clk_src)
		if (!rst_src_n) begin
			r_src_state <= 2'd0;
			r_req_src <= 1'b0;
			src_ready <= 1'b0;
			r_async_data <= {DATA_WIDTH {1'b0}};
		end
		else
			case (r_src_state)
				2'd0: begin
					src_ready <= 1'b1;
					r_req_src <= 1'b0;
					if (src_valid) begin
						r_async_data <= src_data;
						r_req_src <= 1'b1;
						src_ready <= 1'b0;
						r_src_state <= 2'd1;
					end
				end
				2'd1: begin
					src_ready <= 1'b0;
					if (w_ack_sync) begin
						r_req_src <= 1'b0;
						r_src_state <= 2'd2;
					end
					else begin
						r_req_src <= 1'b1;
						r_src_state <= 2'd1;
					end
				end
				2'd2: begin
					src_ready <= 1'b0;
					r_req_src <= 1'b0;
					if (!w_ack_sync) begin
						src_ready <= 1'b1;
						r_src_state <= 2'd0;
					end
					else
						r_src_state <= 2'd2;
				end
				default: begin
					r_src_state <= 2'd0;
					src_ready <= 1'b1;
					r_req_src <= 1'b0;
				end
			endcase
	always @(posedge clk_dst)
		if (!rst_dst_n)
			r_req_sync <= 3'b000;
		else
			r_req_sync <= {r_req_sync[1:0], r_req_src};
	assign w_req_sync = r_req_sync[2];
	always @(posedge clk_dst)
		if (!rst_dst_n) begin
			r_dst_state <= 2'd0;
			r_ack_dst <= 1'b0;
			dst_valid <= 1'b0;
			r_dst_data <= {DATA_WIDTH {1'b0}};
		end
		else
			case (r_dst_state)
				2'd0: begin
					r_ack_dst <= 1'b0;
					if (w_req_sync) begin
						r_dst_data <= r_async_data;
						dst_valid <= 1'b1;
						r_dst_state <= 2'd1;
					end
					else
						dst_valid <= 1'b0;
				end
				2'd1: begin
					dst_valid <= 1'b1;
					if (dst_ready) begin
						r_ack_dst <= 1'b1;
						dst_valid <= 1'b0;
						r_dst_state <= 2'd2;
					end
					else if (!w_req_sync) begin
						dst_valid <= 1'b0;
						r_dst_state <= 2'd0;
					end
				end
				2'd2: begin
					dst_valid <= 1'b0;
					if (!w_req_sync) begin
						r_ack_dst <= 1'b0;
						r_dst_state <= 2'd0;
					end
					else
						r_ack_dst <= 1'b1;
				end
				default: begin
					r_dst_state <= 2'd0;
					r_ack_dst <= 1'b0;
					dst_valid <= 1'b0;
				end
			endcase
	assign dst_data = r_dst_data;
endmodule
module apb_master (
	pclk,
	presetn,
	m_apb_PSEL,
	m_apb_PENABLE,
	m_apb_PADDR,
	m_apb_PWRITE,
	m_apb_PWDATA,
	m_apb_PSTRB,
	m_apb_PPROT,
	m_apb_PRDATA,
	m_apb_PSLVERR,
	m_apb_PREADY,
	cmd_valid,
	cmd_ready,
	cmd_pwrite,
	cmd_paddr,
	cmd_pwdata,
	cmd_pstrb,
	cmd_pprot,
	rsp_valid,
	rsp_ready,
	rsp_prdata,
	rsp_pslverr
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] PROT_WIDTH = 3;
	parameter signed [31:0] CMD_DEPTH = 6;
	parameter signed [31:0] RSP_DEPTH = 6;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = STRB_WIDTH;
	parameter signed [31:0] PW = PROT_WIDTH;
	parameter signed [31:0] CPW = (((AW + DW) + SW) + PW) + 1;
	parameter signed [31:0] RPW = DW + 1;
	input wire pclk;
	input wire presetn;
	output reg m_apb_PSEL;
	output reg m_apb_PENABLE;
	output reg [AW - 1:0] m_apb_PADDR;
	output reg m_apb_PWRITE;
	output reg [DW - 1:0] m_apb_PWDATA;
	output reg [SW - 1:0] m_apb_PSTRB;
	output reg [PW - 1:0] m_apb_PPROT;
	input wire [DW - 1:0] m_apb_PRDATA;
	input wire m_apb_PSLVERR;
	input wire m_apb_PREADY;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire cmd_pwrite;
	input wire [AW - 1:0] cmd_paddr;
	input wire [DW - 1:0] cmd_pwdata;
	input wire [SW - 1:0] cmd_pstrb;
	input wire [PW - 1:0] cmd_pprot;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [DW - 1:0] rsp_prdata;
	output wire rsp_pslverr;
	wire r_cmd_valid;
	reg w_cmd_ready;
	wire [CPW - 1:0] r_cmd_data_in;
	wire [CPW - 1:0] r_cmd_data_out;
	wire [3:0] w_cmd_count;
	wire [DW - 1:0] r_cmd_pwdata;
	wire [AW - 1:0] r_cmd_paddr;
	wire [SW - 1:0] r_cmd_pstrb;
	wire [2:0] r_cmd_pprot;
	wire r_cmd_pwrite;
	assign r_cmd_data_in = {cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata};
	assign {r_cmd_pwrite, r_cmd_pprot, r_cmd_pstrb, r_cmd_paddr, r_cmd_pwdata} = r_cmd_data_out;
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
	wire [RPW - 1:0] r_rsp_data_in;
	assign r_rsp_data_in = {m_apb_PSLVERR, m_apb_PRDATA};
	gaxi_skid_buffer #(
		.DATA_WIDTH(RPW),
		.DEPTH(RSP_DEPTH)
	) resp_fifo_inst(
		.axi_aclk(pclk),
		.axi_aresetn(presetn),
		.wr_valid(w_rsp_valid),
		.wr_ready(r_rsp_ready),
		.wr_data(r_rsp_data_in),
		.count(),
		.rd_valid(rsp_valid),
		.rd_ready(rsp_ready),
		.rd_data({rsp_pslverr, rsp_prdata}),
		.rd_count()
	);
	reg [2:0] r_apb_state;
	reg [2:0] w_apb_next_state;
	always @(posedge pclk)
		if (!presetn)
			r_apb_state <= 3'b001;
		else
			r_apb_state <= w_apb_next_state;
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
		w_cmd_ready = 1'b0;
		w_rsp_valid = 1'b0;
		casez (r_apb_state)
			3'b001:
				if (r_cmd_valid) begin
					m_apb_PSEL = 1'b1;
					w_apb_next_state = 3'b010;
				end
			3'b010: begin
				m_apb_PSEL = 1'b1;
				w_apb_next_state = 3'b100;
			end
			3'b100: begin
				m_apb_PSEL = 1'b1;
				m_apb_PENABLE = 1'b1;
				if (m_apb_PREADY) begin
					if (r_rsp_ready) begin
						w_rsp_valid = 1'b1;
						w_cmd_ready = 1'b1;
						if (w_cmd_count > 1)
							w_apb_next_state = 3'b010;
						else
							w_apb_next_state = 3'b001;
					end
					else
						w_apb_next_state = 3'b100;
				end
			end
			default: w_apb_next_state = 3'b001;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module apb_master_stub (
	pclk,
	presetn,
	m_apb_PSEL,
	m_apb_PENABLE,
	m_apb_PADDR,
	m_apb_PWRITE,
	m_apb_PWDATA,
	m_apb_PSTRB,
	m_apb_PPROT,
	m_apb_PRDATA,
	m_apb_PSLVERR,
	m_apb_PREADY,
	cmd_valid,
	cmd_ready,
	cmd_data,
	rsp_valid,
	rsp_ready,
	rsp_data
);
	parameter signed [31:0] CMD_DEPTH = 6;
	parameter signed [31:0] RSP_DEPTH = 6;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] STRB_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] CMD_PACKET_WIDTH = ((ADDR_WIDTH + DATA_WIDTH) + STRB_WIDTH) + 6;
	parameter signed [31:0] RESP_PACKET_WIDTH = DATA_WIDTH + 3;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] SW = STRB_WIDTH;
	parameter signed [31:0] CPW = CMD_PACKET_WIDTH;
	parameter signed [31:0] RPW = RESP_PACKET_WIDTH;
	input wire pclk;
	input wire presetn;
	output wire m_apb_PSEL;
	output wire m_apb_PENABLE;
	output wire [ADDR_WIDTH - 1:0] m_apb_PADDR;
	output wire m_apb_PWRITE;
	output wire [DATA_WIDTH - 1:0] m_apb_PWDATA;
	output wire [STRB_WIDTH - 1:0] m_apb_PSTRB;
	output wire [2:0] m_apb_PPROT;
	input wire [DATA_WIDTH - 1:0] m_apb_PRDATA;
	input wire m_apb_PSLVERR;
	input wire m_apb_PREADY;
	input wire cmd_valid;
	output wire cmd_ready;
	input wire [CMD_PACKET_WIDTH - 1:0] cmd_data;
	output wire rsp_valid;
	input wire rsp_ready;
	output wire [RESP_PACKET_WIDTH - 1:0] rsp_data;
	wire [DW - 1:0] cmd_pwdata;
	wire [AW - 1:0] cmd_paddr;
	wire [SW - 1:0] cmd_pstrb;
	wire [2:0] cmd_pprot;
	wire cmd_pwrite;
	wire cmd_first;
	wire cmd_last;
	assign {cmd_last, cmd_first, cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata} = cmd_data;
	wire [DW - 1:0] rsp_prdata;
	wire rsp_pslverr;
	assign rsp_data = {cmd_last, cmd_first, rsp_pslverr, rsp_prdata};
	apb_master #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.DATA_WIDTH(DATA_WIDTH),
		.CMD_DEPTH(CMD_DEPTH),
		.RSP_DEPTH(RSP_DEPTH)
	) u_apb_master(
		.pclk(pclk),
		.presetn(presetn),
		.m_apb_PSEL(m_apb_PSEL),
		.m_apb_PENABLE(m_apb_PENABLE),
		.m_apb_PADDR(m_apb_PADDR),
		.m_apb_PWRITE(m_apb_PWRITE),
		.m_apb_PWDATA(m_apb_PWDATA),
		.m_apb_PSTRB(m_apb_PSTRB),
		.m_apb_PPROT(m_apb_PPROT),
		.m_apb_PRDATA(m_apb_PRDATA),
		.m_apb_PSLVERR(m_apb_PSLVERR),
		.m_apb_PREADY(m_apb_PREADY),
		.cmd_valid(cmd_valid),
		.cmd_ready(cmd_ready),
		.cmd_pwrite(cmd_pwrite),
		.cmd_paddr(cmd_paddr),
		.cmd_pwdata(cmd_pwdata),
		.cmd_pstrb(cmd_pstrb),
		.cmd_pprot(cmd_pprot),
		.rsp_valid(rsp_valid),
		.rsp_ready(rsp_ready),
		.rsp_prdata(rsp_prdata),
		.rsp_pslverr(rsp_pslverr)
	);
endmodule
module axi4_slave_rd_stub (
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
	fub_axi_arvalid,
	fub_axi_arready,
	fub_axi_ar_count,
	fub_axi_ar_pkt,
	fub_axi_rvalid,
	fub_axi_rready,
	fub_axi_r_pkt
);
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	parameter signed [31:0] ARSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] RSize = ((IW + DW) + 3) + UW;
	input wire aclk;
	input wire aresetn;
	input wire [IW - 1:0] s_axi_arid;
	input wire [AW - 1:0] s_axi_araddr;
	input wire [7:0] s_axi_arlen;
	input wire [2:0] s_axi_arsize;
	input wire [1:0] s_axi_arburst;
	input wire s_axi_arlock;
	input wire [3:0] s_axi_arcache;
	input wire [2:0] s_axi_arprot;
	input wire [3:0] s_axi_arqos;
	input wire [3:0] s_axi_arregion;
	input wire [UW - 1:0] s_axi_aruser;
	input wire s_axi_arvalid;
	output wire s_axi_arready;
	output wire [IW - 1:0] s_axi_rid;
	output wire [DW - 1:0] s_axi_rdata;
	output wire [1:0] s_axi_rresp;
	output wire s_axi_rlast;
	output wire [UW - 1:0] s_axi_ruser;
	output wire s_axi_rvalid;
	input wire s_axi_rready;
	output wire fub_axi_arvalid;
	input wire fub_axi_arready;
	output wire [3:0] fub_axi_ar_count;
	output wire [ARSize - 1:0] fub_axi_ar_pkt;
	input wire fub_axi_rvalid;
	output wire fub_axi_rready;
	input wire [RSize - 1:0] fub_axi_r_pkt;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AR),
		.DATA_WIDTH(ARSize)
	) inst_ar_phase(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_arvalid),
		.wr_ready(s_axi_arready),
		.wr_data({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst, s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos, s_axi_arregion, s_axi_aruser}),
		.rd_valid(fub_axi_arvalid),
		.rd_ready(fub_axi_arready),
		.rd_count(fub_axi_ar_count),
		.rd_data(fub_axi_ar_pkt),
		.count()
	);
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_R),
		.DATA_WIDTH(RSize)
	) inst_r_phase(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_axi_rvalid),
		.wr_ready(fub_axi_rready),
		.wr_data(fub_axi_r_pkt),
		.rd_valid(s_axi_rvalid),
		.rd_ready(s_axi_rready),
		.rd_data({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser}),
		.rd_count(),
		.count()
	);
endmodule
module axi4_slave_wr_stub (
	aclk,
	aresetn,
	s_axi_awid,
	s_axi_awaddr,
	s_axi_awlen,
	s_axi_awsize,
	s_axi_awburst,
	s_axi_awlock,
	s_axi_awcache,
	s_axi_awprot,
	s_axi_awqos,
	s_axi_awregion,
	s_axi_awuser,
	s_axi_awvalid,
	s_axi_awready,
	s_axi_wdata,
	s_axi_wstrb,
	s_axi_wlast,
	s_axi_wuser,
	s_axi_wvalid,
	s_axi_wready,
	s_axi_bid,
	s_axi_bresp,
	s_axi_buser,
	s_axi_bvalid,
	s_axi_bready,
	fub_axi_awvalid,
	fub_axi_awready,
	fub_axi_aw_count,
	fub_axi_aw_pkt,
	fub_axi_wvalid,
	fub_axi_wready,
	fub_axi_w_pkt,
	fub_axi_bvalid,
	fub_axi_bready,
	fub_axi_b_pkt
);
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	parameter signed [31:0] AWSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] WSize = ((DW + SW) + 1) + UW;
	parameter signed [31:0] BSize = (IW + 2) + UW;
	input wire aclk;
	input wire aresetn;
	input wire [IW - 1:0] s_axi_awid;
	input wire [AW - 1:0] s_axi_awaddr;
	input wire [7:0] s_axi_awlen;
	input wire [2:0] s_axi_awsize;
	input wire [1:0] s_axi_awburst;
	input wire s_axi_awlock;
	input wire [3:0] s_axi_awcache;
	input wire [2:0] s_axi_awprot;
	input wire [3:0] s_axi_awqos;
	input wire [3:0] s_axi_awregion;
	input wire [UW - 1:0] s_axi_awuser;
	input wire s_axi_awvalid;
	output wire s_axi_awready;
	input wire [DW - 1:0] s_axi_wdata;
	input wire [SW - 1:0] s_axi_wstrb;
	input wire s_axi_wlast;
	input wire [UW - 1:0] s_axi_wuser;
	input wire s_axi_wvalid;
	output wire s_axi_wready;
	output wire [IW - 1:0] s_axi_bid;
	output wire [1:0] s_axi_bresp;
	output wire [UW - 1:0] s_axi_buser;
	output wire s_axi_bvalid;
	input wire s_axi_bready;
	output wire fub_axi_awvalid;
	input wire fub_axi_awready;
	output wire [3:0] fub_axi_aw_count;
	output wire [AWSize - 1:0] fub_axi_aw_pkt;
	output wire fub_axi_wvalid;
	input wire fub_axi_wready;
	output wire [WSize - 1:0] fub_axi_w_pkt;
	input wire fub_axi_bvalid;
	output wire fub_axi_bready;
	input wire [BSize - 1:0] fub_axi_b_pkt;
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_AW),
		.DATA_WIDTH(AWSize)
	) inst_aw_phase(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_awvalid),
		.wr_ready(s_axi_awready),
		.wr_data({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos, s_axi_awregion, s_axi_awuser}),
		.rd_valid(fub_axi_awvalid),
		.rd_ready(fub_axi_awready),
		.rd_count(fub_axi_aw_count),
		.rd_data(fub_axi_aw_pkt),
		.count()
	);
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_W),
		.DATA_WIDTH(WSize)
	) inst_w_phase(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(s_axi_wvalid),
		.wr_ready(s_axi_wready),
		.wr_data({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
		.rd_valid(fub_axi_wvalid),
		.rd_ready(fub_axi_wready),
		.rd_data(fub_axi_w_pkt),
		.rd_count(),
		.count()
	);
	gaxi_skid_buffer #(
		.DEPTH(SKID_DEPTH_B),
		.DATA_WIDTH(BSize)
	) inst_b_phase(
		.axi_aclk(aclk),
		.axi_aresetn(aresetn),
		.wr_valid(fub_axi_bvalid),
		.wr_ready(fub_axi_bready),
		.wr_data(fub_axi_b_pkt),
		.rd_valid(s_axi_bvalid),
		.rd_ready(s_axi_bready),
		.rd_data({s_axi_bid, s_axi_bresp, s_axi_buser}),
		.rd_count(),
		.count()
	);
endmodule
module axi4_slave_stub (
	aclk,
	aresetn,
	s_axi_awid,
	s_axi_awaddr,
	s_axi_awlen,
	s_axi_awsize,
	s_axi_awburst,
	s_axi_awlock,
	s_axi_awcache,
	s_axi_awprot,
	s_axi_awqos,
	s_axi_awregion,
	s_axi_awuser,
	s_axi_awvalid,
	s_axi_awready,
	s_axi_wdata,
	s_axi_wstrb,
	s_axi_wlast,
	s_axi_wuser,
	s_axi_wvalid,
	s_axi_wready,
	s_axi_bid,
	s_axi_bresp,
	s_axi_buser,
	s_axi_bvalid,
	s_axi_bready,
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
	fub_axi_awvalid,
	fub_axi_awready,
	fub_axi_aw_count,
	fub_axi_aw_pkt,
	fub_axi_wvalid,
	fub_axi_wready,
	fub_axi_w_pkt,
	fub_axi_bvalid,
	fub_axi_bready,
	fub_axi_b_pkt,
	fub_axi_arvalid,
	fub_axi_arready,
	fub_axi_ar_count,
	fub_axi_ar_pkt,
	fub_axi_rvalid,
	fub_axi_rready,
	fub_axi_r_pkt
);
	parameter signed [31:0] SKID_DEPTH_AW = 2;
	parameter signed [31:0] SKID_DEPTH_W = 4;
	parameter signed [31:0] SKID_DEPTH_B = 2;
	parameter signed [31:0] SKID_DEPTH_AR = 2;
	parameter signed [31:0] SKID_DEPTH_R = 4;
	parameter signed [31:0] AXI_ID_WIDTH = 8;
	parameter signed [31:0] AXI_ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_DATA_WIDTH = 32;
	parameter signed [31:0] AXI_USER_WIDTH = 1;
	parameter signed [31:0] AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8;
	parameter signed [31:0] AW = AXI_ADDR_WIDTH;
	parameter signed [31:0] DW = AXI_DATA_WIDTH;
	parameter signed [31:0] IW = AXI_ID_WIDTH;
	parameter signed [31:0] SW = AXI_WSTRB_WIDTH;
	parameter signed [31:0] UW = AXI_USER_WIDTH;
	parameter signed [31:0] AWSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] WSize = ((DW + SW) + 1) + UW;
	parameter signed [31:0] BSize = (IW + 2) + UW;
	parameter signed [31:0] ARSize = ((IW + AW) + 29) + UW;
	parameter signed [31:0] RSize = ((IW + DW) + 3) + UW;
	input wire aclk;
	input wire aresetn;
	input wire [AXI_ID_WIDTH - 1:0] s_axi_awid;
	input wire [AXI_ADDR_WIDTH - 1:0] s_axi_awaddr;
	input wire [7:0] s_axi_awlen;
	input wire [2:0] s_axi_awsize;
	input wire [1:0] s_axi_awburst;
	input wire s_axi_awlock;
	input wire [3:0] s_axi_awcache;
	input wire [2:0] s_axi_awprot;
	input wire [3:0] s_axi_awqos;
	input wire [3:0] s_axi_awregion;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_awuser;
	input wire s_axi_awvalid;
	output wire s_axi_awready;
	input wire [AXI_DATA_WIDTH - 1:0] s_axi_wdata;
	input wire [AXI_WSTRB_WIDTH - 1:0] s_axi_wstrb;
	input wire s_axi_wlast;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_wuser;
	input wire s_axi_wvalid;
	output wire s_axi_wready;
	output wire [AXI_ID_WIDTH - 1:0] s_axi_bid;
	output wire [1:0] s_axi_bresp;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_buser;
	output wire s_axi_bvalid;
	input wire s_axi_bready;
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
	output wire [AXI_DATA_WIDTH - 1:0] s_axi_rdata;
	output wire [1:0] s_axi_rresp;
	output wire s_axi_rlast;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_ruser;
	output wire s_axi_rvalid;
	input wire s_axi_rready;
	output wire fub_axi_awvalid;
	input wire fub_axi_awready;
	output wire [3:0] fub_axi_aw_count;
	output wire [AWSize - 1:0] fub_axi_aw_pkt;
	output wire fub_axi_wvalid;
	input wire fub_axi_wready;
	output wire [WSize - 1:0] fub_axi_w_pkt;
	input wire fub_axi_bvalid;
	output wire fub_axi_bready;
	input wire [BSize - 1:0] fub_axi_b_pkt;
	output wire fub_axi_arvalid;
	input wire fub_axi_arready;
	output wire [3:0] fub_axi_ar_count;
	output wire [ARSize - 1:0] fub_axi_ar_pkt;
	input wire fub_axi_rvalid;
	output wire fub_axi_rready;
	input wire [RSize - 1:0] fub_axi_r_pkt;
	axi4_slave_wr_stub #(
		.SKID_DEPTH_AW(SKID_DEPTH_AW),
		.SKID_DEPTH_W(SKID_DEPTH_W),
		.SKID_DEPTH_B(SKID_DEPTH_B),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH),
		.AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH)
	) inst_wr_stub(
		.aclk(aclk),
		.aresetn(aresetn),
		.s_axi_awid(s_axi_awid),
		.s_axi_awaddr(s_axi_awaddr),
		.s_axi_awlen(s_axi_awlen),
		.s_axi_awsize(s_axi_awsize),
		.s_axi_awburst(s_axi_awburst),
		.s_axi_awlock(s_axi_awlock),
		.s_axi_awcache(s_axi_awcache),
		.s_axi_awprot(s_axi_awprot),
		.s_axi_awqos(s_axi_awqos),
		.s_axi_awregion(s_axi_awregion),
		.s_axi_awuser(s_axi_awuser),
		.s_axi_awvalid(s_axi_awvalid),
		.s_axi_awready(s_axi_awready),
		.s_axi_wdata(s_axi_wdata),
		.s_axi_wstrb(s_axi_wstrb),
		.s_axi_wlast(s_axi_wlast),
		.s_axi_wuser(s_axi_wuser),
		.s_axi_wvalid(s_axi_wvalid),
		.s_axi_wready(s_axi_wready),
		.s_axi_bid(s_axi_bid),
		.s_axi_bresp(s_axi_bresp),
		.s_axi_buser(s_axi_buser),
		.s_axi_bvalid(s_axi_bvalid),
		.s_axi_bready(s_axi_bready),
		.fub_axi_awvalid(fub_axi_awvalid),
		.fub_axi_awready(fub_axi_awready),
		.fub_axi_aw_count(fub_axi_aw_count),
		.fub_axi_aw_pkt(fub_axi_aw_pkt),
		.fub_axi_wvalid(fub_axi_wvalid),
		.fub_axi_wready(fub_axi_wready),
		.fub_axi_w_pkt(fub_axi_w_pkt),
		.fub_axi_bvalid(fub_axi_bvalid),
		.fub_axi_bready(fub_axi_bready),
		.fub_axi_b_pkt(fub_axi_b_pkt)
	);
	axi4_slave_rd_stub #(
		.SKID_DEPTH_AR(SKID_DEPTH_AR),
		.SKID_DEPTH_R(SKID_DEPTH_R),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH),
		.AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH)
	) inst_rd_stub(
		.aclk(aclk),
		.aresetn(aresetn),
		.s_axi_arid(s_axi_arid),
		.s_axi_araddr(s_axi_araddr),
		.s_axi_arlen(s_axi_arlen),
		.s_axi_arsize(s_axi_arsize),
		.s_axi_arburst(s_axi_arburst),
		.s_axi_arlock(s_axi_arlock),
		.s_axi_arcache(s_axi_arcache),
		.s_axi_arprot(s_axi_arprot),
		.s_axi_arqos(s_axi_arqos),
		.s_axi_arregion(s_axi_arregion),
		.s_axi_aruser(s_axi_aruser),
		.s_axi_arvalid(s_axi_arvalid),
		.s_axi_arready(s_axi_arready),
		.s_axi_rid(s_axi_rid),
		.s_axi_rdata(s_axi_rdata),
		.s_axi_rresp(s_axi_rresp),
		.s_axi_rlast(s_axi_rlast),
		.s_axi_ruser(s_axi_ruser),
		.s_axi_rvalid(s_axi_rvalid),
		.s_axi_rready(s_axi_rready),
		.fub_axi_arvalid(fub_axi_arvalid),
		.fub_axi_arready(fub_axi_arready),
		.fub_axi_ar_count(fub_axi_ar_count),
		.fub_axi_ar_pkt(fub_axi_ar_pkt),
		.fub_axi_rvalid(fub_axi_rvalid),
		.fub_axi_rready(fub_axi_rready),
		.fub_axi_r_pkt(fub_axi_r_pkt)
	);
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
module axi4_to_apb_shim (
	aclk,
	aresetn,
	pclk,
	presetn,
	s_axi_awid,
	s_axi_awaddr,
	s_axi_awlen,
	s_axi_awsize,
	s_axi_awburst,
	s_axi_awlock,
	s_axi_awcache,
	s_axi_awprot,
	s_axi_awqos,
	s_axi_awregion,
	s_axi_awuser,
	s_axi_awvalid,
	s_axi_awready,
	s_axi_wdata,
	s_axi_wstrb,
	s_axi_wlast,
	s_axi_wuser,
	s_axi_wvalid,
	s_axi_wready,
	s_axi_bid,
	s_axi_bresp,
	s_axi_buser,
	s_axi_bvalid,
	s_axi_bready,
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
	m_apb_PSEL,
	m_apb_PADDR,
	m_apb_PENABLE,
	m_apb_PWRITE,
	m_apb_PWDATA,
	m_apb_PSTRB,
	m_apb_PPROT,
	m_apb_PRDATA,
	m_apb_PREADY,
	m_apb_PSLVERR
);
	parameter signed [31:0] DEPTH_AW = 2;
	parameter signed [31:0] DEPTH_W = 4;
	parameter signed [31:0] DEPTH_B = 2;
	parameter signed [31:0] DEPTH_AR = 2;
	parameter signed [31:0] DEPTH_R = 4;
	parameter signed [31:0] SIDE_DEPTH = 4;
	parameter signed [31:0] APB_CMD_DEPTH = 4;
	parameter signed [31:0] APB_RSP_DEPTH = 4;
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
	parameter signed [31:0] SideSize = ((1 + IW) + 3) + UW;
	input wire aclk;
	input wire aresetn;
	input wire pclk;
	input wire presetn;
	input wire [AXI_ID_WIDTH - 1:0] s_axi_awid;
	input wire [AXI_ADDR_WIDTH - 1:0] s_axi_awaddr;
	input wire [7:0] s_axi_awlen;
	input wire [2:0] s_axi_awsize;
	input wire [1:0] s_axi_awburst;
	input wire s_axi_awlock;
	input wire [3:0] s_axi_awcache;
	input wire [2:0] s_axi_awprot;
	input wire [3:0] s_axi_awqos;
	input wire [3:0] s_axi_awregion;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_awuser;
	input wire s_axi_awvalid;
	output wire s_axi_awready;
	input wire [AXI_DATA_WIDTH - 1:0] s_axi_wdata;
	input wire [AXI_WSTRB_WIDTH - 1:0] s_axi_wstrb;
	input wire s_axi_wlast;
	input wire [AXI_USER_WIDTH - 1:0] s_axi_wuser;
	input wire s_axi_wvalid;
	output wire s_axi_wready;
	output wire [AXI_ID_WIDTH - 1:0] s_axi_bid;
	output wire [1:0] s_axi_bresp;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_buser;
	output wire s_axi_bvalid;
	input wire s_axi_bready;
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
	output wire [AXI_DATA_WIDTH - 1:0] s_axi_rdata;
	output wire [1:0] s_axi_rresp;
	output wire s_axi_rlast;
	output wire [AXI_USER_WIDTH - 1:0] s_axi_ruser;
	output wire s_axi_rvalid;
	input wire s_axi_rready;
	output wire m_apb_PSEL;
	output wire [APB_ADDR_WIDTH - 1:0] m_apb_PADDR;
	output wire m_apb_PENABLE;
	output wire m_apb_PWRITE;
	output wire [APB_DATA_WIDTH - 1:0] m_apb_PWDATA;
	output wire [APB_WSTRB_WIDTH - 1:0] m_apb_PSTRB;
	output wire [2:0] m_apb_PPROT;
	input wire [APB_DATA_WIDTH - 1:0] m_apb_PRDATA;
	input wire m_apb_PREADY;
	input wire m_apb_PSLVERR;
	wire [AWSize - 1:0] r_s_axi_aw_pkt;
	wire [3:0] r_s_axi_aw_count;
	wire r_s_axi_awvalid;
	wire w_s_axi_awready;
	wire [WSize - 1:0] r_s_axi_w_pkt;
	wire r_s_axi_wvalid;
	wire w_s_axi_wready;
	wire [BSize - 1:0] r_s_axi_b_pkt;
	wire w_s_axi_bvalid;
	wire r_s_axi_bready;
	wire [ARSize - 1:0] r_s_axi_ar_pkt;
	wire [3:0] r_s_axi_ar_count;
	wire r_s_axi_arvalid;
	wire w_s_axi_arready;
	wire [RSize - 1:0] r_s_axi_r_pkt;
	wire w_s_axi_rvalid;
	wire r_s_axi_rready;
	wire w_cmd_valid;
	wire r_cmd_ready;
	wire [APBCmdWidth - 1:0] r_cmd_data;
	wire w_cmd_valid_apb;
	wire r_cmd_ready_apb;
	wire [APBCmdWidth - 1:0] r_cmd_data_apb;
	wire r_rsp_valid;
	wire w_rsp_ready;
	wire [APBRspWidth - 1:0] r_rsp_data;
	wire r_rsp_valid_apb;
	wire w_rsp_ready_apb;
	wire [APBRspWidth - 1:0] r_rsp_data_apb;
	axi4_slave_stub #(
		.SKID_DEPTH_AW(DEPTH_AW),
		.SKID_DEPTH_W(DEPTH_W),
		.SKID_DEPTH_B(DEPTH_B),
		.SKID_DEPTH_AR(DEPTH_AR),
		.SKID_DEPTH_R(DEPTH_R),
		.AXI_ID_WIDTH(IW),
		.AXI_ADDR_WIDTH(AW),
		.AXI_DATA_WIDTH(DW),
		.AXI_USER_WIDTH(UW)
	) axi_slave_stub_inst(
		.aclk(aclk),
		.aresetn(aresetn),
		.s_axi_awid(s_axi_awid),
		.s_axi_awaddr(s_axi_awaddr),
		.s_axi_awlen(s_axi_awlen),
		.s_axi_awsize(s_axi_awsize),
		.s_axi_awburst(s_axi_awburst),
		.s_axi_awlock(s_axi_awlock),
		.s_axi_awcache(s_axi_awcache),
		.s_axi_awprot(s_axi_awprot),
		.s_axi_awqos(s_axi_awqos),
		.s_axi_awregion(s_axi_awregion),
		.s_axi_awuser(s_axi_awuser),
		.s_axi_awvalid(s_axi_awvalid),
		.s_axi_awready(s_axi_awready),
		.s_axi_wdata(s_axi_wdata),
		.s_axi_wstrb(s_axi_wstrb),
		.s_axi_wlast(s_axi_wlast),
		.s_axi_wuser(s_axi_wuser),
		.s_axi_wvalid(s_axi_wvalid),
		.s_axi_wready(s_axi_wready),
		.s_axi_bid(s_axi_bid),
		.s_axi_bresp(s_axi_bresp),
		.s_axi_buser(s_axi_buser),
		.s_axi_bvalid(s_axi_bvalid),
		.s_axi_bready(s_axi_bready),
		.s_axi_arid(s_axi_arid),
		.s_axi_araddr(s_axi_araddr),
		.s_axi_arlen(s_axi_arlen),
		.s_axi_arsize(s_axi_arsize),
		.s_axi_arburst(s_axi_arburst),
		.s_axi_arlock(s_axi_arlock),
		.s_axi_arcache(s_axi_arcache),
		.s_axi_arprot(s_axi_arprot),
		.s_axi_arqos(s_axi_arqos),
		.s_axi_arregion(s_axi_arregion),
		.s_axi_aruser(s_axi_aruser),
		.s_axi_arvalid(s_axi_arvalid),
		.s_axi_arready(s_axi_arready),
		.s_axi_rid(s_axi_rid),
		.s_axi_rdata(s_axi_rdata),
		.s_axi_rresp(s_axi_rresp),
		.s_axi_rlast(s_axi_rlast),
		.s_axi_ruser(s_axi_ruser),
		.s_axi_rvalid(s_axi_rvalid),
		.s_axi_rready(s_axi_rready),
		.fub_axi_awvalid(r_s_axi_awvalid),
		.fub_axi_awready(w_s_axi_awready),
		.fub_axi_aw_count(r_s_axi_aw_count),
		.fub_axi_aw_pkt(r_s_axi_aw_pkt),
		.fub_axi_wvalid(r_s_axi_wvalid),
		.fub_axi_wready(w_s_axi_wready),
		.fub_axi_w_pkt(r_s_axi_w_pkt),
		.fub_axi_bvalid(w_s_axi_bvalid),
		.fub_axi_bready(r_s_axi_bready),
		.fub_axi_b_pkt(r_s_axi_b_pkt),
		.fub_axi_arvalid(r_s_axi_arvalid),
		.fub_axi_arready(w_s_axi_arready),
		.fub_axi_ar_count(r_s_axi_ar_count),
		.fub_axi_ar_pkt(r_s_axi_ar_pkt),
		.fub_axi_rvalid(w_s_axi_rvalid),
		.fub_axi_rready(r_s_axi_rready),
		.fub_axi_r_pkt(r_s_axi_r_pkt)
	);
	axi4_to_apb_convert #(
		.SIDE_DEPTH(SIDE_DEPTH),
		.AXI_ID_WIDTH(AXI_ID_WIDTH),
		.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
		.AXI_DATA_WIDTH(AXI_DATA_WIDTH),
		.AXI_USER_WIDTH(AXI_USER_WIDTH),
		.APB_ADDR_WIDTH(APB_ADDR_WIDTH),
		.APB_DATA_WIDTH(APB_DATA_WIDTH),
		.AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH),
		.APB_WSTRB_WIDTH(APB_WSTRB_WIDTH)
	) axi4_to_apb_convert_inst(
		.aclk(aclk),
		.aresetn(aresetn),
		.r_s_axi_aw_pkt(r_s_axi_aw_pkt),
		.r_s_axi_aw_count(r_s_axi_aw_count),
		.r_s_axi_awvalid(r_s_axi_awvalid),
		.w_s_axi_awready(w_s_axi_awready),
		.r_s_axi_w_pkt(r_s_axi_w_pkt),
		.r_s_axi_wvalid(r_s_axi_wvalid),
		.w_s_axi_wready(w_s_axi_wready),
		.r_s_axi_b_pkt(r_s_axi_b_pkt),
		.w_s_axi_bvalid(w_s_axi_bvalid),
		.r_s_axi_bready(r_s_axi_bready),
		.r_s_axi_ar_pkt(r_s_axi_ar_pkt),
		.r_s_axi_ar_count(r_s_axi_ar_count),
		.r_s_axi_arvalid(r_s_axi_arvalid),
		.w_s_axi_arready(w_s_axi_arready),
		.r_s_axi_r_pkt(r_s_axi_r_pkt),
		.w_s_axi_rvalid(w_s_axi_rvalid),
		.r_s_axi_rready(r_s_axi_rready),
		.w_cmd_valid(w_cmd_valid),
		.r_cmd_ready(r_cmd_ready),
		.r_cmd_data(r_cmd_data),
		.r_rsp_valid(r_rsp_valid),
		.w_rsp_ready(w_rsp_ready),
		.r_rsp_data(r_rsp_data)
	);
	cdc_handshake #(.DATA_WIDTH(APBCmdWidth)) u_cmd_cdc_handshake(
		.clk_src(aclk),
		.rst_src_n(aresetn),
		.src_valid(w_cmd_valid),
		.src_ready(r_cmd_ready),
		.src_data(r_cmd_data),
		.clk_dst(pclk),
		.rst_dst_n(presetn),
		.dst_valid(w_cmd_valid_apb),
		.dst_ready(r_cmd_ready_apb),
		.dst_data(r_cmd_data_apb)
	);
	cdc_handshake #(.DATA_WIDTH(APBRspWidth)) u_rsp_cdc_handshake(
		.clk_src(pclk),
		.rst_src_n(presetn),
		.src_valid(r_rsp_valid_apb),
		.src_ready(w_rsp_ready_apb),
		.src_data(r_rsp_data_apb),
		.clk_dst(aclk),
		.rst_dst_n(aresetn),
		.dst_valid(r_rsp_valid),
		.dst_ready(w_rsp_ready),
		.dst_data(r_rsp_data)
	);
	apb_master_stub #(
		.CMD_DEPTH(APB_CMD_DEPTH),
		.RSP_DEPTH(APB_RSP_DEPTH),
		.DATA_WIDTH(APBDW),
		.ADDR_WIDTH(APBAW),
		.STRB_WIDTH(APBSW),
		.CMD_PACKET_WIDTH(APBCmdWidth),
		.RESP_PACKET_WIDTH(APBRspWidth)
	) apb_master_inst(
		.pclk(pclk),
		.presetn(presetn),
		.m_apb_PSEL(m_apb_PSEL),
		.m_apb_PENABLE(m_apb_PENABLE),
		.m_apb_PADDR(m_apb_PADDR),
		.m_apb_PWRITE(m_apb_PWRITE),
		.m_apb_PWDATA(m_apb_PWDATA),
		.m_apb_PSTRB(m_apb_PSTRB),
		.m_apb_PPROT(m_apb_PPROT),
		.m_apb_PRDATA(m_apb_PRDATA),
		.m_apb_PSLVERR(m_apb_PSLVERR),
		.m_apb_PREADY(m_apb_PREADY),
		.cmd_valid(w_cmd_valid_apb),
		.cmd_ready(r_cmd_ready_apb),
		.cmd_data(r_cmd_data_apb),
		.rsp_valid(r_rsp_valid_apb),
		.rsp_ready(w_rsp_ready_apb),
		.rsp_data(r_rsp_data_apb)
	);
endmodule
