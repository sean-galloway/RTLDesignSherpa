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
module dma_address_gen (
	i_clk,
	i_rst_n,
	i_cfg_base_addr,
	i_cfg_stride_0,
	i_cfg_stride_1,
	i_cfg_wrap_mask_0,
	i_cfg_wrap_mask_1,
	i_req_valid,
	o_req_ready,
	i_req_index_0,
	i_req_index_1,
	i_req_tag,
	o_result_valid,
	i_result_ready,
	o_result_addr,
	o_result_tag
);
	reg _sv2v_0;
	parameter signed [31:0] ADDR_WIDTH = 40;
	parameter signed [31:0] INDEX_WIDTH = 16;
	parameter signed [31:0] STRIDE_WIDTH = 24;
	parameter signed [31:0] TAG_WIDTH = 8;
	input wire i_clk;
	input wire i_rst_n;
	input wire [ADDR_WIDTH - 1:0] i_cfg_base_addr;
	input wire signed [STRIDE_WIDTH - 1:0] i_cfg_stride_0;
	input wire signed [STRIDE_WIDTH - 1:0] i_cfg_stride_1;
	input wire [ADDR_WIDTH - 1:0] i_cfg_wrap_mask_0;
	input wire [ADDR_WIDTH - 1:0] i_cfg_wrap_mask_1;
	input wire i_req_valid;
	output wire o_req_ready;
	input wire [INDEX_WIDTH - 1:0] i_req_index_0;
	input wire [INDEX_WIDTH - 1:0] i_req_index_1;
	input wire [TAG_WIDTH - 1:0] i_req_tag;
	output wire o_result_valid;
	input wire i_result_ready;
	output wire [ADDR_WIDTH - 1:0] o_result_addr;
	output wire [TAG_WIDTH - 1:0] o_result_tag;
	localparam signed [31:0] PRODUCT_WIDTH = INDEX_WIDTH + STRIDE_WIDTH;
	wire signed [PRODUCT_WIDTH:0] w_s1_raw_offset_0;
	wire signed [PRODUCT_WIDTH:0] w_s1_raw_offset_1;
	assign w_s1_raw_offset_0 = $signed({1'b0, i_req_index_0}) * i_cfg_stride_0;
	assign w_s1_raw_offset_1 = $signed({1'b0, i_req_index_1}) * i_cfg_stride_1;
	reg [ADDR_WIDTH - 1:0] w_s1_offset_0;
	reg [ADDR_WIDTH - 1:0] w_s1_offset_1;
	function automatic signed [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5_signed;
		input reg signed [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		if (i_cfg_wrap_mask_0 != {ADDR_WIDTH {1'sb0}})
			w_s1_offset_0 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_0) & i_cfg_wrap_mask_0;
		else
			w_s1_offset_0 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_0);
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if (i_cfg_wrap_mask_1 != {ADDR_WIDTH {1'sb0}})
			w_s1_offset_1 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_1) & i_cfg_wrap_mask_1;
		else
			w_s1_offset_1 = sv2v_cast_A5DC5_signed(w_s1_raw_offset_1);
	end
	reg r_s1_valid;
	reg [ADDR_WIDTH - 1:0] r_s1_offset_0;
	reg [ADDR_WIDTH - 1:0] r_s1_offset_1;
	reg [ADDR_WIDTH - 1:0] r_s1_base_addr;
	reg [TAG_WIDTH - 1:0] r_s1_tag;
	wire w_s1_ready;
	wire w_s2_ready;
	assign w_s1_ready = !r_s1_valid || w_s2_ready;
	assign o_req_ready = w_s1_ready;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_s1_valid <= 1'b0;
			r_s1_offset_0 <= 1'sb0;
			r_s1_offset_1 <= 1'sb0;
			r_s1_base_addr <= 1'sb0;
			r_s1_tag <= 1'sb0;
		end
		else if (i_req_valid && w_s1_ready) begin
			r_s1_valid <= 1'b1;
			r_s1_offset_0 <= w_s1_offset_0;
			r_s1_offset_1 <= w_s1_offset_1;
			r_s1_base_addr <= i_cfg_base_addr;
			r_s1_tag <= i_req_tag;
		end
		else if (w_s2_ready)
			r_s1_valid <= 1'b0;
	wire [ADDR_WIDTH - 1:0] w_s2_addr;
	assign w_s2_addr = (r_s1_base_addr + r_s1_offset_0) + r_s1_offset_1;
	reg r_s2_valid;
	reg [ADDR_WIDTH - 1:0] r_s2_addr;
	reg [TAG_WIDTH - 1:0] r_s2_tag;
	assign w_s2_ready = !r_s2_valid || i_result_ready;
	always @(posedge i_clk or negedge i_rst_n)
		if (!i_rst_n) begin
			r_s2_valid <= 1'b0;
			r_s2_addr <= 1'sb0;
			r_s2_tag <= 1'sb0;
		end
		else if (r_s1_valid && w_s2_ready) begin
			r_s2_valid <= 1'b1;
			r_s2_addr <= w_s2_addr;
			r_s2_tag <= r_s1_tag;
		end
		else if (i_result_ready)
			r_s2_valid <= 1'b0;
	assign o_result_valid = r_s2_valid;
	assign o_result_addr = r_s2_addr;
	assign o_result_tag = r_s2_tag;
	initial _sv2v_0 = 0;
endmodule
module stream_run_addr_gen (
	clk,
	rst_n,
	start,
	cfg_per_beat,
	cfg_base_addr,
	cfg_stride_0,
	cfg_stride_1,
	cfg_wrap_mask_0,
	cfg_wrap_mask_1,
	cfg_inner_count,
	cfg_total_beats,
	o_base_valid,
	i_base_ready,
	o_base_addr
);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] STRIDE_WIDTH = 32;
	parameter signed [31:0] INDEX_WIDTH = 16;
	parameter signed [31:0] FIFO_DEPTH = 4;
	parameter signed [31:0] BEATS_WIDTH = 32;
	input wire clk;
	input wire rst_n;
	input wire start;
	input wire cfg_per_beat;
	input wire [ADDR_WIDTH - 1:0] cfg_base_addr;
	input wire signed [STRIDE_WIDTH - 1:0] cfg_stride_0;
	input wire signed [STRIDE_WIDTH - 1:0] cfg_stride_1;
	input wire [ADDR_WIDTH - 1:0] cfg_wrap_mask_0;
	input wire [ADDR_WIDTH - 1:0] cfg_wrap_mask_1;
	input wire [INDEX_WIDTH - 1:0] cfg_inner_count;
	input wire [BEATS_WIDTH - 1:0] cfg_total_beats;
	output wire o_base_valid;
	input wire i_base_ready;
	output wire [ADDR_WIDTH - 1:0] o_base_addr;
	reg r_per_beat;
	reg [ADDR_WIDTH - 1:0] r_base_addr;
	reg signed [STRIDE_WIDTH - 1:0] r_stride_0;
	reg signed [STRIDE_WIDTH - 1:0] r_stride_1;
	reg [ADDR_WIDTH - 1:0] r_wrap_mask_0;
	reg [ADDR_WIDTH - 1:0] r_wrap_mask_1;
	reg [BEATS_WIDTH - 1:0] r_total_beats;
	reg [INDEX_WIDTH - 1:0] r_inner_count;
	reg [INDEX_WIDTH - 1:0] r_i0;
	reg [INDEX_WIDTH - 1:0] r_i1;
	reg [BEATS_WIDTH - 1:0] r_gen_beats;
	reg r_gen_active;
	wire [INDEX_WIDTH - 1:0] w_start_inner;
	function automatic signed [INDEX_WIDTH - 1:0] sv2v_cast_5F989_signed;
		input reg signed [INDEX_WIDTH - 1:0] inp;
		sv2v_cast_5F989_signed = inp;
	endfunction
	assign w_start_inner = (cfg_inner_count == {INDEX_WIDTH {1'sb0}} ? sv2v_cast_5F989_signed(1) : cfg_inner_count);
	wire [BEATS_WIDTH - 1:0] w_step;
	function automatic signed [BEATS_WIDTH - 1:0] sv2v_cast_DF906_signed;
		input reg signed [BEATS_WIDTH - 1:0] inp;
		sv2v_cast_DF906_signed = inp;
	endfunction
	function automatic [BEATS_WIDTH - 1:0] sv2v_cast_DF906;
		input reg [BEATS_WIDTH - 1:0] inp;
		sv2v_cast_DF906 = inp;
	endfunction
	assign w_step = (r_per_beat ? sv2v_cast_DF906_signed(1) : sv2v_cast_DF906(r_inner_count));
	wire w_more;
	assign w_more = r_gen_active && (r_gen_beats < r_total_beats);
	wire w_req_valid;
	wire w_req_ready;
	wire w_res_valid;
	wire w_res_ready;
	wire [ADDR_WIDTH - 1:0] w_res_addr;
	assign w_req_valid = w_more;
	dma_address_gen #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.INDEX_WIDTH(INDEX_WIDTH),
		.STRIDE_WIDTH(STRIDE_WIDTH),
		.TAG_WIDTH(1)
	) u_addr_gen(
		.i_clk(clk),
		.i_rst_n(rst_n),
		.i_cfg_base_addr(r_base_addr),
		.i_cfg_stride_0(r_stride_0),
		.i_cfg_stride_1(r_stride_1),
		.i_cfg_wrap_mask_0(r_wrap_mask_0),
		.i_cfg_wrap_mask_1(r_wrap_mask_1),
		.i_req_valid(w_req_valid),
		.o_req_ready(w_req_ready),
		.i_req_index_0(r_i0),
		.i_req_index_1(r_i1),
		.i_req_tag(1'b0),
		.o_result_valid(w_res_valid),
		.i_result_ready(w_res_ready),
		.o_result_addr(w_res_addr),
		.o_result_tag()
	);
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_per_beat <= 1'b0;
			r_base_addr <= 1'sb0;
			r_stride_0 <= 1'sb0;
			r_stride_1 <= 1'sb0;
			r_wrap_mask_0 <= 1'sb0;
			r_wrap_mask_1 <= 1'sb0;
			r_total_beats <= 1'sb0;
			r_inner_count <= sv2v_cast_5F989_signed(1);
			r_i0 <= 1'sb0;
			r_i1 <= 1'sb0;
			r_gen_beats <= 1'sb0;
			r_gen_active <= 1'b0;
		end
		else if (start) begin
			r_per_beat <= cfg_per_beat;
			r_base_addr <= cfg_base_addr;
			r_stride_0 <= cfg_stride_0;
			r_stride_1 <= cfg_stride_1;
			r_wrap_mask_0 <= cfg_wrap_mask_0;
			r_wrap_mask_1 <= cfg_wrap_mask_1;
			r_total_beats <= cfg_total_beats;
			r_inner_count <= w_start_inner;
			r_gen_active <= 1'b1;
			if (cfg_per_beat) begin
				r_gen_beats <= sv2v_cast_DF906_signed(1);
				if (w_start_inner > sv2v_cast_5F989_signed(1)) begin
					r_i0 <= sv2v_cast_5F989_signed(1);
					r_i1 <= 1'sb0;
				end
				else begin
					r_i0 <= 1'sb0;
					r_i1 <= sv2v_cast_5F989_signed(1);
				end
			end
			else begin
				r_gen_beats <= sv2v_cast_DF906(w_start_inner);
				r_i0 <= 1'sb0;
				r_i1 <= sv2v_cast_5F989_signed(1);
			end
		end
		else if (w_req_valid && w_req_ready) begin
			r_gen_beats <= r_gen_beats + w_step;
			if (r_per_beat) begin
				if (r_i0 == (r_inner_count - sv2v_cast_5F989_signed(1))) begin
					r_i0 <= 1'sb0;
					r_i1 <= r_i1 + sv2v_cast_5F989_signed(1);
				end
				else
					r_i0 <= r_i0 + sv2v_cast_5F989_signed(1);
			end
			else
				r_i1 <= r_i1 + sv2v_cast_5F989_signed(1);
		end
	wire w_fifo_wr_ready;
	assign w_res_ready = w_fifo_wr_ready;
	gaxi_fifo_sync #(
		.DATA_WIDTH(ADDR_WIDTH),
		.DEPTH(FIFO_DEPTH)
	) i_addr_fifo(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(w_res_valid),
		.wr_ready(w_fifo_wr_ready),
		.wr_data(w_res_addr),
		.rd_valid(o_base_valid),
		.rd_ready(i_base_ready),
		.rd_data(o_base_addr),
		.count()
	);
endmodule
module scheduler (
	clk,
	rst_n,
	cfg_channel_enable,
	cfg_channel_reset,
	cfg_sched_timeout_cycles,
	cfg_sched_timeout_limit,
	cfg_sched_timeout_enable,
	cfg_rd_prefetch_enable,
	scheduler_idle,
	scheduler_state,
	descriptor_valid,
	descriptor_ready,
	descriptor_packet,
	descriptor_ext_packet,
	descriptor_error,
	sched_rd_valid,
	sched_rd_addr,
	sched_rd_beats,
	sched_wr_valid,
	sched_wr_ready,
	sched_wr_addr,
	sched_wr_beats,
	sched_rd_done_strobe,
	sched_rd_beats_done,
	sched_wr_done_strobe,
	sched_wr_beats_done,
	sched_wr_commit_strobe,
	sched_wr_commit_beats,
	sched_rd_error,
	sched_wr_error,
	sched_error,
	dbg_descriptor_error,
	dbg_read_error_sticky,
	dbg_write_error_sticky,
	dbg_timeout_expired,
	i_mon_time,
	mon_valid,
	mon_ready,
	mon_packet,
	mon_timestamp
);
	reg _sv2v_0;
	parameter signed [31:0] CHANNEL_ID = 0;
	parameter [0:0] GEN_MON = 1'b1;
	parameter signed [31:0] NUM_CHANNELS = 8;
	parameter signed [31:0] CHAN_WIDTH = (NUM_CHANNELS > 1 ? $clog2(NUM_CHANNELS) : 1);
	parameter signed [31:0] ADDR_WIDTH = 64;
	parameter signed [31:0] DATA_WIDTH = 512;
	parameter [15:0] MON_AGENT_ID = 16'h0040;
	parameter [7:0] MON_UNIT_ID = 8'h01;
	parameter [8:0] MON_CHANNEL_ID = 9'h000;
	parameter signed [31:0] DESC_WIDTH = 256;
	parameter signed [31:0] USE_ROW_COL_MAJOR_ADDRESSING = 1;
	input wire clk;
	input wire rst_n;
	input wire cfg_channel_enable;
	input wire cfg_channel_reset;
	input wire [31:0] cfg_sched_timeout_cycles;
	input wire [7:0] cfg_sched_timeout_limit;
	input wire cfg_sched_timeout_enable;
	input wire cfg_rd_prefetch_enable;
	output wire scheduler_idle;
	output wire [6:0] scheduler_state;
	input wire descriptor_valid;
	output wire descriptor_ready;
	input wire [DESC_WIDTH - 1:0] descriptor_packet;
	input wire [255:0] descriptor_ext_packet;
	input wire descriptor_error;
	output wire sched_rd_valid;
	output wire [ADDR_WIDTH - 1:0] sched_rd_addr;
	output wire [31:0] sched_rd_beats;
	output wire sched_wr_valid;
	input wire sched_wr_ready;
	output wire [ADDR_WIDTH - 1:0] sched_wr_addr;
	output wire [31:0] sched_wr_beats;
	input wire sched_rd_done_strobe;
	input wire [31:0] sched_rd_beats_done;
	input wire sched_wr_done_strobe;
	input wire [31:0] sched_wr_beats_done;
	input wire sched_wr_commit_strobe;
	input wire [31:0] sched_wr_commit_beats;
	input wire sched_rd_error;
	input wire sched_wr_error;
	output wire sched_error;
	output wire dbg_descriptor_error;
	output wire dbg_read_error_sticky;
	output wire dbg_write_error_sticky;
	output wire dbg_timeout_expired;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] i_mon_time;
	output wire mon_valid;
	input wire mon_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	output wire [127:0] mon_packet;
	output wire [63:0] mon_timestamp;
	initial if (DESC_WIDTH != 256) begin
		$display("Fatal [%0t] /mnt/data/github/RTLDesignSherpa/projects/components/dmas/stream/rtl/fub/scheduler.sv:175:13 - scheduler.<unnamed_block>.<unnamed_block>\n msg: ", $time, "scheduler (STREAM): DESC_WIDTH must be 256, got %0d. For RAPIDS, use rapids_scheduler.", DESC_WIDTH);
		$finish(1);
	end
	localparam signed [31:0] DESC_SRC_ADDR_LO = 0;
	localparam signed [31:0] DESC_SRC_ADDR_HI = 63;
	localparam signed [31:0] DESC_DST_ADDR_LO = 64;
	localparam signed [31:0] DESC_DST_ADDR_HI = 127;
	localparam signed [31:0] DESC_LENGTH_LO = 128;
	localparam signed [31:0] DESC_LENGTH_HI = 159;
	localparam signed [31:0] DESC_NEXT_PTR_LO = 160;
	localparam signed [31:0] DESC_NEXT_PTR_HI = 191;
	localparam signed [31:0] DESC_VALID_BIT = 192;
	localparam signed [31:0] DESC_GEN_IRQ = 193;
	localparam signed [31:0] DESC_LAST = 194;
	wire w_pkt_error;
	reg w_pkt_last;
	reg w_pkt_gen_irq;
	reg w_pkt_valid;
	reg [31:0] w_pkt_next_descriptor_ptr;
	reg [31:0] w_pkt_length;
	reg [63:0] w_pkt_dst_addr;
	reg [63:0] w_pkt_src_addr;
	reg [6:0] r_current_state;
	reg [6:0] w_next_state;
	wire w_state_idle = r_current_state == 7'b0000001;
	wire w_state_fetch_desc = r_current_state == 7'b0000010;
	wire w_state_xfer_data = r_current_state == 7'b0000100;
	wire w_state_complete = r_current_state == 7'b0001000;
	wire w_state_next_desc = r_current_state == 7'b0010000;
	wire w_state_error = r_current_state == 7'b0100000;
	reg r_channel_reset_active;
	reg [271:0] r_descriptor;
	reg r_descriptor_loaded;
	reg [ADDR_WIDTH - 1:0] r_src_addr;
	reg [ADDR_WIDTH - 1:0] r_dst_addr;
	reg [31:0] r_beats_remaining;
	reg [31:0] r_read_beats_remaining;
	reg [31:0] r_write_beats_remaining;
	reg [31:0] r_write_beats_to_commit;
	reg [255:0] r_descriptor_ext;
	reg r_is_ext;
	wire w_is_ext;
	assign w_is_ext = r_is_ext;
	wire [255:0] w_descriptor_ext_in;
	wire w_is_ext_in;
	assign w_descriptor_ext_in = descriptor_ext_packet;
	assign w_is_ext_in = (USE_ROW_COL_MAJOR_ADDRESSING != 0) && (descriptor_packet[210:208] == 3'd1);
	reg [31:0] r_rd_run_remaining;
	reg [31:0] r_wr_run_remaining;
	wire w_rd_base_valid;
	wire w_rd_base_ready;
	wire [ADDR_WIDTH - 1:0] w_rd_base_addr;
	wire w_wr_base_valid;
	wire w_wr_base_ready;
	wire [ADDR_WIDTH - 1:0] w_wr_base_addr;
	wire w_rd_need_base;
	wire w_wr_need_base;
	assign w_rd_need_base = (w_is_ext && (r_rd_run_remaining == 32'h00000000)) && (r_read_beats_remaining != 32'h00000000);
	assign w_wr_need_base = (w_is_ext && (r_wr_run_remaining == 32'h00000000)) && (r_write_beats_remaining != 32'h00000000);
	assign w_rd_base_ready = w_rd_need_base;
	assign w_wr_base_ready = w_wr_need_base;
	reg r_fetch_desc_d;
	wire w_addrgen_start;
	assign w_addrgen_start = (w_state_fetch_desc && !r_fetch_desc_d) && w_is_ext;
	localparam signed [31:0] stream_pkg_STREAM_ADDRGEN_STRIDE_WIDTH = 32;
	function automatic signed [31:0] sv2v_cast_32_signed;
		input reg signed [31:0] inp;
		sv2v_cast_32_signed = inp;
	endfunction
	localparam signed [31:0] BEAT_BYTES = sv2v_cast_32_signed(DATA_WIDTH / 8);
	reg r_rd_per_beat;
	reg r_wr_per_beat;
	wire w_rd_per_beat;
	wire w_wr_per_beat;
	assign w_rd_per_beat = r_rd_per_beat;
	assign w_wr_per_beat = r_wr_per_beat;
	wire [31:0] w_rd_inner_beats;
	wire [31:0] w_wr_inner_beats;
	assign w_rd_inner_beats = (r_descriptor_ext[79-:16] == {16 {1'sb0}} ? 32'd1 : {16'h0000, r_descriptor_ext[79-:16]});
	assign w_wr_inner_beats = (r_descriptor_ext[175-:16] == {16 {1'sb0}} ? 32'd1 : {16'h0000, r_descriptor_ext[175-:16]});
	wire [31:0] w_rd_run_size;
	wire [31:0] w_wr_run_size;
	assign w_rd_run_size = (w_rd_per_beat ? 32'd1 : w_rd_inner_beats);
	assign w_wr_run_size = (w_wr_per_beat ? 32'd1 : w_wr_inner_beats);
	wire [31:0] w_rd_run_init;
	wire [31:0] w_wr_run_init;
	assign w_rd_run_init = (!w_is_ext ? r_descriptor[159-:32] : (w_rd_run_size < r_descriptor[159-:32] ? w_rd_run_size : r_descriptor[159-:32]));
	assign w_wr_run_init = (!w_is_ext ? r_descriptor[159-:32] : (w_wr_run_size < r_descriptor[159-:32] ? w_wr_run_size : r_descriptor[159-:32]));
	reg [31:0] r_timeout_counter;
	wire w_timeout_expired;
	reg [7:0] r_timeout_strikes;
	wire w_hard_error;
	wire w_timeout_escalate;
	reg r_read_error_sticky;
	reg r_write_error_sticky;
	reg r_descriptor_error;
	reg r_mon_valid;
	reg [127:0] r_mon_packet;
	reg [63:0] r_mon_timestamp;
	reg r_error_pkt_sent;
	wire w_read_complete;
	wire w_write_issued;
	wire w_write_complete;
	wire w_transfer_complete;
	wire w_desc_launch;
	reg [31:0] w_ctc_next;
	wire w_ctc_add_en;
	wire [31:0] w_ctc_add_len;
	reg [31:0] r_ctc_pending_add;
	reg r_rd_ahead;
	wire w_desc_chained;
	reg r_desc_chained;
	wire w_rd_prefetch_en;
	wire w_rd_peek;
	wire w_wr_advance;
	wire [63:0] w_next_src_addr;
	wire [63:0] w_next_dst_addr;
	wire [31:0] w_next_length;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_channel_reset_active <= 1'b0;
		else
			r_channel_reset_active <= cfg_channel_reset;
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_current_state <= 7'b0000001;
		else
			r_current_state <= w_next_state;
	always @(*) begin
		if (_sv2v_0)
			;
		w_next_state = r_current_state;
		if (r_channel_reset_active)
			w_next_state = 7'b0000001;
		else if (w_hard_error || w_timeout_escalate)
			w_next_state = 7'b0100000;
		else
			case (r_current_state)
				7'b0000001:
					if (descriptor_valid && cfg_channel_enable)
						w_next_state = 7'b0000010;
				7'b0000010:
					if (r_descriptor[192])
						w_next_state = 7'b0000100;
					else
						w_next_state = 7'b0100000;
				7'b0000100:
					if (w_wr_advance)
						w_next_state = 7'b0000100;
					else if (w_transfer_complete && !r_rd_ahead)
						w_next_state = 7'b0001000;
				7'b0001000:
					if ((r_descriptor[191-:32] != 32'h00000000) && !r_descriptor[194])
						w_next_state = 7'b0010000;
					else if (w_write_complete)
						w_next_state = 7'b0000001;
				7'b0010000:
					if (descriptor_valid)
						w_next_state = 7'b0000010;
				7'b0100000: w_next_state = 7'b0100000;
				default: w_next_state = 7'b0100000;
			endcase
	end
	always @(*) begin
		if (_sv2v_0)
			;
		w_pkt_last = r_descriptor[194];
		w_pkt_gen_irq = r_descriptor[193];
		w_pkt_valid = r_descriptor[192];
		w_pkt_next_descriptor_ptr = r_descriptor[191-:32];
		w_pkt_length = r_descriptor[159-:32];
		w_pkt_dst_addr = r_descriptor[127-:64];
		w_pkt_src_addr = r_descriptor[63-:64];
	end
	function automatic [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5;
		input reg [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5 = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_descriptor <= 1'sb0;
			r_descriptor_ext <= 1'sb0;
			r_descriptor_loaded <= 1'b0;
			r_src_addr <= 1'sb0;
			r_dst_addr <= 1'sb0;
			r_beats_remaining <= 32'h00000000;
			r_read_beats_remaining <= 32'h00000000;
			r_write_beats_remaining <= 32'h00000000;
			r_rd_run_remaining <= 32'h00000000;
			r_wr_run_remaining <= 32'h00000000;
			r_is_ext <= 1'b0;
			r_rd_per_beat <= 1'b0;
			r_wr_per_beat <= 1'b0;
			r_fetch_desc_d <= 1'b0;
			r_rd_ahead <= 1'b0;
			r_desc_chained <= 1'b0;
		end
		else begin
			r_fetch_desc_d <= w_state_fetch_desc;
			if ((((r_current_state == 7'b0000001) || (r_current_state == 7'b0010000)) && descriptor_valid) && descriptor_ready) begin
				r_descriptor[63-:64] <= descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
				r_descriptor[127-:64] <= descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
				r_descriptor[159-:32] <= descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
				r_descriptor[191-:32] <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
				r_descriptor[192] <= descriptor_packet[DESC_VALID_BIT];
				r_descriptor[193] <= descriptor_packet[DESC_GEN_IRQ];
				r_descriptor[194] <= descriptor_packet[DESC_LAST];
				r_descriptor[210-:3] <= descriptor_packet[210:208];
				r_descriptor_ext <= descriptor_ext_packet;
				r_is_ext <= w_is_ext_in;
				r_desc_chained <= (descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO] != 32'h00000000) && !descriptor_packet[DESC_LAST];
				r_rd_per_beat <= w_is_ext_in && ($signed(w_descriptor_ext_in[31-:32]) != BEAT_BYTES);
				r_wr_per_beat <= w_is_ext_in && ($signed(w_descriptor_ext_in[127-:32]) != BEAT_BYTES);
				r_descriptor_loaded <= 1'b1;
			end
			case (r_current_state)
				7'b0000010: begin
					r_src_addr <= r_descriptor[ADDR_WIDTH - 1:0];
					r_dst_addr <= r_descriptor[63 + ADDR_WIDTH:64];
					r_beats_remaining <= r_descriptor[159-:32];
					r_read_beats_remaining <= r_descriptor[159-:32];
					r_write_beats_remaining <= r_descriptor[159-:32];
					r_rd_run_remaining <= w_rd_run_init;
					r_wr_run_remaining <= w_wr_run_init;
				end
				7'b0000100: begin
					if (sched_rd_done_strobe) begin
						r_read_beats_remaining <= (r_read_beats_remaining >= sched_rd_beats_done ? r_read_beats_remaining - sched_rd_beats_done : 32'h00000000);
						r_src_addr <= r_src_addr + (sv2v_cast_A5DC5(sched_rd_beats_done) << $clog2(DATA_WIDTH / 8));
						if (w_is_ext)
							r_rd_run_remaining <= (r_rd_run_remaining >= sched_rd_beats_done ? r_rd_run_remaining - sched_rd_beats_done : 32'h00000000);
					end
					if (w_rd_need_base && w_rd_base_valid) begin
						r_src_addr <= w_rd_base_addr;
						r_rd_run_remaining <= (r_read_beats_remaining >= w_rd_run_size ? w_rd_run_size : r_read_beats_remaining);
					end
					if (sched_wr_done_strobe) begin
						r_write_beats_remaining <= (r_write_beats_remaining >= sched_wr_beats_done ? r_write_beats_remaining - sched_wr_beats_done : 32'h00000000);
						r_dst_addr <= r_dst_addr + (sv2v_cast_A5DC5(sched_wr_beats_done) << $clog2(DATA_WIDTH / 8));
						if (w_is_ext)
							r_wr_run_remaining <= (r_wr_run_remaining >= sched_wr_beats_done ? r_wr_run_remaining - sched_wr_beats_done : 32'h00000000);
					end
					if (w_wr_need_base && w_wr_base_valid) begin
						r_dst_addr <= w_wr_base_addr;
						r_wr_run_remaining <= (r_write_beats_remaining >= w_wr_run_size ? w_wr_run_size : r_write_beats_remaining);
					end
				end
				7'b0001000: r_descriptor_loaded <= 1'b0;
				default:
					;
			endcase
			if (w_rd_peek) begin
				r_src_addr <= w_next_src_addr[ADDR_WIDTH - 1:0];
				r_read_beats_remaining <= w_next_length;
				r_rd_run_remaining <= w_next_length;
				r_rd_ahead <= 1'b1;
			end
			if (w_wr_advance) begin
				r_dst_addr <= w_next_dst_addr[ADDR_WIDTH - 1:0];
				r_write_beats_remaining <= w_next_length;
				r_wr_run_remaining <= w_next_length;
				r_descriptor[63-:64] <= w_next_src_addr;
				r_descriptor[127-:64] <= w_next_dst_addr;
				r_descriptor[159-:32] <= w_next_length;
				r_descriptor[191-:32] <= descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO];
				r_descriptor[192] <= descriptor_packet[DESC_VALID_BIT];
				r_descriptor[193] <= descriptor_packet[DESC_GEN_IRQ];
				r_descriptor[194] <= descriptor_packet[DESC_LAST];
				r_descriptor[210-:3] <= descriptor_packet[210:208];
				r_is_ext <= w_is_ext_in;
				r_desc_chained <= (descriptor_packet[DESC_NEXT_PTR_HI:DESC_NEXT_PTR_LO] != 32'h00000000) && !descriptor_packet[DESC_LAST];
				if (!r_rd_ahead) begin
					r_src_addr <= w_next_src_addr[ADDR_WIDTH - 1:0];
					r_read_beats_remaining <= w_next_length;
					r_rd_run_remaining <= w_next_length;
				end
				r_rd_ahead <= 1'b0;
			end
			if (r_channel_reset_active) begin
				r_descriptor_loaded <= 1'b0;
				r_read_beats_remaining <= 32'h00000000;
				r_write_beats_remaining <= 32'h00000000;
				r_rd_ahead <= 1'b0;
			end
		end
	assign w_read_complete = r_read_beats_remaining == 32'h00000000;
	assign w_desc_launch = w_state_fetch_desc && (w_next_state == 7'b0000100);
	assign w_ctc_add_en = w_desc_launch || w_wr_advance;
	assign w_ctc_add_len = (w_desc_launch ? r_descriptor[159-:32] : w_next_length);
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_ctc_pending_add <= 32'h00000000;
		else if (r_channel_reset_active)
			r_ctc_pending_add <= 32'h00000000;
		else
			r_ctc_pending_add <= (w_ctc_add_en ? w_ctc_add_len : 32'h00000000);
	always @(*) begin
		if (_sv2v_0)
			;
		w_ctc_next = r_write_beats_to_commit + r_ctc_pending_add;
		if (sched_wr_commit_strobe)
			w_ctc_next = (w_ctc_next >= sched_wr_commit_beats ? w_ctc_next - sched_wr_commit_beats : 32'h00000000);
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_write_beats_to_commit <= 32'h00000000;
		else if (r_channel_reset_active)
			r_write_beats_to_commit <= 32'h00000000;
		else
			r_write_beats_to_commit <= w_ctc_next;
	assign w_write_issued = r_write_beats_remaining == 32'h00000000;
	assign w_write_complete = r_write_beats_to_commit == 32'h00000000;
	assign w_transfer_complete = w_read_complete && w_write_issued;
	assign w_next_src_addr = descriptor_packet[DESC_SRC_ADDR_HI:DESC_SRC_ADDR_LO];
	assign w_next_dst_addr = descriptor_packet[DESC_DST_ADDR_HI:DESC_DST_ADDR_LO];
	assign w_next_length = descriptor_packet[DESC_LENGTH_HI:DESC_LENGTH_LO];
	assign w_desc_chained = r_desc_chained;
	assign w_rd_prefetch_en = (cfg_rd_prefetch_enable && !w_is_ext) && !w_is_ext_in;
	assign w_rd_peek = (((((w_rd_prefetch_en && w_state_xfer_data) && !r_rd_ahead) && (r_read_beats_remaining == 32'h00000000)) && !w_write_issued) && w_desc_chained) && descriptor_valid;
	assign w_wr_advance = (((w_rd_prefetch_en && w_state_xfer_data) && w_write_issued) && w_desc_chained) && descriptor_valid;
	wire w_sched_rd_completing_this_cycle;
	wire w_sched_wr_completing_this_cycle;
	assign w_sched_rd_completing_this_cycle = sched_rd_done_strobe && (r_read_beats_remaining <= sched_rd_beats_done);
	assign w_sched_wr_completing_this_cycle = sched_wr_done_strobe && (r_write_beats_remaining <= sched_wr_beats_done);
	assign sched_rd_valid = (((r_current_state == 7'b0000100) && !w_read_complete) && !w_sched_rd_completing_this_cycle) && !w_rd_need_base;
	assign sched_rd_addr = r_src_addr;
	assign sched_rd_beats = (w_is_ext ? r_rd_run_remaining : r_read_beats_remaining);
	assign sched_wr_valid = ((((r_current_state == 7'b0000100) && (r_write_beats_remaining != 32'h00000000)) && !w_write_complete) && !w_sched_wr_completing_this_cycle) && !w_wr_need_base;
	assign sched_wr_addr = r_dst_addr;
	assign sched_wr_beats = (w_is_ext ? r_wr_run_remaining : r_write_beats_remaining);
	localparam signed [31:0] stream_pkg_STREAM_ADDRGEN_INDEX_WIDTH = 16;
	localparam signed [31:0] stream_pkg_STREAM_ADDR_WIDTH = 64;
	function automatic [63:0] stream_pkg_wrap_log2_to_mask;
		input reg [5:0] wrap_log2;
		stream_pkg_wrap_log2_to_mask = (wrap_log2 == 6'd0 ? {64 {1'sb0}} : (64'h0000000000000001 << wrap_log2) - 64'h0000000000000001);
	endfunction
	generate
		if (USE_ROW_COL_MAJOR_ADDRESSING != 0) begin : g_addrgen
			stream_run_addr_gen #(
				.ADDR_WIDTH(ADDR_WIDTH),
				.STRIDE_WIDTH(stream_pkg_STREAM_ADDRGEN_STRIDE_WIDTH),
				.INDEX_WIDTH(stream_pkg_STREAM_ADDRGEN_INDEX_WIDTH),
				.FIFO_DEPTH(4),
				.BEATS_WIDTH(32)
			) u_rd_addr_gen(
				.clk(clk),
				.rst_n(rst_n),
				.start(w_addrgen_start),
				.cfg_per_beat(w_rd_per_beat),
				.cfg_base_addr(r_descriptor[ADDR_WIDTH - 1:0]),
				.cfg_stride_0($signed(r_descriptor_ext[31-:32])),
				.cfg_stride_1($signed(r_descriptor_ext[63-:32])),
				.cfg_wrap_mask_0(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[85-:6]))),
				.cfg_wrap_mask_1(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[91-:6]))),
				.cfg_inner_count(r_descriptor_ext[79-:16]),
				.cfg_total_beats(r_descriptor[159-:32]),
				.o_base_valid(w_rd_base_valid),
				.i_base_ready(w_rd_base_ready),
				.o_base_addr(w_rd_base_addr)
			);
			stream_run_addr_gen #(
				.ADDR_WIDTH(ADDR_WIDTH),
				.STRIDE_WIDTH(stream_pkg_STREAM_ADDRGEN_STRIDE_WIDTH),
				.INDEX_WIDTH(stream_pkg_STREAM_ADDRGEN_INDEX_WIDTH),
				.FIFO_DEPTH(4),
				.BEATS_WIDTH(32)
			) u_wr_addr_gen(
				.clk(clk),
				.rst_n(rst_n),
				.start(w_addrgen_start),
				.cfg_per_beat(w_wr_per_beat),
				.cfg_base_addr(r_descriptor[63 + ADDR_WIDTH:64]),
				.cfg_stride_0($signed(r_descriptor_ext[127-:32])),
				.cfg_stride_1($signed(r_descriptor_ext[159-:32])),
				.cfg_wrap_mask_0(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[181-:6]))),
				.cfg_wrap_mask_1(sv2v_cast_A5DC5(stream_pkg_wrap_log2_to_mask(r_descriptor_ext[187-:6]))),
				.cfg_inner_count(r_descriptor_ext[175-:16]),
				.cfg_total_beats(r_descriptor[159-:32]),
				.o_base_valid(w_wr_base_valid),
				.i_base_ready(w_wr_base_ready),
				.o_base_addr(w_wr_base_addr)
			);
		end
		else begin : g_no_addrgen
			assign w_rd_base_valid = 1'b0;
			assign w_rd_base_addr = 1'sb0;
			assign w_wr_base_valid = 1'b0;
			assign w_wr_base_addr = 1'sb0;
		end
	endgenerate
	assign descriptor_ready = ((r_current_state == 7'b0000001) || (r_current_state == 7'b0010000)) || w_wr_advance;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_timeout_counter <= 32'h00000000;
			r_timeout_strikes <= 8'h00;
			r_read_error_sticky <= 1'b0;
			r_write_error_sticky <= 1'b0;
			r_descriptor_error <= 1'b0;
		end
		else begin
			if (sched_wr_done_strobe || sched_wr_commit_strobe)
				r_timeout_counter <= 32'h00000000;
			else if (w_timeout_expired)
				r_timeout_counter <= 32'h00000000;
			else if (sched_wr_valid && !sched_wr_ready)
				r_timeout_counter <= r_timeout_counter + 1;
			else
				r_timeout_counter <= 32'h00000000;
			if (r_channel_reset_active || (r_current_state == 7'b0000001))
				r_timeout_strikes <= 8'h00;
			else if (sched_wr_done_strobe || sched_wr_commit_strobe)
				r_timeout_strikes <= 8'h00;
			else if (w_timeout_expired && !(&r_timeout_strikes))
				r_timeout_strikes <= r_timeout_strikes + 8'h01;
			if (descriptor_error)
				r_descriptor_error <= 1'b1;
			if (sched_rd_error)
				r_read_error_sticky <= 1'b1;
			if (sched_wr_error)
				r_write_error_sticky <= 1'b1;
			if ((sched_rd_error || sched_wr_error) || w_timeout_escalate)
				r_descriptor_error <= 1'b1;
			if (r_current_state == 7'b0000001) begin
				r_read_error_sticky <= 1'b0;
				r_write_error_sticky <= 1'b0;
				r_descriptor_error <= 1'b0;
			end
		end
	assign w_timeout_expired = cfg_sched_timeout_enable && (r_timeout_counter >= cfg_sched_timeout_cycles);
	assign w_timeout_escalate = (cfg_sched_timeout_limit != 8'd0) && (r_timeout_strikes >= cfg_sched_timeout_limit);
	assign w_hard_error = (((descriptor_error || sched_rd_error) || sched_wr_error) || r_read_error_sticky) || r_write_error_sticky;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	function automatic [127:0] monitor_common_pkg_create_monitor_packet;
		input reg [3:0] packet_type;
		input reg [3:0] protocol;
		input reg [7:0] event_code;
		input reg [8:0] channel_id;
		input reg [7:0] unit_id;
		input reg [15:0] agent_id;
		input reg [63:0] event_data;
		monitor_common_pkg_create_monitor_packet = {packet_type, 15'h0000, protocol, event_code, channel_id, agent_id, unit_id, event_data};
	endfunction
	localparam [7:0] stream_pkg_STREAM_EVENT_DESC_COMPLETE = 8'h01;
	localparam [7:0] stream_pkg_STREAM_EVENT_DESC_START = 8'h00;
	localparam [7:0] stream_pkg_STREAM_EVENT_ERROR = 8'h0f;
	localparam [7:0] stream_pkg_STREAM_EVENT_IRQ = 8'h07;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			r_mon_timestamp <= 1'sb0;
			r_error_pkt_sent <= 1'b0;
		end
		else begin
			r_mon_valid <= 1'b0;
			r_mon_packet <= 1'sb0;
			if (r_current_state == 7'b0000001)
				r_error_pkt_sent <= 1'b0;
			case (r_current_state)
				7'b0000010: begin
					r_mon_valid <= 1'b1;
					r_mon_timestamp <= i_mon_time;
					r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_DESC_START, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
				end
				7'b0000100:
					if (w_wr_advance) begin
						r_mon_valid <= 1'b1;
						r_mon_timestamp <= i_mon_time;
						if (r_descriptor[193])
							r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_IRQ, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
						else
							r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_DESC_COMPLETE, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
					end
				7'b0001000: begin
					r_mon_valid <= 1'b1;
					r_mon_timestamp <= i_mon_time;
					if (r_descriptor[193])
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_IRQ, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
					else
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeCompletion, 4'h4, stream_pkg_STREAM_EVENT_DESC_COMPLETE, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {32'h00000000, r_descriptor[159-:32]});
				end
				7'b0100000:
					if (!r_error_pkt_sent) begin
						r_mon_valid <= 1'b1;
						r_mon_timestamp <= i_mon_time;
						r_mon_packet <= monitor_common_pkg_create_monitor_packet(monitor_common_pkg_PktTypeError, 4'h4, stream_pkg_STREAM_EVENT_ERROR, MON_CHANNEL_ID, MON_UNIT_ID, MON_AGENT_ID, {29'h00000000, r_write_error_sticky, r_read_error_sticky, 33'h000000000});
						r_error_pkt_sent <= 1'b1;
					end
				default:
					;
			endcase
		end
	assign scheduler_idle = (r_current_state == 7'b0000001) && !r_channel_reset_active;
	assign scheduler_state = r_current_state;
	assign sched_error = w_state_error;
	assign dbg_descriptor_error = r_descriptor_error;
	assign dbg_read_error_sticky = r_read_error_sticky;
	assign dbg_write_error_sticky = r_write_error_sticky;
	assign dbg_timeout_expired = w_timeout_expired;
	assign mon_valid = (GEN_MON ? r_mon_valid : 1'b0);
	assign mon_packet = (GEN_MON ? r_mon_packet : {128 {1'sb0}});
	assign mon_timestamp = (GEN_MON ? r_mon_timestamp : {64 {1'sb0}});
	initial _sv2v_0 = 0;
endmodule
