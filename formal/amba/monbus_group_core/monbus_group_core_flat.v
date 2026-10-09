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
module math_adder_carry_save_nbit (
	i_a,
	i_b,
	i_c,
	ow_sum,
	ow_carry
);
	parameter signed [31:0] N = 4;
	input wire [N - 1:0] i_a;
	input wire [N - 1:0] i_b;
	input wire [N - 1:0] i_c;
	output wire [N - 1:0] ow_sum;
	output wire [N - 1:0] ow_carry;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_carry_save
			localparam i = _gv_i_1;
			assign ow_sum[i] = (i_a[i] ^ i_b[i]) ^ i_c[i];
			assign ow_carry[i] = ((i_a[i] & i_b[i]) | (i_a[i] & i_c[i])) | (i_b[i] & i_c[i]);
		end
	endgenerate
endmodule
module math_mod_3_compress (
	d_in,
	rem_out
);
	input wire [15:0] d_in;
	output wire [1:0] rem_out;
	localparam signed [31:0] BITS = 6;
	wire [5:0] w_g0;
	wire [5:0] w_g1;
	wire [5:0] w_g2;
	wire [5:0] w_g3;
	wire [5:0] w_g4;
	wire [5:0] w_g5;
	wire [5:0] w_g6;
	wire [5:0] w_g7;
	assign w_g0 = {{4 {1'b0}}, d_in[1:0]};
	assign w_g1 = {{4 {1'b0}}, d_in[3:2]};
	assign w_g2 = {{4 {1'b0}}, d_in[5:4]};
	assign w_g3 = {{4 {1'b0}}, d_in[7:6]};
	assign w_g4 = {{4 {1'b0}}, d_in[9:8]};
	assign w_g5 = {{4 {1'b0}}, d_in[11:10]};
	assign w_g6 = {{4 {1'b0}}, d_in[13:12]};
	assign w_g7 = {{4 {1'b0}}, d_in[15:14]};
	wire [5:0] w_sumA1;
	wire [5:0] w_carryA1;
	wire [5:0] w_sumB1;
	wire [5:0] w_carryB1;
	wire [5:0] w_sumC1;
	wire [5:0] w_carryC1;
	wire [5:0] w_sumD2;
	wire [5:0] w_carryD2;
	wire [5:0] w_sumE2;
	wire [5:0] w_carryE2;
	wire [5:0] w_sumF3;
	wire [5:0] w_carryF3;
	wire [5:0] w_sumG4;
	wire [5:0] w_carryG4;
	wire [5:0] w_grp_sum;
	math_adder_carry_save_nbit #(.N(BITS)) comp1(
		.i_a(w_g0),
		.i_b(w_g1),
		.i_c(w_g2),
		.ow_sum(w_sumA1),
		.ow_carry(w_carryA1)
	);
	math_adder_carry_save_nbit #(.N(BITS)) comp2(
		.i_a(w_g3),
		.i_b(w_g4),
		.i_c(w_g5),
		.ow_sum(w_sumB1),
		.ow_carry(w_carryB1)
	);
	math_adder_carry_save_nbit #(.N(BITS)) comp3(
		.i_a(w_g6),
		.i_b(w_g7),
		.i_c({BITS {1'b0}}),
		.ow_sum(w_sumC1),
		.ow_carry(w_carryC1)
	);
	math_adder_carry_save_nbit #(.N(BITS)) comp4(
		.i_a(w_sumA1),
		.i_b({w_carryA1[4:0], 1'b0}),
		.i_c(w_sumB1),
		.ow_sum(w_sumD2),
		.ow_carry(w_carryD2)
	);
	math_adder_carry_save_nbit #(.N(BITS)) comp5(
		.i_a({w_carryB1[4:0], 1'b0}),
		.i_b(w_sumC1),
		.i_c({w_carryC1[4:0], 1'b0}),
		.ow_sum(w_sumE2),
		.ow_carry(w_carryE2)
	);
	math_adder_carry_save_nbit #(.N(BITS)) comp6(
		.i_a(w_sumD2),
		.i_b({w_carryD2[4:0], 1'b0}),
		.i_c(w_sumE2),
		.ow_sum(w_sumF3),
		.ow_carry(w_carryF3)
	);
	math_adder_carry_save_nbit #(.N(BITS)) comp7(
		.i_a(w_sumF3),
		.i_b({w_carryF3[4:0], 1'b0}),
		.i_c({w_carryE2[4:0], 1'b0}),
		.ow_sum(w_sumG4),
		.ow_carry(w_carryG4)
	);
	assign w_grp_sum = w_sumG4 + {w_carryG4[4:0], 1'b0};
	wire [3:0] w_fold;
	assign w_fold = ({2'b00, w_grp_sum[1:0]} + {2'b00, w_grp_sum[3:2]}) + {3'b000, w_grp_sum[4]};
	function automatic [1:0] sv2v_cast_2;
		input reg [1:0] inp;
		sv2v_cast_2 = inp;
	endfunction
	assign rem_out = sv2v_cast_2((w_fold >= 4'd6 ? w_fold - 4'd6 : (w_fold >= 4'd3 ? w_fold - 4'd3 : w_fold)));
endmodule
module monbus_cam (
	clk,
	rst_n,
	access_key,
	access_hit,
	access_idx,
	access_old_data,
	access_old_ts,
	access_action,
	access_new_data,
	access_new_ts,
	cam_full,
	cam_count,
	evicted,
	evict_key,
	evict_data,
	dump_idx,
	dump_valid,
	dump_key,
	dump_data,
	soft_clear
);
	reg _sv2v_0;
	parameter signed [31:0] KEY_WIDTH = 49;
	parameter signed [31:0] DATA_WIDTH = 64;
	parameter signed [31:0] TS_WIDTH = 24;
	parameter signed [31:0] DEPTH = 32;
	parameter signed [31:0] IDX_WIDTH = (DEPTH > 1 ? $clog2(DEPTH) : 1);
	parameter signed [31:0] CNT_WIDTH = $clog2(DEPTH + 1);
	input wire clk;
	input wire rst_n;
	input wire [KEY_WIDTH - 1:0] access_key;
	output reg access_hit;
	output reg [IDX_WIDTH - 1:0] access_idx;
	output reg [DATA_WIDTH - 1:0] access_old_data;
	output reg [TS_WIDTH - 1:0] access_old_ts;
	input wire [1:0] access_action;
	input wire [DATA_WIDTH - 1:0] access_new_data;
	input wire [TS_WIDTH - 1:0] access_new_ts;
	output wire cam_full;
	output wire [CNT_WIDTH - 1:0] cam_count;
	output wire evicted;
	output wire [KEY_WIDTH - 1:0] evict_key;
	output wire [DATA_WIDTH - 1:0] evict_data;
	input wire [IDX_WIDTH - 1:0] dump_idx;
	output wire dump_valid;
	output wire [KEY_WIDTH - 1:0] dump_key;
	output wire [DATA_WIDTH - 1:0] dump_data;
	input wire soft_clear;
	localparam [1:0] ACTION_NONE = 2'b00;
	localparam [1:0] ACTION_TOUCH = 2'b01;
	localparam [1:0] ACTION_INSTALL = 2'b10;
	reg r_valid [0:DEPTH - 1];
	reg [KEY_WIDTH - 1:0] r_key [0:DEPTH - 1];
	reg [DATA_WIDTH - 1:0] r_data [0:DEPTH - 1];
	reg [TS_WIDTH - 1:0] r_ts [0:DEPTH - 1];
	reg [CNT_WIDTH - 1:0] r_count;
	reg [DEPTH - 1:0] w_match_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				w_match_oh[i] = r_valid[i] && (r_key[i] == access_key);
		end
	end
	function automatic signed [IDX_WIDTH - 1:0] sv2v_cast_34E60_signed;
		input reg signed [IDX_WIDTH - 1:0] inp;
		sv2v_cast_34E60_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		access_hit = 1'b0;
		access_idx = 1'sb0;
		access_old_data = 1'sb0;
		access_old_ts = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = DEPTH - 1; i >= 0; i = i - 1)
				if (w_match_oh[i]) begin
					access_hit = 1'b1;
					access_idx = sv2v_cast_34E60_signed(i);
					access_old_data = r_data[i];
					access_old_ts = r_ts[i];
				end
		end
	end
	assign cam_count = r_count;
	function automatic signed [CNT_WIDTH - 1:0] sv2v_cast_1924C_signed;
		input reg signed [CNT_WIDTH - 1:0] inp;
		sv2v_cast_1924C_signed = inp;
	endfunction
	assign cam_full = r_count == sv2v_cast_1924C_signed(DEPTH);
	assign evicted = (access_action == ACTION_INSTALL) && cam_full;
	assign evict_key = r_key[DEPTH - 1];
	assign evict_data = r_data[DEPTH - 1];
	assign dump_valid = r_valid[dump_idx];
	assign dump_key = r_key[dump_idx];
	assign dump_data = r_data[dump_idx];
	reg [CNT_WIDTH - 1:0] shift_to;
	reg do_shift;
	reg [KEY_WIDTH - 1:0] new_key;
	reg [DATA_WIDTH - 1:0] new_data;
	reg [TS_WIDTH - 1:0] new_ts;
	function automatic [CNT_WIDTH - 1:0] sv2v_cast_1924C;
		input reg [CNT_WIDTH - 1:0] inp;
		sv2v_cast_1924C = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		do_shift = 1'b0;
		shift_to = 1'sb0;
		new_key = access_key;
		new_data = access_new_data;
		new_ts = access_new_ts;
		(* full_case, parallel_case *)
		case (access_action)
			ACTION_TOUCH:
				if (access_hit) begin
					do_shift = 1'b1;
					shift_to = sv2v_cast_1924C(access_idx);
				end
			ACTION_INSTALL: begin
				do_shift = 1'b1;
				shift_to = (cam_full ? sv2v_cast_1924C_signed(DEPTH - 1) : r_count);
			end
			default:
				;
		endcase
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					begin
						r_valid[i] <= 1'b0;
						r_key[i] <= 1'sb0;
						r_data[i] <= 1'sb0;
						r_ts[i] <= 1'sb0;
					end
			end
			r_count <= 1'sb0;
		end
		else if (soft_clear) begin
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					r_valid[i] <= 1'b0;
			end
			r_count <= 1'sb0;
		end
		else if (do_shift) begin
			r_valid[0] <= 1'b1;
			r_key[0] <= new_key;
			r_data[0] <= new_data;
			r_ts[0] <= new_ts;
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 1; i < DEPTH; i = i + 1)
					if (sv2v_cast_1924C_signed(i) <= shift_to) begin
						r_valid[i] <= r_valid[i - 1];
						r_key[i] <= r_key[i - 1];
						r_data[i] <= r_data[i - 1];
						r_ts[i] <= r_ts[i - 1];
					end
			end
			if ((access_action == ACTION_INSTALL) && !cam_full)
				r_count <= r_count + 1'b1;
		end
	initial _sv2v_0 = 0;
endmodule
module monbus_cam_pipe (
	clk,
	rst_n,
	clear,
	access_en,
	access_key,
	access_new_data,
	access_new_ts,
	result_valid,
	result_hit,
	result_idx,
	result_old_data,
	result_old_ts,
	cam_full,
	cam_count
);
	reg _sv2v_0;
	parameter signed [31:0] KEY_WIDTH = 49;
	parameter signed [31:0] DATA_WIDTH = 64;
	parameter signed [31:0] TS_WIDTH = 24;
	parameter signed [31:0] DEPTH = 32;
	parameter signed [31:0] IDX_WIDTH = (DEPTH > 1 ? $clog2(DEPTH) : 1);
	parameter signed [31:0] CNT_WIDTH = $clog2(DEPTH + 1);
	input wire clk;
	input wire rst_n;
	input wire clear;
	input wire access_en;
	input wire [KEY_WIDTH - 1:0] access_key;
	input wire [DATA_WIDTH - 1:0] access_new_data;
	input wire [TS_WIDTH - 1:0] access_new_ts;
	output reg result_valid;
	output reg result_hit;
	output reg [IDX_WIDTH - 1:0] result_idx;
	output reg [DATA_WIDTH - 1:0] result_old_data;
	output reg [TS_WIDTH - 1:0] result_old_ts;
	output wire cam_full;
	output wire [CNT_WIDTH - 1:0] cam_count;
	localparam [1:0] ACTION_NONE = 2'b00;
	localparam [1:0] ACTION_TOUCH = 2'b01;
	localparam [1:0] ACTION_INSTALL = 2'b10;
	reg r_valid [0:DEPTH - 1];
	reg [KEY_WIDTH - 1:0] r_key [0:DEPTH - 1];
	reg [DATA_WIDTH - 1:0] r_data [0:DEPTH - 1];
	reg [TS_WIDTH - 1:0] r_ts [0:DEPTH - 1];
	reg [CNT_WIDTH - 1:0] r_count;
	assign cam_count = r_count;
	function automatic signed [CNT_WIDTH - 1:0] sv2v_cast_1924C_signed;
		input reg signed [CNT_WIDTH - 1:0] inp;
		sv2v_cast_1924C_signed = inp;
	endfunction
	assign cam_full = r_count == sv2v_cast_1924C_signed(DEPTH);
	reg [DEPTH - 1:0] w_match_oh;
	always @(*) begin
		if (_sv2v_0)
			;
		begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < DEPTH; i = i + 1)
				w_match_oh[i] = r_valid[i] && (r_key[i] == access_key);
		end
	end
	reg raw_hit;
	reg [IDX_WIDTH - 1:0] raw_idx;
	reg [DATA_WIDTH - 1:0] raw_old_data;
	reg [TS_WIDTH - 1:0] raw_old_ts;
	function automatic signed [IDX_WIDTH - 1:0] sv2v_cast_34E60_signed;
		input reg signed [IDX_WIDTH - 1:0] inp;
		sv2v_cast_34E60_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		raw_hit = 1'b0;
		raw_idx = 1'sb0;
		raw_old_data = 1'sb0;
		raw_old_ts = 1'sb0;
		begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = DEPTH - 1; i >= 0; i = i - 1)
				if (w_match_oh[i]) begin
					raw_hit = 1'b1;
					raw_idx = sv2v_cast_34E60_signed(i);
					raw_old_data = r_data[i];
					raw_old_ts = r_ts[i];
				end
		end
	end
	reg s1_valid;
	reg [1:0] s1_action;
	reg [KEY_WIDTH - 1:0] s1_key;
	reg [DATA_WIDTH - 1:0] s1_new_data;
	reg [TS_WIDTH - 1:0] s1_new_ts;
	reg [IDX_WIDTH - 1:0] s1_eff_idx;
	reg s1_eff_hit;
	reg [CNT_WIDTH - 1:0] s1_shift_to;
	reg s1_do_shift;
	reg s1_evict;
	function automatic [CNT_WIDTH - 1:0] sv2v_cast_1924C;
		input reg [CNT_WIDTH - 1:0] inp;
		sv2v_cast_1924C = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		s1_do_shift = 1'b0;
		s1_shift_to = 1'sb0;
		s1_evict = 1'b0;
		if (s1_valid) begin
			if (s1_action == ACTION_TOUCH) begin
				if (s1_eff_hit) begin
					s1_do_shift = 1'b1;
					s1_shift_to = sv2v_cast_1924C(s1_eff_idx);
				end
			end
			else if (s1_action == ACTION_INSTALL) begin
				s1_do_shift = 1'b1;
				s1_shift_to = (cam_full ? sv2v_cast_1924C_signed(DEPTH - 1) : r_count);
				s1_evict = cam_full;
			end
		end
	end
	reg eff_hit;
	reg [IDX_WIDTH - 1:0] eff_idx;
	reg [DATA_WIDTH - 1:0] eff_old_data;
	reg [TS_WIDTH - 1:0] eff_old_ts;
	always @(*) begin
		if (_sv2v_0)
			;
		eff_hit = raw_hit;
		eff_idx = raw_idx;
		eff_old_data = raw_old_data;
		eff_old_ts = raw_old_ts;
		if (s1_do_shift) begin
			if (access_key == s1_key) begin
				eff_hit = 1'b1;
				eff_idx = 1'sb0;
				eff_old_data = s1_new_data;
				eff_old_ts = s1_new_ts;
			end
			else if (raw_hit) begin
				if (s1_evict && (raw_idx == sv2v_cast_34E60_signed(DEPTH - 1)))
					eff_hit = 1'b0;
				else if (sv2v_cast_1924C(raw_idx) < s1_shift_to)
					eff_idx = raw_idx + sv2v_cast_34E60_signed(1);
			end
		end
		if (!eff_hit) begin
			eff_idx = 1'sb0;
			eff_old_data = 1'sb0;
			eff_old_ts = 1'sb0;
		end
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			begin : sv2v_autoblock_3
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					begin
						r_valid[i] <= 1'b0;
						r_key[i] <= 1'sb0;
						r_data[i] <= 1'sb0;
						r_ts[i] <= 1'sb0;
					end
			end
			r_count <= 1'sb0;
			s1_valid <= 1'b0;
			s1_action <= ACTION_NONE;
			s1_key <= 1'sb0;
			s1_new_data <= 1'sb0;
			s1_new_ts <= 1'sb0;
			s1_eff_idx <= 1'sb0;
			s1_eff_hit <= 1'b0;
			result_valid <= 1'b0;
			result_hit <= 1'b0;
			result_idx <= 1'sb0;
			result_old_data <= 1'sb0;
			result_old_ts <= 1'sb0;
		end
		else if (clear) begin
			begin : sv2v_autoblock_4
				reg signed [31:0] i;
				for (i = 0; i < DEPTH; i = i + 1)
					r_valid[i] <= 1'b0;
			end
			r_count <= 1'sb0;
			s1_valid <= 1'b0;
			result_valid <= 1'b0;
		end
		else begin
			if (s1_do_shift) begin
				r_valid[0] <= 1'b1;
				r_key[0] <= s1_key;
				r_data[0] <= s1_new_data;
				r_ts[0] <= s1_new_ts;
				begin : sv2v_autoblock_5
					reg signed [31:0] i;
					for (i = 1; i < DEPTH; i = i + 1)
						if (sv2v_cast_1924C_signed(i) <= s1_shift_to) begin
							r_valid[i] <= r_valid[i - 1];
							r_key[i] <= r_key[i - 1];
							r_data[i] <= r_data[i - 1];
							r_ts[i] <= r_ts[i - 1];
						end
				end
				if ((s1_action == ACTION_INSTALL) && !cam_full)
					r_count <= r_count + 1'b1;
			end
			if (access_en) begin
				s1_valid <= 1'b1;
				s1_action <= (eff_hit ? ACTION_TOUCH : ACTION_INSTALL);
				s1_key <= access_key;
				s1_new_data <= access_new_data;
				s1_new_ts <= access_new_ts;
				s1_eff_idx <= eff_idx;
				s1_eff_hit <= eff_hit;
				result_valid <= 1'b1;
				result_hit <= eff_hit;
				result_idx <= eff_idx;
				result_old_data <= eff_old_data;
				result_old_ts <= eff_old_ts;
			end
			else begin
				s1_valid <= 1'b0;
				result_valid <= 1'b0;
			end
		end
	initial _sv2v_0 = 0;
endmodule
module monbus_compressor (
	clk,
	rst_n,
	clear,
	in_valid,
	in_ready,
	in_packet,
	in_source_ts,
	out_valid,
	out_ready,
	out_slot,
	out_half_valid,
	out_half_slot,
	stat_tier1_a,
	stat_tier1_b,
	stat_tier1_c,
	stat_tier0,
	stat_cam_miss,
	stat_delta_ts_ovf,
	stat_event_data_ovf,
	stat_ed_delta_ovf
);
	reg _sv2v_0;
	parameter signed [31:0] HALF_BEAT_EN = 0;
	input wire clk;
	input wire rst_n;
	input wire clear;
	input wire in_valid;
	output wire in_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	input wire [127:0] in_packet;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] in_source_ts;
	output reg out_valid;
	input wire out_ready;
	output reg [63:0] out_slot;
	output wire out_half_valid;
	output wire [29:0] out_half_slot;
	output wire [31:0] stat_tier1_a;
	output wire [31:0] stat_tier1_b;
	output wire [31:0] stat_tier1_c;
	output wire [31:0] stat_tier0;
	output wire [31:0] stat_cam_miss;
	output wire [31:0] stat_delta_ts_ovf;
	output wire [31:0] stat_event_data_ovf;
	output wire [31:0] stat_ed_delta_ovf;
	localparam [3:0] TAG_RAW = 4'h0;
	localparam [3:0] TAG_FORMAT_A = 4'h1;
	localparam [3:0] TAG_FORMAT_B = 4'h2;
	localparam [3:0] TAG_FORMAT_C = 4'h3;
	localparam signed [31:0] HALF_DELTA_BITS = 10;
	localparam signed [31:0] HALF_DATA_BITS = 13;
	localparam [1:0] HSUB_A = 2'h1;
	localparam [1:0] HSUB_C = 2'h2;
	localparam signed [31:0] TS_BITS = 60;
	localparam signed [31:0] DELTA_TS_A_BITS = 15;
	localparam signed [31:0] DELTA_TS_B_BITS = 23;
	localparam signed [31:0] DELTA_TS_C_BITS = 15;
	localparam signed [31:0] EVENT_DATA_A_BITS = 40;
	localparam signed [31:0] EVENT_DATA_B_BITS = 32;
	localparam signed [31:0] EVENT_DATA_C_DELTA = 40;
	localparam signed [31:0] TMPL_IDX_BITS = 5;
	localparam signed [31:0] TMPL_IDX_SHIFT = 55;
	localparam signed [31:0] CAM_DEPTH = 32;
	localparam signed [31:0] KEY_WIDTH = 49;
	wire [3:0] in_packet_type;
	wire [3:0] in_protocol;
	wire [7:0] in_event_code;
	wire [8:0] in_channel_id;
	wire [15:0] in_agent_id;
	wire [7:0] in_unit_id;
	wire [63:0] in_event_data;
	wire [48:0] in_key;
	assign in_packet_type = in_packet[127:124];
	assign in_protocol = in_packet[108:105];
	assign in_event_code = in_packet[104:97];
	assign in_channel_id = in_packet[96:88];
	assign in_agent_id = in_packet[87:72];
	assign in_unit_id = in_packet[71:64];
	assign in_event_data = in_packet[63:0];
	assign in_key = {in_packet_type, in_protocol, in_event_code, in_channel_id, in_agent_id, in_unit_id};
	localparam signed [31:0] TS_STORE_BITS = 24;
	wire [59:0] in_src_ts60;
	wire [23:0] in_src_ts_lo;
	assign in_src_ts60 = in_source_ts[59:0];
	assign in_src_ts_lo = in_src_ts60[23:0];
	wire p_valid;
	wire p_hit;
	wire [4:0] p_idx;
	wire [63:0] p_old_data;
	wire [59:0] p_delta_ts;
	wire [63:0] p_event_data;
	wire [59:0] p_src_ts60;
	wire [127:0] p_packet;
	wire enc_commit;
	wire cam_en;
	localparam signed [31:0] SKID_DEPTH = 3;
	localparam signed [31:0] P_W = 382;
	wire pipe_res_valid;
	wire pipe_res_hit;
	wire [4:0] pipe_res_idx;
	wire [63:0] pipe_res_old_data;
	wire [23:0] pipe_res_old_ts;
	reg [2:0] r_credit;
	wire pop;
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign cam_en = (in_valid && !clear) && (r_credit < sv2v_cast_3_signed(SKID_DEPTH));
	monbus_cam_pipe #(
		.KEY_WIDTH(KEY_WIDTH),
		.DATA_WIDTH(64),
		.TS_WIDTH(TS_STORE_BITS),
		.DEPTH(CAM_DEPTH)
	) u_cam_pipe(
		.clk(clk),
		.rst_n(rst_n),
		.clear(clear),
		.access_en(cam_en),
		.access_key(in_key),
		.access_new_data(in_event_data),
		.access_new_ts(in_src_ts_lo),
		.result_valid(pipe_res_valid),
		.result_hit(pipe_res_hit),
		.result_idx(pipe_res_idx),
		.result_old_data(pipe_res_old_data),
		.result_old_ts(pipe_res_old_ts),
		.cam_full(),
		.cam_count()
	);
	reg [127:0] m_packet;
	reg [63:0] m_event_data;
	reg [59:0] m_src_ts60;
	reg [23:0] m_src_ts_lo;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			m_packet <= 1'sb0;
			m_event_data <= 1'sb0;
			m_src_ts60 <= 1'sb0;
			m_src_ts_lo <= 1'sb0;
		end
		else if (cam_en) begin
			m_packet <= in_packet;
			m_event_data <= in_event_data;
			m_src_ts60 <= in_src_ts60;
			m_src_ts_lo <= in_src_ts_lo;
		end
	wire [59:0] pipe_delta_ts;
	assign pipe_delta_ts = {{TS_BITS - TS_STORE_BITS {1'b0}}, m_src_ts_lo - pipe_res_old_ts};
	wire [381:0] skid_wr_data;
	wire [381:0] skid_rd_data;
	wire [3:0] w_skid_count;
	wire skid_rd_valid;
	wire skid_wr_ready;
	assign skid_wr_data = {pipe_res_hit, pipe_res_idx, pipe_res_old_data, pipe_delta_ts, m_event_data, m_src_ts60, m_packet};
	gaxi_skid_buffer #(
		.DATA_WIDTH(P_W),
		.DEPTH(SKID_DEPTH)
	) u_res_skid(
		.axi_aclk(clk),
		.axi_aresetn(rst_n),
		.wr_valid(pipe_res_valid),
		.wr_ready(skid_wr_ready),
		.wr_data(skid_wr_data),
		.count(w_skid_count),
		.rd_valid(skid_rd_valid),
		.rd_ready(pop),
		.rd_count(),
		.rd_data(skid_rd_data)
	);
	assign p_valid = skid_rd_valid;
	assign {p_hit, p_idx, p_old_data, p_delta_ts, p_event_data, p_src_ts60, p_packet} = skid_rd_data;
	assign pop = enc_commit;
	function automatic [2:0] sv2v_cast_3;
		input reg [2:0] inp;
		sv2v_cast_3 = inp;
	endfunction
	always @(posedge clk or negedge rst_n)
		if (!rst_n)
			r_credit <= 3'd0;
		else if (clear)
			r_credit <= sv2v_cast_3(w_skid_count) - sv2v_cast_3(pop && skid_rd_valid);
		else
			r_credit <= (r_credit + sv2v_cast_3(cam_en)) - sv2v_cast_3(pop && skid_rd_valid);
	localparam [1:0] BEAT0 = 2'd0;
	localparam [1:0] BEAT1 = 2'd1;
	localparam [1:0] BEAT2 = 2'd2;
	reg q_valid;
	reg q_is_raw;
	reg [63:0] q_beat0;
	reg [127:0] q_packet;
	reg [1:0] r_beat;
	reg q_half_valid;
	reg [29:0] q_half_slot;
	wire fits_a;
	wire fits_b;
	wire fits_c_ts;
	wire fits_c_ed;
	wire fits_c;
	assign fits_a = (p_delta_ts < (60'sd1 << DELTA_TS_A_BITS)) && (p_event_data < (64'sd1 << EVENT_DATA_A_BITS));
	assign fits_b = (p_delta_ts < (60'sd1 << DELTA_TS_B_BITS)) && (p_event_data < (64'sd1 << EVENT_DATA_B_BITS));
	assign fits_c_ts = p_delta_ts < (60'sd1 << DELTA_TS_C_BITS);
	wire signed [64:0] ed_delta_full;
	assign ed_delta_full = $signed({1'b0, p_event_data}) - $signed({1'b0, p_old_data});
	assign fits_c_ed = (ed_delta_full >= -(65'sd1 <<< 39)) && (ed_delta_full < (65'sd1 <<< 39));
	assign fits_c = fits_c_ts && fits_c_ed;
	reg [1:0] fmt_sel;
	always @(*) begin
		if (_sv2v_0)
			;
		if (p_hit && fits_a)
			fmt_sel = 2'd0;
		else if (p_hit && fits_b)
			fmt_sel = 2'd1;
		else if (p_hit && fits_c)
			fmt_sel = 2'd2;
		else
			fmt_sel = 2'd3;
	end
	wire [63:0] slot_a;
	wire [63:0] slot_b;
	wire [63:0] slot_c;
	wire [63:0] slot_raw0;
	assign slot_a = {TAG_FORMAT_A, p_idx, p_delta_ts[14:0], p_event_data[39:0]};
	assign slot_b = {TAG_FORMAT_B, p_idx, p_delta_ts[22:0], p_event_data[31:0]};
	assign slot_c = {TAG_FORMAT_C, p_idx, p_delta_ts[14:0], ed_delta_full[39:0]};
	assign slot_raw0 = {TAG_RAW, p_src_ts60};
	reg [63:0] beat0_slot;
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (fmt_sel)
			2'd0: beat0_slot = slot_a;
			2'd1: beat0_slot = slot_b;
			2'd2: beat0_slot = slot_c;
			2'd3: beat0_slot = slot_raw0;
			default: beat0_slot = 64'h0000000000000000;
		endcase
	end
	wire half_a_fit;
	wire half_c_fit;
	wire [29:0] half_slot_a;
	wire [29:0] half_slot_c;
	wire half_valid_c;
	wire [29:0] half_slot_sel;
	assign half_a_fit = (((HALF_BEAT_EN != 0) && p_hit) && (p_delta_ts < (60'sd1 << HALF_DELTA_BITS))) && (p_event_data < (64'sd1 << HALF_DATA_BITS));
	assign half_c_fit = ((((HALF_BEAT_EN != 0) && p_hit) && (p_delta_ts < (60'sd1 << HALF_DELTA_BITS))) && (ed_delta_full >= -(65'sd1 <<< 12))) && (ed_delta_full < (65'sd1 <<< 12));
	assign half_slot_a = {HSUB_A, p_idx, p_delta_ts[9:0], p_event_data[12:0]};
	assign half_slot_c = {HSUB_C, p_idx, p_delta_ts[9:0], ed_delta_full[12:0]};
	assign half_valid_c = half_a_fit || half_c_fit;
	assign half_slot_sel = (half_a_fit ? half_slot_a : half_slot_c);
	reg [1:0] stat_class;
	always @(*) begin
		if (_sv2v_0)
			;
		if (half_a_fit)
			stat_class = 2'd0;
		else if (half_c_fit)
			stat_class = 2'd2;
		else
			stat_class = fmt_sel;
	end
	always @(*) begin
		if (_sv2v_0)
			;
		out_valid = q_valid;
		(* full_case, parallel_case *)
		case (r_beat)
			BEAT0: out_slot = q_beat0;
			BEAT1: out_slot = q_packet[127:64];
			BEAT2: out_slot = q_packet[63:0];
			default: out_slot = 64'h0000000000000000;
		endcase
	end
	assign out_half_valid = (q_valid && q_half_valid) && (r_beat == BEAT0);
	assign out_half_slot = q_half_slot;
	wire q_retire;
	wire q_can_load;
	assign q_retire = (q_valid && out_ready) && (((r_beat == BEAT0) && !q_is_raw) || (r_beat == BEAT2));
	assign q_can_load = !q_valid || q_retire;
	assign enc_commit = p_valid && q_can_load;
	assign in_ready = cam_en;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			q_valid <= 1'b0;
			q_is_raw <= 1'b0;
			q_beat0 <= 1'sb0;
			q_packet <= 1'sb0;
			r_beat <= BEAT0;
			q_half_valid <= 1'b0;
			q_half_slot <= 1'sb0;
		end
		else if (enc_commit) begin
			q_valid <= 1'b1;
			q_is_raw <= fmt_sel == 2'd3;
			q_beat0 <= beat0_slot;
			q_packet <= p_packet;
			r_beat <= BEAT0;
			q_half_valid <= half_valid_c;
			q_half_slot <= half_slot_sel;
		end
		else if (q_retire)
			q_valid <= 1'b0;
		else if (q_valid && out_ready) begin
			if (r_beat == BEAT0)
				r_beat <= BEAT1;
			else if (r_beat == BEAT1)
				r_beat <= BEAT2;
		end
	reg [31:0] r_tier1_a;
	reg [31:0] r_tier1_b;
	reg [31:0] r_tier1_c;
	reg [31:0] r_tier0;
	reg [31:0] r_cam_miss;
	reg [31:0] r_delta_ts_ovf;
	reg [31:0] r_event_data_ovf;
	reg [31:0] r_ed_delta_ovf;
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_tier1_a <= 1'sb0;
			r_tier1_b <= 1'sb0;
			r_tier1_c <= 1'sb0;
			r_tier0 <= 1'sb0;
			r_cam_miss <= 1'sb0;
			r_delta_ts_ovf <= 1'sb0;
			r_event_data_ovf <= 1'sb0;
			r_ed_delta_ovf <= 1'sb0;
		end
		else if (clear) begin
			r_tier1_a <= 1'sb0;
			r_tier1_b <= 1'sb0;
			r_tier1_c <= 1'sb0;
			r_tier0 <= 1'sb0;
			r_cam_miss <= 1'sb0;
			r_delta_ts_ovf <= 1'sb0;
			r_event_data_ovf <= 1'sb0;
			r_ed_delta_ovf <= 1'sb0;
		end
		else if (enc_commit)
			(* full_case, parallel_case *)
			case (stat_class)
				2'd0: r_tier1_a <= r_tier1_a + 1;
				2'd1: r_tier1_b <= r_tier1_b + 1;
				2'd2: r_tier1_c <= r_tier1_c + 1;
				2'd3: begin
					r_tier0 <= r_tier0 + 1;
					if (!p_hit)
						r_cam_miss <= r_cam_miss + 1;
					else if (p_delta_ts >= (60'sd1 << DELTA_TS_B_BITS))
						r_delta_ts_ovf <= r_delta_ts_ovf + 1;
					else if (p_event_data >= (64'sd1 << EVENT_DATA_A_BITS))
						r_event_data_ovf <= r_event_data_ovf + 1;
					else
						r_ed_delta_ovf <= r_ed_delta_ovf + 1;
				end
				default:
					;
			endcase
	assign stat_tier1_a = r_tier1_a;
	assign stat_tier1_b = r_tier1_b;
	assign stat_tier1_c = r_tier1_c;
	assign stat_tier0 = r_tier0;
	assign stat_cam_miss = r_cam_miss;
	assign stat_delta_ts_ovf = r_delta_ts_ovf;
	assign stat_event_data_ovf = r_event_data_ovf;
	assign stat_ed_delta_ovf = r_ed_delta_ovf;
	initial _sv2v_0 = 0;
endmodule
module monbus_halfbeat_packer (
	clk,
	rst_n,
	in_valid,
	in_ready,
	in_slot,
	in_half_valid,
	in_half_slot,
	out_valid,
	out_ready,
	out_slot
);
	reg _sv2v_0;
	input wire clk;
	input wire rst_n;
	input wire in_valid;
	output reg in_ready;
	input wire [63:0] in_slot;
	input wire in_half_valid;
	input wire [29:0] in_half_slot;
	output reg out_valid;
	input wire out_ready;
	output reg [63:0] out_slot;
	localparam [3:0] TAG_HALF_PAIR = 4'h4;
	localparam [29:0] NOP_SLOT = 30'd0;
	reg r_pend_valid;
	reg [29:0] r_pend_slot;
	wire pair_now;
	wire buffer_now;
	wire fwd_now;
	wire flush_fwd;
	wire idle_flush;
	assign pair_now = (in_valid && in_half_valid) && r_pend_valid;
	assign buffer_now = (in_valid && in_half_valid) && !r_pend_valid;
	assign fwd_now = (in_valid && !in_half_valid) && !r_pend_valid;
	assign flush_fwd = (in_valid && !in_half_valid) && r_pend_valid;
	assign idle_flush = !in_valid && r_pend_valid;
	always @(*) begin
		if (_sv2v_0)
			;
		out_valid = ((pair_now || fwd_now) || flush_fwd) || idle_flush;
		if (pair_now)
			out_slot = {TAG_HALF_PAIR, r_pend_slot, in_half_slot};
		else if (fwd_now)
			out_slot = in_slot;
		else
			out_slot = {TAG_HALF_PAIR, r_pend_slot, NOP_SLOT};
		if (buffer_now)
			in_ready = 1'b1;
		else if (pair_now)
			in_ready = out_ready;
		else if (fwd_now)
			in_ready = out_ready;
		else
			in_ready = 1'b0;
	end
	always @(posedge clk or negedge rst_n)
		if (!rst_n) begin
			r_pend_valid <= 1'b0;
			r_pend_slot <= 1'sb0;
		end
		else if (buffer_now) begin
			r_pend_valid <= 1'b1;
			r_pend_slot <= in_half_slot;
		end
		else if (out_ready && ((pair_now || flush_fwd) || idle_flush))
			r_pend_valid <= 1'b0;
	initial _sv2v_0 = 0;
endmodule
module monbus_group_core (
	axi_aclk,
	axi_aresetn,
	cam_clear,
	monbus_valid,
	monbus_ready,
	monbus_packet,
	monbus_timestamp,
	mon_time_out,
	irq_out,
	err_fifo_full,
	write_fifo_full,
	err_fifo_count,
	write_fifo_count,
	cfg_base_addr,
	cfg_limit_addr,
	cfg_flush_watermark,
	cfg_compress_en,
	cfg_axi_pkt_mask,
	cfg_axi_err_select,
	cfg_axi_error_mask,
	cfg_axi_timeout_mask,
	cfg_axi_compl_mask,
	cfg_axi_thresh_mask,
	cfg_axi_perf_mask,
	cfg_axi_addr_mask,
	cfg_axi_debug_mask,
	cfg_axis_pkt_mask,
	cfg_axis_err_select,
	cfg_axis_error_mask,
	cfg_axis_timeout_mask,
	cfg_axis_compl_mask,
	cfg_axis_credit_mask,
	cfg_axis_channel_mask,
	cfg_axis_stream_mask,
	cfg_core_pkt_mask,
	cfg_core_err_select,
	cfg_core_error_mask,
	cfg_core_timeout_mask,
	cfg_core_compl_mask,
	cfg_core_thresh_mask,
	cfg_core_perf_mask,
	cfg_core_debug_mask,
	mon_compressor_stat_tier1_a,
	mon_compressor_stat_tier1_b,
	mon_compressor_stat_tier1_c,
	mon_compressor_stat_tier0,
	mon_compressor_stat_cam_miss,
	mon_compressor_stat_delta_ts_ovf,
	mon_compressor_stat_event_data_ovf,
	mon_compressor_stat_ed_delta_ovf,
	fub_m_awid,
	fub_m_awaddr,
	fub_m_awlen,
	fub_m_awsize,
	fub_m_awburst,
	fub_m_awvalid,
	fub_m_awready,
	fub_m_wdata,
	fub_m_wstrb,
	fub_m_wlast,
	fub_m_wvalid,
	fub_m_wready,
	fub_m_bid,
	fub_m_bresp,
	fub_m_bvalid,
	fub_m_bready,
	fub_s_arid,
	fub_s_araddr,
	fub_s_arlen,
	fub_s_arsize,
	fub_s_arburst,
	fub_s_arvalid,
	fub_s_arready,
	fub_s_rid,
	fub_s_rdata,
	fub_s_rresp,
	fub_s_rlast,
	fub_s_rvalid,
	fub_s_rready,
	f_r_wr_state,
	f_r_wr_addr,
	f_r_cyc_total,
	f_r_aw_cov_beats,
	f_r_b_beats,
	f_r_aw_subs,
	f_r_b_subs,
	f_r_os_count,
	f_r_ws_count,
	f_r_w_rem_in_sub,
	f_w_aw_issue
);
	reg _sv2v_0;
	parameter signed [31:0] FIFO_DEPTH_ERR = 64;
	parameter signed [31:0] FIFO_DEPTH_WRITE = 96;
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] AXI_ID_WIDTH_M = 1;
	parameter signed [31:0] AXI_ID_WIDTH_S = 1;
	parameter signed [31:0] MAX_BURST_BEATS = 1;
	parameter signed [31:0] FLUSH_TIMEOUT_CYCLES = 1024;
	parameter signed [31:0] NUM_PROTOCOLS = 3;
	parameter signed [31:0] USE_COMPRESSION = 0;
	parameter signed [31:0] HALF_BEAT_EN = 0;
	input wire axi_aclk;
	input wire axi_aresetn;
	input wire cam_clear;
	input wire monbus_valid;
	output wire monbus_ready;
	localparam signed [31:0] monitor_common_pkg_MONBUS_PKT_WIDTH = 128;
	input wire [127:0] monbus_packet;
	localparam signed [31:0] monitor_common_pkg_MONBUS_TS_WIDTH = 64;
	input wire [63:0] monbus_timestamp;
	output wire [63:0] mon_time_out;
	output wire irq_out;
	output wire err_fifo_full;
	output wire write_fifo_full;
	output wire [15:0] err_fifo_count;
	output wire [15:0] write_fifo_count;
	input wire [ADDR_WIDTH - 1:0] cfg_base_addr;
	input wire [ADDR_WIDTH - 1:0] cfg_limit_addr;
	input wire [15:0] cfg_flush_watermark;
	input wire cfg_compress_en;
	input wire [15:0] cfg_axi_pkt_mask;
	input wire [15:0] cfg_axi_err_select;
	input wire [15:0] cfg_axi_error_mask;
	input wire [15:0] cfg_axi_timeout_mask;
	input wire [15:0] cfg_axi_compl_mask;
	input wire [15:0] cfg_axi_thresh_mask;
	input wire [15:0] cfg_axi_perf_mask;
	input wire [15:0] cfg_axi_addr_mask;
	input wire [15:0] cfg_axi_debug_mask;
	input wire [15:0] cfg_axis_pkt_mask;
	input wire [15:0] cfg_axis_err_select;
	input wire [15:0] cfg_axis_error_mask;
	input wire [15:0] cfg_axis_timeout_mask;
	input wire [15:0] cfg_axis_compl_mask;
	input wire [15:0] cfg_axis_credit_mask;
	input wire [15:0] cfg_axis_channel_mask;
	input wire [15:0] cfg_axis_stream_mask;
	input wire [15:0] cfg_core_pkt_mask;
	input wire [15:0] cfg_core_err_select;
	input wire [15:0] cfg_core_error_mask;
	input wire [15:0] cfg_core_timeout_mask;
	input wire [15:0] cfg_core_compl_mask;
	input wire [15:0] cfg_core_thresh_mask;
	input wire [15:0] cfg_core_perf_mask;
	input wire [15:0] cfg_core_debug_mask;
	output wire [31:0] mon_compressor_stat_tier1_a;
	output wire [31:0] mon_compressor_stat_tier1_b;
	output wire [31:0] mon_compressor_stat_tier1_c;
	output wire [31:0] mon_compressor_stat_tier0;
	output wire [31:0] mon_compressor_stat_cam_miss;
	output wire [31:0] mon_compressor_stat_delta_ts_ovf;
	output wire [31:0] mon_compressor_stat_event_data_ovf;
	output wire [31:0] mon_compressor_stat_ed_delta_ovf;
	output wire [AXI_ID_WIDTH_M - 1:0] fub_m_awid;
	output wire [ADDR_WIDTH - 1:0] fub_m_awaddr;
	output wire [7:0] fub_m_awlen;
	output wire [2:0] fub_m_awsize;
	output wire [1:0] fub_m_awburst;
	output wire fub_m_awvalid;
	input wire fub_m_awready;
	output wire [63:0] fub_m_wdata;
	output wire [7:0] fub_m_wstrb;
	output wire fub_m_wlast;
	output wire fub_m_wvalid;
	input wire fub_m_wready;
	input wire [AXI_ID_WIDTH_M - 1:0] fub_m_bid;
	input wire [1:0] fub_m_bresp;
	input wire fub_m_bvalid;
	output wire fub_m_bready;
	input wire [AXI_ID_WIDTH_S - 1:0] fub_s_arid;
	input wire [ADDR_WIDTH - 1:0] fub_s_araddr;
	input wire [7:0] fub_s_arlen;
	input wire [2:0] fub_s_arsize;
	input wire [1:0] fub_s_arburst;
	input wire fub_s_arvalid;
	output wire fub_s_arready;
	output wire [AXI_ID_WIDTH_S - 1:0] fub_s_rid;
	output reg [63:0] fub_s_rdata;
	output wire [1:0] fub_s_rresp;
	output wire fub_s_rlast;
	output wire fub_s_rvalid;
	input wire fub_s_rready;
	output wire [1:0] f_r_wr_state;
	output wire [ADDR_WIDTH - 1:0] f_r_wr_addr;
	output wire [15:0] f_r_cyc_total;
	output wire [16:0] f_r_aw_cov_beats;
	output wire [16:0] f_r_b_beats;
	output wire [8:0] f_r_aw_subs;
	output wire [8:0] f_r_b_subs;
	output wire [2:0] f_r_os_count;
	output wire [2:0] f_r_ws_count;
	output wire [9:0] f_r_w_rem_in_sub;
	output wire f_w_aw_issue;
	localparam signed [31:0] BYTES_PER_BEAT = 8;
	localparam [3:0] WRITE_TAG_RAW = 4'h0;
	wire w_use_comp;
	assign w_use_comp = (USE_COMPRESSION != 0) && cfg_compress_en;
	wire [15:0] w_beats_per_unit;
	assign w_beats_per_unit = (w_use_comp ? 16'd1 : 16'd3);
	wire [1:0] w_geo_rem3;
	wire [1:0] w_fifo_rem3;
	localparam signed [31:0] ERR_REC_WIDTH = monitor_common_pkg_MONBUS_PKT_WIDTH + monitor_common_pkg_MONBUS_TS_WIDTH;
	localparam signed [31:0] WRITE_FIFO_AW = $clog2(FIFO_DEPTH_WRITE);
	localparam signed [31:0] NUM_PROTOCOLS_LP = NUM_PROTOCOLS;
	wire [3:0] pkt_type;
	wire [3:0] pkt_protocol;
	wire [7:0] pkt_event_code;
	wire [3:0] ec_idx;
	wire ec_in_mask_range;
	wire [63:0] pkt_event_data;
	reg pkt_drop;
	reg pkt_to_err_fifo;
	reg pkt_to_write_path;
	reg pkt_event_masked;
	reg [63:0] r_ts_counter;
	wire err_fifo_wr_valid;
	wire err_fifo_wr_ready;
	wire [ERR_REC_WIDTH - 1:0] err_fifo_wr_data;
	wire err_fifo_rd_valid;
	wire err_fifo_rd_ready;
	wire [ERR_REC_WIDTH - 1:0] err_fifo_rd_data;
	wire err_fifo_empty;
	wire [$clog2(FIFO_DEPTH_ERR):0] err_fifo_count_full;
	wire write_fifo_wr_valid;
	wire write_fifo_wr_ready;
	wire [63:0] write_fifo_wr_data;
	wire write_fifo_rd_valid;
	wire write_fifo_rd_ready;
	wire [63:0] write_fifo_rd_data;
	wire write_fifo_empty;
	wire [WRITE_FIFO_AW:0] write_fifo_beat_count;
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn)
			r_ts_counter <= 1'sb0;
		else
			r_ts_counter <= r_ts_counter + 1'b1;
	assign mon_time_out = r_ts_counter;
	function automatic [3:0] monitor_common_pkg_get_packet_type;
		input reg [127:0] pkt;
		monitor_common_pkg_get_packet_type = pkt[127:124];
	endfunction
	assign pkt_type = monitor_common_pkg_get_packet_type(monbus_packet);
	assign pkt_protocol = monbus_packet[108:105];
	function automatic [7:0] monitor_common_pkg_get_event_code;
		input reg [127:0] pkt;
		monitor_common_pkg_get_event_code = pkt[104:97];
	endfunction
	assign pkt_event_code = monitor_common_pkg_get_event_code(monbus_packet);
	function automatic [63:0] monitor_common_pkg_get_event_data;
		input reg [127:0] pkt;
		monitor_common_pkg_get_event_data = pkt[63:0];
	endfunction
	assign pkt_event_data = monitor_common_pkg_get_event_data(monbus_packet);
	assign ec_idx = pkt_event_code[3:0];
	assign ec_in_mask_range = pkt_event_code[7:4] == 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypeAddrMatch = 4'h8;
	localparam [3:0] monitor_common_pkg_PktTypeChannel = 4'h6;
	localparam [3:0] monitor_common_pkg_PktTypeCompletion = 4'h1;
	localparam [3:0] monitor_common_pkg_PktTypeCredit = 4'h5;
	localparam [3:0] monitor_common_pkg_PktTypeDebug = 4'hf;
	localparam [3:0] monitor_common_pkg_PktTypeError = 4'h0;
	localparam [3:0] monitor_common_pkg_PktTypePerf = 4'h4;
	localparam [3:0] monitor_common_pkg_PktTypeStream = 4'h7;
	localparam [3:0] monitor_common_pkg_PktTypeThreshold = 4'h2;
	localparam [3:0] monitor_common_pkg_PktTypeTimeout = 4'h3;
	always @(*) begin
		if (_sv2v_0)
			;
		pkt_drop = 1'b0;
		pkt_to_err_fifo = 1'b0;
		pkt_to_write_path = 1'b0;
		pkt_event_masked = 1'b0;
		if (monbus_valid) begin
			case (pkt_protocol)
				4'h0: begin
					pkt_drop = cfg_axi_pkt_mask[pkt_type];
					pkt_to_err_fifo = cfg_axi_err_select[pkt_type] && !pkt_drop;
					if (ec_in_mask_range)
						case (pkt_type)
							monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_axi_error_mask[ec_idx];
							monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_axi_timeout_mask[ec_idx];
							monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask[ec_idx];
							monitor_common_pkg_PktTypeThreshold: pkt_event_masked = cfg_axi_thresh_mask[ec_idx];
							monitor_common_pkg_PktTypePerf: pkt_event_masked = cfg_axi_perf_mask[ec_idx];
							monitor_common_pkg_PktTypeAddrMatch: pkt_event_masked = cfg_axi_addr_mask[ec_idx];
							monitor_common_pkg_PktTypeDebug: pkt_event_masked = cfg_axi_debug_mask[ec_idx];
							default: pkt_event_masked = 1'b0;
						endcase
				end
				4'h1: begin
					pkt_drop = cfg_axis_pkt_mask[pkt_type];
					pkt_to_err_fifo = cfg_axis_err_select[pkt_type] && !pkt_drop;
					if (ec_in_mask_range)
						case (pkt_type)
							monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_axis_error_mask[ec_idx];
							monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_axis_timeout_mask[ec_idx];
							monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_axis_compl_mask[ec_idx];
							monitor_common_pkg_PktTypeCredit: pkt_event_masked = cfg_axis_credit_mask[ec_idx];
							monitor_common_pkg_PktTypeChannel: pkt_event_masked = cfg_axis_channel_mask[ec_idx];
							monitor_common_pkg_PktTypeStream: pkt_event_masked = cfg_axis_stream_mask[ec_idx];
							default: pkt_event_masked = 1'b0;
						endcase
				end
				4'h4: begin
					pkt_drop = cfg_core_pkt_mask[pkt_type];
					pkt_to_err_fifo = cfg_core_err_select[pkt_type] && !pkt_drop;
					if (ec_in_mask_range)
						case (pkt_type)
							monitor_common_pkg_PktTypeError: pkt_event_masked = cfg_core_error_mask[ec_idx];
							monitor_common_pkg_PktTypeTimeout: pkt_event_masked = cfg_core_timeout_mask[ec_idx];
							monitor_common_pkg_PktTypeCompletion: pkt_event_masked = cfg_core_compl_mask[ec_idx];
							monitor_common_pkg_PktTypeThreshold: pkt_event_masked = cfg_core_thresh_mask[ec_idx];
							monitor_common_pkg_PktTypePerf: pkt_event_masked = cfg_core_perf_mask[ec_idx];
							monitor_common_pkg_PktTypeDebug: pkt_event_masked = cfg_core_debug_mask[ec_idx];
							default: pkt_event_masked = 1'b0;
						endcase
				end
				default: pkt_drop = 1'b1;
			endcase
			if (pkt_event_masked) begin
				pkt_drop = 1'b1;
				pkt_to_err_fifo = 1'b0;
			end
			pkt_to_write_path = !pkt_drop && !pkt_to_err_fifo;
		end
	end
	assign err_fifo_wr_valid = (monbus_valid && pkt_to_err_fifo) && !pkt_drop;
	assign err_fifo_wr_data = {monbus_timestamp, monbus_packet};
	gaxi_fifo_sync #(
		.REGISTERED(0),
		.DATA_WIDTH(ERR_REC_WIDTH),
		.DEPTH(FIFO_DEPTH_ERR)
	) u_err_fifo(
		.axi_aclk(axi_aclk),
		.axi_aresetn(axi_aresetn),
		.wr_valid(err_fifo_wr_valid),
		.wr_ready(err_fifo_wr_ready),
		.wr_data(err_fifo_wr_data),
		.rd_valid(err_fifo_rd_valid),
		.rd_ready(err_fifo_rd_ready),
		.rd_data(err_fifo_rd_data),
		.count(err_fifo_count_full)
	);
	assign err_fifo_empty = !err_fifo_rd_valid;
	assign err_fifo_full = !err_fifo_wr_ready;
	assign irq_out = !err_fifo_empty;
	assign err_fifo_count = {{(16 - $clog2(FIFO_DEPTH_ERR)) - 1 {1'b0}}, err_fifo_count_full};
	reg [1:0] r_slice_idx;
	reg [8:0] r_rd_beats_remaining;
	reg r_rd_in_burst;
	reg [AXI_ID_WIDTH_S - 1:0] r_rd_burst_id;
	assign fub_s_arready = !r_rd_in_burst;
	assign fub_s_rvalid = r_rd_in_burst && !err_fifo_empty;
	assign fub_s_rlast = r_rd_in_burst && (r_rd_beats_remaining == 9'd1);
	assign fub_s_rid = r_rd_burst_id;
	assign fub_s_rresp = 2'b00;
	always @(*) begin
		if (_sv2v_0)
			;
		(* full_case, parallel_case *)
		case (r_slice_idx)
			2'd0: fub_s_rdata = {WRITE_TAG_RAW, err_fifo_rd_data[187:monitor_common_pkg_MONBUS_PKT_WIDTH]};
			2'd1: fub_s_rdata = err_fifo_rd_data[127:64];
			2'd2: fub_s_rdata = err_fifo_rd_data[63:0];
			default: fub_s_rdata = 1'sb0;
		endcase
	end
	assign err_fifo_rd_ready = (fub_s_rvalid && fub_s_rready) && (r_slice_idx == 2'd2);
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			r_slice_idx <= 2'd0;
			r_rd_beats_remaining <= 9'd0;
			r_rd_in_burst <= 1'b0;
			r_rd_burst_id <= 1'sb0;
		end
		else begin
			if (fub_s_arvalid && fub_s_arready) begin
				r_rd_in_burst <= 1'b1;
				r_rd_beats_remaining <= {1'b0, fub_s_arlen} + 9'd1;
				r_rd_burst_id <= fub_s_arid;
			end
			if (fub_s_rvalid && fub_s_rready) begin
				r_rd_beats_remaining <= r_rd_beats_remaining - 9'd1;
				if (r_slice_idx == 2'd2)
					r_slice_idx <= 2'd0;
				else
					r_slice_idx <= r_slice_idx + 2'd1;
				if (r_rd_beats_remaining == 9'd1)
					r_rd_in_burst <= 1'b0;
			end
		end
	reg [2:0] _unused_arsize = fub_s_arsize;
	reg [1:0] _unused_arburst = fub_s_arburst;
	reg [ADDR_WIDTH - 1:0] _unused_araddr = fub_s_araddr;
	reg exp_wr_valid;
	reg [63:0] exp_wr_data;
	wire exp_term;
	wire comp_wr_valid;
	wire [63:0] comp_wr_data;
	wire comp_in_ready;
	reg [1:0] r_exp_state;
	reg [127:0] r_lat_packet;
	reg [63:0] r_lat_source_ts;
	wire exp_accepting_now;
	assign exp_accepting_now = (((r_exp_state == 2'd0) && monbus_valid) && pkt_to_write_path) && !w_use_comp;
	always @(*) begin
		if (_sv2v_0)
			;
		exp_wr_valid = 1'b0;
		exp_wr_data = 64'd0;
		(* full_case, parallel_case *)
		case (r_exp_state)
			2'd0:
				if (exp_accepting_now) begin
					exp_wr_valid = 1'b1;
					exp_wr_data = {WRITE_TAG_RAW, monbus_timestamp[59:0]};
				end
			2'd1: begin
				exp_wr_valid = 1'b1;
				exp_wr_data = r_lat_packet[127:64];
			end
			2'd2: begin
				exp_wr_valid = 1'b1;
				exp_wr_data = r_lat_packet[63:0];
			end
			default:
				;
		endcase
	end
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			r_exp_state <= 2'd0;
			r_lat_packet <= 1'sb0;
			r_lat_source_ts <= 1'sb0;
		end
		else
			(* full_case, parallel_case *)
			case (r_exp_state)
				2'd0:
					if (exp_accepting_now && write_fifo_wr_ready) begin
						r_lat_packet <= monbus_packet;
						r_lat_source_ts <= monbus_timestamp;
						r_exp_state <= 2'd1;
					end
				2'd1:
					if (write_fifo_wr_ready)
						r_exp_state <= 2'd2;
				2'd2:
					if (write_fifo_wr_ready)
						r_exp_state <= 2'd0;
				default: r_exp_state <= 2'd0;
			endcase
	assign exp_term = exp_accepting_now && write_fifo_wr_ready;
	reg [63:0] _unused_lat_ts = r_lat_source_ts;
	generate
		if (USE_COMPRESSION != 0) begin : gen_compressor
			localparam signed [31:0] COMP_IN_W = monitor_common_pkg_MONBUS_TS_WIDTH + monitor_common_pkg_MONBUS_PKT_WIDTH;
			wire comp_skid_wr_valid;
			wire comp_skid_wr_ready;
			wire [COMP_IN_W - 1:0] comp_skid_wr_data;
			wire comp_skid_rd_valid;
			wire comp_core_in_ready;
			wire [COMP_IN_W - 1:0] comp_skid_rd_data;
			wire [127:0] comp_in_packet;
			wire [63:0] comp_in_source_ts;
			wire comp_out_valid;
			wire comp_out_ready;
			wire [63:0] comp_out_slot;
			wire comp_out_half_valid;
			wire [29:0] comp_out_half_slot;
			assign comp_skid_wr_valid = ((monbus_valid && pkt_to_write_path) && !pkt_drop) && w_use_comp;
			assign comp_skid_wr_data = {monbus_timestamp, monbus_packet};
			gaxi_skid_buffer #(
				.DATA_WIDTH(COMP_IN_W),
				.DEPTH(2)
			) u_comp_in_skid(
				.axi_aclk(axi_aclk),
				.axi_aresetn(axi_aresetn),
				.wr_valid(comp_skid_wr_valid),
				.wr_ready(comp_skid_wr_ready),
				.wr_data(comp_skid_wr_data),
				.count(),
				.rd_valid(comp_skid_rd_valid),
				.rd_ready(comp_core_in_ready),
				.rd_count(),
				.rd_data(comp_skid_rd_data)
			);
			assign {comp_in_source_ts, comp_in_packet} = comp_skid_rd_data;
			assign comp_in_ready = comp_skid_wr_ready;
			monbus_compressor #(.HALF_BEAT_EN(HALF_BEAT_EN)) u_compressor(
				.clk(axi_aclk),
				.rst_n(axi_aresetn),
				.clear(cam_clear),
				.in_valid(comp_skid_rd_valid),
				.in_ready(comp_core_in_ready),
				.in_packet(comp_in_packet),
				.in_source_ts(comp_in_source_ts),
				.out_valid(comp_out_valid),
				.out_ready(comp_out_ready),
				.out_slot(comp_out_slot),
				.out_half_valid(comp_out_half_valid),
				.out_half_slot(comp_out_half_slot),
				.stat_tier1_a(mon_compressor_stat_tier1_a),
				.stat_tier1_b(mon_compressor_stat_tier1_b),
				.stat_tier1_c(mon_compressor_stat_tier1_c),
				.stat_tier0(mon_compressor_stat_tier0),
				.stat_cam_miss(mon_compressor_stat_cam_miss),
				.stat_delta_ts_ovf(mon_compressor_stat_delta_ts_ovf),
				.stat_event_data_ovf(mon_compressor_stat_event_data_ovf),
				.stat_ed_delta_ovf(mon_compressor_stat_ed_delta_ovf)
			);
			if (HALF_BEAT_EN != 0) begin : gen_halfbeat_packer
				monbus_halfbeat_packer u_packer(
					.clk(axi_aclk),
					.rst_n(axi_aresetn),
					.in_valid(comp_out_valid),
					.in_ready(comp_out_ready),
					.in_slot(comp_out_slot),
					.in_half_valid(comp_out_half_valid),
					.in_half_slot(comp_out_half_slot),
					.out_valid(comp_wr_valid),
					.out_ready(write_fifo_wr_ready),
					.out_slot(comp_wr_data)
				);
			end
			else begin : gen_no_halfbeat
				assign comp_wr_valid = comp_out_valid;
				assign comp_wr_data = comp_out_slot;
				assign comp_out_ready = write_fifo_wr_ready;
			end
		end
		else begin : gen_no_compressor
			assign comp_wr_valid = 1'b0;
			assign comp_wr_data = 64'd0;
			assign comp_in_ready = 1'b0;
			assign mon_compressor_stat_tier1_a = 32'd0;
			assign mon_compressor_stat_tier1_b = 32'd0;
			assign mon_compressor_stat_tier1_c = 32'd0;
			assign mon_compressor_stat_tier0 = 32'd0;
			assign mon_compressor_stat_cam_miss = 32'd0;
			assign mon_compressor_stat_delta_ts_ovf = 32'd0;
			assign mon_compressor_stat_event_data_ovf = 32'd0;
			assign mon_compressor_stat_ed_delta_ovf = 32'd0;
		end
	endgenerate
	assign write_fifo_wr_valid = (w_use_comp ? comp_wr_valid : exp_wr_valid);
	assign write_fifo_wr_data = (w_use_comp ? comp_wr_data : exp_wr_data);
	assign monbus_ready = (pkt_drop || (pkt_to_err_fifo && err_fifo_wr_ready)) || (pkt_to_write_path && (w_use_comp ? comp_in_ready : exp_term));
	gaxi_fifo_sync #(
		.REGISTERED(0),
		.DATA_WIDTH(64),
		.DEPTH(FIFO_DEPTH_WRITE)
	) u_write_fifo(
		.axi_aclk(axi_aclk),
		.axi_aresetn(axi_aresetn),
		.wr_valid(write_fifo_wr_valid),
		.wr_ready(write_fifo_wr_ready),
		.wr_data(write_fifo_wr_data),
		.rd_valid(write_fifo_rd_valid),
		.rd_ready(write_fifo_rd_ready),
		.rd_data(write_fifo_rd_data),
		.count(write_fifo_beat_count)
	);
	assign write_fifo_empty = !write_fifo_rd_valid;
	assign write_fifo_full = !write_fifo_wr_ready;
	assign write_fifo_count = {{(16 - WRITE_FIFO_AW) - 1 {1'b0}}, write_fifo_beat_count};
	localparam signed [31:0] WR_OS_CAP = 4;
	reg [1:0] r_wr_state;
	reg [ADDR_WIDTH - 1:0] r_wr_addr;
	reg [15:0] r_cyc_total;
	reg [16:0] r_aw_cov_beats;
	reg [8:0] r_aw_subs;
	reg [8:0] r_b_subs;
	reg [16:0] r_b_beats;
	reg [9:0] r_w_rem_in_sub;
	reg [8:0] r_os_len [0:3];
	reg [1:0] r_os_rd;
	reg [1:0] r_os_wr;
	reg [2:0] r_os_count;
	reg [8:0] r_ws_len [0:3];
	reg [1:0] r_ws_rd;
	reg [1:0] r_ws_wr;
	reg [2:0] r_ws_count;
	reg [31:0] r_timeout_cnt;
	wire [15:0] beats_in_fifo;
	reg s0_in_window;
	reg [ADDR_WIDTH - 1:0] s0_gaddr;
	reg [ADDR_WIDTH - 1:0] s0_wr_addr;
	reg [15:0] s1_beats_to_limit;
	reg [15:0] s1_beats_to_4kb;
	reg s1_in_window;
	reg [ADDR_WIDTH - 1:0] s1_wr_addr;
	(* max_fanout = 24 *) reg [ADDR_WIDTH - 1:0] r_cfg_base_addr;
	(* max_fanout = 24 *) reg [ADDR_WIDTH - 1:0] r_cfg_limit_addr;
	reg [ADDR_WIDTH:0] r_cfg_limit_p1;
	reg [15:0] s2_beats_planned;
	reg s2_in_window;
	reg [ADDR_WIDTH - 1:0] s2_wr_addr;
	reg [15:0] r_plan_geo_units;
	reg [ADDR_WIDTH - 1:0] r_plan_addr;
	reg r_plan_ok;
	reg [15:0] r_fifo_beats;
	reg [2:0] r_geom_settle;
	wire geom_valid;
	wire flush_trigger_watermark;
	wire flush_trigger_timeout;
	wire have_one_unit;
	wire do_flush;
	assign beats_in_fifo = {{(16 - WRITE_FIFO_AW) - 1 {1'b0}}, write_fifo_beat_count};
	assign geom_valid = r_geom_settle == 3'd5;
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			r_cfg_base_addr <= 1'sb0;
			r_cfg_limit_addr <= 1'sb0;
			r_cfg_limit_p1 <= 1'sb0;
		end
		else begin
			r_cfg_base_addr <= cfg_base_addr;
			r_cfg_limit_addr <= cfg_limit_addr;
			r_cfg_limit_p1 <= {1'b0, cfg_limit_addr} + 1'b1;
		end
	function automatic [15:0] sv2v_cast_16;
		input reg [15:0] inp;
		sv2v_cast_16 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			s0_in_window <= 1'b0;
			s0_gaddr <= 1'sb0;
			s0_wr_addr <= 1'sb0;
			s1_beats_to_limit <= 16'd0;
			s1_beats_to_4kb <= 16'd0;
			s1_in_window <= 1'b0;
			s1_wr_addr <= 1'sb0;
			s2_beats_planned <= 16'd0;
			s2_in_window <= 1'b0;
			s2_wr_addr <= 1'sb0;
			r_plan_geo_units <= 16'd0;
			r_plan_addr <= 1'sb0;
			r_plan_ok <= 1'b0;
			r_fifo_beats <= 16'd0;
		end
		else begin
			r_fifo_beats <= beats_in_fifo;
			begin : stage0
				reg in_w;
				in_w = (r_wr_addr >= r_cfg_base_addr) && (r_wr_addr <= r_cfg_limit_addr);
				s0_in_window <= in_w;
				s0_gaddr <= (in_w ? r_wr_addr : r_cfg_base_addr);
				s0_wr_addr <= r_wr_addr;
			end
			begin : stage1
				reg [ADDR_WIDTH:0] beats_raw;
				reg [12:0] bytes4;
				beats_raw = (r_cfg_limit_p1 - {1'b0, s0_gaddr}) >> 3;
				bytes4 = 13'h1000 - {1'b0, s0_gaddr[11:0]};
				s1_in_window <= s0_in_window;
				s1_wr_addr <= s0_wr_addr;
				s1_beats_to_limit <= (|beats_raw[ADDR_WIDTH:16] ? 16'hffff : beats_raw[15:0]);
				s1_beats_to_4kb <= {6'd0, bytes4[12:3]};
			end
			begin : stage2
				reg [15:0] cap_geo;
				cap_geo = (s1_beats_to_limit < s1_beats_to_4kb ? s1_beats_to_limit : s1_beats_to_4kb);
				s2_beats_planned <= cap_geo;
				s2_in_window <= s1_in_window;
				s2_wr_addr <= s1_wr_addr;
			end
			begin : stage3
				reg [15:0] units;
				reg rew;
				units = (w_beats_per_unit == 16'd1 ? s2_beats_planned : s2_beats_planned - sv2v_cast_16(w_geo_rem3));
				rew = !s2_in_window || (units < w_beats_per_unit);
				r_plan_geo_units <= units;
				r_plan_addr <= (rew ? r_cfg_base_addr : s2_wr_addr);
				r_plan_ok <= units >= w_beats_per_unit;
			end
		end
	wire [15:0] w_fifo_units;
	assign w_fifo_units = (w_use_comp ? r_fifo_beats : r_fifo_beats - sv2v_cast_16(w_fifo_rem3));
	math_mod_3_compress u_mod3_geo(
		.d_in(s2_beats_planned),
		.rem_out(w_geo_rem3)
	);
	math_mod_3_compress u_mod3_fifo(
		.d_in(r_fifo_beats),
		.rem_out(w_fifo_rem3)
	);
	assign have_one_unit = w_fifo_units >= w_beats_per_unit;
	assign flush_trigger_watermark = r_fifo_beats >= cfg_flush_watermark;
	assign flush_trigger_timeout = r_timeout_cnt >= FLUSH_TIMEOUT_CYCLES;
	assign do_flush = (flush_trigger_watermark || flush_trigger_timeout) && have_one_unit;
	wire [16:0] w_aw_beats_rem;
	wire [16:0] w_aw_sub_len_p1;
	wire w_aw_issue;
	wire w_w_issue;
	wire w_b_issue;
	reg w_ws_pop;
	function automatic [16:0] sv2v_cast_17;
		input reg [16:0] inp;
		sv2v_cast_17 = inp;
	endfunction
	assign w_aw_beats_rem = sv2v_cast_17(r_cyc_total) - r_aw_cov_beats;
	function automatic signed [16:0] sv2v_cast_17_signed;
		input reg signed [16:0] inp;
		sv2v_cast_17_signed = inp;
	endfunction
	assign w_aw_sub_len_p1 = (w_aw_beats_rem < sv2v_cast_17_signed(MAX_BURST_BEATS) ? w_aw_beats_rem : sv2v_cast_17_signed(MAX_BURST_BEATS));
	assign fub_m_awid = 1'sb0;
	assign fub_m_awsize = 3'd3;
	assign fub_m_awburst = 2'b01;
	function automatic signed [2:0] sv2v_cast_3_signed;
		input reg signed [2:0] inp;
		sv2v_cast_3_signed = inp;
	endfunction
	assign fub_m_awvalid = ((r_wr_state == 2'd1) && (w_aw_beats_rem != 17'd0)) && (r_os_count < sv2v_cast_3_signed(WR_OS_CAP));
	assign fub_m_awaddr = r_wr_addr;
	function automatic [7:0] sv2v_cast_8;
		input reg [7:0] inp;
		sv2v_cast_8 = inp;
	endfunction
	assign fub_m_awlen = sv2v_cast_8(w_aw_sub_len_p1 - 17'd1);
	assign w_aw_issue = fub_m_awvalid && fub_m_awready;
	assign fub_m_wvalid = ((r_wr_state == 2'd1) && (r_w_rem_in_sub != 10'd0)) && write_fifo_rd_valid;
	assign fub_m_wdata = write_fifo_rd_data;
	assign fub_m_wstrb = 8'hff;
	assign fub_m_wlast = r_w_rem_in_sub == 10'd1;
	assign write_fifo_rd_ready = fub_m_wvalid && fub_m_wready;
	assign w_w_issue = write_fifo_rd_ready;
	assign fub_m_bready = r_wr_state == 2'd1;
	assign w_b_issue = fub_m_bvalid && fub_m_bready;
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_w_issue)
			w_ws_pop = (r_w_rem_in_sub == 10'd1) && (r_ws_count != 3'd0);
		else
			w_ws_pop = (r_w_rem_in_sub == 10'd0) && (r_ws_count != 3'd0);
	end
	function automatic [ADDR_WIDTH - 1:0] sv2v_cast_A5DC5;
		input reg [ADDR_WIDTH - 1:0] inp;
		sv2v_cast_A5DC5 = inp;
	endfunction
	function automatic [8:0] sv2v_cast_9;
		input reg [8:0] inp;
		sv2v_cast_9 = inp;
	endfunction
	function automatic [9:0] sv2v_cast_10;
		input reg [9:0] inp;
		sv2v_cast_10 = inp;
	endfunction
	always @(posedge axi_aclk or negedge axi_aresetn)
		if (!axi_aresetn) begin
			r_wr_state <= 2'd0;
			r_wr_addr <= 1'sb0;
			r_cyc_total <= 16'd0;
			r_aw_cov_beats <= 17'd0;
			r_aw_subs <= 9'd0;
			r_b_subs <= 9'd0;
			r_b_beats <= 17'd0;
			r_w_rem_in_sub <= 10'd0;
			r_os_len[0] <= 9'd0;
			r_os_len[1] <= 9'd0;
			r_os_len[2] <= 9'd0;
			r_os_len[3] <= 9'd0;
			r_os_rd <= 2'd0;
			r_os_wr <= 2'd0;
			r_os_count <= 3'd0;
			r_ws_len[0] <= 9'd0;
			r_ws_len[1] <= 9'd0;
			r_ws_len[2] <= 9'd0;
			r_ws_len[3] <= 9'd0;
			r_ws_rd <= 2'd0;
			r_ws_wr <= 2'd0;
			r_ws_count <= 3'd0;
			r_timeout_cnt <= 32'd0;
			r_geom_settle <= 3'd0;
		end
		else begin
			if (write_fifo_empty)
				r_timeout_cnt <= 32'd0;
			else if (w_w_issue)
				r_timeout_cnt <= 32'd0;
			else if (r_timeout_cnt < FLUSH_TIMEOUT_CYCLES)
				r_timeout_cnt <= r_timeout_cnt + 32'd1;
			if (((r_wr_state != 2'd0) || (cfg_base_addr != r_cfg_base_addr)) || (cfg_limit_addr != r_cfg_limit_addr))
				r_geom_settle <= 3'd0;
			else if (r_geom_settle != 3'd5)
				r_geom_settle <= r_geom_settle + 3'd1;
			case (r_wr_state)
				2'd0:
					if ((do_flush && geom_valid) && r_plan_ok) begin : sv2v_autoblock_1
						reg [15:0] total_units;
						total_units = (r_plan_geo_units < w_fifo_units ? r_plan_geo_units : w_fifo_units);
						r_wr_addr <= r_plan_addr;
						r_cyc_total <= total_units;
						r_aw_cov_beats <= 17'd0;
						r_aw_subs <= 9'd0;
						r_b_subs <= 9'd0;
						r_b_beats <= 17'd0;
						r_w_rem_in_sub <= 10'd0;
						r_os_count <= 3'd0;
						r_ws_count <= 3'd0;
						r_wr_state <= 2'd1;
					end
					else if (((do_flush && geom_valid) && !r_plan_ok) && (r_wr_addr == r_cfg_base_addr))
						r_wr_addr <= {r_cfg_base_addr[ADDR_WIDTH - 1:12] + 1'b1, 12'd0};
					else if (((do_flush && geom_valid) && !r_plan_ok) && (r_wr_addr != r_cfg_base_addr))
						r_wr_addr <= r_cfg_base_addr;
				2'd1: begin
					if (w_aw_issue) begin
						r_aw_cov_beats <= r_aw_cov_beats + w_aw_sub_len_p1;
						r_aw_subs <= r_aw_subs + 9'd1;
						r_wr_addr <= r_wr_addr + sv2v_cast_A5DC5(w_aw_sub_len_p1 * sv2v_cast_17_signed(BYTES_PER_BEAT));
						r_os_len[r_os_wr] <= sv2v_cast_9(w_aw_sub_len_p1 - 17'd1);
						r_os_wr <= r_os_wr + 2'd1;
						r_ws_len[r_ws_wr] <= sv2v_cast_9(w_aw_sub_len_p1 - 17'd1);
						r_ws_wr <= r_ws_wr + 2'd1;
					end
					if (w_b_issue) begin
						r_b_beats <= (r_b_beats + sv2v_cast_17(r_os_len[r_os_rd])) + 17'd1;
						r_b_subs <= r_b_subs + 9'd1;
						r_os_rd <= r_os_rd + 2'd1;
					end
					if ((((r_b_beats + (w_b_issue ? sv2v_cast_17(r_os_len[r_os_rd]) + 17'd1 : 17'd0)) == sv2v_cast_17(r_cyc_total)) && (r_w_rem_in_sub == 10'd0)) && (r_ws_count == 3'd0))
						r_wr_state <= 2'd0;
					if (w_w_issue) begin
						if (r_w_rem_in_sub == 10'd1)
							r_w_rem_in_sub <= (w_ws_pop ? sv2v_cast_10(r_ws_len[r_ws_rd]) + 10'd1 : 10'd0);
						else
							r_w_rem_in_sub <= r_w_rem_in_sub - 10'd1;
					end
					else if (w_ws_pop)
						r_w_rem_in_sub <= sv2v_cast_10(r_ws_len[r_ws_rd]) + 10'd1;
					if (w_ws_pop)
						r_ws_rd <= r_ws_rd + 2'd1;
					case ({w_aw_issue, w_b_issue})
						2'b10: r_os_count <= r_os_count + 3'd1;
						2'b01: r_os_count <= r_os_count - 3'd1;
						default:
							;
					endcase
					case ({w_aw_issue, w_ws_pop})
						2'b10: r_ws_count <= r_ws_count + 3'd1;
						2'b01: r_ws_count <= r_ws_count - 3'd1;
						default:
							;
					endcase
				end
				default: r_wr_state <= 2'd0;
			endcase
		end
	assign f_r_wr_state = r_wr_state;
	assign f_r_wr_addr = r_wr_addr;
	assign f_r_cyc_total = r_cyc_total;
	assign f_r_aw_cov_beats = r_aw_cov_beats;
	assign f_r_b_beats = r_b_beats;
	assign f_r_aw_subs = r_aw_subs;
	assign f_r_b_subs = r_b_subs;
	assign f_r_os_count = r_os_count;
	assign f_r_ws_count = r_ws_count;
	assign f_r_w_rem_in_sub = r_w_rem_in_sub;
	assign f_w_aw_issue = w_aw_issue;
	reg [AXI_ID_WIDTH_M - 1:0] _unused_bid = fub_m_bid;
	reg [1:0] _unused_bresp = fub_m_bresp;
	initial _sv2v_0 = 0;
endmodule
