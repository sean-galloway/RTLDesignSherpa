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
module gray2bin (
	gray,
	binary
);
	parameter signed [31:0] WIDTH = 4;
	input wire [WIDTH - 1:0] gray;
	output wire [WIDTH - 1:0] binary;
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < WIDTH; _gv_i_2 = _gv_i_2 + 1) begin : gen_gray_to_bin
			localparam i = _gv_i_2;
			assign binary[i] = ^(gray >> i);
		end
	endgenerate
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
module wb4_slave (
	clk,
	aresetn,
	s_wb_CYC,
	s_wb_STB,
	s_wb_WE,
	s_wb_ADR,
	s_wb_DAT_W,
	s_wb_SEL,
	s_wb_CTI,
	s_wb_BTE,
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
	cmd_cti,
	cmd_bte,
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
	parameter signed [31:0] USE_BURST_HINTS = 0;
	parameter signed [31:0] SEL_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = SEL_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_STATUS_WIDTH = 2;
	parameter signed [31:0] STW = wb4_pkg_WB4_STATUS_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_CTI_WIDTH = 3;
	parameter signed [31:0] CTW = wb4_pkg_WB4_CTI_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_BTE_WIDTH = 2;
	parameter signed [31:0] BTW = wb4_pkg_WB4_BTE_WIDTH;
	parameter signed [31:0] CPW = (((1 + AW) + DW) + SW) + (USE_BURST_HINTS != 0 ? CTW + BTW : 0);
	parameter signed [31:0] RPW = STW + DW;
	input wire clk;
	input wire aresetn;
	input wire s_wb_CYC;
	input wire s_wb_STB;
	input wire s_wb_WE;
	input wire [AW - 1:0] s_wb_ADR;
	input wire [DW - 1:0] s_wb_DAT_W;
	input wire [SW - 1:0] s_wb_SEL;
	input wire [CTW - 1:0] s_wb_CTI;
	input wire [BTW - 1:0] s_wb_BTE;
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
	output wire [CTW - 1:0] cmd_cti;
	output wire [BTW - 1:0] cmd_bte;
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
	function automatic [2:0] sv2v_cast_90DB4;
		input reg [2:0] inp;
		sv2v_cast_90DB4 = inp;
	endfunction
	function automatic [CTW - 1:0] sv2v_cast_E0906;
		input reg [CTW - 1:0] inp;
		sv2v_cast_E0906 = inp;
	endfunction
	function automatic [1:0] sv2v_cast_F1CE9;
		input reg [1:0] inp;
		sv2v_cast_F1CE9 = inp;
	endfunction
	function automatic [BTW - 1:0] sv2v_cast_85537;
		input reg [BTW - 1:0] inp;
		sv2v_cast_85537 = inp;
	endfunction
	generate
		if (USE_BURST_HINTS != 0) begin : g_hints
			assign w_cmd_data_in = {s_wb_WE, s_wb_ADR, s_wb_DAT_W, s_wb_SEL, s_wb_CTI, s_wb_BTE};
			assign {cmd_we, cmd_adr, cmd_dat, cmd_sel, cmd_cti, cmd_bte} = r_cmd_data_out;
		end
		else begin : g_no_hints
			assign w_cmd_data_in = {s_wb_WE, s_wb_ADR, s_wb_DAT_W, s_wb_SEL};
			assign {cmd_we, cmd_adr, cmd_dat, cmd_sel} = r_cmd_data_out;
			assign cmd_cti = sv2v_cast_E0906(sv2v_cast_90DB4(3'b000));
			assign cmd_bte = sv2v_cast_85537(sv2v_cast_F1CE9(2'b00));
			wire w_unused_hints;
			assign w_unused_hints = ^{s_wb_CTI, s_wb_BTE};
		end
	endgenerate
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
module wb4_slave_cdc (
	wb_clk,
	wb_resetn,
	aclk,
	aresetn,
	s_wb_CYC,
	s_wb_STB,
	s_wb_WE,
	s_wb_ADR,
	s_wb_DAT_W,
	s_wb_SEL,
	s_wb_CTI,
	s_wb_BTE,
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
	cmd_cti,
	cmd_bte,
	rsp_valid,
	rsp_ready,
	rsp_status,
	rsp_dat
);
	parameter signed [31:0] ADDR_WIDTH = 32;
	parameter signed [31:0] DATA_WIDTH = 32;
	parameter signed [31:0] CMD_DEPTH = 2;
	parameter signed [31:0] RSP_DEPTH = 2;
	parameter signed [31:0] USE_BURST_HINTS = 0;
	parameter signed [31:0] MAX_OUTSTANDING = 16;
	parameter signed [31:0] CLASSIC = 0;
	parameter signed [31:0] CDC_DEPTH = 4;
	parameter signed [31:0] USE_JOHNSON = 0;
	parameter signed [31:0] SEL_WIDTH = DATA_WIDTH / 8;
	parameter signed [31:0] AW = ADDR_WIDTH;
	parameter signed [31:0] DW = DATA_WIDTH;
	parameter signed [31:0] SW = SEL_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_STATUS_WIDTH = 2;
	parameter signed [31:0] STW = wb4_pkg_WB4_STATUS_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_CTI_WIDTH = 3;
	parameter signed [31:0] CTW = wb4_pkg_WB4_CTI_WIDTH;
	localparam signed [31:0] wb4_pkg_WB4_BTE_WIDTH = 2;
	parameter signed [31:0] BTW = wb4_pkg_WB4_BTE_WIDTH;
	parameter signed [31:0] CPW = (((1 + AW) + DW) + SW) + (USE_BURST_HINTS != 0 ? CTW + BTW : 0);
	parameter signed [31:0] RPW = STW + DW;
	input wire wb_clk;
	input wire wb_resetn;
	input wire aclk;
	input wire aresetn;
	input wire s_wb_CYC;
	input wire s_wb_STB;
	input wire s_wb_WE;
	input wire [AW - 1:0] s_wb_ADR;
	input wire [DW - 1:0] s_wb_DAT_W;
	input wire [SW - 1:0] s_wb_SEL;
	input wire [CTW - 1:0] s_wb_CTI;
	input wire [BTW - 1:0] s_wb_BTE;
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
	output wire [CTW - 1:0] cmd_cti;
	output wire [BTW - 1:0] cmd_bte;
	input wire rsp_valid;
	output wire rsp_ready;
	input wire [STW - 1:0] rsp_status;
	input wire [DW - 1:0] rsp_dat;
	localparam signed [31:0] CDC_FIFO_DEPTH = (CDC_DEPTH < 4 ? 4 : CDC_DEPTH);
	wire w_cmd_valid;
	wire w_cmd_ready;
	wire w_cmd_we;
	wire [CTW - 1:0] w_cmd_cti;
	wire [BTW - 1:0] w_cmd_bte;
	wire [AW - 1:0] w_cmd_adr;
	wire [DW - 1:0] w_cmd_dat;
	wire [DW - 1:0] w_rsp_dat;
	wire [SW - 1:0] w_cmd_sel;
	wire w_rsp_valid;
	wire w_rsp_ready;
	wire [STW - 1:0] w_rsp_status;
	wb4_slave #(
		.ADDR_WIDTH(ADDR_WIDTH),
		.DATA_WIDTH(DATA_WIDTH),
		.CMD_DEPTH(CMD_DEPTH),
		.RSP_DEPTH(RSP_DEPTH),
		.MAX_OUTSTANDING(MAX_OUTSTANDING),
		.CLASSIC(CLASSIC),
		.USE_BURST_HINTS(USE_BURST_HINTS),
		.SEL_WIDTH(SEL_WIDTH)
	) u_wb4_slave(
		.clk(wb_clk),
		.aresetn(wb_resetn),
		.s_wb_CYC(s_wb_CYC),
		.s_wb_STB(s_wb_STB),
		.s_wb_WE(s_wb_WE),
		.s_wb_ADR(s_wb_ADR),
		.s_wb_DAT_W(s_wb_DAT_W),
		.s_wb_SEL(s_wb_SEL),
		.s_wb_CTI(s_wb_CTI),
		.s_wb_BTE(s_wb_BTE),
		.s_wb_STALL(s_wb_STALL),
		.s_wb_ACK(s_wb_ACK),
		.s_wb_ERR(s_wb_ERR),
		.s_wb_RTY(s_wb_RTY),
		.s_wb_DAT_R(s_wb_DAT_R),
		.cmd_valid(w_cmd_valid),
		.cmd_ready(w_cmd_ready),
		.cmd_we(w_cmd_we),
		.cmd_adr(w_cmd_adr),
		.cmd_dat(w_cmd_dat),
		.cmd_sel(w_cmd_sel),
		.cmd_cti(w_cmd_cti),
		.cmd_bte(w_cmd_bte),
		.rsp_valid(w_rsp_valid),
		.rsp_ready(w_rsp_ready),
		.rsp_status(w_rsp_status),
		.rsp_dat(w_rsp_dat)
	);
	wire [CPW - 1:0] w_cmd_cdc_in;
	wire [CPW - 1:0] w_cmd_cdc_out;
	function automatic [2:0] sv2v_cast_90DB4;
		input reg [2:0] inp;
		sv2v_cast_90DB4 = inp;
	endfunction
	function automatic [CTW - 1:0] sv2v_cast_E0906;
		input reg [CTW - 1:0] inp;
		sv2v_cast_E0906 = inp;
	endfunction
	function automatic [1:0] sv2v_cast_F1CE9;
		input reg [1:0] inp;
		sv2v_cast_F1CE9 = inp;
	endfunction
	function automatic [BTW - 1:0] sv2v_cast_85537;
		input reg [BTW - 1:0] inp;
		sv2v_cast_85537 = inp;
	endfunction
	generate
		if (USE_BURST_HINTS != 0) begin : g_cdc_hints
			assign w_cmd_cdc_in = {w_cmd_we, w_cmd_adr, w_cmd_dat, w_cmd_sel, w_cmd_cti, w_cmd_bte};
			assign {cmd_we, cmd_adr, cmd_dat, cmd_sel, cmd_cti, cmd_bte} = w_cmd_cdc_out;
		end
		else begin : g_cdc_no_hints
			assign w_cmd_cdc_in = {w_cmd_we, w_cmd_adr, w_cmd_dat, w_cmd_sel};
			assign {cmd_we, cmd_adr, cmd_dat, cmd_sel} = w_cmd_cdc_out;
			assign cmd_cti = sv2v_cast_E0906(sv2v_cast_90DB4(3'b000));
			assign cmd_bte = sv2v_cast_85537(sv2v_cast_F1CE9(2'b00));
			wire w_unused_cdc_hints;
			assign w_unused_cdc_hints = ^{w_cmd_cti, w_cmd_bte};
		end
	endgenerate
	gaxi_fifo_async #(
		.DATA_WIDTH(CPW),
		.DEPTH(CDC_FIFO_DEPTH),
		.USE_JOHNSON(USE_JOHNSON),
		.N_FLOP_CROSS(2)
	) u_cmd_cdc_fifo(
		.axi_wr_aclk(wb_clk),
		.axi_wr_aresetn(wb_resetn),
		.axi_rd_aclk(aclk),
		.axi_rd_aresetn(aresetn),
		.wr_valid(w_cmd_valid),
		.wr_ready(w_cmd_ready),
		.wr_data(w_cmd_cdc_in),
		.rd_ready(cmd_ready),
		.rd_valid(cmd_valid),
		.rd_data(w_cmd_cdc_out)
	);
	gaxi_fifo_async #(
		.DATA_WIDTH(RPW),
		.DEPTH(CDC_FIFO_DEPTH),
		.USE_JOHNSON(USE_JOHNSON),
		.N_FLOP_CROSS(2)
	) u_rsp_cdc_fifo(
		.axi_wr_aclk(aclk),
		.axi_wr_aresetn(aresetn),
		.axi_rd_aclk(wb_clk),
		.axi_rd_aresetn(wb_resetn),
		.wr_valid(rsp_valid),
		.wr_ready(rsp_ready),
		.wr_data({rsp_status, rsp_dat}),
		.rd_ready(w_rsp_ready),
		.rd_valid(w_rsp_valid),
		.rd_data({w_rsp_status, w_rsp_dat})
	);
endmodule
