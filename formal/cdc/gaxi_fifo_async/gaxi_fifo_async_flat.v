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
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < WIDTH; _gv_i_2 = _gv_i_2 + 1) begin : gen_gray_to_bin
			localparam i = _gv_i_2;
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
			initial $display("Error [elaboration] /tmp/claude-1000/defork_gaxi_fifo_async/gaxi_fifo_async.sv:83:9 - gaxi_fifo_async.g_bad_depth\n msg: ", "gaxi_fifo_async: USE_JOHNSON=0 (Gray) requires a power-of-2 DEPTH, got %0d. Set USE_JOHNSON=1 for arbitrary depths.", DEPTH);
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
