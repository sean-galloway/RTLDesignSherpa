module math_prefix_cell (
	i_g_hi,
	i_p_hi,
	i_g_lo,
	i_p_lo,
	ow_g,
	ow_p
);
	input wire i_g_hi;
	input wire i_p_hi;
	input wire i_g_lo;
	input wire i_p_lo;
	output wire ow_g;
	output wire ow_p;
	assign ow_g = i_g_hi | (i_p_hi & i_g_lo);
	assign ow_p = i_p_hi & i_p_lo;
endmodule
module math_prefix_cell_gray (
	i_g_hi,
	i_p_hi,
	i_g_lo,
	ow_g
);
	input wire i_g_hi;
	input wire i_p_hi;
	input wire i_g_lo;
	output wire ow_g;
	assign ow_g = i_g_hi | (i_p_hi & i_g_lo);
endmodule
module math_adder_full (
	i_a,
	i_b,
	i_c,
	ow_sum,
	ow_carry
);
	parameter signed [31:0] N = 1;
	input wire i_a;
	input wire i_b;
	input wire i_c;
	output wire ow_sum;
	output wire ow_carry;
	assign ow_sum = (i_a ^ i_b) ^ i_c;
	assign ow_carry = (i_a & i_b) | (i_c & (i_a ^ i_b));
endmodule
module math_adder_han_carlson_016 (
	i_a,
	i_b,
	i_cin,
	ow_sum,
	ow_cout
);
	parameter signed [31:0] N = 16;
	input wire [N - 1:0] i_a;
	input wire [N - 1:0] i_b;
	input wire i_cin;
	output wire [N - 1:0] ow_sum;
	output wire ow_cout;
	wire [N - 1:0] w_p0;
	wire [N - 1:0] w_g0;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_pg
			localparam i = _gv_i_1;
			assign w_p0[i] = i_a[i] ^ i_b[i];
			assign w_g0[i] = i_a[i] & i_b[i];
		end
	endgenerate
	wire [N - 1:0] w_p1;
	wire [N - 1:0] w_g1;
	wire [N - 1:0] w_p2;
	wire [N - 1:0] w_g2;
	wire [N - 1:0] w_p3;
	wire [N - 1:0] w_g3;
	wire [N - 1:0] w_p4;
	wire [N - 1:0] w_g4;
	wire [N - 1:0] w_p5;
	wire [N - 1:0] w_g5;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_stage1
			localparam i = _gv_i_1;
			if (i == 0) begin : gen_s1_bit0
				assign w_g1[0] = w_g0[0] | (w_p0[0] & i_cin);
				assign w_p1[0] = w_p0[0];
			end
			else if ((i % 2) == 0) begin : gen_s1_even
				math_prefix_cell u_pf_s1(
					.i_g_hi(w_g0[i]),
					.i_p_hi(w_p0[i]),
					.i_g_lo(w_g0[i - 1]),
					.i_p_lo(w_p0[i - 1]),
					.ow_g(w_g1[i]),
					.ow_p(w_p1[i])
				);
			end
			else begin : gen_s1_odd
				assign w_g1[i] = w_g0[i];
				assign w_p1[i] = w_p0[i];
			end
		end
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_stage2
			localparam i = _gv_i_1;
			if (((i % 2) == 0) && (i >= 2)) begin : gen_s2_active
				math_prefix_cell u_pf_s2(
					.i_g_hi(w_g1[i]),
					.i_p_hi(w_p1[i]),
					.i_g_lo(w_g1[i - 2]),
					.i_p_lo(w_p1[i - 2]),
					.ow_g(w_g2[i]),
					.ow_p(w_p2[i])
				);
			end
			else begin : gen_s2_pass
				assign w_g2[i] = w_g1[i];
				assign w_p2[i] = w_p1[i];
			end
		end
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_stage3
			localparam i = _gv_i_1;
			if (((i % 2) == 0) && (i >= 4)) begin : gen_s3_active
				math_prefix_cell u_pf_s3(
					.i_g_hi(w_g2[i]),
					.i_p_hi(w_p2[i]),
					.i_g_lo(w_g2[i - 4]),
					.i_p_lo(w_p2[i - 4]),
					.ow_g(w_g3[i]),
					.ow_p(w_p3[i])
				);
			end
			else begin : gen_s3_pass
				assign w_g3[i] = w_g2[i];
				assign w_p3[i] = w_p2[i];
			end
		end
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_stage4
			localparam i = _gv_i_1;
			if (((i % 2) == 0) && (i >= 8)) begin : gen_s4_active
				math_prefix_cell u_pf_s4(
					.i_g_hi(w_g3[i]),
					.i_p_hi(w_p3[i]),
					.i_g_lo(w_g3[i - 8]),
					.i_p_lo(w_p3[i - 8]),
					.ow_g(w_g4[i]),
					.ow_p(w_p4[i])
				);
			end
			else begin : gen_s4_pass
				assign w_g4[i] = w_g3[i];
				assign w_p4[i] = w_p3[i];
			end
		end
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_stage5
			localparam i = _gv_i_1;
			if ((i % 2) == 1) begin : gen_s5_odd
				math_prefix_cell_gray u_pf_s5(
					.i_g_hi(w_g4[i]),
					.i_p_hi(w_p4[i]),
					.i_g_lo(w_g4[i - 1]),
					.ow_g(w_g5[i])
				);
				assign w_p5[i] = w_p4[i];
			end
			else begin : gen_s5_even
				assign w_g5[i] = w_g4[i];
				assign w_p5[i] = w_p4[i];
			end
		end
		for (_gv_i_1 = 0; _gv_i_1 < N; _gv_i_1 = _gv_i_1 + 1) begin : gen_sum
			localparam i = _gv_i_1;
			if (i == 0) begin : gen_sum_bit0
				assign ow_sum[0] = w_p0[0] ^ i_cin;
			end
			else begin : gen_sum_other
				assign ow_sum[i] = w_p0[i] ^ w_g5[i - 1];
			end
		end
	endgenerate
	assign ow_cout = w_g5[N - 1];
endmodule
module math_compressor_4to2 (
	i_x1,
	i_x2,
	i_x3,
	i_x4,
	i_cin,
	ow_sum,
	ow_carry,
	ow_cout
);
	input wire i_x1;
	input wire i_x2;
	input wire i_x3;
	input wire i_x4;
	input wire i_cin;
	output wire ow_sum;
	output wire ow_carry;
	output wire ow_cout;
	wire w_int_sum;
	wire w_int_carry;
	math_adder_full u_fa1(
		.i_a(i_x1),
		.i_b(i_x2),
		.i_c(i_x3),
		.ow_sum(w_int_sum),
		.ow_carry(ow_cout)
	);
	math_adder_full u_fa2(
		.i_a(w_int_sum),
		.i_b(i_x4),
		.i_c(i_cin),
		.ow_sum(ow_sum),
		.ow_carry(ow_carry)
	);
endmodule
module math_multiplier_dadda_4to2_008 (
	i_multiplier,
	i_multiplicand,
	ow_product
);
	parameter signed [31:0] N = 8;
	input wire [N - 1:0] i_multiplier;
	input wire [N - 1:0] i_multiplicand;
	output wire [(2 * N) - 1:0] ow_product;
	wire w_pp_0_0 = i_multiplier[0] & i_multiplicand[0];
	wire w_pp_0_1 = i_multiplier[0] & i_multiplicand[1];
	wire w_pp_0_2 = i_multiplier[0] & i_multiplicand[2];
	wire w_pp_0_3 = i_multiplier[0] & i_multiplicand[3];
	wire w_pp_0_4 = i_multiplier[0] & i_multiplicand[4];
	wire w_pp_0_5 = i_multiplier[0] & i_multiplicand[5];
	wire w_pp_0_6 = i_multiplier[0] & i_multiplicand[6];
	wire w_pp_0_7 = i_multiplier[0] & i_multiplicand[7];
	wire w_pp_1_0 = i_multiplier[1] & i_multiplicand[0];
	wire w_pp_1_1 = i_multiplier[1] & i_multiplicand[1];
	wire w_pp_1_2 = i_multiplier[1] & i_multiplicand[2];
	wire w_pp_1_3 = i_multiplier[1] & i_multiplicand[3];
	wire w_pp_1_4 = i_multiplier[1] & i_multiplicand[4];
	wire w_pp_1_5 = i_multiplier[1] & i_multiplicand[5];
	wire w_pp_1_6 = i_multiplier[1] & i_multiplicand[6];
	wire w_pp_1_7 = i_multiplier[1] & i_multiplicand[7];
	wire w_pp_2_0 = i_multiplier[2] & i_multiplicand[0];
	wire w_pp_2_1 = i_multiplier[2] & i_multiplicand[1];
	wire w_pp_2_2 = i_multiplier[2] & i_multiplicand[2];
	wire w_pp_2_3 = i_multiplier[2] & i_multiplicand[3];
	wire w_pp_2_4 = i_multiplier[2] & i_multiplicand[4];
	wire w_pp_2_5 = i_multiplier[2] & i_multiplicand[5];
	wire w_pp_2_6 = i_multiplier[2] & i_multiplicand[6];
	wire w_pp_2_7 = i_multiplier[2] & i_multiplicand[7];
	wire w_pp_3_0 = i_multiplier[3] & i_multiplicand[0];
	wire w_pp_3_1 = i_multiplier[3] & i_multiplicand[1];
	wire w_pp_3_2 = i_multiplier[3] & i_multiplicand[2];
	wire w_pp_3_3 = i_multiplier[3] & i_multiplicand[3];
	wire w_pp_3_4 = i_multiplier[3] & i_multiplicand[4];
	wire w_pp_3_5 = i_multiplier[3] & i_multiplicand[5];
	wire w_pp_3_6 = i_multiplier[3] & i_multiplicand[6];
	wire w_pp_3_7 = i_multiplier[3] & i_multiplicand[7];
	wire w_pp_4_0 = i_multiplier[4] & i_multiplicand[0];
	wire w_pp_4_1 = i_multiplier[4] & i_multiplicand[1];
	wire w_pp_4_2 = i_multiplier[4] & i_multiplicand[2];
	wire w_pp_4_3 = i_multiplier[4] & i_multiplicand[3];
	wire w_pp_4_4 = i_multiplier[4] & i_multiplicand[4];
	wire w_pp_4_5 = i_multiplier[4] & i_multiplicand[5];
	wire w_pp_4_6 = i_multiplier[4] & i_multiplicand[6];
	wire w_pp_4_7 = i_multiplier[4] & i_multiplicand[7];
	wire w_pp_5_0 = i_multiplier[5] & i_multiplicand[0];
	wire w_pp_5_1 = i_multiplier[5] & i_multiplicand[1];
	wire w_pp_5_2 = i_multiplier[5] & i_multiplicand[2];
	wire w_pp_5_3 = i_multiplier[5] & i_multiplicand[3];
	wire w_pp_5_4 = i_multiplier[5] & i_multiplicand[4];
	wire w_pp_5_5 = i_multiplier[5] & i_multiplicand[5];
	wire w_pp_5_6 = i_multiplier[5] & i_multiplicand[6];
	wire w_pp_5_7 = i_multiplier[5] & i_multiplicand[7];
	wire w_pp_6_0 = i_multiplier[6] & i_multiplicand[0];
	wire w_pp_6_1 = i_multiplier[6] & i_multiplicand[1];
	wire w_pp_6_2 = i_multiplier[6] & i_multiplicand[2];
	wire w_pp_6_3 = i_multiplier[6] & i_multiplicand[3];
	wire w_pp_6_4 = i_multiplier[6] & i_multiplicand[4];
	wire w_pp_6_5 = i_multiplier[6] & i_multiplicand[5];
	wire w_pp_6_6 = i_multiplier[6] & i_multiplicand[6];
	wire w_pp_6_7 = i_multiplier[6] & i_multiplicand[7];
	wire w_pp_7_0 = i_multiplier[7] & i_multiplicand[0];
	wire w_pp_7_1 = i_multiplier[7] & i_multiplicand[1];
	wire w_pp_7_2 = i_multiplier[7] & i_multiplicand[2];
	wire w_pp_7_3 = i_multiplier[7] & i_multiplicand[3];
	wire w_pp_7_4 = i_multiplier[7] & i_multiplicand[4];
	wire w_pp_7_5 = i_multiplier[7] & i_multiplicand[5];
	wire w_pp_7_6 = i_multiplier[7] & i_multiplicand[6];
	wire w_pp_7_7 = i_multiplier[7] & i_multiplicand[7];
	wire w_c4to2_sum_06_000;
	wire w_c4to2_carry_06_000;
	wire w_c4to2_cout_06_000;
	math_compressor_4to2 u_c4to2_06_000(
		.i_x1(w_pp_0_6),
		.i_x2(w_pp_1_5),
		.i_x3(w_pp_2_4),
		.i_x4(w_pp_3_3),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_06_000),
		.ow_carry(w_c4to2_carry_06_000),
		.ow_cout(w_c4to2_cout_06_000)
	);
	wire w_c4to2_sum_07_001;
	wire w_c4to2_carry_07_001;
	wire w_c4to2_cout_07_001;
	math_compressor_4to2 u_c4to2_07_001(
		.i_x1(w_pp_0_7),
		.i_x2(w_pp_1_6),
		.i_x3(w_pp_2_5),
		.i_x4(w_pp_3_4),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_07_001),
		.ow_carry(w_c4to2_carry_07_001),
		.ow_cout(w_c4to2_cout_07_001)
	);
	wire w_c4to2_sum_07_002;
	wire w_c4to2_carry_07_002;
	wire w_c4to2_cout_07_002;
	math_compressor_4to2 u_c4to2_07_002(
		.i_x1(w_pp_4_3),
		.i_x2(w_pp_5_2),
		.i_x3(w_pp_6_1),
		.i_x4(w_pp_7_0),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_07_002),
		.ow_carry(w_c4to2_carry_07_002),
		.ow_cout(w_c4to2_cout_07_002)
	);
	wire w_c4to2_sum_08_003;
	wire w_c4to2_carry_08_003;
	wire w_c4to2_cout_08_003;
	math_compressor_4to2 u_c4to2_08_003(
		.i_x1(w_pp_1_7),
		.i_x2(w_pp_2_6),
		.i_x3(w_pp_3_5),
		.i_x4(w_pp_4_4),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_08_003),
		.ow_carry(w_c4to2_carry_08_003),
		.ow_cout(w_c4to2_cout_08_003)
	);
	wire w_c4to2_sum_08_004;
	wire w_c4to2_carry_08_004;
	wire w_c4to2_cout_08_004;
	math_compressor_4to2 u_c4to2_08_004(
		.i_x1(w_pp_5_3),
		.i_x2(w_pp_6_2),
		.i_x3(w_pp_7_1),
		.i_x4(w_c4to2_carry_07_001),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_08_004),
		.ow_carry(w_c4to2_carry_08_004),
		.ow_cout(w_c4to2_cout_08_004)
	);
	wire w_c4to2_sum_09_005;
	wire w_c4to2_carry_09_005;
	wire w_c4to2_cout_09_005;
	math_compressor_4to2 u_c4to2_09_005(
		.i_x1(w_pp_2_7),
		.i_x2(w_pp_3_6),
		.i_x3(w_pp_4_5),
		.i_x4(w_pp_5_4),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_09_005),
		.ow_carry(w_c4to2_carry_09_005),
		.ow_cout(w_c4to2_cout_09_005)
	);
	wire w_c4to2_sum_09_006;
	wire w_c4to2_carry_09_006;
	wire w_c4to2_cout_09_006;
	math_compressor_4to2 u_c4to2_09_006(
		.i_x1(w_pp_6_3),
		.i_x2(w_pp_7_2),
		.i_x3(w_c4to2_carry_08_003),
		.i_x4(w_c4to2_cout_08_003),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_09_006),
		.ow_carry(w_c4to2_carry_09_006),
		.ow_cout(w_c4to2_cout_09_006)
	);
	wire w_c4to2_sum_10_007;
	wire w_c4to2_carry_10_007;
	wire w_c4to2_cout_10_007;
	math_compressor_4to2 u_c4to2_10_007(
		.i_x1(w_pp_3_7),
		.i_x2(w_pp_4_6),
		.i_x3(w_pp_5_5),
		.i_x4(w_pp_6_4),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_10_007),
		.ow_carry(w_c4to2_carry_10_007),
		.ow_cout(w_c4to2_cout_10_007)
	);
	wire w_c4to2_sum_04_008;
	wire w_c4to2_carry_04_008;
	wire w_c4to2_cout_04_008;
	math_compressor_4to2 u_c4to2_04_008(
		.i_x1(w_pp_0_4),
		.i_x2(w_pp_1_3),
		.i_x3(w_pp_2_2),
		.i_x4(w_pp_3_1),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_04_008),
		.ow_carry(w_c4to2_carry_04_008),
		.ow_cout(w_c4to2_cout_04_008)
	);
	wire w_c4to2_sum_05_009;
	wire w_c4to2_carry_05_009;
	wire w_c4to2_cout_05_009;
	math_compressor_4to2 u_c4to2_05_009(
		.i_x1(w_pp_0_5),
		.i_x2(w_pp_1_4),
		.i_x3(w_pp_2_3),
		.i_x4(w_pp_3_2),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_05_009),
		.ow_carry(w_c4to2_carry_05_009),
		.ow_cout(w_c4to2_cout_05_009)
	);
	wire w_c4to2_sum_05_010;
	wire w_c4to2_carry_05_010;
	wire w_c4to2_cout_05_010;
	math_compressor_4to2 u_c4to2_05_010(
		.i_x1(w_pp_4_1),
		.i_x2(w_pp_5_0),
		.i_x3(w_c4to2_carry_04_008),
		.i_x4(w_c4to2_cout_04_008),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_05_010),
		.ow_carry(w_c4to2_carry_05_010),
		.ow_cout(w_c4to2_cout_05_010)
	);
	wire w_c4to2_sum_06_011;
	wire w_c4to2_carry_06_011;
	wire w_c4to2_cout_06_011;
	math_compressor_4to2 u_c4to2_06_011(
		.i_x1(w_pp_4_2),
		.i_x2(w_pp_5_1),
		.i_x3(w_pp_6_0),
		.i_x4(w_c4to2_sum_06_000),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_06_011),
		.ow_carry(w_c4to2_carry_06_011),
		.ow_cout(w_c4to2_cout_06_011)
	);
	wire w_c4to2_sum_06_012;
	wire w_c4to2_carry_06_012;
	wire w_c4to2_cout_06_012;
	math_compressor_4to2 u_c4to2_06_012(
		.i_x1(w_c4to2_carry_05_009),
		.i_x2(w_c4to2_cout_05_009),
		.i_x3(w_c4to2_carry_05_010),
		.i_x4(w_c4to2_cout_05_010),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_06_012),
		.ow_carry(w_c4to2_carry_06_012),
		.ow_cout(w_c4to2_cout_06_012)
	);
	wire w_c4to2_sum_07_013;
	wire w_c4to2_carry_07_013;
	wire w_c4to2_cout_07_013;
	math_compressor_4to2 u_c4to2_07_013(
		.i_x1(w_c4to2_carry_06_000),
		.i_x2(w_c4to2_cout_06_000),
		.i_x3(w_c4to2_sum_07_001),
		.i_x4(w_c4to2_sum_07_002),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_07_013),
		.ow_carry(w_c4to2_carry_07_013),
		.ow_cout(w_c4to2_cout_07_013)
	);
	wire w_c4to2_sum_07_014;
	wire w_c4to2_carry_07_014;
	wire w_c4to2_cout_07_014;
	math_compressor_4to2 u_c4to2_07_014(
		.i_x1(w_c4to2_carry_06_011),
		.i_x2(w_c4to2_cout_06_011),
		.i_x3(w_c4to2_carry_06_012),
		.i_x4(w_c4to2_cout_06_012),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_07_014),
		.ow_carry(w_c4to2_carry_07_014),
		.ow_cout(w_c4to2_cout_07_014)
	);
	wire w_c4to2_sum_08_015;
	wire w_c4to2_carry_08_015;
	wire w_c4to2_cout_08_015;
	math_compressor_4to2 u_c4to2_08_015(
		.i_x1(w_c4to2_cout_07_001),
		.i_x2(w_c4to2_carry_07_002),
		.i_x3(w_c4to2_cout_07_002),
		.i_x4(w_c4to2_sum_08_003),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_08_015),
		.ow_carry(w_c4to2_carry_08_015),
		.ow_cout(w_c4to2_cout_08_015)
	);
	wire w_c4to2_sum_08_016;
	wire w_c4to2_carry_08_016;
	wire w_c4to2_cout_08_016;
	math_compressor_4to2 u_c4to2_08_016(
		.i_x1(w_c4to2_sum_08_004),
		.i_x2(w_c4to2_carry_07_013),
		.i_x3(w_c4to2_cout_07_013),
		.i_x4(w_c4to2_carry_07_014),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_08_016),
		.ow_carry(w_c4to2_carry_08_016),
		.ow_cout(w_c4to2_cout_08_016)
	);
	wire w_c4to2_sum_09_017;
	wire w_c4to2_carry_09_017;
	wire w_c4to2_cout_09_017;
	math_compressor_4to2 u_c4to2_09_017(
		.i_x1(w_c4to2_carry_08_004),
		.i_x2(w_c4to2_cout_08_004),
		.i_x3(w_c4to2_sum_09_005),
		.i_x4(w_c4to2_sum_09_006),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_09_017),
		.ow_carry(w_c4to2_carry_09_017),
		.ow_cout(w_c4to2_cout_09_017)
	);
	wire w_c4to2_sum_09_018;
	wire w_c4to2_carry_09_018;
	wire w_c4to2_cout_09_018;
	math_compressor_4to2 u_c4to2_09_018(
		.i_x1(w_c4to2_carry_08_015),
		.i_x2(w_c4to2_cout_08_015),
		.i_x3(w_c4to2_carry_08_016),
		.i_x4(w_c4to2_cout_08_016),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_09_018),
		.ow_carry(w_c4to2_carry_09_018),
		.ow_cout(w_c4to2_cout_09_018)
	);
	wire w_c4to2_sum_10_019;
	wire w_c4to2_carry_10_019;
	wire w_c4to2_cout_10_019;
	math_compressor_4to2 u_c4to2_10_019(
		.i_x1(w_pp_7_3),
		.i_x2(w_c4to2_carry_09_005),
		.i_x3(w_c4to2_cout_09_005),
		.i_x4(w_c4to2_carry_09_006),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_10_019),
		.ow_carry(w_c4to2_carry_10_019),
		.ow_cout(w_c4to2_cout_10_019)
	);
	wire w_c4to2_sum_10_020;
	wire w_c4to2_carry_10_020;
	wire w_c4to2_cout_10_020;
	math_compressor_4to2 u_c4to2_10_020(
		.i_x1(w_c4to2_cout_09_006),
		.i_x2(w_c4to2_sum_10_007),
		.i_x3(w_c4to2_carry_09_017),
		.i_x4(w_c4to2_cout_09_017),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_10_020),
		.ow_carry(w_c4to2_carry_10_020),
		.ow_cout(w_c4to2_cout_10_020)
	);
	wire w_c4to2_sum_11_021;
	wire w_c4to2_carry_11_021;
	wire w_c4to2_cout_11_021;
	math_compressor_4to2 u_c4to2_11_021(
		.i_x1(w_pp_4_7),
		.i_x2(w_pp_5_6),
		.i_x3(w_pp_6_5),
		.i_x4(w_pp_7_4),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_11_021),
		.ow_carry(w_c4to2_carry_11_021),
		.ow_cout(w_c4to2_cout_11_021)
	);
	wire w_c4to2_sum_11_022;
	wire w_c4to2_carry_11_022;
	wire w_c4to2_cout_11_022;
	math_compressor_4to2 u_c4to2_11_022(
		.i_x1(w_c4to2_carry_10_007),
		.i_x2(w_c4to2_cout_10_007),
		.i_x3(w_c4to2_carry_10_019),
		.i_x4(w_c4to2_cout_10_019),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_11_022),
		.ow_carry(w_c4to2_carry_11_022),
		.ow_cout(w_c4to2_cout_11_022)
	);
	wire w_c4to2_sum_12_023;
	wire w_c4to2_carry_12_023;
	wire w_c4to2_cout_12_023;
	math_compressor_4to2 u_c4to2_12_023(
		.i_x1(w_pp_5_7),
		.i_x2(w_pp_6_6),
		.i_x3(w_pp_7_5),
		.i_x4(w_c4to2_carry_11_021),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_12_023),
		.ow_carry(w_c4to2_carry_12_023),
		.ow_cout(w_c4to2_cout_12_023)
	);
	wire w_c4to2_sum_03_024;
	wire w_c4to2_carry_03_024;
	wire w_c4to2_cout_03_024;
	math_compressor_4to2 u_c4to2_03_024(
		.i_x1(w_pp_0_3),
		.i_x2(w_pp_1_2),
		.i_x3(w_pp_2_1),
		.i_x4(w_pp_3_0),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_03_024),
		.ow_carry(w_c4to2_carry_03_024),
		.ow_cout(w_c4to2_cout_03_024)
	);
	wire w_c4to2_sum_04_025;
	wire w_c4to2_carry_04_025;
	wire w_c4to2_cout_04_025;
	math_compressor_4to2 u_c4to2_04_025(
		.i_x1(w_pp_4_0),
		.i_x2(w_c4to2_sum_04_008),
		.i_x3(w_c4to2_carry_03_024),
		.i_x4(w_c4to2_cout_03_024),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_04_025),
		.ow_carry(w_c4to2_carry_04_025),
		.ow_cout(w_c4to2_cout_04_025)
	);
	wire w_c4to2_sum_05_026;
	wire w_c4to2_carry_05_026;
	wire w_c4to2_cout_05_026;
	math_compressor_4to2 u_c4to2_05_026(
		.i_x1(w_c4to2_sum_05_009),
		.i_x2(w_c4to2_sum_05_010),
		.i_x3(w_c4to2_carry_04_025),
		.i_x4(w_c4to2_cout_04_025),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_05_026),
		.ow_carry(w_c4to2_carry_05_026),
		.ow_cout(w_c4to2_cout_05_026)
	);
	wire w_c4to2_sum_06_027;
	wire w_c4to2_carry_06_027;
	wire w_c4to2_cout_06_027;
	math_compressor_4to2 u_c4to2_06_027(
		.i_x1(w_c4to2_sum_06_011),
		.i_x2(w_c4to2_sum_06_012),
		.i_x3(w_c4to2_carry_05_026),
		.i_x4(w_c4to2_cout_05_026),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_06_027),
		.ow_carry(w_c4to2_carry_06_027),
		.ow_cout(w_c4to2_cout_06_027)
	);
	wire w_c4to2_sum_07_028;
	wire w_c4to2_carry_07_028;
	wire w_c4to2_cout_07_028;
	math_compressor_4to2 u_c4to2_07_028(
		.i_x1(w_c4to2_sum_07_013),
		.i_x2(w_c4to2_sum_07_014),
		.i_x3(w_c4to2_carry_06_027),
		.i_x4(w_c4to2_cout_06_027),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_07_028),
		.ow_carry(w_c4to2_carry_07_028),
		.ow_cout(w_c4to2_cout_07_028)
	);
	wire w_c4to2_sum_08_029;
	wire w_c4to2_carry_08_029;
	wire w_c4to2_cout_08_029;
	math_compressor_4to2 u_c4to2_08_029(
		.i_x1(w_c4to2_cout_07_014),
		.i_x2(w_c4to2_sum_08_015),
		.i_x3(w_c4to2_sum_08_016),
		.i_x4(w_c4to2_carry_07_028),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_08_029),
		.ow_carry(w_c4to2_carry_08_029),
		.ow_cout(w_c4to2_cout_08_029)
	);
	wire w_c4to2_sum_09_030;
	wire w_c4to2_carry_09_030;
	wire w_c4to2_cout_09_030;
	math_compressor_4to2 u_c4to2_09_030(
		.i_x1(w_c4to2_sum_09_017),
		.i_x2(w_c4to2_sum_09_018),
		.i_x3(w_c4to2_carry_08_029),
		.i_x4(w_c4to2_cout_08_029),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_09_030),
		.ow_carry(w_c4to2_carry_09_030),
		.ow_cout(w_c4to2_cout_09_030)
	);
	wire w_c4to2_sum_10_031;
	wire w_c4to2_carry_10_031;
	wire w_c4to2_cout_10_031;
	math_compressor_4to2 u_c4to2_10_031(
		.i_x1(w_c4to2_carry_09_018),
		.i_x2(w_c4to2_cout_09_018),
		.i_x3(w_c4to2_sum_10_019),
		.i_x4(w_c4to2_sum_10_020),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_10_031),
		.ow_carry(w_c4to2_carry_10_031),
		.ow_cout(w_c4to2_cout_10_031)
	);
	wire w_c4to2_sum_11_032;
	wire w_c4to2_carry_11_032;
	wire w_c4to2_cout_11_032;
	math_compressor_4to2 u_c4to2_11_032(
		.i_x1(w_c4to2_carry_10_020),
		.i_x2(w_c4to2_cout_10_020),
		.i_x3(w_c4to2_sum_11_021),
		.i_x4(w_c4to2_sum_11_022),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_11_032),
		.ow_carry(w_c4to2_carry_11_032),
		.ow_cout(w_c4to2_cout_11_032)
	);
	wire w_c4to2_sum_12_033;
	wire w_c4to2_carry_12_033;
	wire w_c4to2_cout_12_033;
	math_compressor_4to2 u_c4to2_12_033(
		.i_x1(w_c4to2_cout_11_021),
		.i_x2(w_c4to2_carry_11_022),
		.i_x3(w_c4to2_cout_11_022),
		.i_x4(w_c4to2_sum_12_023),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_12_033),
		.ow_carry(w_c4to2_carry_12_033),
		.ow_cout(w_c4to2_cout_12_033)
	);
	wire w_c4to2_sum_13_034;
	wire w_c4to2_carry_13_034;
	wire w_c4to2_cout_13_034;
	math_compressor_4to2 u_c4to2_13_034(
		.i_x1(w_pp_6_7),
		.i_x2(w_pp_7_6),
		.i_x3(w_c4to2_carry_12_023),
		.i_x4(w_c4to2_cout_12_023),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_13_034),
		.ow_carry(w_c4to2_carry_13_034),
		.ow_cout(w_c4to2_cout_13_034)
	);
	wire w_fa_sum_02_000;
	wire w_fa_carry_02_000;
	math_adder_full u_fa_02_000(
		.i_a(w_pp_0_2),
		.i_b(w_pp_1_1),
		.i_c(w_pp_2_0),
		.ow_sum(w_fa_sum_02_000),
		.ow_carry(w_fa_carry_02_000)
	);
	wire w_fa_sum_10_001;
	wire w_fa_carry_10_001;
	math_adder_full u_fa_10_001(
		.i_a(w_c4to2_carry_09_030),
		.i_b(w_c4to2_cout_09_030),
		.i_c(w_c4to2_sum_10_031),
		.ow_sum(w_fa_sum_10_001),
		.ow_carry(w_fa_carry_10_001)
	);
	wire w_c4to2_sum_11_035;
	wire w_c4to2_carry_11_035;
	wire w_c4to2_cout_11_035;
	math_compressor_4to2 u_c4to2_11_035(
		.i_x1(w_c4to2_carry_10_031),
		.i_x2(w_c4to2_cout_10_031),
		.i_x3(w_c4to2_sum_11_032),
		.i_x4(w_fa_carry_10_001),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_11_035),
		.ow_carry(w_c4to2_carry_11_035),
		.ow_cout(w_c4to2_cout_11_035)
	);
	wire w_c4to2_sum_12_036;
	wire w_c4to2_carry_12_036;
	wire w_c4to2_cout_12_036;
	math_compressor_4to2 u_c4to2_12_036(
		.i_x1(w_c4to2_carry_11_032),
		.i_x2(w_c4to2_cout_11_032),
		.i_x3(w_c4to2_sum_12_033),
		.i_x4(w_c4to2_carry_11_035),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_12_036),
		.ow_carry(w_c4to2_carry_12_036),
		.ow_cout(w_c4to2_cout_12_036)
	);
	wire w_c4to2_sum_13_037;
	wire w_c4to2_carry_13_037;
	wire w_c4to2_cout_13_037;
	math_compressor_4to2 u_c4to2_13_037(
		.i_x1(w_c4to2_carry_12_033),
		.i_x2(w_c4to2_cout_12_033),
		.i_x3(w_c4to2_sum_13_034),
		.i_x4(w_c4to2_carry_12_036),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_13_037),
		.ow_carry(w_c4to2_carry_13_037),
		.ow_cout(w_c4to2_cout_13_037)
	);
	wire w_c4to2_sum_14_038;
	wire w_c4to2_carry_14_038;
	wire w_c4to2_cout_14_038;
	math_compressor_4to2 u_c4to2_14_038(
		.i_x1(w_pp_7_7),
		.i_x2(w_c4to2_carry_13_034),
		.i_x3(w_c4to2_cout_13_034),
		.i_x4(w_c4to2_carry_13_037),
		.i_cin(1'b0),
		.ow_sum(w_c4to2_sum_14_038),
		.ow_carry(w_c4to2_carry_14_038),
		.ow_cout(w_c4to2_cout_14_038)
	);
	wire [(2 * N) - 1:0] w_cpa_a;
	wire [(2 * N) - 1:0] w_cpa_b;
	assign w_cpa_a[0] = w_pp_0_0;
	assign w_cpa_b[0] = 1'b0;
	assign w_cpa_a[1] = w_pp_0_1;
	assign w_cpa_b[1] = w_pp_1_0;
	assign w_cpa_a[2] = w_fa_sum_02_000;
	assign w_cpa_b[2] = 1'b0;
	assign w_cpa_a[3] = w_c4to2_sum_03_024;
	assign w_cpa_b[3] = w_fa_carry_02_000;
	assign w_cpa_a[4] = w_c4to2_sum_04_025;
	assign w_cpa_b[4] = 1'b0;
	assign w_cpa_a[5] = w_c4to2_sum_05_026;
	assign w_cpa_b[5] = 1'b0;
	assign w_cpa_a[6] = w_c4to2_sum_06_027;
	assign w_cpa_b[6] = 1'b0;
	assign w_cpa_a[7] = w_c4to2_sum_07_028;
	assign w_cpa_b[7] = 1'b0;
	assign w_cpa_a[8] = w_c4to2_cout_07_028;
	assign w_cpa_b[8] = w_c4to2_sum_08_029;
	assign w_cpa_a[9] = w_c4to2_sum_09_030;
	assign w_cpa_b[9] = 1'b0;
	assign w_cpa_a[10] = w_fa_sum_10_001;
	assign w_cpa_b[10] = 1'b0;
	assign w_cpa_a[11] = w_c4to2_sum_11_035;
	assign w_cpa_b[11] = 1'b0;
	assign w_cpa_a[12] = w_c4to2_cout_11_035;
	assign w_cpa_b[12] = w_c4to2_sum_12_036;
	assign w_cpa_a[13] = w_c4to2_cout_12_036;
	assign w_cpa_b[13] = w_c4to2_sum_13_037;
	assign w_cpa_a[14] = w_c4to2_cout_13_037;
	assign w_cpa_b[14] = w_c4to2_sum_14_038;
	assign w_cpa_a[15] = w_c4to2_carry_14_038;
	assign w_cpa_b[15] = w_c4to2_cout_14_038;
	wire w_cpa_cout;
	math_adder_han_carlson_016 u_final_cpa(
		.i_a(w_cpa_a),
		.i_b(w_cpa_b),
		.i_cin(1'b0),
		.ow_sum(ow_product),
		.ow_cout(w_cpa_cout)
	);
endmodule
module math_bf16_exponent_adder (
	i_exp_a,
	i_exp_b,
	i_norm_adjust,
	ow_exp_out,
	ow_overflow,
	ow_underflow,
	ow_a_is_zero,
	ow_b_is_zero,
	ow_a_is_inf,
	ow_b_is_inf,
	ow_a_is_nan,
	ow_b_is_nan
);
	reg _sv2v_0;
	input wire [7:0] i_exp_a;
	input wire [7:0] i_exp_b;
	input wire i_norm_adjust;
	output reg [7:0] ow_exp_out;
	output wire ow_overflow;
	output wire ow_underflow;
	output wire ow_a_is_zero;
	output wire ow_b_is_zero;
	output wire ow_a_is_inf;
	output wire ow_b_is_inf;
	output wire ow_a_is_nan;
	output wire ow_b_is_nan;
	assign ow_a_is_zero = i_exp_a == 8'h00;
	assign ow_b_is_zero = i_exp_b == 8'h00;
	assign ow_a_is_inf = i_exp_a == 8'hff;
	assign ow_b_is_inf = i_exp_b == 8'hff;
	assign ow_a_is_nan = i_exp_a == 8'hff;
	assign ow_b_is_nan = i_exp_b == 8'hff;
	wire [9:0] w_exp_sum_raw;
	assign w_exp_sum_raw = (({2'b00, i_exp_a} + {2'b00, i_exp_b}) + {9'b000000000, i_norm_adjust}) - 10'd127;
	wire w_underflow_raw = w_exp_sum_raw[9] | (w_exp_sum_raw == 10'd0);
	wire w_overflow_raw = ~w_underflow_raw & (w_exp_sum_raw > 10'd254);
	wire w_either_special = ((ow_a_is_inf | ow_b_is_inf) | ow_a_is_zero) | ow_b_is_zero;
	assign ow_overflow = w_overflow_raw & ~w_either_special;
	assign ow_underflow = w_underflow_raw & ~w_either_special;
	always @(*) begin
		if (_sv2v_0)
			;
		if (ow_overflow)
			ow_exp_out = 8'hff;
		else if (ow_underflow)
			ow_exp_out = 8'h00;
		else
			ow_exp_out = w_exp_sum_raw[7:0];
	end
	initial _sv2v_0 = 0;
endmodule
module math_bf16_mantissa_mult (
	i_mant_a,
	i_mant_b,
	i_a_is_normal,
	i_b_is_normal,
	ow_product,
	ow_needs_norm,
	ow_mant_out,
	ow_guard_bit,
	ow_round_bit,
	ow_sticky_bit
);
	input wire [6:0] i_mant_a;
	input wire [6:0] i_mant_b;
	input wire i_a_is_normal;
	input wire i_b_is_normal;
	output wire [15:0] ow_product;
	output wire ow_needs_norm;
	output wire [6:0] ow_mant_out;
	output wire ow_guard_bit;
	output wire ow_round_bit;
	output wire ow_sticky_bit;
	wire [7:0] w_mant_a_ext = {i_a_is_normal, i_mant_a};
	wire [7:0] w_mant_b_ext = {i_b_is_normal, i_mant_b};
	math_multiplier_dadda_4to2_008 u_mult(
		.i_multiplier(w_mant_a_ext),
		.i_multiplicand(w_mant_b_ext),
		.ow_product(ow_product)
	);
	assign ow_needs_norm = ow_product[15];
	assign ow_mant_out = (ow_needs_norm ? ow_product[14:8] : ow_product[13:7]);
	wire w_guard_norm = ow_product[7];
	wire w_guard_nonorm = ow_product[6];
	wire w_round_norm = ow_product[6];
	wire w_round_nonorm = ow_product[5];
	wire w_sticky_norm = |ow_product[5:0];
	wire w_sticky_nonorm = |ow_product[4:0];
	assign ow_guard_bit = (ow_needs_norm ? w_guard_norm : w_guard_nonorm);
	assign ow_round_bit = (ow_needs_norm ? w_round_norm : w_round_nonorm);
	assign ow_sticky_bit = (ow_needs_norm ? w_sticky_norm : w_sticky_nonorm);
endmodule
module math_bf16_multiplier (
	i_a,
	i_b,
	ow_result,
	ow_overflow,
	ow_underflow,
	ow_invalid
);
	reg _sv2v_0;
	input wire [15:0] i_a;
	input wire [15:0] i_b;
	output reg [15:0] ow_result;
	output reg ow_overflow;
	output reg ow_underflow;
	output reg ow_invalid;
	wire w_sign_a = i_a[15];
	wire [7:0] w_exp_a = i_a[14:7];
	wire [6:0] w_mant_a = i_a[6:0];
	wire w_sign_b = i_b[15];
	wire [7:0] w_exp_b = i_b[14:7];
	wire [6:0] w_mant_b = i_b[6:0];
	wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 7'h00);
	wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 7'h00);
	wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 7'h00);
	wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 7'h00);
	wire w_a_is_inf = (w_exp_a == 8'hff) & (w_mant_a == 7'h00);
	wire w_b_is_inf = (w_exp_b == 8'hff) & (w_mant_b == 7'h00);
	wire w_a_is_nan = (w_exp_a == 8'hff) & (w_mant_a != 7'h00);
	wire w_b_is_nan = (w_exp_b == 8'hff) & (w_mant_b != 7'h00);
	wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
	wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
	wire w_a_is_normal = (~w_a_eff_zero & ~w_a_is_inf) & ~w_a_is_nan;
	wire w_b_is_normal = (~w_b_eff_zero & ~w_b_is_inf) & ~w_b_is_nan;
	wire w_sign_result = w_sign_a ^ w_sign_b;
	wire [15:0] w_mant_product;
	wire w_needs_norm;
	wire [6:0] w_mant_mult_out;
	wire w_guard_bit;
	wire w_round_bit;
	wire w_sticky_bit;
	math_bf16_mantissa_mult u_mant_mult(
		.i_mant_a(w_mant_a),
		.i_mant_b(w_mant_b),
		.i_a_is_normal(w_a_is_normal),
		.i_b_is_normal(w_b_is_normal),
		.ow_product(w_mant_product),
		.ow_needs_norm(w_needs_norm),
		.ow_mant_out(w_mant_mult_out),
		.ow_guard_bit(w_guard_bit),
		.ow_round_bit(w_round_bit),
		.ow_sticky_bit(w_sticky_bit)
	);
	wire [7:0] w_exp_sum;
	wire w_exp_overflow;
	wire w_exp_underflow;
	wire w_exp_a_zero;
	wire w_exp_b_zero;
	wire w_exp_a_inf;
	wire w_exp_b_inf;
	wire w_exp_a_nan;
	wire w_exp_b_nan;
	math_bf16_exponent_adder u_exp_add(
		.i_exp_a(w_exp_a),
		.i_exp_b(w_exp_b),
		.i_norm_adjust(w_needs_norm),
		.ow_exp_out(w_exp_sum),
		.ow_overflow(w_exp_overflow),
		.ow_underflow(w_exp_underflow),
		.ow_a_is_zero(w_exp_a_zero),
		.ow_b_is_zero(w_exp_b_zero),
		.ow_a_is_inf(w_exp_a_inf),
		.ow_b_is_inf(w_exp_b_inf),
		.ow_a_is_nan(w_exp_a_nan),
		.ow_b_is_nan(w_exp_b_nan)
	);
	wire w_lsb = w_mant_mult_out[0];
	wire w_round_up = w_guard_bit & ((w_round_bit | w_sticky_bit) | w_lsb);
	wire [7:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {7'b0000000, w_round_up};
	wire w_mant_round_overflow = w_mant_rounded[7];
	wire [6:0] w_mant_final = (w_mant_round_overflow ? 7'h00 : w_mant_rounded[6:0]);
	wire [7:0] w_exp_final = (w_mant_round_overflow ? w_exp_sum + 8'd1 : w_exp_sum);
	wire w_final_overflow = w_exp_overflow | (w_exp_final == 8'hff);
	wire w_exp_sum_was_zero = (({1'b0, w_exp_a} + {1'b0, w_exp_b}) + {8'b00000000, w_needs_norm}) == 9'd127;
	wire w_uf_rescued = w_exp_sum_was_zero & w_mant_round_overflow;
	wire w_any_nan = w_a_is_nan | w_b_is_nan;
	wire w_invalid_op = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
	wire w_result_zero = w_a_eff_zero | w_b_eff_zero;
	wire w_result_inf = (w_a_is_inf | w_b_is_inf) & ~w_invalid_op;
	always @(*) begin
		if (_sv2v_0)
			;
		ow_result = {w_sign_result, w_exp_final, w_mant_final};
		ow_overflow = 1'b0;
		ow_underflow = 1'b0;
		ow_invalid = 1'b0;
		if (w_any_nan | w_invalid_op) begin
			ow_result = {w_sign_result, 15'h7fc0};
			ow_invalid = w_invalid_op;
		end
		else if (w_result_zero)
			ow_result = {w_sign_result, 15'h0000};
		else if (w_result_inf | w_final_overflow) begin
			ow_result = {w_sign_result, 15'h7f80};
			ow_overflow = w_final_overflow & ~w_result_inf;
		end
		else if (w_exp_underflow & ~w_uf_rescued) begin
			ow_result = {w_sign_result, 15'h0000};
			ow_underflow = 1'b1;
		end
	end
	initial _sv2v_0 = 0;
endmodule
module shifter_barrel (
	data,
	ctrl,
	shift_amount,
	data_out
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 8;
	input wire [WIDTH - 1:0] data;
	input wire [2:0] ctrl;
	input wire [$clog2(WIDTH):0] shift_amount;
	output reg [WIDTH - 1:0] data_out;
	wire [WIDTH - 1:0] w_array_rs [0:WIDTH - 1];
	wire [WIDTH - 1:0] w_array_ls [0:WIDTH - 1];
	wire [(WIDTH * 2) - 1:0] w_data_double;
	assign w_data_double = {data, data};
	wire [$clog2(WIDTH) - 1:0] w_shift_amount_mod;
	wire [$clog2(WIDTH) - 1:0] w_shift_amount_trunc;
	assign w_shift_amount_trunc = shift_amount[$clog2(WIDTH) - 1:0];
	function automatic [31:0] sv2v_cast_32;
		input reg [31:0] inp;
		sv2v_cast_32 = inp;
	endfunction
	function automatic [$clog2(WIDTH) - 1:0] sv2v_cast_EFDAE;
		input reg [$clog2(WIDTH) - 1:0] inp;
		sv2v_cast_EFDAE = inp;
	endfunction
	assign w_shift_amount_mod = (sv2v_cast_32(w_shift_amount_trunc) >= WIDTH ? sv2v_cast_EFDAE(sv2v_cast_32(w_shift_amount_trunc) - WIDTH) : w_shift_amount_trunc);
	genvar _gv_i_2;
	generate
		for (_gv_i_2 = 0; _gv_i_2 < WIDTH; _gv_i_2 = _gv_i_2 + 1) begin : gen_unrolled_shifts
			localparam i = _gv_i_2;
			assign w_array_rs[i] = w_data_double[(WIDTH - 1) + i:i];
			assign w_array_ls[i] = w_data_double[((WIDTH * 2) - 1) - i:WIDTH - i];
		end
	endgenerate
	function automatic signed [(($clog2(WIDTH) + 0) >= 0 ? $clog2(WIDTH) + 1 : 1 - ($clog2(WIDTH) + 0)) - 1:0] sv2v_cast_9FC3A_signed;
		input reg signed [(($clog2(WIDTH) + 0) >= 0 ? $clog2(WIDTH) + 1 : 1 - ($clog2(WIDTH) + 0)) - 1:0] inp;
		sv2v_cast_9FC3A_signed = inp;
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		case (ctrl)
			3'b000: data_out = data;
			3'b001: data_out = data >> shift_amount;
			3'b011: data_out = w_array_rs[w_shift_amount_mod];
			3'b010:
				if (shift_amount >= sv2v_cast_9FC3A_signed(WIDTH))
					data_out = {WIDTH {data[WIDTH - 1]}};
				else
					data_out = $signed(data) >>> shift_amount;
			3'b100: data_out = data << shift_amount;
			3'b110: data_out = w_array_ls[w_shift_amount_mod];
			default: data_out = data;
		endcase
	end
	initial _sv2v_0 = 0;
endmodule
module count_leading_zeros (
	data,
	clz
);
	reg _sv2v_0;
	parameter signed [31:0] WIDTH = 32;
	input wire [WIDTH - 1:0] data;
	output reg [$clog2(WIDTH):0] clz;
	function automatic [$clog2(WIDTH):0] clz_func;
		input [WIDTH - 1:0] input_data;
		reg found;
		begin
			clz_func = 0;
			found = 1'b0;
			begin : sv2v_autoblock_1
				reg signed [31:0] i;
				for (i = WIDTH - 1; i >= 0; i = i - 1)
					if (!input_data[i] && !found)
						clz_func = clz_func + 1;
					else
						found = 1'b1;
			end
		end
	endfunction
	always @(*) begin
		if (_sv2v_0)
			;
		clz = clz_func(data);
	end
	initial _sv2v_0 = 0;
endmodule
module math_bf16_adder (
	i_clk,
	i_rst_n,
	i_a,
	i_b,
	i_valid,
	ow_result,
	ow_overflow,
	ow_underflow,
	ow_invalid,
	ow_valid
);
	reg _sv2v_0;
	parameter signed [31:0] PIPE_STAGE_1 = 0;
	parameter signed [31:0] PIPE_STAGE_2 = 0;
	parameter signed [31:0] PIPE_STAGE_3 = 0;
	parameter signed [31:0] PIPE_STAGE_4 = 0;
	input wire i_clk;
	input wire i_rst_n;
	input wire [15:0] i_a;
	input wire [15:0] i_b;
	input wire i_valid;
	output reg [15:0] ow_result;
	output reg ow_overflow;
	output reg ow_underflow;
	output reg ow_invalid;
	output wire ow_valid;
	localparam signed [31:0] MANT_WIDTH = 7;
	localparam signed [31:0] EXP_WIDTH = 8;
	localparam signed [31:0] EXT_MANT_WIDTH = 11;
	localparam signed [31:0] CLZ_WIDTH = 5;
	localparam [2:0] SHIFT_NONE = 3'b000;
	localparam [2:0] SHIFT_RIGHT_LOGIC = 3'b001;
	localparam [2:0] SHIFT_LEFT_LOGIC = 3'b100;
	wire w_sign_a = i_a[15];
	wire [7:0] w_exp_a = i_a[14:7];
	wire [6:0] w_mant_a = i_a[6:0];
	wire w_sign_b = i_b[15];
	wire [7:0] w_exp_b = i_b[14:7];
	wire [6:0] w_mant_b = i_b[6:0];
	wire w_a_is_zero = (w_exp_a == 8'h00) && (w_mant_a == 7'h00);
	wire w_b_is_zero = (w_exp_b == 8'h00) && (w_mant_b == 7'h00);
	wire w_a_is_subnorm = (w_exp_a == 8'h00) && (w_mant_a != 7'h00);
	wire w_b_is_subnorm = (w_exp_b == 8'h00) && (w_mant_b != 7'h00);
	wire w_a_is_inf = (w_exp_a == 8'hff) && (w_mant_a == 7'h00);
	wire w_b_is_inf = (w_exp_b == 8'hff) && (w_mant_b == 7'h00);
	wire w_a_is_nan = (w_exp_a == 8'hff) && (w_mant_a != 7'h00);
	wire w_b_is_nan = (w_exp_b == 8'hff) && (w_mant_b != 7'h00);
	wire w_a_eff_zero = w_a_is_zero || w_a_is_subnorm;
	wire w_b_eff_zero = w_b_is_zero || w_b_is_subnorm;
	wire w_a_is_normal = (~w_a_eff_zero && ~w_a_is_inf) && ~w_a_is_nan;
	wire w_b_is_normal = (~w_b_eff_zero && ~w_b_is_inf) && ~w_b_is_nan;
	wire w_any_nan = w_a_is_nan || w_b_is_nan;
	wire w_inf_minus_inf = (w_a_is_inf && w_b_is_inf) && (w_sign_a != w_sign_b);
	wire w_any_inf = w_a_is_inf || w_b_is_inf;
	wire [8:0] w_exp_diff_raw = {1'b0, w_exp_a} - {1'b0, w_exp_b};
	wire w_exp_a_larger = ~w_exp_diff_raw[8];
	wire w_exp_equal = w_exp_a == w_exp_b;
	wire w_mant_a_larger = w_mant_a >= w_mant_b;
	wire w_a_larger = w_exp_a_larger && (~w_exp_equal || w_mant_a_larger);
	wire [7:0] w_exp_diff = (w_a_larger ? w_exp_a - w_exp_b : w_exp_b - w_exp_a);
	wire w_sign_l = (w_a_larger ? w_sign_a : w_sign_b);
	wire w_sign_s = (w_a_larger ? w_sign_b : w_sign_a);
	wire [7:0] w_exp_l = (w_a_larger ? w_exp_a : w_exp_b);
	wire [6:0] w_mant_l = (w_a_larger ? w_mant_a : w_mant_b);
	wire [6:0] w_mant_s = (w_a_larger ? w_mant_b : w_mant_a);
	wire w_l_is_normal = (w_a_larger ? w_a_is_normal : w_b_is_normal);
	wire w_s_is_normal = (w_a_larger ? w_b_is_normal : w_a_is_normal);
	wire w_s_eff_zero = (w_a_larger ? w_b_eff_zero : w_a_eff_zero);
	wire w_eff_sub = w_sign_l ^ w_sign_s;
	wire w_result_sign = w_sign_l;
	reg r1_valid;
	reg r1_any_nan;
	reg r1_inf_minus_inf;
	reg r1_any_inf;
	reg r1_a_is_inf;
	reg r1_b_is_inf;
	reg r1_a_eff_zero;
	reg r1_b_eff_zero;
	reg r1_sign_a;
	reg r1_sign_b;
	reg r1_result_sign;
	reg r1_eff_sub;
	reg [7:0] r1_exp_l;
	reg [7:0] r1_exp_diff;
	reg [6:0] r1_mant_l;
	reg [6:0] r1_mant_s;
	reg r1_l_is_normal;
	reg r1_s_is_normal;
	reg r1_s_eff_zero;
	generate
		if (PIPE_STAGE_1) begin : gen_pipe1
			always @(posedge i_clk or negedge i_rst_n)
				if (!i_rst_n) begin
					r1_valid <= 1'b0;
					r1_any_nan <= 1'b0;
					r1_inf_minus_inf <= 1'b0;
					r1_any_inf <= 1'b0;
					r1_a_is_inf <= 1'b0;
					r1_b_is_inf <= 1'b0;
					r1_a_eff_zero <= 1'b0;
					r1_b_eff_zero <= 1'b0;
					r1_sign_a <= 1'b0;
					r1_sign_b <= 1'b0;
					r1_result_sign <= 1'b0;
					r1_eff_sub <= 1'b0;
					r1_exp_l <= 8'h00;
					r1_exp_diff <= 8'h00;
					r1_mant_l <= 7'h00;
					r1_mant_s <= 7'h00;
					r1_l_is_normal <= 1'b0;
					r1_s_is_normal <= 1'b0;
					r1_s_eff_zero <= 1'b0;
				end
				else begin
					r1_valid <= i_valid;
					r1_any_nan <= w_any_nan;
					r1_inf_minus_inf <= w_inf_minus_inf;
					r1_any_inf <= w_any_inf;
					r1_a_is_inf <= w_a_is_inf;
					r1_b_is_inf <= w_b_is_inf;
					r1_a_eff_zero <= w_a_eff_zero;
					r1_b_eff_zero <= w_b_eff_zero;
					r1_sign_a <= w_sign_a;
					r1_sign_b <= w_sign_b;
					r1_result_sign <= w_result_sign;
					r1_eff_sub <= w_eff_sub;
					r1_exp_l <= w_exp_l;
					r1_exp_diff <= w_exp_diff;
					r1_mant_l <= w_mant_l;
					r1_mant_s <= w_mant_s;
					r1_l_is_normal <= w_l_is_normal;
					r1_s_is_normal <= w_s_is_normal;
					r1_s_eff_zero <= w_s_eff_zero;
				end
		end
		else begin : gen_no_pipe1
			always @(*) begin
				if (_sv2v_0)
					;
				r1_valid = i_valid;
				r1_any_nan = w_any_nan;
				r1_inf_minus_inf = w_inf_minus_inf;
				r1_any_inf = w_any_inf;
				r1_a_is_inf = w_a_is_inf;
				r1_b_is_inf = w_b_is_inf;
				r1_a_eff_zero = w_a_eff_zero;
				r1_b_eff_zero = w_b_eff_zero;
				r1_sign_a = w_sign_a;
				r1_sign_b = w_sign_b;
				r1_result_sign = w_result_sign;
				r1_eff_sub = w_eff_sub;
				r1_exp_l = w_exp_l;
				r1_exp_diff = w_exp_diff;
				r1_mant_l = w_mant_l;
				r1_mant_s = w_mant_s;
				r1_l_is_normal = w_l_is_normal;
				r1_s_is_normal = w_s_is_normal;
				r1_s_eff_zero = w_s_eff_zero;
			end
		end
	endgenerate
	wire [10:0] w_mant_l_ext = {r1_l_is_normal, r1_mant_l, 3'b000};
	wire [10:0] w_mant_s_ext = {r1_s_is_normal, r1_mant_s, 3'b000};
	wire [10:0] w_mant_s_aligned;
	wire [4:0] w_shift_amt;
	assign w_shift_amt = (r1_exp_diff > EXT_MANT_WIDTH ? EXT_MANT_WIDTH[4:0] : r1_exp_diff[4:0]);
	shifter_barrel #(.WIDTH(EXT_MANT_WIDTH)) u_align_shifter(
		.data(w_mant_s_ext),
		.ctrl(SHIFT_RIGHT_LOGIC),
		.shift_amount(w_shift_amt),
		.data_out(w_mant_s_aligned)
	);
	reg [10:0] w_sticky_mask;
	reg w_sticky_from_shift;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r1_exp_diff >= EXT_MANT_WIDTH)
			w_sticky_mask = 11'h7ff;
		else
			w_sticky_mask = (11'h001 << r1_exp_diff) - 11'h001;
		w_sticky_from_shift = |(w_mant_s_ext & w_sticky_mask);
	end
	wire [10:0] w_mant_s_final = (r1_s_eff_zero ? 11'h000 : w_mant_s_aligned);
	wire w_sticky_s = (r1_s_eff_zero ? 1'b0 : w_sticky_from_shift);
	reg r2_valid;
	reg r2_any_nan;
	reg r2_inf_minus_inf;
	reg r2_any_inf;
	reg r2_a_is_inf;
	reg r2_b_is_inf;
	reg r2_a_eff_zero;
	reg r2_b_eff_zero;
	reg r2_sign_a;
	reg r2_sign_b;
	reg r2_result_sign;
	reg r2_eff_sub;
	reg [7:0] r2_exp_l;
	reg [10:0] r2_mant_l_ext;
	reg [10:0] r2_mant_s_aligned;
	reg r2_sticky_s;
	generate
		if (PIPE_STAGE_2) begin : gen_pipe2
			always @(posedge i_clk or negedge i_rst_n)
				if (!i_rst_n) begin
					r2_valid <= 1'b0;
					r2_any_nan <= 1'b0;
					r2_inf_minus_inf <= 1'b0;
					r2_any_inf <= 1'b0;
					r2_a_is_inf <= 1'b0;
					r2_b_is_inf <= 1'b0;
					r2_a_eff_zero <= 1'b0;
					r2_b_eff_zero <= 1'b0;
					r2_sign_a <= 1'b0;
					r2_sign_b <= 1'b0;
					r2_result_sign <= 1'b0;
					r2_eff_sub <= 1'b0;
					r2_exp_l <= 8'h00;
					r2_mant_l_ext <= 11'h000;
					r2_mant_s_aligned <= 11'h000;
					r2_sticky_s <= 1'b0;
				end
				else begin
					r2_valid <= r1_valid;
					r2_any_nan <= r1_any_nan;
					r2_inf_minus_inf <= r1_inf_minus_inf;
					r2_any_inf <= r1_any_inf;
					r2_a_is_inf <= r1_a_is_inf;
					r2_b_is_inf <= r1_b_is_inf;
					r2_a_eff_zero <= r1_a_eff_zero;
					r2_b_eff_zero <= r1_b_eff_zero;
					r2_sign_a <= r1_sign_a;
					r2_sign_b <= r1_sign_b;
					r2_result_sign <= r1_result_sign;
					r2_eff_sub <= r1_eff_sub;
					r2_exp_l <= r1_exp_l;
					r2_mant_l_ext <= w_mant_l_ext;
					r2_mant_s_aligned <= w_mant_s_final;
					r2_sticky_s <= w_sticky_s;
				end
		end
		else begin : gen_no_pipe2
			always @(*) begin
				if (_sv2v_0)
					;
				r2_valid = r1_valid;
				r2_any_nan = r1_any_nan;
				r2_inf_minus_inf = r1_inf_minus_inf;
				r2_any_inf = r1_any_inf;
				r2_a_is_inf = r1_a_is_inf;
				r2_b_is_inf = r1_b_is_inf;
				r2_a_eff_zero = r1_a_eff_zero;
				r2_b_eff_zero = r1_b_eff_zero;
				r2_sign_a = r1_sign_a;
				r2_sign_b = r1_sign_b;
				r2_result_sign = r1_result_sign;
				r2_eff_sub = r1_eff_sub;
				r2_exp_l = r1_exp_l;
				r2_mant_l_ext = w_mant_l_ext;
				r2_mant_s_aligned = w_mant_s_final;
				r2_sticky_s = w_sticky_s;
			end
		end
	endgenerate
	reg [11:0] w_mant_sum;
	reg w_mant_sum_sign;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r2_eff_sub) begin
			w_mant_sum = {1'b0, r2_mant_l_ext} - {1'b0, r2_mant_s_aligned};
			w_mant_sum_sign = 1'b0;
		end
		else begin
			w_mant_sum = {1'b0, r2_mant_l_ext} + {1'b0, r2_mant_s_aligned};
			w_mant_sum_sign = 1'b0;
		end
	end
	wire w_add_overflow = w_mant_sum[11];
	wire w_sum_is_zero = (w_mant_sum == 12'h000) && ~r2_sticky_s;
	reg r3_valid;
	reg r3_any_nan;
	reg r3_inf_minus_inf;
	reg r3_any_inf;
	reg r3_a_is_inf;
	reg r3_b_is_inf;
	reg r3_a_eff_zero;
	reg r3_b_eff_zero;
	reg r3_sign_a;
	reg r3_sign_b;
	reg r3_result_sign;
	reg r3_eff_sub;
	reg [7:0] r3_exp_l;
	reg [11:0] r3_mant_sum;
	reg r3_add_overflow;
	reg r3_sum_is_zero;
	reg r3_sticky_s;
	generate
		if (PIPE_STAGE_3) begin : gen_pipe3
			always @(posedge i_clk or negedge i_rst_n)
				if (!i_rst_n) begin
					r3_valid <= 1'b0;
					r3_any_nan <= 1'b0;
					r3_inf_minus_inf <= 1'b0;
					r3_any_inf <= 1'b0;
					r3_a_is_inf <= 1'b0;
					r3_b_is_inf <= 1'b0;
					r3_a_eff_zero <= 1'b0;
					r3_b_eff_zero <= 1'b0;
					r3_sign_a <= 1'b0;
					r3_sign_b <= 1'b0;
					r3_result_sign <= 1'b0;
					r3_eff_sub <= 1'b0;
					r3_exp_l <= 8'h00;
					r3_mant_sum <= 12'h000;
					r3_add_overflow <= 1'b0;
					r3_sum_is_zero <= 1'b0;
					r3_sticky_s <= 1'b0;
				end
				else begin
					r3_valid <= r2_valid;
					r3_any_nan <= r2_any_nan;
					r3_inf_minus_inf <= r2_inf_minus_inf;
					r3_any_inf <= r2_any_inf;
					r3_a_is_inf <= r2_a_is_inf;
					r3_b_is_inf <= r2_b_is_inf;
					r3_a_eff_zero <= r2_a_eff_zero;
					r3_b_eff_zero <= r2_b_eff_zero;
					r3_sign_a <= r2_sign_a;
					r3_sign_b <= r2_sign_b;
					r3_result_sign <= r2_result_sign;
					r3_eff_sub <= r2_eff_sub;
					r3_exp_l <= r2_exp_l;
					r3_mant_sum <= w_mant_sum;
					r3_add_overflow <= w_add_overflow;
					r3_sum_is_zero <= w_sum_is_zero;
					r3_sticky_s <= r2_sticky_s;
				end
		end
		else begin : gen_no_pipe3
			always @(*) begin
				if (_sv2v_0)
					;
				r3_valid = r2_valid;
				r3_any_nan = r2_any_nan;
				r3_inf_minus_inf = r2_inf_minus_inf;
				r3_any_inf = r2_any_inf;
				r3_a_is_inf = r2_a_is_inf;
				r3_b_is_inf = r2_b_is_inf;
				r3_a_eff_zero = r2_a_eff_zero;
				r3_b_eff_zero = r2_b_eff_zero;
				r3_sign_a = r2_sign_a;
				r3_sign_b = r2_sign_b;
				r3_result_sign = r2_result_sign;
				r3_eff_sub = r2_eff_sub;
				r3_exp_l = r2_exp_l;
				r3_mant_sum = w_mant_sum;
				r3_add_overflow = w_add_overflow;
				r3_sum_is_zero = w_sum_is_zero;
				r3_sticky_s = r2_sticky_s;
			end
		end
	endgenerate
	wire [4:0] w_lzc;
	count_leading_zeros #(.WIDTH(12)) u_clz(
		.data(r3_mant_sum),
		.clz(w_lzc)
	);
	reg [3:0] w_norm_shift_amt;
	reg w_norm_shift_right;
	reg [10:0] w_mant_prenorm;
	reg w_norm_sticky;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r3_add_overflow) begin
			w_norm_shift_right = 1'b0;
			w_norm_shift_amt = 4'd0;
			w_mant_prenorm = r3_mant_sum[11:1];
			w_norm_sticky = r3_mant_sum[0] | r3_sticky_s;
		end
		else if (w_lzc == 0) begin
			w_norm_shift_right = 1'b0;
			w_norm_shift_amt = 4'd0;
			w_mant_prenorm = r3_mant_sum[10:0];
			w_norm_sticky = r3_sticky_s;
		end
		else begin
			w_norm_shift_right = 1'b0;
			w_norm_shift_amt = (w_lzc > 1 ? w_lzc[3:0] - 4'd1 : 4'd0);
			w_mant_prenorm = r3_mant_sum[10:0];
			w_norm_sticky = r3_sticky_s;
		end
	end
	wire [10:0] w_mant_normalized;
	wire [4:0] w_norm_shift_amt_ext;
	assign w_norm_shift_amt_ext = {1'b0, w_norm_shift_amt[3:0]};
	shifter_barrel #(.WIDTH(EXT_MANT_WIDTH)) u_norm_shifter(
		.data(w_mant_prenorm),
		.ctrl((w_norm_shift_right ? SHIFT_RIGHT_LOGIC : SHIFT_LEFT_LOGIC)),
		.shift_amount(w_norm_shift_amt_ext),
		.data_out(w_mant_normalized)
	);
	reg [8:0] w_exp_adjusted;
	always @(*) begin
		if (_sv2v_0)
			;
		if (r3_add_overflow)
			w_exp_adjusted = {1'b0, r3_exp_l} + 9'd1;
		else if (w_norm_shift_amt > 0)
			w_exp_adjusted = {1'b0, r3_exp_l} - {5'b00000, w_norm_shift_amt};
		else
			w_exp_adjusted = {1'b0, r3_exp_l};
	end
	wire w_exp_overflow = !w_exp_adjusted[8] && (w_exp_adjusted[7:0] >= 8'hff);
	wire w_exp_underflow = w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);
	reg r4_valid;
	reg r4_any_nan;
	reg r4_inf_minus_inf;
	reg r4_any_inf;
	reg r4_a_is_inf;
	reg r4_b_is_inf;
	reg r4_a_eff_zero;
	reg r4_b_eff_zero;
	reg r4_sign_a;
	reg r4_sign_b;
	reg r4_result_sign;
	reg [7:0] r4_exp_adjusted;
	reg [10:0] r4_mant_normalized;
	reg r4_exp_overflow;
	reg r4_exp_underflow;
	reg r4_sum_is_zero;
	reg r4_norm_sticky;
	generate
		if (PIPE_STAGE_4) begin : gen_pipe4
			always @(posedge i_clk or negedge i_rst_n)
				if (!i_rst_n) begin
					r4_valid <= 1'b0;
					r4_any_nan <= 1'b0;
					r4_inf_minus_inf <= 1'b0;
					r4_any_inf <= 1'b0;
					r4_a_is_inf <= 1'b0;
					r4_b_is_inf <= 1'b0;
					r4_a_eff_zero <= 1'b0;
					r4_b_eff_zero <= 1'b0;
					r4_sign_a <= 1'b0;
					r4_sign_b <= 1'b0;
					r4_result_sign <= 1'b0;
					r4_exp_adjusted <= 8'h00;
					r4_mant_normalized <= 11'h000;
					r4_exp_overflow <= 1'b0;
					r4_exp_underflow <= 1'b0;
					r4_sum_is_zero <= 1'b0;
					r4_norm_sticky <= 1'b0;
				end
				else begin
					r4_valid <= r3_valid;
					r4_any_nan <= r3_any_nan;
					r4_inf_minus_inf <= r3_inf_minus_inf;
					r4_any_inf <= r3_any_inf;
					r4_a_is_inf <= r3_a_is_inf;
					r4_b_is_inf <= r3_b_is_inf;
					r4_a_eff_zero <= r3_a_eff_zero;
					r4_b_eff_zero <= r3_b_eff_zero;
					r4_sign_a <= r3_sign_a;
					r4_sign_b <= r3_sign_b;
					r4_result_sign <= r3_result_sign;
					r4_exp_adjusted <= w_exp_adjusted[7:0];
					r4_mant_normalized <= w_mant_normalized;
					r4_exp_overflow <= w_exp_overflow;
					r4_exp_underflow <= w_exp_underflow;
					r4_sum_is_zero <= r3_sum_is_zero;
					r4_norm_sticky <= w_norm_sticky;
				end
		end
		else begin : gen_no_pipe4
			always @(*) begin
				if (_sv2v_0)
					;
				r4_valid = r3_valid;
				r4_any_nan = r3_any_nan;
				r4_inf_minus_inf = r3_inf_minus_inf;
				r4_any_inf = r3_any_inf;
				r4_a_is_inf = r3_a_is_inf;
				r4_b_is_inf = r3_b_is_inf;
				r4_a_eff_zero = r3_a_eff_zero;
				r4_b_eff_zero = r3_b_eff_zero;
				r4_sign_a = r3_sign_a;
				r4_sign_b = r3_sign_b;
				r4_result_sign = r3_result_sign;
				r4_exp_adjusted = w_exp_adjusted[7:0];
				r4_mant_normalized = w_mant_normalized;
				r4_exp_overflow = w_exp_overflow;
				r4_exp_underflow = w_exp_underflow;
				r4_sum_is_zero = r3_sum_is_zero;
				r4_norm_sticky = w_norm_sticky;
			end
		end
	endgenerate
	wire [6:0] w_mant_final_raw = r4_mant_normalized[9:3];
	wire w_guard_bit = r4_mant_normalized[2];
	wire w_round_bit = r4_mant_normalized[1];
	wire w_sticky_bit = r4_mant_normalized[0] | r4_norm_sticky;
	wire w_round_up = w_guard_bit && ((w_round_bit || w_sticky_bit) || w_mant_final_raw[0]);
	wire [7:0] w_mant_rounded = {1'b0, w_mant_final_raw} + {7'b0000000, w_round_up};
	wire w_round_overflow = w_mant_rounded[7];
	wire [6:0] w_mant_out = (w_round_overflow ? 7'h00 : w_mant_rounded[6:0]);
	wire [8:0] w_exp_out_raw = {1'b0, r4_exp_adjusted} + {8'b00000000, w_round_overflow};
	wire [7:0] w_exp_out = w_exp_out_raw[7:0];
	wire w_final_overflow = r4_exp_overflow || (w_exp_out_raw >= 9'h0ff);
	wire w_final_sign = (r4_sum_is_zero ? 1'b0 : r4_result_sign);
	always @(*) begin
		if (_sv2v_0)
			;
		ow_result = {w_final_sign, w_exp_out, w_mant_out};
		ow_overflow = 1'b0;
		ow_underflow = 1'b0;
		ow_invalid = 1'b0;
		if (r4_any_nan || r4_inf_minus_inf) begin
			ow_result = 16'h7fc0;
			ow_invalid = r4_inf_minus_inf;
		end
		else if (r4_any_inf)
			ow_result = {(r4_a_is_inf ? r4_sign_a : r4_sign_b), 15'h7f80};
		else if (r4_a_eff_zero && r4_b_eff_zero)
			ow_result = {r4_sign_a & r4_sign_b, 15'h0000};
		else if (r4_a_eff_zero)
			ow_result = {r4_sign_b, r4_exp_adjusted, w_mant_out};
		else if (r4_b_eff_zero)
			ow_result = {r4_sign_a, r4_exp_adjusted, w_mant_out};
		else if (r4_sum_is_zero)
			ow_result = 16'h0000;
		else if (w_final_overflow) begin
			ow_result = {w_final_sign, 15'h7f80};
			ow_overflow = 1'b1;
		end
		else if (r4_exp_underflow) begin
			ow_result = {w_final_sign, 15'h0000};
			ow_underflow = 1'b1;
		end
	end
	assign ow_valid = r4_valid;
	initial _sv2v_0 = 0;
endmodule
module math_bf16_fast_reciprocal (
	i_bf16,
	ow_reciprocal,
	ow_is_zero,
	ow_is_inf,
	ow_is_nan,
	ow_underflow,
	ow_mant_approx,
	ow_mant_interp
);
	reg _sv2v_0;
	parameter signed [31:0] LUT_DEPTH = 32;
	parameter signed [31:0] LUT_ADDR_BITS = $clog2(LUT_DEPTH);
	input wire [15:0] i_bf16;
	output reg [15:0] ow_reciprocal;
	output wire ow_is_zero;
	output wire ow_is_inf;
	output wire ow_is_nan;
	output wire ow_underflow;
	output wire [6:0] ow_mant_approx;
	output wire [6:0] ow_mant_interp;
	wire w_sign;
	wire [7:0] w_exp;
	wire [6:0] w_mant;
	assign w_sign = i_bf16[15];
	assign w_exp = i_bf16[14:7];
	assign w_mant = i_bf16[6:0];
	wire w_is_zero_or_subnormal;
	wire w_is_inf;
	wire w_is_nan;
	assign w_is_zero_or_subnormal = w_exp == 8'd0;
	assign w_is_inf = (w_exp == 8'd255) && (w_mant == 7'd0);
	assign w_is_nan = (w_exp == 8'd255) && (w_mant != 7'd0);
	reg [6:0] w_recip_mant_lut;
	reg [6:0] w_recip_mant_nxt;
	wire [LUT_ADDR_BITS - 1:0] w_lut_addr;
	wire [LUT_ADDR_BITS - 1:0] w_lut_addr_nxt;
	assign w_lut_addr = w_mant[6-:LUT_ADDR_BITS];
	assign w_lut_addr_nxt = (w_lut_addr == {LUT_ADDR_BITS {1'b1}} ? w_lut_addr : w_lut_addr + 1'b1);
	generate
		if (LUT_DEPTH == 32) begin : gen_lut_32
			function automatic [6:0] lut_32;
				input reg [4:0] addr;
				reg [6:0] lut;
				begin
					case (addr)
						5'd0: lut = 7'd127;
						5'd1: lut = 7'd120;
						5'd2: lut = 7'd113;
						5'd3: lut = 7'd107;
						5'd4: lut = 7'd100;
						5'd5: lut = 7'd94;
						5'd6: lut = 7'd88;
						5'd7: lut = 7'd83;
						5'd8: lut = 7'd78;
						5'd9: lut = 7'd73;
						5'd10: lut = 7'd68;
						5'd11: lut = 7'd64;
						5'd12: lut = 7'd59;
						5'd13: lut = 7'd55;
						5'd14: lut = 7'd51;
						5'd15: lut = 7'd47;
						5'd16: lut = 7'd43;
						5'd17: lut = 7'd40;
						5'd18: lut = 7'd36;
						5'd19: lut = 7'd33;
						5'd20: lut = 7'd30;
						5'd21: lut = 7'd27;
						5'd22: lut = 7'd24;
						5'd23: lut = 7'd21;
						5'd24: lut = 7'd18;
						5'd25: lut = 7'd16;
						5'd26: lut = 7'd13;
						5'd27: lut = 7'd11;
						5'd28: lut = 7'd8;
						5'd29: lut = 7'd6;
						5'd30: lut = 7'd4;
						5'd31: lut = 7'd2;
					endcase
					lut_32 = lut;
				end
			endfunction
			always @(*) begin
				if (_sv2v_0)
					;
				w_recip_mant_lut = lut_32(w_lut_addr);
				w_recip_mant_nxt = lut_32(w_lut_addr_nxt);
			end
		end
		else if (LUT_DEPTH == 64) begin : gen_lut_64
			function automatic [6:0] lut_64;
				input reg [5:0] addr;
				reg [6:0] lut;
				begin
					case (addr)
						6'd0: lut = 7'd127;
						6'd1: lut = 7'd123;
						6'd2: lut = 7'd120;
						6'd3: lut = 7'd117;
						6'd4: lut = 7'd113;
						6'd5: lut = 7'd110;
						6'd6: lut = 7'd107;
						6'd7: lut = 7'd104;
						6'd8: lut = 7'd100;
						6'd9: lut = 7'd97;
						6'd10: lut = 7'd94;
						6'd11: lut = 7'd91;
						6'd12: lut = 7'd88;
						6'd13: lut = 7'd86;
						6'd14: lut = 7'd83;
						6'd15: lut = 7'd80;
						6'd16: lut = 7'd78;
						6'd17: lut = 7'd75;
						6'd18: lut = 7'd73;
						6'd19: lut = 7'd70;
						6'd20: lut = 7'd68;
						6'd21: lut = 7'd66;
						6'd22: lut = 7'd64;
						6'd23: lut = 7'd61;
						6'd24: lut = 7'd59;
						6'd25: lut = 7'd57;
						6'd26: lut = 7'd55;
						6'd27: lut = 7'd53;
						6'd28: lut = 7'd51;
						6'd29: lut = 7'd49;
						6'd30: lut = 7'd47;
						6'd31: lut = 7'd46;
						6'd32: lut = 7'd44;
						6'd33: lut = 7'd42;
						6'd34: lut = 7'd40;
						6'd35: lut = 7'd39;
						6'd36: lut = 7'd37;
						6'd37: lut = 7'd35;
						6'd38: lut = 7'd34;
						6'd39: lut = 7'd32;
						6'd40: lut = 7'd31;
						6'd41: lut = 7'd29;
						6'd42: lut = 7'd28;
						6'd43: lut = 7'd26;
						6'd44: lut = 7'd25;
						6'd45: lut = 7'd23;
						6'd46: lut = 7'd22;
						6'd47: lut = 7'd21;
						6'd48: lut = 7'd19;
						6'd49: lut = 7'd18;
						6'd50: lut = 7'd17;
						6'd51: lut = 7'd15;
						6'd52: lut = 7'd14;
						6'd53: lut = 7'd13;
						6'd54: lut = 7'd12;
						6'd55: lut = 7'd10;
						6'd56: lut = 7'd9;
						6'd57: lut = 7'd8;
						6'd58: lut = 7'd7;
						6'd59: lut = 7'd6;
						6'd60: lut = 7'd5;
						6'd61: lut = 7'd4;
						6'd62: lut = 7'd3;
						6'd63: lut = 7'd2;
					endcase
					lut_64 = lut;
				end
			endfunction
			always @(*) begin
				if (_sv2v_0)
					;
				w_recip_mant_lut = lut_64(w_lut_addr);
				w_recip_mant_nxt = lut_64(w_lut_addr_nxt);
			end
		end
		else begin : gen_lut_128
			function automatic [6:0] lut_128;
				input reg [6:0] addr;
				reg [6:0] lut;
				begin
					case (addr)
						7'd0: lut = 7'd127;
						7'd1: lut = 7'd126;
						7'd2: lut = 7'd124;
						7'd3: lut = 7'd122;
						7'd4: lut = 7'd120;
						7'd5: lut = 7'd118;
						7'd6: lut = 7'd117;
						7'd7: lut = 7'd115;
						7'd8: lut = 7'd113;
						7'd9: lut = 7'd111;
						7'd10: lut = 7'd109;
						7'd11: lut = 7'd108;
						7'd12: lut = 7'd106;
						7'd13: lut = 7'd104;
						7'd14: lut = 7'd103;
						7'd15: lut = 7'd101;
						7'd16: lut = 7'd100;
						7'd17: lut = 7'd98;
						7'd18: lut = 7'd96;
						7'd19: lut = 7'd95;
						7'd20: lut = 7'd93;
						7'd21: lut = 7'd92;
						7'd22: lut = 7'd90;
						7'd23: lut = 7'd89;
						7'd24: lut = 7'd88;
						7'd25: lut = 7'd86;
						7'd26: lut = 7'd85;
						7'd27: lut = 7'd83;
						7'd28: lut = 7'd82;
						7'd29: lut = 7'd81;
						7'd30: lut = 7'd79;
						7'd31: lut = 7'd78;
						7'd32: lut = 7'd77;
						7'd33: lut = 7'd76;
						7'd34: lut = 7'd74;
						7'd35: lut = 7'd73;
						7'd36: lut = 7'd72;
						7'd37: lut = 7'd71;
						7'd38: lut = 7'd69;
						7'd39: lut = 7'd68;
						7'd40: lut = 7'd67;
						7'd41: lut = 7'd66;
						7'd42: lut = 7'd65;
						7'd43: lut = 7'd64;
						7'd44: lut = 7'd63;
						7'd45: lut = 7'd61;
						7'd46: lut = 7'd60;
						7'd47: lut = 7'd59;
						7'd48: lut = 7'd58;
						7'd49: lut = 7'd57;
						7'd50: lut = 7'd56;
						7'd51: lut = 7'd55;
						7'd52: lut = 7'd54;
						7'd53: lut = 7'd53;
						7'd54: lut = 7'd52;
						7'd55: lut = 7'd51;
						7'd56: lut = 7'd50;
						7'd57: lut = 7'd49;
						7'd58: lut = 7'd48;
						7'd59: lut = 7'd47;
						7'd60: lut = 7'd46;
						7'd61: lut = 7'd45;
						7'd62: lut = 7'd44;
						7'd63: lut = 7'd44;
						7'd64: lut = 7'd43;
						7'd65: lut = 7'd42;
						7'd66: lut = 7'd41;
						7'd67: lut = 7'd40;
						7'd68: lut = 7'd39;
						7'd69: lut = 7'd38;
						7'd70: lut = 7'd37;
						7'd71: lut = 7'd37;
						7'd72: lut = 7'd36;
						7'd73: lut = 7'd35;
						7'd74: lut = 7'd34;
						7'd75: lut = 7'd33;
						7'd76: lut = 7'd33;
						7'd77: lut = 7'd32;
						7'd78: lut = 7'd31;
						7'd79: lut = 7'd30;
						7'd80: lut = 7'd30;
						7'd81: lut = 7'd29;
						7'd82: lut = 7'd28;
						7'd83: lut = 7'd27;
						7'd84: lut = 7'd27;
						7'd85: lut = 7'd26;
						7'd86: lut = 7'd25;
						7'd87: lut = 7'd24;
						7'd88: lut = 7'd24;
						7'd89: lut = 7'd23;
						7'd90: lut = 7'd22;
						7'd91: lut = 7'd22;
						7'd92: lut = 7'd21;
						7'd93: lut = 7'd20;
						7'd94: lut = 7'd20;
						7'd95: lut = 7'd19;
						7'd96: lut = 7'd18;
						7'd97: lut = 7'd18;
						7'd98: lut = 7'd17;
						7'd99: lut = 7'd16;
						7'd100: lut = 7'd16;
						7'd101: lut = 7'd15;
						7'd102: lut = 7'd14;
						7'd103: lut = 7'd14;
						7'd104: lut = 7'd13;
						7'd105: lut = 7'd13;
						7'd106: lut = 7'd12;
						7'd107: lut = 7'd11;
						7'd108: lut = 7'd11;
						7'd109: lut = 7'd10;
						7'd110: lut = 7'd10;
						7'd111: lut = 7'd9;
						7'd112: lut = 7'd9;
						7'd113: lut = 7'd8;
						7'd114: lut = 7'd7;
						7'd115: lut = 7'd7;
						7'd116: lut = 7'd6;
						7'd117: lut = 7'd6;
						7'd118: lut = 7'd5;
						7'd119: lut = 7'd5;
						7'd120: lut = 7'd4;
						7'd121: lut = 7'd4;
						7'd122: lut = 7'd3;
						7'd123: lut = 7'd3;
						7'd124: lut = 7'd2;
						7'd125: lut = 7'd2;
						7'd126: lut = 7'd1;
						7'd127: lut = 7'd1;
					endcase
					lut_128 = lut;
				end
			endfunction
			always @(*) begin
				if (_sv2v_0)
					;
				w_recip_mant_lut = lut_128(w_lut_addr);
				w_recip_mant_nxt = lut_128(w_lut_addr_nxt);
			end
		end
	endgenerate
	wire [7:0] w_recip_exp;
	wire w_mant_nonzero;
	wire w_recip_underflow;
	assign w_mant_nonzero = w_mant != 7'd0;
	assign w_recip_underflow = (w_mant_nonzero ? w_exp > 8'd253 : w_exp > 8'd254);
	assign w_recip_exp = (w_recip_underflow ? 8'd0 : (w_mant_nonzero ? 8'd253 - w_exp : 8'd254 - w_exp));
	wire [6:0] w_recip_mant;
	assign w_recip_mant = (w_mant_nonzero ? w_recip_mant_lut : 7'd0);
	localparam [15:0] BF16_POS_INF = 16'h7f80;
	localparam [15:0] BF16_NEG_INF = 16'hff80;
	localparam [15:0] BF16_POS_ZERO = 16'h0000;
	localparam [15:0] BF16_NEG_ZERO = 16'h8000;
	localparam [15:0] BF16_QNAN = 16'h7fc0;
	always @(*) begin
		if (_sv2v_0)
			;
		if (w_is_nan)
			ow_reciprocal = BF16_QNAN;
		else if (w_is_inf)
			ow_reciprocal = (w_sign ? BF16_NEG_ZERO : BF16_POS_ZERO);
		else if (w_is_zero_or_subnormal)
			ow_reciprocal = (w_sign ? BF16_NEG_INF : BF16_POS_INF);
		else if (w_recip_underflow)
			ow_reciprocal = (w_sign ? BF16_NEG_ZERO : BF16_POS_ZERO);
		else
			ow_reciprocal = {w_sign, w_recip_exp, w_recip_mant};
	end
	assign ow_is_zero = w_is_zero_or_subnormal;
	assign ow_is_inf = w_is_inf;
	assign ow_is_nan = w_is_nan;
	assign ow_underflow = w_recip_underflow;
	function automatic signed [13:0] sv2v_cast_14_signed;
		input reg signed [13:0] inp;
		sv2v_cast_14_signed = inp;
	endfunction
	function automatic [6:0] sv2v_cast_7;
		input reg [6:0] inp;
		sv2v_cast_7 = inp;
	endfunction
	generate
		if (LUT_ADDR_BITS >= 7) begin : gen_no_interp
			assign ow_mant_interp = w_recip_mant;
		end
		else begin : gen_interp
			localparam signed [31:0] FRAC_BITS = 7 - LUT_ADDR_BITS;
			localparam signed [31:0] FRAC_HALF = 1 << (FRAC_BITS - 1);
			wire [FRAC_BITS - 1:0] w_frac;
			assign w_frac = w_mant[FRAC_BITS - 1:0];
			wire [6:0] w_step;
			assign w_step = w_recip_mant_lut - w_recip_mant_nxt;
			wire [13:0] w_scaled;
			assign w_scaled = ({{7 - FRAC_BITS {1'b0}}, w_frac} * w_step) + sv2v_cast_14_signed(FRAC_HALF);
			assign ow_mant_interp = w_recip_mant - sv2v_cast_7(w_scaled >> FRAC_BITS);
		end
	endgenerate
	assign ow_mant_approx = w_recip_mant;
	initial _sv2v_0 = 0;
endmodule
module math_bf16_newton_raphson_recip (
	i_bf16,
	ow_reciprocal,
	ow_is_zero,
	ow_is_inf,
	ow_is_nan
);
	parameter signed [31:0] ITERATIONS = 1;
	parameter signed [31:0] LUT_DEPTH = 32;
	input wire [15:0] i_bf16;
	output wire [15:0] ow_reciprocal;
	output wire ow_is_zero;
	output wire ow_is_inf;
	output wire ow_is_nan;
	localparam [15:0] BF16_TWO = 16'h4000;
	localparam [15:0] BF16_ZERO = 16'h0000;
	localparam [15:0] BF16_POS_INF = 16'h7f80;
	localparam [15:0] BF16_NEG_INF = 16'hff80;
	localparam [15:0] BF16_NAN = 16'h7fc0;
	wire [15:0] w_x0;
	wire w_init_zero;
	wire w_init_inf;
	wire w_init_nan;
	wire w_init_underflow;
	wire [6:0] w_init_mant_approx;
	math_bf16_fast_reciprocal #(.LUT_DEPTH(LUT_DEPTH)) u_initial_estimate(
		.i_bf16(i_bf16),
		.ow_reciprocal(w_x0),
		.ow_is_zero(w_init_zero),
		.ow_is_inf(w_init_inf),
		.ow_is_nan(w_init_nan),
		.ow_underflow(w_init_underflow),
		.ow_mant_approx(w_init_mant_approx),
		.ow_mant_interp()
	);
	wire [15:0] w_a_times_x0;
	wire [15:0] w_two_minus_ax0;
	wire [15:0] w_x1;
	wire w_mult_ax0_ovf;
	wire w_mult_ax0_udf;
	wire w_mult_ax0_inv;
	wire w_mult_x1_ovf;
	wire w_mult_x1_udf;
	wire w_mult_x1_inv;
	math_bf16_multiplier u_mult_ax0(
		.i_a(i_bf16),
		.i_b(w_x0),
		.ow_result(w_a_times_x0),
		.ow_overflow(w_mult_ax0_ovf),
		.ow_underflow(w_mult_ax0_udf),
		.ow_invalid(w_mult_ax0_inv)
	);
	wire [15:0] w_neg_ax0;
	assign w_neg_ax0 = {~w_a_times_x0[15], w_a_times_x0[14:0]};
	wire w_add1_ovf;
	wire w_add1_udf;
	wire w_add1_inv;
	wire w_add1_valid;
	math_bf16_adder #(
		.PIPE_STAGE_1(0),
		.PIPE_STAGE_2(0),
		.PIPE_STAGE_3(0),
		.PIPE_STAGE_4(0)
	) u_sub_iter1(
		.i_clk(1'b0),
		.i_rst_n(1'b1),
		.i_a(BF16_TWO),
		.i_b(w_neg_ax0),
		.i_valid(1'b1),
		.ow_result(w_two_minus_ax0),
		.ow_overflow(w_add1_ovf),
		.ow_underflow(w_add1_udf),
		.ow_invalid(w_add1_inv),
		.ow_valid(w_add1_valid)
	);
	math_bf16_multiplier u_mult_x1(
		.i_a(w_x0),
		.i_b(w_two_minus_ax0),
		.ow_result(w_x1),
		.ow_overflow(w_mult_x1_ovf),
		.ow_underflow(w_mult_x1_udf),
		.ow_invalid(w_mult_x1_inv)
	);
	generate
		if (ITERATIONS >= 2) begin : gen_iter2
			wire [15:0] w_a_times_x1;
			wire [15:0] w_two_minus_ax1;
			wire [15:0] w_x2;
			wire w_mult_ax1_ovf;
			wire w_mult_ax1_udf;
			wire w_mult_ax1_inv;
			wire w_mult_x2_ovf;
			wire w_mult_x2_udf;
			wire w_mult_x2_inv;
			wire w_add2_ovf;
			wire w_add2_udf;
			wire w_add2_inv;
			wire w_add2_valid;
			math_bf16_multiplier u_mult_ax1(
				.i_a(i_bf16),
				.i_b(w_x1),
				.ow_result(w_a_times_x1),
				.ow_overflow(w_mult_ax1_ovf),
				.ow_underflow(w_mult_ax1_udf),
				.ow_invalid(w_mult_ax1_inv)
			);
			wire [15:0] w_neg_ax1;
			assign w_neg_ax1 = {~w_a_times_x1[15], w_a_times_x1[14:0]};
			math_bf16_adder #(
				.PIPE_STAGE_1(0),
				.PIPE_STAGE_2(0),
				.PIPE_STAGE_3(0),
				.PIPE_STAGE_4(0)
			) u_sub_iter2(
				.i_clk(1'b0),
				.i_rst_n(1'b1),
				.i_a(BF16_TWO),
				.i_b(w_neg_ax1),
				.i_valid(1'b1),
				.ow_result(w_two_minus_ax1),
				.ow_overflow(w_add2_ovf),
				.ow_underflow(w_add2_udf),
				.ow_invalid(w_add2_inv),
				.ow_valid(w_add2_valid)
			);
			math_bf16_multiplier u_mult_x2(
				.i_a(w_x1),
				.i_b(w_two_minus_ax1),
				.ow_result(w_x2),
				.ow_overflow(w_mult_x2_ovf),
				.ow_underflow(w_mult_x2_udf),
				.ow_invalid(w_mult_x2_inv)
			);
			wire [15:0] w_result_iter2;
			assign w_result_iter2 = {i_bf16[15], w_x2[14:0]};
			assign ow_reciprocal = (w_init_nan ? BF16_NAN : (w_init_zero ? (i_bf16[15] ? BF16_NEG_INF : BF16_POS_INF) : (w_init_inf ? {i_bf16[15], 15'b000000000000000} : w_result_iter2)));
		end
		else begin : gen_iter1
			wire [15:0] w_result_iter1;
			assign w_result_iter1 = {i_bf16[15], w_x1[14:0]};
			assign ow_reciprocal = (w_init_nan ? BF16_NAN : (w_init_zero ? (i_bf16[15] ? BF16_NEG_INF : BF16_POS_INF) : (w_init_inf ? {i_bf16[15], 15'b000000000000000} : w_result_iter1)));
		end
	endgenerate
	assign ow_is_zero = w_init_zero;
	assign ow_is_inf = w_init_inf;
	assign ow_is_nan = w_init_nan;
endmodule
