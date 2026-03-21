// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_multiplier_dadda_4to2_008
// Purpose: Dadda 8x8 multiplier with 4:2 compressors for BF16 mantissa
//
// Documentation: BF16_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-11-25
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/bf16/dadda_4to2_multiplier.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_multiplier_dadda_4to2_008 #(parameter int  N = 8)(
    input  logic [N-1:0]   i_multiplier,
    input  logic [N-1:0]   i_multiplicand,
    output logic [2*N-1:0] ow_product
);

// Partial Products (AND gate array)
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

// Dadda Reduction Stage 1: height 8 -> 6

wire w_c4to2_sum_06_000, w_c4to2_carry_06_000, w_c4to2_cout_06_000;
math_compressor_4to2 u_c4to2_06_000 (
    .i_x1(w_pp_0_6), .i_x2(w_pp_1_5),
    .i_x3(w_pp_2_4), .i_x4(w_pp_3_3),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_000), .ow_carry(w_c4to2_carry_06_000), .ow_cout(w_c4to2_cout_06_000)
);
wire w_c4to2_sum_07_001, w_c4to2_carry_07_001, w_c4to2_cout_07_001;
math_compressor_4to2 u_c4to2_07_001 (
    .i_x1(w_pp_0_7), .i_x2(w_pp_1_6),
    .i_x3(w_pp_2_5), .i_x4(w_pp_3_4),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_001), .ow_carry(w_c4to2_carry_07_001), .ow_cout(w_c4to2_cout_07_001)
);
wire w_c4to2_sum_07_002, w_c4to2_carry_07_002, w_c4to2_cout_07_002;
math_compressor_4to2 u_c4to2_07_002 (
    .i_x1(w_pp_4_3), .i_x2(w_pp_5_2),
    .i_x3(w_pp_6_1), .i_x4(w_pp_7_0),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_002), .ow_carry(w_c4to2_carry_07_002), .ow_cout(w_c4to2_cout_07_002)
);
wire w_c4to2_sum_08_003, w_c4to2_carry_08_003, w_c4to2_cout_08_003;
math_compressor_4to2 u_c4to2_08_003 (
    .i_x1(w_pp_1_7), .i_x2(w_pp_2_6),
    .i_x3(w_pp_3_5), .i_x4(w_pp_4_4),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_003), .ow_carry(w_c4to2_carry_08_003), .ow_cout(w_c4to2_cout_08_003)
);
wire w_c4to2_sum_08_004, w_c4to2_carry_08_004, w_c4to2_cout_08_004;
math_compressor_4to2 u_c4to2_08_004 (
    .i_x1(w_pp_5_3), .i_x2(w_pp_6_2),
    .i_x3(w_pp_7_1), .i_x4(w_c4to2_carry_07_001),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_004), .ow_carry(w_c4to2_carry_08_004), .ow_cout(w_c4to2_cout_08_004)
);
wire w_c4to2_sum_09_005, w_c4to2_carry_09_005, w_c4to2_cout_09_005;
math_compressor_4to2 u_c4to2_09_005 (
    .i_x1(w_pp_2_7), .i_x2(w_pp_3_6),
    .i_x3(w_pp_4_5), .i_x4(w_pp_5_4),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_005), .ow_carry(w_c4to2_carry_09_005), .ow_cout(w_c4to2_cout_09_005)
);
wire w_c4to2_sum_09_006, w_c4to2_carry_09_006, w_c4to2_cout_09_006;
math_compressor_4to2 u_c4to2_09_006 (
    .i_x1(w_pp_6_3), .i_x2(w_pp_7_2),
    .i_x3(w_c4to2_carry_08_003), .i_x4(w_c4to2_cout_08_003),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_006), .ow_carry(w_c4to2_carry_09_006), .ow_cout(w_c4to2_cout_09_006)
);
wire w_c4to2_sum_10_007, w_c4to2_carry_10_007, w_c4to2_cout_10_007;
math_compressor_4to2 u_c4to2_10_007 (
    .i_x1(w_pp_3_7), .i_x2(w_pp_4_6),
    .i_x3(w_pp_5_5), .i_x4(w_pp_6_4),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_007), .ow_carry(w_c4to2_carry_10_007), .ow_cout(w_c4to2_cout_10_007)
);

// Dadda Reduction Stage 2: height 6 -> 4

wire w_c4to2_sum_04_008, w_c4to2_carry_04_008, w_c4to2_cout_04_008;
math_compressor_4to2 u_c4to2_04_008 (
    .i_x1(w_pp_0_4), .i_x2(w_pp_1_3),
    .i_x3(w_pp_2_2), .i_x4(w_pp_3_1),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_04_008), .ow_carry(w_c4to2_carry_04_008), .ow_cout(w_c4to2_cout_04_008)
);
wire w_c4to2_sum_05_009, w_c4to2_carry_05_009, w_c4to2_cout_05_009;
math_compressor_4to2 u_c4to2_05_009 (
    .i_x1(w_pp_0_5), .i_x2(w_pp_1_4),
    .i_x3(w_pp_2_3), .i_x4(w_pp_3_2),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_05_009), .ow_carry(w_c4to2_carry_05_009), .ow_cout(w_c4to2_cout_05_009)
);
wire w_c4to2_sum_05_010, w_c4to2_carry_05_010, w_c4to2_cout_05_010;
math_compressor_4to2 u_c4to2_05_010 (
    .i_x1(w_pp_4_1), .i_x2(w_pp_5_0),
    .i_x3(w_c4to2_carry_04_008), .i_x4(w_c4to2_cout_04_008),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_05_010), .ow_carry(w_c4to2_carry_05_010), .ow_cout(w_c4to2_cout_05_010)
);
wire w_c4to2_sum_06_011, w_c4to2_carry_06_011, w_c4to2_cout_06_011;
math_compressor_4to2 u_c4to2_06_011 (
    .i_x1(w_pp_4_2), .i_x2(w_pp_5_1),
    .i_x3(w_pp_6_0), .i_x4(w_c4to2_sum_06_000),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_011), .ow_carry(w_c4to2_carry_06_011), .ow_cout(w_c4to2_cout_06_011)
);
wire w_c4to2_sum_06_012, w_c4to2_carry_06_012, w_c4to2_cout_06_012;
math_compressor_4to2 u_c4to2_06_012 (
    .i_x1(w_c4to2_carry_05_009), .i_x2(w_c4to2_cout_05_009),
    .i_x3(w_c4to2_carry_05_010), .i_x4(w_c4to2_cout_05_010),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_012), .ow_carry(w_c4to2_carry_06_012), .ow_cout(w_c4to2_cout_06_012)
);
wire w_c4to2_sum_07_013, w_c4to2_carry_07_013, w_c4to2_cout_07_013;
math_compressor_4to2 u_c4to2_07_013 (
    .i_x1(w_c4to2_carry_06_000), .i_x2(w_c4to2_cout_06_000),
    .i_x3(w_c4to2_sum_07_001), .i_x4(w_c4to2_sum_07_002),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_013), .ow_carry(w_c4to2_carry_07_013), .ow_cout(w_c4to2_cout_07_013)
);
wire w_c4to2_sum_07_014, w_c4to2_carry_07_014, w_c4to2_cout_07_014;
math_compressor_4to2 u_c4to2_07_014 (
    .i_x1(w_c4to2_carry_06_011), .i_x2(w_c4to2_cout_06_011),
    .i_x3(w_c4to2_carry_06_012), .i_x4(w_c4to2_cout_06_012),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_014), .ow_carry(w_c4to2_carry_07_014), .ow_cout(w_c4to2_cout_07_014)
);
wire w_c4to2_sum_08_015, w_c4to2_carry_08_015, w_c4to2_cout_08_015;
math_compressor_4to2 u_c4to2_08_015 (
    .i_x1(w_c4to2_cout_07_001), .i_x2(w_c4to2_carry_07_002),
    .i_x3(w_c4to2_cout_07_002), .i_x4(w_c4to2_sum_08_003),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_015), .ow_carry(w_c4to2_carry_08_015), .ow_cout(w_c4to2_cout_08_015)
);
wire w_c4to2_sum_08_016, w_c4to2_carry_08_016, w_c4to2_cout_08_016;
math_compressor_4to2 u_c4to2_08_016 (
    .i_x1(w_c4to2_sum_08_004), .i_x2(w_c4to2_carry_07_013),
    .i_x3(w_c4to2_cout_07_013), .i_x4(w_c4to2_carry_07_014),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_016), .ow_carry(w_c4to2_carry_08_016), .ow_cout(w_c4to2_cout_08_016)
);
wire w_c4to2_sum_09_017, w_c4to2_carry_09_017, w_c4to2_cout_09_017;
math_compressor_4to2 u_c4to2_09_017 (
    .i_x1(w_c4to2_carry_08_004), .i_x2(w_c4to2_cout_08_004),
    .i_x3(w_c4to2_sum_09_005), .i_x4(w_c4to2_sum_09_006),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_017), .ow_carry(w_c4to2_carry_09_017), .ow_cout(w_c4to2_cout_09_017)
);
wire w_c4to2_sum_09_018, w_c4to2_carry_09_018, w_c4to2_cout_09_018;
math_compressor_4to2 u_c4to2_09_018 (
    .i_x1(w_c4to2_carry_08_015), .i_x2(w_c4to2_cout_08_015),
    .i_x3(w_c4to2_carry_08_016), .i_x4(w_c4to2_cout_08_016),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_018), .ow_carry(w_c4to2_carry_09_018), .ow_cout(w_c4to2_cout_09_018)
);
wire w_c4to2_sum_10_019, w_c4to2_carry_10_019, w_c4to2_cout_10_019;
math_compressor_4to2 u_c4to2_10_019 (
    .i_x1(w_pp_7_3), .i_x2(w_c4to2_carry_09_005),
    .i_x3(w_c4to2_cout_09_005), .i_x4(w_c4to2_carry_09_006),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_019), .ow_carry(w_c4to2_carry_10_019), .ow_cout(w_c4to2_cout_10_019)
);
wire w_c4to2_sum_10_020, w_c4to2_carry_10_020, w_c4to2_cout_10_020;
math_compressor_4to2 u_c4to2_10_020 (
    .i_x1(w_c4to2_cout_09_006), .i_x2(w_c4to2_sum_10_007),
    .i_x3(w_c4to2_carry_09_017), .i_x4(w_c4to2_cout_09_017),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_020), .ow_carry(w_c4to2_carry_10_020), .ow_cout(w_c4to2_cout_10_020)
);
wire w_c4to2_sum_11_021, w_c4to2_carry_11_021, w_c4to2_cout_11_021;
math_compressor_4to2 u_c4to2_11_021 (
    .i_x1(w_pp_4_7), .i_x2(w_pp_5_6),
    .i_x3(w_pp_6_5), .i_x4(w_pp_7_4),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_021), .ow_carry(w_c4to2_carry_11_021), .ow_cout(w_c4to2_cout_11_021)
);
wire w_c4to2_sum_11_022, w_c4to2_carry_11_022, w_c4to2_cout_11_022;
math_compressor_4to2 u_c4to2_11_022 (
    .i_x1(w_c4to2_carry_10_007), .i_x2(w_c4to2_cout_10_007),
    .i_x3(w_c4to2_carry_10_019), .i_x4(w_c4to2_cout_10_019),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_022), .ow_carry(w_c4to2_carry_11_022), .ow_cout(w_c4to2_cout_11_022)
);
wire w_c4to2_sum_12_023, w_c4to2_carry_12_023, w_c4to2_cout_12_023;
math_compressor_4to2 u_c4to2_12_023 (
    .i_x1(w_pp_5_7), .i_x2(w_pp_6_6),
    .i_x3(w_pp_7_5), .i_x4(w_c4to2_carry_11_021),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_023), .ow_carry(w_c4to2_carry_12_023), .ow_cout(w_c4to2_cout_12_023)
);

// Dadda Reduction Stage 3: height 4 -> 3

wire w_c4to2_sum_03_024, w_c4to2_carry_03_024, w_c4to2_cout_03_024;
math_compressor_4to2 u_c4to2_03_024 (
    .i_x1(w_pp_0_3), .i_x2(w_pp_1_2),
    .i_x3(w_pp_2_1), .i_x4(w_pp_3_0),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_03_024), .ow_carry(w_c4to2_carry_03_024), .ow_cout(w_c4to2_cout_03_024)
);
wire w_c4to2_sum_04_025, w_c4to2_carry_04_025, w_c4to2_cout_04_025;
math_compressor_4to2 u_c4to2_04_025 (
    .i_x1(w_pp_4_0), .i_x2(w_c4to2_sum_04_008),
    .i_x3(w_c4to2_carry_03_024), .i_x4(w_c4to2_cout_03_024),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_04_025), .ow_carry(w_c4to2_carry_04_025), .ow_cout(w_c4to2_cout_04_025)
);
wire w_c4to2_sum_05_026, w_c4to2_carry_05_026, w_c4to2_cout_05_026;
math_compressor_4to2 u_c4to2_05_026 (
    .i_x1(w_c4to2_sum_05_009), .i_x2(w_c4to2_sum_05_010),
    .i_x3(w_c4to2_carry_04_025), .i_x4(w_c4to2_cout_04_025),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_05_026), .ow_carry(w_c4to2_carry_05_026), .ow_cout(w_c4to2_cout_05_026)
);
wire w_c4to2_sum_06_027, w_c4to2_carry_06_027, w_c4to2_cout_06_027;
math_compressor_4to2 u_c4to2_06_027 (
    .i_x1(w_c4to2_sum_06_011), .i_x2(w_c4to2_sum_06_012),
    .i_x3(w_c4to2_carry_05_026), .i_x4(w_c4to2_cout_05_026),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_027), .ow_carry(w_c4to2_carry_06_027), .ow_cout(w_c4to2_cout_06_027)
);
wire w_c4to2_sum_07_028, w_c4to2_carry_07_028, w_c4to2_cout_07_028;
math_compressor_4to2 u_c4to2_07_028 (
    .i_x1(w_c4to2_sum_07_013), .i_x2(w_c4to2_sum_07_014),
    .i_x3(w_c4to2_carry_06_027), .i_x4(w_c4to2_cout_06_027),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_028), .ow_carry(w_c4to2_carry_07_028), .ow_cout(w_c4to2_cout_07_028)
);
wire w_c4to2_sum_08_029, w_c4to2_carry_08_029, w_c4to2_cout_08_029;
math_compressor_4to2 u_c4to2_08_029 (
    .i_x1(w_c4to2_cout_07_014), .i_x2(w_c4to2_sum_08_015),
    .i_x3(w_c4to2_sum_08_016), .i_x4(w_c4to2_carry_07_028),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_029), .ow_carry(w_c4to2_carry_08_029), .ow_cout(w_c4to2_cout_08_029)
);
wire w_c4to2_sum_09_030, w_c4to2_carry_09_030, w_c4to2_cout_09_030;
math_compressor_4to2 u_c4to2_09_030 (
    .i_x1(w_c4to2_sum_09_017), .i_x2(w_c4to2_sum_09_018),
    .i_x3(w_c4to2_carry_08_029), .i_x4(w_c4to2_cout_08_029),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_030), .ow_carry(w_c4to2_carry_09_030), .ow_cout(w_c4to2_cout_09_030)
);
wire w_c4to2_sum_10_031, w_c4to2_carry_10_031, w_c4to2_cout_10_031;
math_compressor_4to2 u_c4to2_10_031 (
    .i_x1(w_c4to2_carry_09_018), .i_x2(w_c4to2_cout_09_018),
    .i_x3(w_c4to2_sum_10_019), .i_x4(w_c4to2_sum_10_020),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_031), .ow_carry(w_c4to2_carry_10_031), .ow_cout(w_c4to2_cout_10_031)
);
wire w_c4to2_sum_11_032, w_c4to2_carry_11_032, w_c4to2_cout_11_032;
math_compressor_4to2 u_c4to2_11_032 (
    .i_x1(w_c4to2_carry_10_020), .i_x2(w_c4to2_cout_10_020),
    .i_x3(w_c4to2_sum_11_021), .i_x4(w_c4to2_sum_11_022),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_032), .ow_carry(w_c4to2_carry_11_032), .ow_cout(w_c4to2_cout_11_032)
);
wire w_c4to2_sum_12_033, w_c4to2_carry_12_033, w_c4to2_cout_12_033;
math_compressor_4to2 u_c4to2_12_033 (
    .i_x1(w_c4to2_cout_11_021), .i_x2(w_c4to2_carry_11_022),
    .i_x3(w_c4to2_cout_11_022), .i_x4(w_c4to2_sum_12_023),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_033), .ow_carry(w_c4to2_carry_12_033), .ow_cout(w_c4to2_cout_12_033)
);
wire w_c4to2_sum_13_034, w_c4to2_carry_13_034, w_c4to2_cout_13_034;
math_compressor_4to2 u_c4to2_13_034 (
    .i_x1(w_pp_6_7), .i_x2(w_pp_7_6),
    .i_x3(w_c4to2_carry_12_023), .i_x4(w_c4to2_cout_12_023),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_034), .ow_carry(w_c4to2_carry_13_034), .ow_cout(w_c4to2_cout_13_034)
);

// Dadda Reduction Stage 4: height 3 -> 2

wire w_fa_sum_02_000, w_fa_carry_02_000;
math_adder_full u_fa_02_000 (
    .i_a(w_pp_0_2), .i_b(w_pp_1_1), .i_c(w_pp_2_0),
    .ow_sum(w_fa_sum_02_000), .ow_carry(w_fa_carry_02_000)
);
wire w_fa_sum_10_001, w_fa_carry_10_001;
math_adder_full u_fa_10_001 (
    .i_a(w_c4to2_carry_09_030), .i_b(w_c4to2_cout_09_030), .i_c(w_c4to2_sum_10_031),
    .ow_sum(w_fa_sum_10_001), .ow_carry(w_fa_carry_10_001)
);
wire w_c4to2_sum_11_035, w_c4to2_carry_11_035, w_c4to2_cout_11_035;
math_compressor_4to2 u_c4to2_11_035 (
    .i_x1(w_c4to2_carry_10_031), .i_x2(w_c4to2_cout_10_031),
    .i_x3(w_c4to2_sum_11_032), .i_x4(w_fa_carry_10_001),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_035), .ow_carry(w_c4to2_carry_11_035), .ow_cout(w_c4to2_cout_11_035)
);
wire w_c4to2_sum_12_036, w_c4to2_carry_12_036, w_c4to2_cout_12_036;
math_compressor_4to2 u_c4to2_12_036 (
    .i_x1(w_c4to2_carry_11_032), .i_x2(w_c4to2_cout_11_032),
    .i_x3(w_c4to2_sum_12_033), .i_x4(w_c4to2_carry_11_035),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_036), .ow_carry(w_c4to2_carry_12_036), .ow_cout(w_c4to2_cout_12_036)
);
wire w_c4to2_sum_13_037, w_c4to2_carry_13_037, w_c4to2_cout_13_037;
math_compressor_4to2 u_c4to2_13_037 (
    .i_x1(w_c4to2_carry_12_033), .i_x2(w_c4to2_cout_12_033),
    .i_x3(w_c4to2_sum_13_034), .i_x4(w_c4to2_carry_12_036),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_037), .ow_carry(w_c4to2_carry_13_037), .ow_cout(w_c4to2_cout_13_037)
);
wire w_c4to2_sum_14_038, w_c4to2_carry_14_038, w_c4to2_cout_14_038;
math_compressor_4to2 u_c4to2_14_038 (
    .i_x1(w_pp_7_7), .i_x2(w_c4to2_carry_13_034),
    .i_x3(w_c4to2_cout_13_034), .i_x4(w_c4to2_carry_13_037),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_038), .ow_carry(w_c4to2_carry_14_038), .ow_cout(w_c4to2_cout_14_038)
);

// Final CPA: Two operands from reduction tree
wire [2*N-1:0] w_cpa_a, w_cpa_b;
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

// Han-Carlson prefix adder for final CPA
wire w_cpa_cout;  // Unused for unsigned multiply
math_adder_han_carlson_016 u_final_cpa (
    .i_a(w_cpa_a),
    .i_b(w_cpa_b),
    .i_cin(1'b0),
    .ow_sum(ow_product),
    .ow_cout(w_cpa_cout)
);

endmodule
