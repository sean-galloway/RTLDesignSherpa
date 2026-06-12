// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_multiplier_dadda_4to2_011
// Purpose: Dadda 11x11 multiplier with 4:2 compressors for FP32 mantissa
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/dadda_4to2_multiplier.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_multiplier_dadda_4to2_011 #(parameter int  N = 11)(
    input  logic [N-1:0]   i_multiplier,
    input  logic [N-1:0]   i_multiplicand,
    output logic [2*N-1:0] ow_product
);

// Partial Products (AND gate array)
wire w_pp_00_00 = i_multiplier[0] & i_multiplicand[0];
wire w_pp_00_01 = i_multiplier[0] & i_multiplicand[1];
wire w_pp_00_02 = i_multiplier[0] & i_multiplicand[2];
wire w_pp_00_03 = i_multiplier[0] & i_multiplicand[3];
wire w_pp_00_04 = i_multiplier[0] & i_multiplicand[4];
wire w_pp_00_05 = i_multiplier[0] & i_multiplicand[5];
wire w_pp_00_06 = i_multiplier[0] & i_multiplicand[6];
wire w_pp_00_07 = i_multiplier[0] & i_multiplicand[7];
wire w_pp_00_08 = i_multiplier[0] & i_multiplicand[8];
wire w_pp_00_09 = i_multiplier[0] & i_multiplicand[9];
wire w_pp_00_10 = i_multiplier[0] & i_multiplicand[10];
wire w_pp_01_00 = i_multiplier[1] & i_multiplicand[0];
wire w_pp_01_01 = i_multiplier[1] & i_multiplicand[1];
wire w_pp_01_02 = i_multiplier[1] & i_multiplicand[2];
wire w_pp_01_03 = i_multiplier[1] & i_multiplicand[3];
wire w_pp_01_04 = i_multiplier[1] & i_multiplicand[4];
wire w_pp_01_05 = i_multiplier[1] & i_multiplicand[5];
wire w_pp_01_06 = i_multiplier[1] & i_multiplicand[6];
wire w_pp_01_07 = i_multiplier[1] & i_multiplicand[7];
wire w_pp_01_08 = i_multiplier[1] & i_multiplicand[8];
wire w_pp_01_09 = i_multiplier[1] & i_multiplicand[9];
wire w_pp_01_10 = i_multiplier[1] & i_multiplicand[10];
wire w_pp_02_00 = i_multiplier[2] & i_multiplicand[0];
wire w_pp_02_01 = i_multiplier[2] & i_multiplicand[1];
wire w_pp_02_02 = i_multiplier[2] & i_multiplicand[2];
wire w_pp_02_03 = i_multiplier[2] & i_multiplicand[3];
wire w_pp_02_04 = i_multiplier[2] & i_multiplicand[4];
wire w_pp_02_05 = i_multiplier[2] & i_multiplicand[5];
wire w_pp_02_06 = i_multiplier[2] & i_multiplicand[6];
wire w_pp_02_07 = i_multiplier[2] & i_multiplicand[7];
wire w_pp_02_08 = i_multiplier[2] & i_multiplicand[8];
wire w_pp_02_09 = i_multiplier[2] & i_multiplicand[9];
wire w_pp_02_10 = i_multiplier[2] & i_multiplicand[10];
wire w_pp_03_00 = i_multiplier[3] & i_multiplicand[0];
wire w_pp_03_01 = i_multiplier[3] & i_multiplicand[1];
wire w_pp_03_02 = i_multiplier[3] & i_multiplicand[2];
wire w_pp_03_03 = i_multiplier[3] & i_multiplicand[3];
wire w_pp_03_04 = i_multiplier[3] & i_multiplicand[4];
wire w_pp_03_05 = i_multiplier[3] & i_multiplicand[5];
wire w_pp_03_06 = i_multiplier[3] & i_multiplicand[6];
wire w_pp_03_07 = i_multiplier[3] & i_multiplicand[7];
wire w_pp_03_08 = i_multiplier[3] & i_multiplicand[8];
wire w_pp_03_09 = i_multiplier[3] & i_multiplicand[9];
wire w_pp_03_10 = i_multiplier[3] & i_multiplicand[10];
wire w_pp_04_00 = i_multiplier[4] & i_multiplicand[0];
wire w_pp_04_01 = i_multiplier[4] & i_multiplicand[1];
wire w_pp_04_02 = i_multiplier[4] & i_multiplicand[2];
wire w_pp_04_03 = i_multiplier[4] & i_multiplicand[3];
wire w_pp_04_04 = i_multiplier[4] & i_multiplicand[4];
wire w_pp_04_05 = i_multiplier[4] & i_multiplicand[5];
wire w_pp_04_06 = i_multiplier[4] & i_multiplicand[6];
wire w_pp_04_07 = i_multiplier[4] & i_multiplicand[7];
wire w_pp_04_08 = i_multiplier[4] & i_multiplicand[8];
wire w_pp_04_09 = i_multiplier[4] & i_multiplicand[9];
wire w_pp_04_10 = i_multiplier[4] & i_multiplicand[10];
wire w_pp_05_00 = i_multiplier[5] & i_multiplicand[0];
wire w_pp_05_01 = i_multiplier[5] & i_multiplicand[1];
wire w_pp_05_02 = i_multiplier[5] & i_multiplicand[2];
wire w_pp_05_03 = i_multiplier[5] & i_multiplicand[3];
wire w_pp_05_04 = i_multiplier[5] & i_multiplicand[4];
wire w_pp_05_05 = i_multiplier[5] & i_multiplicand[5];
wire w_pp_05_06 = i_multiplier[5] & i_multiplicand[6];
wire w_pp_05_07 = i_multiplier[5] & i_multiplicand[7];
wire w_pp_05_08 = i_multiplier[5] & i_multiplicand[8];
wire w_pp_05_09 = i_multiplier[5] & i_multiplicand[9];
wire w_pp_05_10 = i_multiplier[5] & i_multiplicand[10];
wire w_pp_06_00 = i_multiplier[6] & i_multiplicand[0];
wire w_pp_06_01 = i_multiplier[6] & i_multiplicand[1];
wire w_pp_06_02 = i_multiplier[6] & i_multiplicand[2];
wire w_pp_06_03 = i_multiplier[6] & i_multiplicand[3];
wire w_pp_06_04 = i_multiplier[6] & i_multiplicand[4];
wire w_pp_06_05 = i_multiplier[6] & i_multiplicand[5];
wire w_pp_06_06 = i_multiplier[6] & i_multiplicand[6];
wire w_pp_06_07 = i_multiplier[6] & i_multiplicand[7];
wire w_pp_06_08 = i_multiplier[6] & i_multiplicand[8];
wire w_pp_06_09 = i_multiplier[6] & i_multiplicand[9];
wire w_pp_06_10 = i_multiplier[6] & i_multiplicand[10];
wire w_pp_07_00 = i_multiplier[7] & i_multiplicand[0];
wire w_pp_07_01 = i_multiplier[7] & i_multiplicand[1];
wire w_pp_07_02 = i_multiplier[7] & i_multiplicand[2];
wire w_pp_07_03 = i_multiplier[7] & i_multiplicand[3];
wire w_pp_07_04 = i_multiplier[7] & i_multiplicand[4];
wire w_pp_07_05 = i_multiplier[7] & i_multiplicand[5];
wire w_pp_07_06 = i_multiplier[7] & i_multiplicand[6];
wire w_pp_07_07 = i_multiplier[7] & i_multiplicand[7];
wire w_pp_07_08 = i_multiplier[7] & i_multiplicand[8];
wire w_pp_07_09 = i_multiplier[7] & i_multiplicand[9];
wire w_pp_07_10 = i_multiplier[7] & i_multiplicand[10];
wire w_pp_08_00 = i_multiplier[8] & i_multiplicand[0];
wire w_pp_08_01 = i_multiplier[8] & i_multiplicand[1];
wire w_pp_08_02 = i_multiplier[8] & i_multiplicand[2];
wire w_pp_08_03 = i_multiplier[8] & i_multiplicand[3];
wire w_pp_08_04 = i_multiplier[8] & i_multiplicand[4];
wire w_pp_08_05 = i_multiplier[8] & i_multiplicand[5];
wire w_pp_08_06 = i_multiplier[8] & i_multiplicand[6];
wire w_pp_08_07 = i_multiplier[8] & i_multiplicand[7];
wire w_pp_08_08 = i_multiplier[8] & i_multiplicand[8];
wire w_pp_08_09 = i_multiplier[8] & i_multiplicand[9];
wire w_pp_08_10 = i_multiplier[8] & i_multiplicand[10];
wire w_pp_09_00 = i_multiplier[9] & i_multiplicand[0];
wire w_pp_09_01 = i_multiplier[9] & i_multiplicand[1];
wire w_pp_09_02 = i_multiplier[9] & i_multiplicand[2];
wire w_pp_09_03 = i_multiplier[9] & i_multiplicand[3];
wire w_pp_09_04 = i_multiplier[9] & i_multiplicand[4];
wire w_pp_09_05 = i_multiplier[9] & i_multiplicand[5];
wire w_pp_09_06 = i_multiplier[9] & i_multiplicand[6];
wire w_pp_09_07 = i_multiplier[9] & i_multiplicand[7];
wire w_pp_09_08 = i_multiplier[9] & i_multiplicand[8];
wire w_pp_09_09 = i_multiplier[9] & i_multiplicand[9];
wire w_pp_09_10 = i_multiplier[9] & i_multiplicand[10];
wire w_pp_10_00 = i_multiplier[10] & i_multiplicand[0];
wire w_pp_10_01 = i_multiplier[10] & i_multiplicand[1];
wire w_pp_10_02 = i_multiplier[10] & i_multiplicand[2];
wire w_pp_10_03 = i_multiplier[10] & i_multiplicand[3];
wire w_pp_10_04 = i_multiplier[10] & i_multiplicand[4];
wire w_pp_10_05 = i_multiplier[10] & i_multiplicand[5];
wire w_pp_10_06 = i_multiplier[10] & i_multiplicand[6];
wire w_pp_10_07 = i_multiplier[10] & i_multiplicand[7];
wire w_pp_10_08 = i_multiplier[10] & i_multiplicand[8];
wire w_pp_10_09 = i_multiplier[10] & i_multiplicand[9];
wire w_pp_10_10 = i_multiplier[10] & i_multiplicand[10];

// Dadda Reduction Stage 1: height 11 -> 9

wire w_c4to2_sum_09_000, w_c4to2_carry_09_000, w_c4to2_cout_09_000;
math_compressor_4to2 u_c4to2_09_000 (
    .i_x1(w_pp_00_09), .i_x2(w_pp_01_08),
    .i_x3(w_pp_02_07), .i_x4(w_pp_03_06),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_000), .ow_carry(w_c4to2_carry_09_000), .ow_cout(w_c4to2_cout_09_000)
);
wire w_c4to2_sum_10_001, w_c4to2_carry_10_001, w_c4to2_cout_10_001;
math_compressor_4to2 u_c4to2_10_001 (
    .i_x1(w_pp_00_10), .i_x2(w_pp_01_09),
    .i_x3(w_pp_02_08), .i_x4(w_pp_03_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_001), .ow_carry(w_c4to2_carry_10_001), .ow_cout(w_c4to2_cout_10_001)
);
wire w_c4to2_sum_10_002, w_c4to2_carry_10_002, w_c4to2_cout_10_002;
math_compressor_4to2 u_c4to2_10_002 (
    .i_x1(w_pp_04_06), .i_x2(w_pp_05_05),
    .i_x3(w_pp_06_04), .i_x4(w_pp_07_03),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_002), .ow_carry(w_c4to2_carry_10_002), .ow_cout(w_c4to2_cout_10_002)
);
wire w_c4to2_sum_11_003, w_c4to2_carry_11_003, w_c4to2_cout_11_003;
math_compressor_4to2 u_c4to2_11_003 (
    .i_x1(w_pp_01_10), .i_x2(w_pp_02_09),
    .i_x3(w_pp_03_08), .i_x4(w_pp_04_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_003), .ow_carry(w_c4to2_carry_11_003), .ow_cout(w_c4to2_cout_11_003)
);
wire w_c4to2_sum_11_004, w_c4to2_carry_11_004, w_c4to2_cout_11_004;
math_compressor_4to2 u_c4to2_11_004 (
    .i_x1(w_pp_05_06), .i_x2(w_pp_06_05),
    .i_x3(w_pp_07_04), .i_x4(w_pp_08_03),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_004), .ow_carry(w_c4to2_carry_11_004), .ow_cout(w_c4to2_cout_11_004)
);
wire w_c4to2_sum_12_005, w_c4to2_carry_12_005, w_c4to2_cout_12_005;
math_compressor_4to2 u_c4to2_12_005 (
    .i_x1(w_pp_02_10), .i_x2(w_pp_03_09),
    .i_x3(w_pp_04_08), .i_x4(w_pp_05_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_005), .ow_carry(w_c4to2_carry_12_005), .ow_cout(w_c4to2_cout_12_005)
);
wire w_c4to2_sum_12_006, w_c4to2_carry_12_006, w_c4to2_cout_12_006;
math_compressor_4to2 u_c4to2_12_006 (
    .i_x1(w_pp_06_06), .i_x2(w_pp_07_05),
    .i_x3(w_pp_08_04), .i_x4(w_pp_09_03),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_006), .ow_carry(w_c4to2_carry_12_006), .ow_cout(w_c4to2_cout_12_006)
);
wire w_c4to2_sum_13_007, w_c4to2_carry_13_007, w_c4to2_cout_13_007;
math_compressor_4to2 u_c4to2_13_007 (
    .i_x1(w_pp_03_10), .i_x2(w_pp_04_09),
    .i_x3(w_pp_05_08), .i_x4(w_pp_06_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_007), .ow_carry(w_c4to2_carry_13_007), .ow_cout(w_c4to2_cout_13_007)
);

// Dadda Reduction Stage 2: height 9 -> 6

wire w_c4to2_sum_06_008, w_c4to2_carry_06_008, w_c4to2_cout_06_008;
math_compressor_4to2 u_c4to2_06_008 (
    .i_x1(w_pp_00_06), .i_x2(w_pp_01_05),
    .i_x3(w_pp_02_04), .i_x4(w_pp_03_03),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_008), .ow_carry(w_c4to2_carry_06_008), .ow_cout(w_c4to2_cout_06_008)
);
wire w_c4to2_sum_07_009, w_c4to2_carry_07_009, w_c4to2_cout_07_009;
math_compressor_4to2 u_c4to2_07_009 (
    .i_x1(w_pp_00_07), .i_x2(w_pp_01_06),
    .i_x3(w_pp_02_05), .i_x4(w_pp_03_04),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_009), .ow_carry(w_c4to2_carry_07_009), .ow_cout(w_c4to2_cout_07_009)
);
wire w_c4to2_sum_07_010, w_c4to2_carry_07_010, w_c4to2_cout_07_010;
math_compressor_4to2 u_c4to2_07_010 (
    .i_x1(w_pp_04_03), .i_x2(w_pp_05_02),
    .i_x3(w_pp_06_01), .i_x4(w_pp_07_00),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_010), .ow_carry(w_c4to2_carry_07_010), .ow_cout(w_c4to2_cout_07_010)
);
wire w_c4to2_sum_08_011, w_c4to2_carry_08_011, w_c4to2_cout_08_011;
math_compressor_4to2 u_c4to2_08_011 (
    .i_x1(w_pp_00_08), .i_x2(w_pp_01_07),
    .i_x3(w_pp_02_06), .i_x4(w_pp_03_05),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_011), .ow_carry(w_c4to2_carry_08_011), .ow_cout(w_c4to2_cout_08_011)
);
wire w_c4to2_sum_08_012, w_c4to2_carry_08_012, w_c4to2_cout_08_012;
math_compressor_4to2 u_c4to2_08_012 (
    .i_x1(w_pp_04_04), .i_x2(w_pp_05_03),
    .i_x3(w_pp_06_02), .i_x4(w_pp_07_01),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_012), .ow_carry(w_c4to2_carry_08_012), .ow_cout(w_c4to2_cout_08_012)
);
wire w_c4to2_sum_08_013, w_c4to2_carry_08_013, w_c4to2_cout_08_013;
math_compressor_4to2 u_c4to2_08_013 (
    .i_x1(w_pp_08_00), .i_x2(w_c4to2_carry_07_009),
    .i_x3(w_c4to2_cout_07_009), .i_x4(w_c4to2_carry_07_010),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_013), .ow_carry(w_c4to2_carry_08_013), .ow_cout(w_c4to2_cout_08_013)
);
wire w_c4to2_sum_09_014, w_c4to2_carry_09_014, w_c4to2_cout_09_014;
math_compressor_4to2 u_c4to2_09_014 (
    .i_x1(w_pp_04_05), .i_x2(w_pp_05_04),
    .i_x3(w_pp_06_03), .i_x4(w_pp_07_02),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_014), .ow_carry(w_c4to2_carry_09_014), .ow_cout(w_c4to2_cout_09_014)
);
wire w_c4to2_sum_09_015, w_c4to2_carry_09_015, w_c4to2_cout_09_015;
math_compressor_4to2 u_c4to2_09_015 (
    .i_x1(w_pp_08_01), .i_x2(w_pp_09_00),
    .i_x3(w_c4to2_sum_09_000), .i_x4(w_c4to2_carry_08_011),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_015), .ow_carry(w_c4to2_carry_09_015), .ow_cout(w_c4to2_cout_09_015)
);
wire w_c4to2_sum_09_016, w_c4to2_carry_09_016, w_c4to2_cout_09_016;
math_compressor_4to2 u_c4to2_09_016 (
    .i_x1(w_c4to2_cout_08_011), .i_x2(w_c4to2_carry_08_012),
    .i_x3(w_c4to2_cout_08_012), .i_x4(w_c4to2_carry_08_013),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_016), .ow_carry(w_c4to2_carry_09_016), .ow_cout(w_c4to2_cout_09_016)
);
wire w_c4to2_sum_10_017, w_c4to2_carry_10_017, w_c4to2_cout_10_017;
math_compressor_4to2 u_c4to2_10_017 (
    .i_x1(w_pp_08_02), .i_x2(w_pp_09_01),
    .i_x3(w_pp_10_00), .i_x4(w_c4to2_carry_09_000),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_017), .ow_carry(w_c4to2_carry_10_017), .ow_cout(w_c4to2_cout_10_017)
);
wire w_c4to2_sum_10_018, w_c4to2_carry_10_018, w_c4to2_cout_10_018;
math_compressor_4to2 u_c4to2_10_018 (
    .i_x1(w_c4to2_cout_09_000), .i_x2(w_c4to2_sum_10_001),
    .i_x3(w_c4to2_sum_10_002), .i_x4(w_c4to2_carry_09_014),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_018), .ow_carry(w_c4to2_carry_10_018), .ow_cout(w_c4to2_cout_10_018)
);
wire w_c4to2_sum_10_019, w_c4to2_carry_10_019, w_c4to2_cout_10_019;
math_compressor_4to2 u_c4to2_10_019 (
    .i_x1(w_c4to2_cout_09_014), .i_x2(w_c4to2_carry_09_015),
    .i_x3(w_c4to2_cout_09_015), .i_x4(w_c4to2_carry_09_016),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_019), .ow_carry(w_c4to2_carry_10_019), .ow_cout(w_c4to2_cout_10_019)
);
wire w_c4to2_sum_11_020, w_c4to2_carry_11_020, w_c4to2_cout_11_020;
math_compressor_4to2 u_c4to2_11_020 (
    .i_x1(w_pp_09_02), .i_x2(w_pp_10_01),
    .i_x3(w_c4to2_carry_10_001), .i_x4(w_c4to2_cout_10_001),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_020), .ow_carry(w_c4to2_carry_11_020), .ow_cout(w_c4to2_cout_11_020)
);
wire w_c4to2_sum_11_021, w_c4to2_carry_11_021, w_c4to2_cout_11_021;
math_compressor_4to2 u_c4to2_11_021 (
    .i_x1(w_c4to2_carry_10_002), .i_x2(w_c4to2_cout_10_002),
    .i_x3(w_c4to2_sum_11_003), .i_x4(w_c4to2_sum_11_004),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_021), .ow_carry(w_c4to2_carry_11_021), .ow_cout(w_c4to2_cout_11_021)
);
wire w_c4to2_sum_11_022, w_c4to2_carry_11_022, w_c4to2_cout_11_022;
math_compressor_4to2 u_c4to2_11_022 (
    .i_x1(w_c4to2_carry_10_017), .i_x2(w_c4to2_cout_10_017),
    .i_x3(w_c4to2_carry_10_018), .i_x4(w_c4to2_cout_10_018),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_022), .ow_carry(w_c4to2_carry_11_022), .ow_cout(w_c4to2_cout_11_022)
);
wire w_c4to2_sum_12_023, w_c4to2_carry_12_023, w_c4to2_cout_12_023;
math_compressor_4to2 u_c4to2_12_023 (
    .i_x1(w_pp_10_02), .i_x2(w_c4to2_carry_11_003),
    .i_x3(w_c4to2_cout_11_003), .i_x4(w_c4to2_carry_11_004),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_023), .ow_carry(w_c4to2_carry_12_023), .ow_cout(w_c4to2_cout_12_023)
);
wire w_c4to2_sum_12_024, w_c4to2_carry_12_024, w_c4to2_cout_12_024;
math_compressor_4to2 u_c4to2_12_024 (
    .i_x1(w_c4to2_cout_11_004), .i_x2(w_c4to2_sum_12_005),
    .i_x3(w_c4to2_sum_12_006), .i_x4(w_c4to2_carry_11_020),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_024), .ow_carry(w_c4to2_carry_12_024), .ow_cout(w_c4to2_cout_12_024)
);
wire w_c4to2_sum_12_025, w_c4to2_carry_12_025, w_c4to2_cout_12_025;
math_compressor_4to2 u_c4to2_12_025 (
    .i_x1(w_c4to2_cout_11_020), .i_x2(w_c4to2_carry_11_021),
    .i_x3(w_c4to2_cout_11_021), .i_x4(w_c4to2_carry_11_022),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_025), .ow_carry(w_c4to2_carry_12_025), .ow_cout(w_c4to2_cout_12_025)
);
wire w_c4to2_sum_13_026, w_c4to2_carry_13_026, w_c4to2_cout_13_026;
math_compressor_4to2 u_c4to2_13_026 (
    .i_x1(w_pp_07_06), .i_x2(w_pp_08_05),
    .i_x3(w_pp_09_04), .i_x4(w_pp_10_03),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_026), .ow_carry(w_c4to2_carry_13_026), .ow_cout(w_c4to2_cout_13_026)
);
wire w_c4to2_sum_13_027, w_c4to2_carry_13_027, w_c4to2_cout_13_027;
math_compressor_4to2 u_c4to2_13_027 (
    .i_x1(w_c4to2_carry_12_005), .i_x2(w_c4to2_cout_12_005),
    .i_x3(w_c4to2_carry_12_006), .i_x4(w_c4to2_cout_12_006),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_027), .ow_carry(w_c4to2_carry_13_027), .ow_cout(w_c4to2_cout_13_027)
);
wire w_c4to2_sum_13_028, w_c4to2_carry_13_028, w_c4to2_cout_13_028;
math_compressor_4to2 u_c4to2_13_028 (
    .i_x1(w_c4to2_sum_13_007), .i_x2(w_c4to2_carry_12_023),
    .i_x3(w_c4to2_cout_12_023), .i_x4(w_c4to2_carry_12_024),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_028), .ow_carry(w_c4to2_carry_13_028), .ow_cout(w_c4to2_cout_13_028)
);
wire w_c4to2_sum_14_029, w_c4to2_carry_14_029, w_c4to2_cout_14_029;
math_compressor_4to2 u_c4to2_14_029 (
    .i_x1(w_pp_04_10), .i_x2(w_pp_05_09),
    .i_x3(w_pp_06_08), .i_x4(w_pp_07_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_029), .ow_carry(w_c4to2_carry_14_029), .ow_cout(w_c4to2_cout_14_029)
);
wire w_c4to2_sum_14_030, w_c4to2_carry_14_030, w_c4to2_cout_14_030;
math_compressor_4to2 u_c4to2_14_030 (
    .i_x1(w_pp_08_06), .i_x2(w_pp_09_05),
    .i_x3(w_pp_10_04), .i_x4(w_c4to2_carry_13_007),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_030), .ow_carry(w_c4to2_carry_14_030), .ow_cout(w_c4to2_cout_14_030)
);
wire w_c4to2_sum_14_031, w_c4to2_carry_14_031, w_c4to2_cout_14_031;
math_compressor_4to2 u_c4to2_14_031 (
    .i_x1(w_c4to2_cout_13_007), .i_x2(w_c4to2_carry_13_026),
    .i_x3(w_c4to2_cout_13_026), .i_x4(w_c4to2_carry_13_027),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_031), .ow_carry(w_c4to2_carry_14_031), .ow_cout(w_c4to2_cout_14_031)
);
wire w_c4to2_sum_15_032, w_c4to2_carry_15_032, w_c4to2_cout_15_032;
math_compressor_4to2 u_c4to2_15_032 (
    .i_x1(w_pp_05_10), .i_x2(w_pp_06_09),
    .i_x3(w_pp_07_08), .i_x4(w_pp_08_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_15_032), .ow_carry(w_c4to2_carry_15_032), .ow_cout(w_c4to2_cout_15_032)
);
wire w_c4to2_sum_15_033, w_c4to2_carry_15_033, w_c4to2_cout_15_033;
math_compressor_4to2 u_c4to2_15_033 (
    .i_x1(w_pp_09_06), .i_x2(w_pp_10_05),
    .i_x3(w_c4to2_carry_14_029), .i_x4(w_c4to2_cout_14_029),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_15_033), .ow_carry(w_c4to2_carry_15_033), .ow_cout(w_c4to2_cout_15_033)
);
wire w_c4to2_sum_16_034, w_c4to2_carry_16_034, w_c4to2_cout_16_034;
math_compressor_4to2 u_c4to2_16_034 (
    .i_x1(w_pp_06_10), .i_x2(w_pp_07_09),
    .i_x3(w_pp_08_08), .i_x4(w_pp_09_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_16_034), .ow_carry(w_c4to2_carry_16_034), .ow_cout(w_c4to2_cout_16_034)
);

// Dadda Reduction Stage 3: height 6 -> 4

wire w_c4to2_sum_04_035, w_c4to2_carry_04_035, w_c4to2_cout_04_035;
math_compressor_4to2 u_c4to2_04_035 (
    .i_x1(w_pp_00_04), .i_x2(w_pp_01_03),
    .i_x3(w_pp_02_02), .i_x4(w_pp_03_01),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_04_035), .ow_carry(w_c4to2_carry_04_035), .ow_cout(w_c4to2_cout_04_035)
);
wire w_c4to2_sum_05_036, w_c4to2_carry_05_036, w_c4to2_cout_05_036;
math_compressor_4to2 u_c4to2_05_036 (
    .i_x1(w_pp_00_05), .i_x2(w_pp_01_04),
    .i_x3(w_pp_02_03), .i_x4(w_pp_03_02),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_05_036), .ow_carry(w_c4to2_carry_05_036), .ow_cout(w_c4to2_cout_05_036)
);
wire w_c4to2_sum_05_037, w_c4to2_carry_05_037, w_c4to2_cout_05_037;
math_compressor_4to2 u_c4to2_05_037 (
    .i_x1(w_pp_04_01), .i_x2(w_pp_05_00),
    .i_x3(w_c4to2_carry_04_035), .i_x4(w_c4to2_cout_04_035),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_05_037), .ow_carry(w_c4to2_carry_05_037), .ow_cout(w_c4to2_cout_05_037)
);
wire w_c4to2_sum_06_038, w_c4to2_carry_06_038, w_c4to2_cout_06_038;
math_compressor_4to2 u_c4to2_06_038 (
    .i_x1(w_pp_04_02), .i_x2(w_pp_05_01),
    .i_x3(w_pp_06_00), .i_x4(w_c4to2_sum_06_008),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_038), .ow_carry(w_c4to2_carry_06_038), .ow_cout(w_c4to2_cout_06_038)
);
wire w_c4to2_sum_06_039, w_c4to2_carry_06_039, w_c4to2_cout_06_039;
math_compressor_4to2 u_c4to2_06_039 (
    .i_x1(w_c4to2_carry_05_036), .i_x2(w_c4to2_cout_05_036),
    .i_x3(w_c4to2_carry_05_037), .i_x4(w_c4to2_cout_05_037),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_039), .ow_carry(w_c4to2_carry_06_039), .ow_cout(w_c4to2_cout_06_039)
);
wire w_c4to2_sum_07_040, w_c4to2_carry_07_040, w_c4to2_cout_07_040;
math_compressor_4to2 u_c4to2_07_040 (
    .i_x1(w_c4to2_carry_06_008), .i_x2(w_c4to2_cout_06_008),
    .i_x3(w_c4to2_sum_07_009), .i_x4(w_c4to2_sum_07_010),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_040), .ow_carry(w_c4to2_carry_07_040), .ow_cout(w_c4to2_cout_07_040)
);
wire w_c4to2_sum_07_041, w_c4to2_carry_07_041, w_c4to2_cout_07_041;
math_compressor_4to2 u_c4to2_07_041 (
    .i_x1(w_c4to2_carry_06_038), .i_x2(w_c4to2_cout_06_038),
    .i_x3(w_c4to2_carry_06_039), .i_x4(w_c4to2_cout_06_039),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_041), .ow_carry(w_c4to2_carry_07_041), .ow_cout(w_c4to2_cout_07_041)
);
wire w_c4to2_sum_08_042, w_c4to2_carry_08_042, w_c4to2_cout_08_042;
math_compressor_4to2 u_c4to2_08_042 (
    .i_x1(w_c4to2_cout_07_010), .i_x2(w_c4to2_sum_08_011),
    .i_x3(w_c4to2_sum_08_012), .i_x4(w_c4to2_sum_08_013),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_042), .ow_carry(w_c4to2_carry_08_042), .ow_cout(w_c4to2_cout_08_042)
);
wire w_c4to2_sum_08_043, w_c4to2_carry_08_043, w_c4to2_cout_08_043;
math_compressor_4to2 u_c4to2_08_043 (
    .i_x1(w_c4to2_carry_07_040), .i_x2(w_c4to2_cout_07_040),
    .i_x3(w_c4to2_carry_07_041), .i_x4(w_c4to2_cout_07_041),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_043), .ow_carry(w_c4to2_carry_08_043), .ow_cout(w_c4to2_cout_08_043)
);
wire w_c4to2_sum_09_044, w_c4to2_carry_09_044, w_c4to2_cout_09_044;
math_compressor_4to2 u_c4to2_09_044 (
    .i_x1(w_c4to2_cout_08_013), .i_x2(w_c4to2_sum_09_014),
    .i_x3(w_c4to2_sum_09_015), .i_x4(w_c4to2_sum_09_016),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_044), .ow_carry(w_c4to2_carry_09_044), .ow_cout(w_c4to2_cout_09_044)
);
wire w_c4to2_sum_09_045, w_c4to2_carry_09_045, w_c4to2_cout_09_045;
math_compressor_4to2 u_c4to2_09_045 (
    .i_x1(w_c4to2_carry_08_042), .i_x2(w_c4to2_cout_08_042),
    .i_x3(w_c4to2_carry_08_043), .i_x4(w_c4to2_cout_08_043),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_045), .ow_carry(w_c4to2_carry_09_045), .ow_cout(w_c4to2_cout_09_045)
);
wire w_c4to2_sum_10_046, w_c4to2_carry_10_046, w_c4to2_cout_10_046;
math_compressor_4to2 u_c4to2_10_046 (
    .i_x1(w_c4to2_cout_09_016), .i_x2(w_c4to2_sum_10_017),
    .i_x3(w_c4to2_sum_10_018), .i_x4(w_c4to2_sum_10_019),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_046), .ow_carry(w_c4to2_carry_10_046), .ow_cout(w_c4to2_cout_10_046)
);
wire w_c4to2_sum_10_047, w_c4to2_carry_10_047, w_c4to2_cout_10_047;
math_compressor_4to2 u_c4to2_10_047 (
    .i_x1(w_c4to2_carry_09_044), .i_x2(w_c4to2_cout_09_044),
    .i_x3(w_c4to2_carry_09_045), .i_x4(w_c4to2_cout_09_045),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_047), .ow_carry(w_c4to2_carry_10_047), .ow_cout(w_c4to2_cout_10_047)
);
wire w_c4to2_sum_11_048, w_c4to2_carry_11_048, w_c4to2_cout_11_048;
math_compressor_4to2 u_c4to2_11_048 (
    .i_x1(w_c4to2_carry_10_019), .i_x2(w_c4to2_cout_10_019),
    .i_x3(w_c4to2_sum_11_020), .i_x4(w_c4to2_sum_11_021),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_048), .ow_carry(w_c4to2_carry_11_048), .ow_cout(w_c4to2_cout_11_048)
);
wire w_c4to2_sum_11_049, w_c4to2_carry_11_049, w_c4to2_cout_11_049;
math_compressor_4to2 u_c4to2_11_049 (
    .i_x1(w_c4to2_sum_11_022), .i_x2(w_c4to2_carry_10_046),
    .i_x3(w_c4to2_cout_10_046), .i_x4(w_c4to2_carry_10_047),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_049), .ow_carry(w_c4to2_carry_11_049), .ow_cout(w_c4to2_cout_11_049)
);
wire w_c4to2_sum_12_050, w_c4to2_carry_12_050, w_c4to2_cout_12_050;
math_compressor_4to2 u_c4to2_12_050 (
    .i_x1(w_c4to2_cout_11_022), .i_x2(w_c4to2_sum_12_023),
    .i_x3(w_c4to2_sum_12_024), .i_x4(w_c4to2_sum_12_025),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_050), .ow_carry(w_c4to2_carry_12_050), .ow_cout(w_c4to2_cout_12_050)
);
wire w_c4to2_sum_12_051, w_c4to2_carry_12_051, w_c4to2_cout_12_051;
math_compressor_4to2 u_c4to2_12_051 (
    .i_x1(w_c4to2_carry_11_048), .i_x2(w_c4to2_cout_11_048),
    .i_x3(w_c4to2_carry_11_049), .i_x4(w_c4to2_cout_11_049),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_051), .ow_carry(w_c4to2_carry_12_051), .ow_cout(w_c4to2_cout_12_051)
);
wire w_c4to2_sum_13_052, w_c4to2_carry_13_052, w_c4to2_cout_13_052;
math_compressor_4to2 u_c4to2_13_052 (
    .i_x1(w_c4to2_cout_12_024), .i_x2(w_c4to2_carry_12_025),
    .i_x3(w_c4to2_cout_12_025), .i_x4(w_c4to2_sum_13_026),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_052), .ow_carry(w_c4to2_carry_13_052), .ow_cout(w_c4to2_cout_13_052)
);
wire w_c4to2_sum_13_053, w_c4to2_carry_13_053, w_c4to2_cout_13_053;
math_compressor_4to2 u_c4to2_13_053 (
    .i_x1(w_c4to2_sum_13_027), .i_x2(w_c4to2_sum_13_028),
    .i_x3(w_c4to2_carry_12_050), .i_x4(w_c4to2_cout_12_050),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_053), .ow_carry(w_c4to2_carry_13_053), .ow_cout(w_c4to2_cout_13_053)
);
wire w_c4to2_sum_14_054, w_c4to2_carry_14_054, w_c4to2_cout_14_054;
math_compressor_4to2 u_c4to2_14_054 (
    .i_x1(w_c4to2_cout_13_027), .i_x2(w_c4to2_carry_13_028),
    .i_x3(w_c4to2_cout_13_028), .i_x4(w_c4to2_sum_14_029),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_054), .ow_carry(w_c4to2_carry_14_054), .ow_cout(w_c4to2_cout_14_054)
);
wire w_c4to2_sum_14_055, w_c4to2_carry_14_055, w_c4to2_cout_14_055;
math_compressor_4to2 u_c4to2_14_055 (
    .i_x1(w_c4to2_sum_14_030), .i_x2(w_c4to2_sum_14_031),
    .i_x3(w_c4to2_carry_13_052), .i_x4(w_c4to2_cout_13_052),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_055), .ow_carry(w_c4to2_carry_14_055), .ow_cout(w_c4to2_cout_14_055)
);
wire w_c4to2_sum_15_056, w_c4to2_carry_15_056, w_c4to2_cout_15_056;
math_compressor_4to2 u_c4to2_15_056 (
    .i_x1(w_c4to2_carry_14_030), .i_x2(w_c4to2_cout_14_030),
    .i_x3(w_c4to2_carry_14_031), .i_x4(w_c4to2_cout_14_031),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_15_056), .ow_carry(w_c4to2_carry_15_056), .ow_cout(w_c4to2_cout_15_056)
);
wire w_c4to2_sum_15_057, w_c4to2_carry_15_057, w_c4to2_cout_15_057;
math_compressor_4to2 u_c4to2_15_057 (
    .i_x1(w_c4to2_sum_15_032), .i_x2(w_c4to2_sum_15_033),
    .i_x3(w_c4to2_carry_14_054), .i_x4(w_c4to2_cout_14_054),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_15_057), .ow_carry(w_c4to2_carry_15_057), .ow_cout(w_c4to2_cout_15_057)
);
wire w_c4to2_sum_16_058, w_c4to2_carry_16_058, w_c4to2_cout_16_058;
math_compressor_4to2 u_c4to2_16_058 (
    .i_x1(w_pp_10_06), .i_x2(w_c4to2_carry_15_032),
    .i_x3(w_c4to2_cout_15_032), .i_x4(w_c4to2_carry_15_033),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_16_058), .ow_carry(w_c4to2_carry_16_058), .ow_cout(w_c4to2_cout_16_058)
);
wire w_c4to2_sum_16_059, w_c4to2_carry_16_059, w_c4to2_cout_16_059;
math_compressor_4to2 u_c4to2_16_059 (
    .i_x1(w_c4to2_cout_15_033), .i_x2(w_c4to2_sum_16_034),
    .i_x3(w_c4to2_carry_15_056), .i_x4(w_c4to2_cout_15_056),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_16_059), .ow_carry(w_c4to2_carry_16_059), .ow_cout(w_c4to2_cout_16_059)
);
wire w_c4to2_sum_17_060, w_c4to2_carry_17_060, w_c4to2_cout_17_060;
math_compressor_4to2 u_c4to2_17_060 (
    .i_x1(w_pp_07_10), .i_x2(w_pp_08_09),
    .i_x3(w_pp_09_08), .i_x4(w_pp_10_07),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_17_060), .ow_carry(w_c4to2_carry_17_060), .ow_cout(w_c4to2_cout_17_060)
);
wire w_c4to2_sum_17_061, w_c4to2_carry_17_061, w_c4to2_cout_17_061;
math_compressor_4to2 u_c4to2_17_061 (
    .i_x1(w_c4to2_carry_16_034), .i_x2(w_c4to2_cout_16_034),
    .i_x3(w_c4to2_carry_16_058), .i_x4(w_c4to2_cout_16_058),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_17_061), .ow_carry(w_c4to2_carry_17_061), .ow_cout(w_c4to2_cout_17_061)
);
wire w_c4to2_sum_18_062, w_c4to2_carry_18_062, w_c4to2_cout_18_062;
math_compressor_4to2 u_c4to2_18_062 (
    .i_x1(w_pp_08_10), .i_x2(w_pp_09_09),
    .i_x3(w_pp_10_08), .i_x4(w_c4to2_carry_17_060),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_18_062), .ow_carry(w_c4to2_carry_18_062), .ow_cout(w_c4to2_cout_18_062)
);

// Dadda Reduction Stage 4: height 4 -> 3

wire w_c4to2_sum_03_063, w_c4to2_carry_03_063, w_c4to2_cout_03_063;
math_compressor_4to2 u_c4to2_03_063 (
    .i_x1(w_pp_00_03), .i_x2(w_pp_01_02),
    .i_x3(w_pp_02_01), .i_x4(w_pp_03_00),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_03_063), .ow_carry(w_c4to2_carry_03_063), .ow_cout(w_c4to2_cout_03_063)
);
wire w_c4to2_sum_04_064, w_c4to2_carry_04_064, w_c4to2_cout_04_064;
math_compressor_4to2 u_c4to2_04_064 (
    .i_x1(w_pp_04_00), .i_x2(w_c4to2_sum_04_035),
    .i_x3(w_c4to2_carry_03_063), .i_x4(w_c4to2_cout_03_063),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_04_064), .ow_carry(w_c4to2_carry_04_064), .ow_cout(w_c4to2_cout_04_064)
);
wire w_c4to2_sum_05_065, w_c4to2_carry_05_065, w_c4to2_cout_05_065;
math_compressor_4to2 u_c4to2_05_065 (
    .i_x1(w_c4to2_sum_05_036), .i_x2(w_c4to2_sum_05_037),
    .i_x3(w_c4to2_carry_04_064), .i_x4(w_c4to2_cout_04_064),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_05_065), .ow_carry(w_c4to2_carry_05_065), .ow_cout(w_c4to2_cout_05_065)
);
wire w_c4to2_sum_06_066, w_c4to2_carry_06_066, w_c4to2_cout_06_066;
math_compressor_4to2 u_c4to2_06_066 (
    .i_x1(w_c4to2_sum_06_038), .i_x2(w_c4to2_sum_06_039),
    .i_x3(w_c4to2_carry_05_065), .i_x4(w_c4to2_cout_05_065),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_06_066), .ow_carry(w_c4to2_carry_06_066), .ow_cout(w_c4to2_cout_06_066)
);
wire w_c4to2_sum_07_067, w_c4to2_carry_07_067, w_c4to2_cout_07_067;
math_compressor_4to2 u_c4to2_07_067 (
    .i_x1(w_c4to2_sum_07_040), .i_x2(w_c4to2_sum_07_041),
    .i_x3(w_c4to2_carry_06_066), .i_x4(w_c4to2_cout_06_066),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_07_067), .ow_carry(w_c4to2_carry_07_067), .ow_cout(w_c4to2_cout_07_067)
);
wire w_c4to2_sum_08_068, w_c4to2_carry_08_068, w_c4to2_cout_08_068;
math_compressor_4to2 u_c4to2_08_068 (
    .i_x1(w_c4to2_sum_08_042), .i_x2(w_c4to2_sum_08_043),
    .i_x3(w_c4to2_carry_07_067), .i_x4(w_c4to2_cout_07_067),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_08_068), .ow_carry(w_c4to2_carry_08_068), .ow_cout(w_c4to2_cout_08_068)
);
wire w_c4to2_sum_09_069, w_c4to2_carry_09_069, w_c4to2_cout_09_069;
math_compressor_4to2 u_c4to2_09_069 (
    .i_x1(w_c4to2_sum_09_044), .i_x2(w_c4to2_sum_09_045),
    .i_x3(w_c4to2_carry_08_068), .i_x4(w_c4to2_cout_08_068),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_09_069), .ow_carry(w_c4to2_carry_09_069), .ow_cout(w_c4to2_cout_09_069)
);
wire w_c4to2_sum_10_070, w_c4to2_carry_10_070, w_c4to2_cout_10_070;
math_compressor_4to2 u_c4to2_10_070 (
    .i_x1(w_c4to2_sum_10_046), .i_x2(w_c4to2_sum_10_047),
    .i_x3(w_c4to2_carry_09_069), .i_x4(w_c4to2_cout_09_069),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_10_070), .ow_carry(w_c4to2_carry_10_070), .ow_cout(w_c4to2_cout_10_070)
);
wire w_c4to2_sum_11_071, w_c4to2_carry_11_071, w_c4to2_cout_11_071;
math_compressor_4to2 u_c4to2_11_071 (
    .i_x1(w_c4to2_cout_10_047), .i_x2(w_c4to2_sum_11_048),
    .i_x3(w_c4to2_sum_11_049), .i_x4(w_c4to2_carry_10_070),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_11_071), .ow_carry(w_c4to2_carry_11_071), .ow_cout(w_c4to2_cout_11_071)
);
wire w_c4to2_sum_12_072, w_c4to2_carry_12_072, w_c4to2_cout_12_072;
math_compressor_4to2 u_c4to2_12_072 (
    .i_x1(w_c4to2_sum_12_050), .i_x2(w_c4to2_sum_12_051),
    .i_x3(w_c4to2_carry_11_071), .i_x4(w_c4to2_cout_11_071),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_12_072), .ow_carry(w_c4to2_carry_12_072), .ow_cout(w_c4to2_cout_12_072)
);
wire w_c4to2_sum_13_073, w_c4to2_carry_13_073, w_c4to2_cout_13_073;
math_compressor_4to2 u_c4to2_13_073 (
    .i_x1(w_c4to2_carry_12_051), .i_x2(w_c4to2_cout_12_051),
    .i_x3(w_c4to2_sum_13_052), .i_x4(w_c4to2_sum_13_053),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_13_073), .ow_carry(w_c4to2_carry_13_073), .ow_cout(w_c4to2_cout_13_073)
);
wire w_c4to2_sum_14_074, w_c4to2_carry_14_074, w_c4to2_cout_14_074;
math_compressor_4to2 u_c4to2_14_074 (
    .i_x1(w_c4to2_carry_13_053), .i_x2(w_c4to2_cout_13_053),
    .i_x3(w_c4to2_sum_14_054), .i_x4(w_c4to2_sum_14_055),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_074), .ow_carry(w_c4to2_carry_14_074), .ow_cout(w_c4to2_cout_14_074)
);
wire w_c4to2_sum_15_075, w_c4to2_carry_15_075, w_c4to2_cout_15_075;
math_compressor_4to2 u_c4to2_15_075 (
    .i_x1(w_c4to2_carry_14_055), .i_x2(w_c4to2_cout_14_055),
    .i_x3(w_c4to2_sum_15_056), .i_x4(w_c4to2_sum_15_057),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_15_075), .ow_carry(w_c4to2_carry_15_075), .ow_cout(w_c4to2_cout_15_075)
);
wire w_c4to2_sum_16_076, w_c4to2_carry_16_076, w_c4to2_cout_16_076;
math_compressor_4to2 u_c4to2_16_076 (
    .i_x1(w_c4to2_carry_15_057), .i_x2(w_c4to2_cout_15_057),
    .i_x3(w_c4to2_sum_16_058), .i_x4(w_c4to2_sum_16_059),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_16_076), .ow_carry(w_c4to2_carry_16_076), .ow_cout(w_c4to2_cout_16_076)
);
wire w_c4to2_sum_17_077, w_c4to2_carry_17_077, w_c4to2_cout_17_077;
math_compressor_4to2 u_c4to2_17_077 (
    .i_x1(w_c4to2_carry_16_059), .i_x2(w_c4to2_cout_16_059),
    .i_x3(w_c4to2_sum_17_060), .i_x4(w_c4to2_sum_17_061),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_17_077), .ow_carry(w_c4to2_carry_17_077), .ow_cout(w_c4to2_cout_17_077)
);
wire w_c4to2_sum_18_078, w_c4to2_carry_18_078, w_c4to2_cout_18_078;
math_compressor_4to2 u_c4to2_18_078 (
    .i_x1(w_c4to2_cout_17_060), .i_x2(w_c4to2_carry_17_061),
    .i_x3(w_c4to2_cout_17_061), .i_x4(w_c4to2_sum_18_062),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_18_078), .ow_carry(w_c4to2_carry_18_078), .ow_cout(w_c4to2_cout_18_078)
);
wire w_c4to2_sum_19_079, w_c4to2_carry_19_079, w_c4to2_cout_19_079;
math_compressor_4to2 u_c4to2_19_079 (
    .i_x1(w_pp_09_10), .i_x2(w_pp_10_09),
    .i_x3(w_c4to2_carry_18_062), .i_x4(w_c4to2_cout_18_062),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_19_079), .ow_carry(w_c4to2_carry_19_079), .ow_cout(w_c4to2_cout_19_079)
);

// Dadda Reduction Stage 5: height 3 -> 2

wire w_fa_sum_02_000, w_fa_carry_02_000;
math_adder_full u_fa_02_000 (
    .i_a(w_pp_00_02), .i_b(w_pp_01_01), .i_c(w_pp_02_00),
    .ow_sum(w_fa_sum_02_000), .ow_carry(w_fa_carry_02_000)
);
wire w_fa_sum_13_001, w_fa_carry_13_001;
math_adder_full u_fa_13_001 (
    .i_a(w_c4to2_carry_12_072), .i_b(w_c4to2_cout_12_072), .i_c(w_c4to2_sum_13_073),
    .ow_sum(w_fa_sum_13_001), .ow_carry(w_fa_carry_13_001)
);
wire w_c4to2_sum_14_080, w_c4to2_carry_14_080, w_c4to2_cout_14_080;
math_compressor_4to2 u_c4to2_14_080 (
    .i_x1(w_c4to2_carry_13_073), .i_x2(w_c4to2_cout_13_073),
    .i_x3(w_c4to2_sum_14_074), .i_x4(w_fa_carry_13_001),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_14_080), .ow_carry(w_c4to2_carry_14_080), .ow_cout(w_c4to2_cout_14_080)
);
wire w_c4to2_sum_15_081, w_c4to2_carry_15_081, w_c4to2_cout_15_081;
math_compressor_4to2 u_c4to2_15_081 (
    .i_x1(w_c4to2_carry_14_074), .i_x2(w_c4to2_cout_14_074),
    .i_x3(w_c4to2_sum_15_075), .i_x4(w_c4to2_carry_14_080),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_15_081), .ow_carry(w_c4to2_carry_15_081), .ow_cout(w_c4to2_cout_15_081)
);
wire w_c4to2_sum_16_082, w_c4to2_carry_16_082, w_c4to2_cout_16_082;
math_compressor_4to2 u_c4to2_16_082 (
    .i_x1(w_c4to2_carry_15_075), .i_x2(w_c4to2_cout_15_075),
    .i_x3(w_c4to2_sum_16_076), .i_x4(w_c4to2_carry_15_081),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_16_082), .ow_carry(w_c4to2_carry_16_082), .ow_cout(w_c4to2_cout_16_082)
);
wire w_c4to2_sum_17_083, w_c4to2_carry_17_083, w_c4to2_cout_17_083;
math_compressor_4to2 u_c4to2_17_083 (
    .i_x1(w_c4to2_carry_16_076), .i_x2(w_c4to2_cout_16_076),
    .i_x3(w_c4to2_sum_17_077), .i_x4(w_c4to2_carry_16_082),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_17_083), .ow_carry(w_c4to2_carry_17_083), .ow_cout(w_c4to2_cout_17_083)
);
wire w_c4to2_sum_18_084, w_c4to2_carry_18_084, w_c4to2_cout_18_084;
math_compressor_4to2 u_c4to2_18_084 (
    .i_x1(w_c4to2_carry_17_077), .i_x2(w_c4to2_cout_17_077),
    .i_x3(w_c4to2_sum_18_078), .i_x4(w_c4to2_carry_17_083),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_18_084), .ow_carry(w_c4to2_carry_18_084), .ow_cout(w_c4to2_cout_18_084)
);
wire w_c4to2_sum_19_085, w_c4to2_carry_19_085, w_c4to2_cout_19_085;
math_compressor_4to2 u_c4to2_19_085 (
    .i_x1(w_c4to2_carry_18_078), .i_x2(w_c4to2_cout_18_078),
    .i_x3(w_c4to2_sum_19_079), .i_x4(w_c4to2_carry_18_084),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_19_085), .ow_carry(w_c4to2_carry_19_085), .ow_cout(w_c4to2_cout_19_085)
);
wire w_c4to2_sum_20_086, w_c4to2_carry_20_086, w_c4to2_cout_20_086;
math_compressor_4to2 u_c4to2_20_086 (
    .i_x1(w_pp_10_10), .i_x2(w_c4to2_carry_19_079),
    .i_x3(w_c4to2_cout_19_079), .i_x4(w_c4to2_carry_19_085),
    .i_cin(1'b0),
    .ow_sum(w_c4to2_sum_20_086), .ow_carry(w_c4to2_carry_20_086), .ow_cout(w_c4to2_cout_20_086)
);

// Final CPA: Two operands from reduction tree
wire [2*N-1:0] w_cpa_a, w_cpa_b;
assign w_cpa_a[0] = w_pp_00_00;
assign w_cpa_b[0] = 1'b0;
assign w_cpa_a[1] = w_pp_00_01;
assign w_cpa_b[1] = w_pp_01_00;
assign w_cpa_a[2] = w_fa_sum_02_000;
assign w_cpa_b[2] = 1'b0;
assign w_cpa_a[3] = w_c4to2_sum_03_063;
assign w_cpa_b[3] = w_fa_carry_02_000;
assign w_cpa_a[4] = w_c4to2_sum_04_064;
assign w_cpa_b[4] = 1'b0;
assign w_cpa_a[5] = w_c4to2_sum_05_065;
assign w_cpa_b[5] = 1'b0;
assign w_cpa_a[6] = w_c4to2_sum_06_066;
assign w_cpa_b[6] = 1'b0;
assign w_cpa_a[7] = w_c4to2_sum_07_067;
assign w_cpa_b[7] = 1'b0;
assign w_cpa_a[8] = w_c4to2_sum_08_068;
assign w_cpa_b[8] = 1'b0;
assign w_cpa_a[9] = w_c4to2_sum_09_069;
assign w_cpa_b[9] = 1'b0;
assign w_cpa_a[10] = w_c4to2_sum_10_070;
assign w_cpa_b[10] = 1'b0;
assign w_cpa_a[11] = w_c4to2_cout_10_070;
assign w_cpa_b[11] = w_c4to2_sum_11_071;
assign w_cpa_a[12] = w_c4to2_sum_12_072;
assign w_cpa_b[12] = 1'b0;
assign w_cpa_a[13] = w_fa_sum_13_001;
assign w_cpa_b[13] = 1'b0;
assign w_cpa_a[14] = w_c4to2_sum_14_080;
assign w_cpa_b[14] = 1'b0;
assign w_cpa_a[15] = w_c4to2_cout_14_080;
assign w_cpa_b[15] = w_c4to2_sum_15_081;
assign w_cpa_a[16] = w_c4to2_cout_15_081;
assign w_cpa_b[16] = w_c4to2_sum_16_082;
assign w_cpa_a[17] = w_c4to2_cout_16_082;
assign w_cpa_b[17] = w_c4to2_sum_17_083;
assign w_cpa_a[18] = w_c4to2_cout_17_083;
assign w_cpa_b[18] = w_c4to2_sum_18_084;
assign w_cpa_a[19] = w_c4to2_cout_18_084;
assign w_cpa_b[19] = w_c4to2_sum_19_085;
assign w_cpa_a[20] = w_c4to2_cout_19_085;
assign w_cpa_b[20] = w_c4to2_sum_20_086;
assign w_cpa_a[21] = w_c4to2_carry_20_086;
assign w_cpa_b[21] = w_c4to2_cout_20_086;

// Han-Carlson prefix adder for final CPA
wire w_cpa_cout;  // Unused for unsigned multiply
math_adder_han_carlson_022 u_final_cpa (
    .i_a(w_cpa_a),
    .i_b(w_cpa_b),
    .i_cin(1'b0),
    .ow_sum(ow_product),
    .ow_cout(w_cpa_cout)
);

endmodule
