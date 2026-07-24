// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_multiplier_wallace_tree_016
// Purpose: Math Multiplier Wallace Tree 016 module
//
// Documentation: docs/markdown/RTLCommon/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_multiplier_wallace_tree_016 #(
    parameter int N = 16
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);

    // Partial Products
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
    wire w_pp_00_11 = i_multiplier[0] & i_multiplicand[11];
    wire w_pp_00_12 = i_multiplier[0] & i_multiplicand[12];
    wire w_pp_00_13 = i_multiplier[0] & i_multiplicand[13];
    wire w_pp_00_14 = i_multiplier[0] & i_multiplicand[14];
    wire w_pp_00_15 = i_multiplier[0] & i_multiplicand[15];
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
    wire w_pp_01_11 = i_multiplier[1] & i_multiplicand[11];
    wire w_pp_01_12 = i_multiplier[1] & i_multiplicand[12];
    wire w_pp_01_13 = i_multiplier[1] & i_multiplicand[13];
    wire w_pp_01_14 = i_multiplier[1] & i_multiplicand[14];
    wire w_pp_01_15 = i_multiplier[1] & i_multiplicand[15];
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
    wire w_pp_02_11 = i_multiplier[2] & i_multiplicand[11];
    wire w_pp_02_12 = i_multiplier[2] & i_multiplicand[12];
    wire w_pp_02_13 = i_multiplier[2] & i_multiplicand[13];
    wire w_pp_02_14 = i_multiplier[2] & i_multiplicand[14];
    wire w_pp_02_15 = i_multiplier[2] & i_multiplicand[15];
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
    wire w_pp_03_11 = i_multiplier[3] & i_multiplicand[11];
    wire w_pp_03_12 = i_multiplier[3] & i_multiplicand[12];
    wire w_pp_03_13 = i_multiplier[3] & i_multiplicand[13];
    wire w_pp_03_14 = i_multiplier[3] & i_multiplicand[14];
    wire w_pp_03_15 = i_multiplier[3] & i_multiplicand[15];
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
    wire w_pp_04_11 = i_multiplier[4] & i_multiplicand[11];
    wire w_pp_04_12 = i_multiplier[4] & i_multiplicand[12];
    wire w_pp_04_13 = i_multiplier[4] & i_multiplicand[13];
    wire w_pp_04_14 = i_multiplier[4] & i_multiplicand[14];
    wire w_pp_04_15 = i_multiplier[4] & i_multiplicand[15];
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
    wire w_pp_05_11 = i_multiplier[5] & i_multiplicand[11];
    wire w_pp_05_12 = i_multiplier[5] & i_multiplicand[12];
    wire w_pp_05_13 = i_multiplier[5] & i_multiplicand[13];
    wire w_pp_05_14 = i_multiplier[5] & i_multiplicand[14];
    wire w_pp_05_15 = i_multiplier[5] & i_multiplicand[15];
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
    wire w_pp_06_11 = i_multiplier[6] & i_multiplicand[11];
    wire w_pp_06_12 = i_multiplier[6] & i_multiplicand[12];
    wire w_pp_06_13 = i_multiplier[6] & i_multiplicand[13];
    wire w_pp_06_14 = i_multiplier[6] & i_multiplicand[14];
    wire w_pp_06_15 = i_multiplier[6] & i_multiplicand[15];
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
    wire w_pp_07_11 = i_multiplier[7] & i_multiplicand[11];
    wire w_pp_07_12 = i_multiplier[7] & i_multiplicand[12];
    wire w_pp_07_13 = i_multiplier[7] & i_multiplicand[13];
    wire w_pp_07_14 = i_multiplier[7] & i_multiplicand[14];
    wire w_pp_07_15 = i_multiplier[7] & i_multiplicand[15];
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
    wire w_pp_08_11 = i_multiplier[8] & i_multiplicand[11];
    wire w_pp_08_12 = i_multiplier[8] & i_multiplicand[12];
    wire w_pp_08_13 = i_multiplier[8] & i_multiplicand[13];
    wire w_pp_08_14 = i_multiplier[8] & i_multiplicand[14];
    wire w_pp_08_15 = i_multiplier[8] & i_multiplicand[15];
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
    wire w_pp_09_11 = i_multiplier[9] & i_multiplicand[11];
    wire w_pp_09_12 = i_multiplier[9] & i_multiplicand[12];
    wire w_pp_09_13 = i_multiplier[9] & i_multiplicand[13];
    wire w_pp_09_14 = i_multiplier[9] & i_multiplicand[14];
    wire w_pp_09_15 = i_multiplier[9] & i_multiplicand[15];
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
    wire w_pp_10_11 = i_multiplier[10] & i_multiplicand[11];
    wire w_pp_10_12 = i_multiplier[10] & i_multiplicand[12];
    wire w_pp_10_13 = i_multiplier[10] & i_multiplicand[13];
    wire w_pp_10_14 = i_multiplier[10] & i_multiplicand[14];
    wire w_pp_10_15 = i_multiplier[10] & i_multiplicand[15];
    wire w_pp_11_00 = i_multiplier[11] & i_multiplicand[0];
    wire w_pp_11_01 = i_multiplier[11] & i_multiplicand[1];
    wire w_pp_11_02 = i_multiplier[11] & i_multiplicand[2];
    wire w_pp_11_03 = i_multiplier[11] & i_multiplicand[3];
    wire w_pp_11_04 = i_multiplier[11] & i_multiplicand[4];
    wire w_pp_11_05 = i_multiplier[11] & i_multiplicand[5];
    wire w_pp_11_06 = i_multiplier[11] & i_multiplicand[6];
    wire w_pp_11_07 = i_multiplier[11] & i_multiplicand[7];
    wire w_pp_11_08 = i_multiplier[11] & i_multiplicand[8];
    wire w_pp_11_09 = i_multiplier[11] & i_multiplicand[9];
    wire w_pp_11_10 = i_multiplier[11] & i_multiplicand[10];
    wire w_pp_11_11 = i_multiplier[11] & i_multiplicand[11];
    wire w_pp_11_12 = i_multiplier[11] & i_multiplicand[12];
    wire w_pp_11_13 = i_multiplier[11] & i_multiplicand[13];
    wire w_pp_11_14 = i_multiplier[11] & i_multiplicand[14];
    wire w_pp_11_15 = i_multiplier[11] & i_multiplicand[15];
    wire w_pp_12_00 = i_multiplier[12] & i_multiplicand[0];
    wire w_pp_12_01 = i_multiplier[12] & i_multiplicand[1];
    wire w_pp_12_02 = i_multiplier[12] & i_multiplicand[2];
    wire w_pp_12_03 = i_multiplier[12] & i_multiplicand[3];
    wire w_pp_12_04 = i_multiplier[12] & i_multiplicand[4];
    wire w_pp_12_05 = i_multiplier[12] & i_multiplicand[5];
    wire w_pp_12_06 = i_multiplier[12] & i_multiplicand[6];
    wire w_pp_12_07 = i_multiplier[12] & i_multiplicand[7];
    wire w_pp_12_08 = i_multiplier[12] & i_multiplicand[8];
    wire w_pp_12_09 = i_multiplier[12] & i_multiplicand[9];
    wire w_pp_12_10 = i_multiplier[12] & i_multiplicand[10];
    wire w_pp_12_11 = i_multiplier[12] & i_multiplicand[11];
    wire w_pp_12_12 = i_multiplier[12] & i_multiplicand[12];
    wire w_pp_12_13 = i_multiplier[12] & i_multiplicand[13];
    wire w_pp_12_14 = i_multiplier[12] & i_multiplicand[14];
    wire w_pp_12_15 = i_multiplier[12] & i_multiplicand[15];
    wire w_pp_13_00 = i_multiplier[13] & i_multiplicand[0];
    wire w_pp_13_01 = i_multiplier[13] & i_multiplicand[1];
    wire w_pp_13_02 = i_multiplier[13] & i_multiplicand[2];
    wire w_pp_13_03 = i_multiplier[13] & i_multiplicand[3];
    wire w_pp_13_04 = i_multiplier[13] & i_multiplicand[4];
    wire w_pp_13_05 = i_multiplier[13] & i_multiplicand[5];
    wire w_pp_13_06 = i_multiplier[13] & i_multiplicand[6];
    wire w_pp_13_07 = i_multiplier[13] & i_multiplicand[7];
    wire w_pp_13_08 = i_multiplier[13] & i_multiplicand[8];
    wire w_pp_13_09 = i_multiplier[13] & i_multiplicand[9];
    wire w_pp_13_10 = i_multiplier[13] & i_multiplicand[10];
    wire w_pp_13_11 = i_multiplier[13] & i_multiplicand[11];
    wire w_pp_13_12 = i_multiplier[13] & i_multiplicand[12];
    wire w_pp_13_13 = i_multiplier[13] & i_multiplicand[13];
    wire w_pp_13_14 = i_multiplier[13] & i_multiplicand[14];
    wire w_pp_13_15 = i_multiplier[13] & i_multiplicand[15];
    wire w_pp_14_00 = i_multiplier[14] & i_multiplicand[0];
    wire w_pp_14_01 = i_multiplier[14] & i_multiplicand[1];
    wire w_pp_14_02 = i_multiplier[14] & i_multiplicand[2];
    wire w_pp_14_03 = i_multiplier[14] & i_multiplicand[3];
    wire w_pp_14_04 = i_multiplier[14] & i_multiplicand[4];
    wire w_pp_14_05 = i_multiplier[14] & i_multiplicand[5];
    wire w_pp_14_06 = i_multiplier[14] & i_multiplicand[6];
    wire w_pp_14_07 = i_multiplier[14] & i_multiplicand[7];
    wire w_pp_14_08 = i_multiplier[14] & i_multiplicand[8];
    wire w_pp_14_09 = i_multiplier[14] & i_multiplicand[9];
    wire w_pp_14_10 = i_multiplier[14] & i_multiplicand[10];
    wire w_pp_14_11 = i_multiplier[14] & i_multiplicand[11];
    wire w_pp_14_12 = i_multiplier[14] & i_multiplicand[12];
    wire w_pp_14_13 = i_multiplier[14] & i_multiplicand[13];
    wire w_pp_14_14 = i_multiplier[14] & i_multiplicand[14];
    wire w_pp_14_15 = i_multiplier[14] & i_multiplicand[15];
    wire w_pp_15_00 = i_multiplier[15] & i_multiplicand[0];
    wire w_pp_15_01 = i_multiplier[15] & i_multiplicand[1];
    wire w_pp_15_02 = i_multiplier[15] & i_multiplicand[2];
    wire w_pp_15_03 = i_multiplier[15] & i_multiplicand[3];
    wire w_pp_15_04 = i_multiplier[15] & i_multiplicand[4];
    wire w_pp_15_05 = i_multiplier[15] & i_multiplicand[5];
    wire w_pp_15_06 = i_multiplier[15] & i_multiplicand[6];
    wire w_pp_15_07 = i_multiplier[15] & i_multiplicand[7];
    wire w_pp_15_08 = i_multiplier[15] & i_multiplicand[8];
    wire w_pp_15_09 = i_multiplier[15] & i_multiplicand[9];
    wire w_pp_15_10 = i_multiplier[15] & i_multiplicand[10];
    wire w_pp_15_11 = i_multiplier[15] & i_multiplicand[11];
    wire w_pp_15_12 = i_multiplier[15] & i_multiplicand[12];
    wire w_pp_15_13 = i_multiplier[15] & i_multiplicand[13];
    wire w_pp_15_14 = i_multiplier[15] & i_multiplicand[14];
    wire w_pp_15_15 = i_multiplier[15] & i_multiplicand[15];

    // Partial products reduction using Wallace tree
    // Wallace reduction layer 1
    wire w_sum_01_1_01, w_carry_01_1_01;
    math_adder_half HA_01_1_01 (
        .i_a(w_pp_00_01),
        .i_b(w_pp_01_00),
        .ow_sum(w_sum_01_1_01),
        .ow_carry(w_carry_01_1_01)
    );
    wire w_sum_02_1_01, w_carry_02_1_01;
    math_adder_full FA_02_1_01 (
        .i_a(w_pp_00_02),
        .i_b(w_pp_01_01),
        .i_c(w_pp_02_00),
        .ow_sum(w_sum_02_1_01),
        .ow_carry(w_carry_02_1_01)
    );
    wire w_sum_03_1_01, w_carry_03_1_01;
    math_adder_full FA_03_1_01 (
        .i_a(w_pp_00_03),
        .i_b(w_pp_01_02),
        .i_c(w_pp_02_01),
        .ow_sum(w_sum_03_1_01),
        .ow_carry(w_carry_03_1_01)
    );
    wire w_sum_04_1_01, w_carry_04_1_01;
    math_adder_full FA_04_1_01 (
        .i_a(w_pp_00_04),
        .i_b(w_pp_01_03),
        .i_c(w_pp_02_02),
        .ow_sum(w_sum_04_1_01),
        .ow_carry(w_carry_04_1_01)
    );
    wire w_sum_04_1_02, w_carry_04_1_02;
    math_adder_half HA_04_1_02 (
        .i_a(w_pp_03_01),
        .i_b(w_pp_04_00),
        .ow_sum(w_sum_04_1_02),
        .ow_carry(w_carry_04_1_02)
    );
    wire w_sum_05_1_01, w_carry_05_1_01;
    math_adder_full FA_05_1_01 (
        .i_a(w_pp_00_05),
        .i_b(w_pp_01_04),
        .i_c(w_pp_02_03),
        .ow_sum(w_sum_05_1_01),
        .ow_carry(w_carry_05_1_01)
    );
    wire w_sum_05_1_02, w_carry_05_1_02;
    math_adder_full FA_05_1_02 (
        .i_a(w_pp_03_02),
        .i_b(w_pp_04_01),
        .i_c(w_pp_05_00),
        .ow_sum(w_sum_05_1_02),
        .ow_carry(w_carry_05_1_02)
    );
    wire w_sum_06_1_01, w_carry_06_1_01;
    math_adder_full FA_06_1_01 (
        .i_a(w_pp_00_06),
        .i_b(w_pp_01_05),
        .i_c(w_pp_02_04),
        .ow_sum(w_sum_06_1_01),
        .ow_carry(w_carry_06_1_01)
    );
    wire w_sum_06_1_02, w_carry_06_1_02;
    math_adder_full FA_06_1_02 (
        .i_a(w_pp_03_03),
        .i_b(w_pp_04_02),
        .i_c(w_pp_05_01),
        .ow_sum(w_sum_06_1_02),
        .ow_carry(w_carry_06_1_02)
    );
    wire w_sum_07_1_01, w_carry_07_1_01;
    math_adder_full FA_07_1_01 (
        .i_a(w_pp_00_07),
        .i_b(w_pp_01_06),
        .i_c(w_pp_02_05),
        .ow_sum(w_sum_07_1_01),
        .ow_carry(w_carry_07_1_01)
    );
    wire w_sum_07_1_02, w_carry_07_1_02;
    math_adder_full FA_07_1_02 (
        .i_a(w_pp_03_04),
        .i_b(w_pp_04_03),
        .i_c(w_pp_05_02),
        .ow_sum(w_sum_07_1_02),
        .ow_carry(w_carry_07_1_02)
    );
    wire w_sum_07_1_03, w_carry_07_1_03;
    math_adder_half HA_07_1_03 (
        .i_a(w_pp_06_01),
        .i_b(w_pp_07_00),
        .ow_sum(w_sum_07_1_03),
        .ow_carry(w_carry_07_1_03)
    );
    wire w_sum_08_1_01, w_carry_08_1_01;
    math_adder_full FA_08_1_01 (
        .i_a(w_pp_00_08),
        .i_b(w_pp_01_07),
        .i_c(w_pp_02_06),
        .ow_sum(w_sum_08_1_01),
        .ow_carry(w_carry_08_1_01)
    );
    wire w_sum_08_1_02, w_carry_08_1_02;
    math_adder_full FA_08_1_02 (
        .i_a(w_pp_03_05),
        .i_b(w_pp_04_04),
        .i_c(w_pp_05_03),
        .ow_sum(w_sum_08_1_02),
        .ow_carry(w_carry_08_1_02)
    );
    wire w_sum_08_1_03, w_carry_08_1_03;
    math_adder_full FA_08_1_03 (
        .i_a(w_pp_06_02),
        .i_b(w_pp_07_01),
        .i_c(w_pp_08_00),
        .ow_sum(w_sum_08_1_03),
        .ow_carry(w_carry_08_1_03)
    );
    wire w_sum_09_1_01, w_carry_09_1_01;
    math_adder_full FA_09_1_01 (
        .i_a(w_pp_00_09),
        .i_b(w_pp_01_08),
        .i_c(w_pp_02_07),
        .ow_sum(w_sum_09_1_01),
        .ow_carry(w_carry_09_1_01)
    );
    wire w_sum_09_1_02, w_carry_09_1_02;
    math_adder_full FA_09_1_02 (
        .i_a(w_pp_03_06),
        .i_b(w_pp_04_05),
        .i_c(w_pp_05_04),
        .ow_sum(w_sum_09_1_02),
        .ow_carry(w_carry_09_1_02)
    );
    wire w_sum_09_1_03, w_carry_09_1_03;
    math_adder_full FA_09_1_03 (
        .i_a(w_pp_06_03),
        .i_b(w_pp_07_02),
        .i_c(w_pp_08_01),
        .ow_sum(w_sum_09_1_03),
        .ow_carry(w_carry_09_1_03)
    );
    wire w_sum_10_1_01, w_carry_10_1_01;
    math_adder_full FA_10_1_01 (
        .i_a(w_pp_00_10),
        .i_b(w_pp_01_09),
        .i_c(w_pp_02_08),
        .ow_sum(w_sum_10_1_01),
        .ow_carry(w_carry_10_1_01)
    );
    wire w_sum_10_1_02, w_carry_10_1_02;
    math_adder_full FA_10_1_02 (
        .i_a(w_pp_03_07),
        .i_b(w_pp_04_06),
        .i_c(w_pp_05_05),
        .ow_sum(w_sum_10_1_02),
        .ow_carry(w_carry_10_1_02)
    );
    wire w_sum_10_1_03, w_carry_10_1_03;
    math_adder_full FA_10_1_03 (
        .i_a(w_pp_06_04),
        .i_b(w_pp_07_03),
        .i_c(w_pp_08_02),
        .ow_sum(w_sum_10_1_03),
        .ow_carry(w_carry_10_1_03)
    );
    wire w_sum_10_1_04, w_carry_10_1_04;
    math_adder_half HA_10_1_04 (
        .i_a(w_pp_09_01),
        .i_b(w_pp_10_00),
        .ow_sum(w_sum_10_1_04),
        .ow_carry(w_carry_10_1_04)
    );
    wire w_sum_11_1_01, w_carry_11_1_01;
    math_adder_full FA_11_1_01 (
        .i_a(w_pp_00_11),
        .i_b(w_pp_01_10),
        .i_c(w_pp_02_09),
        .ow_sum(w_sum_11_1_01),
        .ow_carry(w_carry_11_1_01)
    );
    wire w_sum_11_1_02, w_carry_11_1_02;
    math_adder_full FA_11_1_02 (
        .i_a(w_pp_03_08),
        .i_b(w_pp_04_07),
        .i_c(w_pp_05_06),
        .ow_sum(w_sum_11_1_02),
        .ow_carry(w_carry_11_1_02)
    );
    wire w_sum_11_1_03, w_carry_11_1_03;
    math_adder_full FA_11_1_03 (
        .i_a(w_pp_06_05),
        .i_b(w_pp_07_04),
        .i_c(w_pp_08_03),
        .ow_sum(w_sum_11_1_03),
        .ow_carry(w_carry_11_1_03)
    );
    wire w_sum_11_1_04, w_carry_11_1_04;
    math_adder_full FA_11_1_04 (
        .i_a(w_pp_09_02),
        .i_b(w_pp_10_01),
        .i_c(w_pp_11_00),
        .ow_sum(w_sum_11_1_04),
        .ow_carry(w_carry_11_1_04)
    );
    wire w_sum_12_1_01, w_carry_12_1_01;
    math_adder_full FA_12_1_01 (
        .i_a(w_pp_00_12),
        .i_b(w_pp_01_11),
        .i_c(w_pp_02_10),
        .ow_sum(w_sum_12_1_01),
        .ow_carry(w_carry_12_1_01)
    );
    wire w_sum_12_1_02, w_carry_12_1_02;
    math_adder_full FA_12_1_02 (
        .i_a(w_pp_03_09),
        .i_b(w_pp_04_08),
        .i_c(w_pp_05_07),
        .ow_sum(w_sum_12_1_02),
        .ow_carry(w_carry_12_1_02)
    );
    wire w_sum_12_1_03, w_carry_12_1_03;
    math_adder_full FA_12_1_03 (
        .i_a(w_pp_06_06),
        .i_b(w_pp_07_05),
        .i_c(w_pp_08_04),
        .ow_sum(w_sum_12_1_03),
        .ow_carry(w_carry_12_1_03)
    );
    wire w_sum_12_1_04, w_carry_12_1_04;
    math_adder_full FA_12_1_04 (
        .i_a(w_pp_09_03),
        .i_b(w_pp_10_02),
        .i_c(w_pp_11_01),
        .ow_sum(w_sum_12_1_04),
        .ow_carry(w_carry_12_1_04)
    );
    wire w_sum_13_1_01, w_carry_13_1_01;
    math_adder_full FA_13_1_01 (
        .i_a(w_pp_00_13),
        .i_b(w_pp_01_12),
        .i_c(w_pp_02_11),
        .ow_sum(w_sum_13_1_01),
        .ow_carry(w_carry_13_1_01)
    );
    wire w_sum_13_1_02, w_carry_13_1_02;
    math_adder_full FA_13_1_02 (
        .i_a(w_pp_03_10),
        .i_b(w_pp_04_09),
        .i_c(w_pp_05_08),
        .ow_sum(w_sum_13_1_02),
        .ow_carry(w_carry_13_1_02)
    );
    wire w_sum_13_1_03, w_carry_13_1_03;
    math_adder_full FA_13_1_03 (
        .i_a(w_pp_06_07),
        .i_b(w_pp_07_06),
        .i_c(w_pp_08_05),
        .ow_sum(w_sum_13_1_03),
        .ow_carry(w_carry_13_1_03)
    );
    wire w_sum_13_1_04, w_carry_13_1_04;
    math_adder_full FA_13_1_04 (
        .i_a(w_pp_09_04),
        .i_b(w_pp_10_03),
        .i_c(w_pp_11_02),
        .ow_sum(w_sum_13_1_04),
        .ow_carry(w_carry_13_1_04)
    );
    wire w_sum_13_1_05, w_carry_13_1_05;
    math_adder_half HA_13_1_05 (
        .i_a(w_pp_12_01),
        .i_b(w_pp_13_00),
        .ow_sum(w_sum_13_1_05),
        .ow_carry(w_carry_13_1_05)
    );
    wire w_sum_14_1_01, w_carry_14_1_01;
    math_adder_full FA_14_1_01 (
        .i_a(w_pp_00_14),
        .i_b(w_pp_01_13),
        .i_c(w_pp_02_12),
        .ow_sum(w_sum_14_1_01),
        .ow_carry(w_carry_14_1_01)
    );
    wire w_sum_14_1_02, w_carry_14_1_02;
    math_adder_full FA_14_1_02 (
        .i_a(w_pp_03_11),
        .i_b(w_pp_04_10),
        .i_c(w_pp_05_09),
        .ow_sum(w_sum_14_1_02),
        .ow_carry(w_carry_14_1_02)
    );
    wire w_sum_14_1_03, w_carry_14_1_03;
    math_adder_full FA_14_1_03 (
        .i_a(w_pp_06_08),
        .i_b(w_pp_07_07),
        .i_c(w_pp_08_06),
        .ow_sum(w_sum_14_1_03),
        .ow_carry(w_carry_14_1_03)
    );
    wire w_sum_14_1_04, w_carry_14_1_04;
    math_adder_full FA_14_1_04 (
        .i_a(w_pp_09_05),
        .i_b(w_pp_10_04),
        .i_c(w_pp_11_03),
        .ow_sum(w_sum_14_1_04),
        .ow_carry(w_carry_14_1_04)
    );
    wire w_sum_14_1_05, w_carry_14_1_05;
    math_adder_full FA_14_1_05 (
        .i_a(w_pp_12_02),
        .i_b(w_pp_13_01),
        .i_c(w_pp_14_00),
        .ow_sum(w_sum_14_1_05),
        .ow_carry(w_carry_14_1_05)
    );
    wire w_sum_15_1_01, w_carry_15_1_01;
    math_adder_full FA_15_1_01 (
        .i_a(w_pp_00_15),
        .i_b(w_pp_01_14),
        .i_c(w_pp_02_13),
        .ow_sum(w_sum_15_1_01),
        .ow_carry(w_carry_15_1_01)
    );
    wire w_sum_15_1_02, w_carry_15_1_02;
    math_adder_full FA_15_1_02 (
        .i_a(w_pp_03_12),
        .i_b(w_pp_04_11),
        .i_c(w_pp_05_10),
        .ow_sum(w_sum_15_1_02),
        .ow_carry(w_carry_15_1_02)
    );
    wire w_sum_15_1_03, w_carry_15_1_03;
    math_adder_full FA_15_1_03 (
        .i_a(w_pp_06_09),
        .i_b(w_pp_07_08),
        .i_c(w_pp_08_07),
        .ow_sum(w_sum_15_1_03),
        .ow_carry(w_carry_15_1_03)
    );
    wire w_sum_15_1_04, w_carry_15_1_04;
    math_adder_full FA_15_1_04 (
        .i_a(w_pp_09_06),
        .i_b(w_pp_10_05),
        .i_c(w_pp_11_04),
        .ow_sum(w_sum_15_1_04),
        .ow_carry(w_carry_15_1_04)
    );
    wire w_sum_15_1_05, w_carry_15_1_05;
    math_adder_full FA_15_1_05 (
        .i_a(w_pp_12_03),
        .i_b(w_pp_13_02),
        .i_c(w_pp_14_01),
        .ow_sum(w_sum_15_1_05),
        .ow_carry(w_carry_15_1_05)
    );
    wire w_sum_16_1_01, w_carry_16_1_01;
    math_adder_full FA_16_1_01 (
        .i_a(w_pp_01_15),
        .i_b(w_pp_02_14),
        .i_c(w_pp_03_13),
        .ow_sum(w_sum_16_1_01),
        .ow_carry(w_carry_16_1_01)
    );
    wire w_sum_16_1_02, w_carry_16_1_02;
    math_adder_full FA_16_1_02 (
        .i_a(w_pp_04_12),
        .i_b(w_pp_05_11),
        .i_c(w_pp_06_10),
        .ow_sum(w_sum_16_1_02),
        .ow_carry(w_carry_16_1_02)
    );
    wire w_sum_16_1_03, w_carry_16_1_03;
    math_adder_full FA_16_1_03 (
        .i_a(w_pp_07_09),
        .i_b(w_pp_08_08),
        .i_c(w_pp_09_07),
        .ow_sum(w_sum_16_1_03),
        .ow_carry(w_carry_16_1_03)
    );
    wire w_sum_16_1_04, w_carry_16_1_04;
    math_adder_full FA_16_1_04 (
        .i_a(w_pp_10_06),
        .i_b(w_pp_11_05),
        .i_c(w_pp_12_04),
        .ow_sum(w_sum_16_1_04),
        .ow_carry(w_carry_16_1_04)
    );
    wire w_sum_16_1_05, w_carry_16_1_05;
    math_adder_full FA_16_1_05 (
        .i_a(w_pp_13_03),
        .i_b(w_pp_14_02),
        .i_c(w_pp_15_01),
        .ow_sum(w_sum_16_1_05),
        .ow_carry(w_carry_16_1_05)
    );
    wire w_sum_17_1_01, w_carry_17_1_01;
    math_adder_full FA_17_1_01 (
        .i_a(w_pp_02_15),
        .i_b(w_pp_03_14),
        .i_c(w_pp_04_13),
        .ow_sum(w_sum_17_1_01),
        .ow_carry(w_carry_17_1_01)
    );
    wire w_sum_17_1_02, w_carry_17_1_02;
    math_adder_full FA_17_1_02 (
        .i_a(w_pp_05_12),
        .i_b(w_pp_06_11),
        .i_c(w_pp_07_10),
        .ow_sum(w_sum_17_1_02),
        .ow_carry(w_carry_17_1_02)
    );
    wire w_sum_17_1_03, w_carry_17_1_03;
    math_adder_full FA_17_1_03 (
        .i_a(w_pp_08_09),
        .i_b(w_pp_09_08),
        .i_c(w_pp_10_07),
        .ow_sum(w_sum_17_1_03),
        .ow_carry(w_carry_17_1_03)
    );
    wire w_sum_17_1_04, w_carry_17_1_04;
    math_adder_full FA_17_1_04 (
        .i_a(w_pp_11_06),
        .i_b(w_pp_12_05),
        .i_c(w_pp_13_04),
        .ow_sum(w_sum_17_1_04),
        .ow_carry(w_carry_17_1_04)
    );
    wire w_sum_17_1_05, w_carry_17_1_05;
    math_adder_half HA_17_1_05 (
        .i_a(w_pp_14_03),
        .i_b(w_pp_15_02),
        .ow_sum(w_sum_17_1_05),
        .ow_carry(w_carry_17_1_05)
    );
    wire w_sum_18_1_01, w_carry_18_1_01;
    math_adder_full FA_18_1_01 (
        .i_a(w_pp_03_15),
        .i_b(w_pp_04_14),
        .i_c(w_pp_05_13),
        .ow_sum(w_sum_18_1_01),
        .ow_carry(w_carry_18_1_01)
    );
    wire w_sum_18_1_02, w_carry_18_1_02;
    math_adder_full FA_18_1_02 (
        .i_a(w_pp_06_12),
        .i_b(w_pp_07_11),
        .i_c(w_pp_08_10),
        .ow_sum(w_sum_18_1_02),
        .ow_carry(w_carry_18_1_02)
    );
    wire w_sum_18_1_03, w_carry_18_1_03;
    math_adder_full FA_18_1_03 (
        .i_a(w_pp_09_09),
        .i_b(w_pp_10_08),
        .i_c(w_pp_11_07),
        .ow_sum(w_sum_18_1_03),
        .ow_carry(w_carry_18_1_03)
    );
    wire w_sum_18_1_04, w_carry_18_1_04;
    math_adder_full FA_18_1_04 (
        .i_a(w_pp_12_06),
        .i_b(w_pp_13_05),
        .i_c(w_pp_14_04),
        .ow_sum(w_sum_18_1_04),
        .ow_carry(w_carry_18_1_04)
    );
    wire w_sum_19_1_01, w_carry_19_1_01;
    math_adder_full FA_19_1_01 (
        .i_a(w_pp_04_15),
        .i_b(w_pp_05_14),
        .i_c(w_pp_06_13),
        .ow_sum(w_sum_19_1_01),
        .ow_carry(w_carry_19_1_01)
    );
    wire w_sum_19_1_02, w_carry_19_1_02;
    math_adder_full FA_19_1_02 (
        .i_a(w_pp_07_12),
        .i_b(w_pp_08_11),
        .i_c(w_pp_09_10),
        .ow_sum(w_sum_19_1_02),
        .ow_carry(w_carry_19_1_02)
    );
    wire w_sum_19_1_03, w_carry_19_1_03;
    math_adder_full FA_19_1_03 (
        .i_a(w_pp_10_09),
        .i_b(w_pp_11_08),
        .i_c(w_pp_12_07),
        .ow_sum(w_sum_19_1_03),
        .ow_carry(w_carry_19_1_03)
    );
    wire w_sum_19_1_04, w_carry_19_1_04;
    math_adder_full FA_19_1_04 (
        .i_a(w_pp_13_06),
        .i_b(w_pp_14_05),
        .i_c(w_pp_15_04),
        .ow_sum(w_sum_19_1_04),
        .ow_carry(w_carry_19_1_04)
    );
    wire w_sum_20_1_01, w_carry_20_1_01;
    math_adder_full FA_20_1_01 (
        .i_a(w_pp_05_15),
        .i_b(w_pp_06_14),
        .i_c(w_pp_07_13),
        .ow_sum(w_sum_20_1_01),
        .ow_carry(w_carry_20_1_01)
    );
    wire w_sum_20_1_02, w_carry_20_1_02;
    math_adder_full FA_20_1_02 (
        .i_a(w_pp_08_12),
        .i_b(w_pp_09_11),
        .i_c(w_pp_10_10),
        .ow_sum(w_sum_20_1_02),
        .ow_carry(w_carry_20_1_02)
    );
    wire w_sum_20_1_03, w_carry_20_1_03;
    math_adder_full FA_20_1_03 (
        .i_a(w_pp_11_09),
        .i_b(w_pp_12_08),
        .i_c(w_pp_13_07),
        .ow_sum(w_sum_20_1_03),
        .ow_carry(w_carry_20_1_03)
    );
    wire w_sum_20_1_04, w_carry_20_1_04;
    math_adder_half HA_20_1_04 (
        .i_a(w_pp_14_06),
        .i_b(w_pp_15_05),
        .ow_sum(w_sum_20_1_04),
        .ow_carry(w_carry_20_1_04)
    );
    wire w_sum_21_1_01, w_carry_21_1_01;
    math_adder_full FA_21_1_01 (
        .i_a(w_pp_06_15),
        .i_b(w_pp_07_14),
        .i_c(w_pp_08_13),
        .ow_sum(w_sum_21_1_01),
        .ow_carry(w_carry_21_1_01)
    );
    wire w_sum_21_1_02, w_carry_21_1_02;
    math_adder_full FA_21_1_02 (
        .i_a(w_pp_09_12),
        .i_b(w_pp_10_11),
        .i_c(w_pp_11_10),
        .ow_sum(w_sum_21_1_02),
        .ow_carry(w_carry_21_1_02)
    );
    wire w_sum_21_1_03, w_carry_21_1_03;
    math_adder_full FA_21_1_03 (
        .i_a(w_pp_12_09),
        .i_b(w_pp_13_08),
        .i_c(w_pp_14_07),
        .ow_sum(w_sum_21_1_03),
        .ow_carry(w_carry_21_1_03)
    );
    wire w_sum_22_1_01, w_carry_22_1_01;
    math_adder_full FA_22_1_01 (
        .i_a(w_pp_07_15),
        .i_b(w_pp_08_14),
        .i_c(w_pp_09_13),
        .ow_sum(w_sum_22_1_01),
        .ow_carry(w_carry_22_1_01)
    );
    wire w_sum_22_1_02, w_carry_22_1_02;
    math_adder_full FA_22_1_02 (
        .i_a(w_pp_10_12),
        .i_b(w_pp_11_11),
        .i_c(w_pp_12_10),
        .ow_sum(w_sum_22_1_02),
        .ow_carry(w_carry_22_1_02)
    );
    wire w_sum_22_1_03, w_carry_22_1_03;
    math_adder_full FA_22_1_03 (
        .i_a(w_pp_13_09),
        .i_b(w_pp_14_08),
        .i_c(w_pp_15_07),
        .ow_sum(w_sum_22_1_03),
        .ow_carry(w_carry_22_1_03)
    );
    wire w_sum_23_1_01, w_carry_23_1_01;
    math_adder_full FA_23_1_01 (
        .i_a(w_pp_08_15),
        .i_b(w_pp_09_14),
        .i_c(w_pp_10_13),
        .ow_sum(w_sum_23_1_01),
        .ow_carry(w_carry_23_1_01)
    );
    wire w_sum_23_1_02, w_carry_23_1_02;
    math_adder_full FA_23_1_02 (
        .i_a(w_pp_11_12),
        .i_b(w_pp_12_11),
        .i_c(w_pp_13_10),
        .ow_sum(w_sum_23_1_02),
        .ow_carry(w_carry_23_1_02)
    );
    wire w_sum_23_1_03, w_carry_23_1_03;
    math_adder_half HA_23_1_03 (
        .i_a(w_pp_14_09),
        .i_b(w_pp_15_08),
        .ow_sum(w_sum_23_1_03),
        .ow_carry(w_carry_23_1_03)
    );
    wire w_sum_24_1_01, w_carry_24_1_01;
    math_adder_full FA_24_1_01 (
        .i_a(w_pp_09_15),
        .i_b(w_pp_10_14),
        .i_c(w_pp_11_13),
        .ow_sum(w_sum_24_1_01),
        .ow_carry(w_carry_24_1_01)
    );
    wire w_sum_24_1_02, w_carry_24_1_02;
    math_adder_full FA_24_1_02 (
        .i_a(w_pp_12_12),
        .i_b(w_pp_13_11),
        .i_c(w_pp_14_10),
        .ow_sum(w_sum_24_1_02),
        .ow_carry(w_carry_24_1_02)
    );
    wire w_sum_25_1_01, w_carry_25_1_01;
    math_adder_full FA_25_1_01 (
        .i_a(w_pp_10_15),
        .i_b(w_pp_11_14),
        .i_c(w_pp_12_13),
        .ow_sum(w_sum_25_1_01),
        .ow_carry(w_carry_25_1_01)
    );
    wire w_sum_25_1_02, w_carry_25_1_02;
    math_adder_full FA_25_1_02 (
        .i_a(w_pp_13_12),
        .i_b(w_pp_14_11),
        .i_c(w_pp_15_10),
        .ow_sum(w_sum_25_1_02),
        .ow_carry(w_carry_25_1_02)
    );
    wire w_sum_26_1_01, w_carry_26_1_01;
    math_adder_full FA_26_1_01 (
        .i_a(w_pp_11_15),
        .i_b(w_pp_12_14),
        .i_c(w_pp_13_13),
        .ow_sum(w_sum_26_1_01),
        .ow_carry(w_carry_26_1_01)
    );
    wire w_sum_26_1_02, w_carry_26_1_02;
    math_adder_half HA_26_1_02 (
        .i_a(w_pp_14_12),
        .i_b(w_pp_15_11),
        .ow_sum(w_sum_26_1_02),
        .ow_carry(w_carry_26_1_02)
    );
    wire w_sum_27_1_01, w_carry_27_1_01;
    math_adder_full FA_27_1_01 (
        .i_a(w_pp_12_15),
        .i_b(w_pp_13_14),
        .i_c(w_pp_14_13),
        .ow_sum(w_sum_27_1_01),
        .ow_carry(w_carry_27_1_01)
    );
    wire w_sum_28_1_01, w_carry_28_1_01;
    math_adder_full FA_28_1_01 (
        .i_a(w_pp_13_15),
        .i_b(w_pp_14_14),
        .i_c(w_pp_15_13),
        .ow_sum(w_sum_28_1_01),
        .ow_carry(w_carry_28_1_01)
    );
    wire w_sum_29_1_01, w_carry_29_1_01;
    math_adder_half HA_29_1_01 (
        .i_a(w_pp_14_15),
        .i_b(w_pp_15_14),
        .ow_sum(w_sum_29_1_01),
        .ow_carry(w_carry_29_1_01)
    );

    // Wallace reduction layer 2
    wire w_sum_02_2_01, w_carry_02_2_01;
    math_adder_half HA_02_2_01 (
        .i_a(w_carry_01_1_01),
        .i_b(w_sum_02_1_01),
        .ow_sum(w_sum_02_2_01),
        .ow_carry(w_carry_02_2_01)
    );
    wire w_sum_03_2_01, w_carry_03_2_01;
    math_adder_full FA_03_2_01 (
        .i_a(w_carry_02_1_01),
        .i_b(w_sum_03_1_01),
        .i_c(w_pp_03_00),
        .ow_sum(w_sum_03_2_01),
        .ow_carry(w_carry_03_2_01)
    );
    wire w_sum_04_2_01, w_carry_04_2_01;
    math_adder_full FA_04_2_01 (
        .i_a(w_carry_03_1_01),
        .i_b(w_sum_04_1_01),
        .i_c(w_sum_04_1_02),
        .ow_sum(w_sum_04_2_01),
        .ow_carry(w_carry_04_2_01)
    );
    wire w_sum_05_2_01, w_carry_05_2_01;
    math_adder_full FA_05_2_01 (
        .i_a(w_carry_04_1_01),
        .i_b(w_carry_04_1_02),
        .i_c(w_sum_05_1_01),
        .ow_sum(w_sum_05_2_01),
        .ow_carry(w_carry_05_2_01)
    );
    wire w_sum_06_2_01, w_carry_06_2_01;
    math_adder_full FA_06_2_01 (
        .i_a(w_carry_05_1_01),
        .i_b(w_carry_05_1_02),
        .i_c(w_sum_06_1_01),
        .ow_sum(w_sum_06_2_01),
        .ow_carry(w_carry_06_2_01)
    );
    wire w_sum_06_2_02, w_carry_06_2_02;
    math_adder_half HA_06_2_02 (
        .i_a(w_sum_06_1_02),
        .i_b(w_pp_06_00),
        .ow_sum(w_sum_06_2_02),
        .ow_carry(w_carry_06_2_02)
    );
    wire w_sum_07_2_01, w_carry_07_2_01;
    math_adder_full FA_07_2_01 (
        .i_a(w_carry_06_1_01),
        .i_b(w_carry_06_1_02),
        .i_c(w_sum_07_1_01),
        .ow_sum(w_sum_07_2_01),
        .ow_carry(w_carry_07_2_01)
    );
    wire w_sum_07_2_02, w_carry_07_2_02;
    math_adder_half HA_07_2_02 (
        .i_a(w_sum_07_1_02),
        .i_b(w_sum_07_1_03),
        .ow_sum(w_sum_07_2_02),
        .ow_carry(w_carry_07_2_02)
    );
    wire w_sum_08_2_01, w_carry_08_2_01;
    math_adder_full FA_08_2_01 (
        .i_a(w_carry_07_1_01),
        .i_b(w_carry_07_1_02),
        .i_c(w_carry_07_1_03),
        .ow_sum(w_sum_08_2_01),
        .ow_carry(w_carry_08_2_01)
    );
    wire w_sum_08_2_02, w_carry_08_2_02;
    math_adder_full FA_08_2_02 (
        .i_a(w_sum_08_1_01),
        .i_b(w_sum_08_1_02),
        .i_c(w_sum_08_1_03),
        .ow_sum(w_sum_08_2_02),
        .ow_carry(w_carry_08_2_02)
    );
    wire w_sum_09_2_01, w_carry_09_2_01;
    math_adder_full FA_09_2_01 (
        .i_a(w_carry_08_1_01),
        .i_b(w_carry_08_1_02),
        .i_c(w_carry_08_1_03),
        .ow_sum(w_sum_09_2_01),
        .ow_carry(w_carry_09_2_01)
    );
    wire w_sum_09_2_02, w_carry_09_2_02;
    math_adder_full FA_09_2_02 (
        .i_a(w_sum_09_1_01),
        .i_b(w_sum_09_1_02),
        .i_c(w_sum_09_1_03),
        .ow_sum(w_sum_09_2_02),
        .ow_carry(w_carry_09_2_02)
    );
    wire w_sum_10_2_01, w_carry_10_2_01;
    math_adder_full FA_10_2_01 (
        .i_a(w_carry_09_1_01),
        .i_b(w_carry_09_1_02),
        .i_c(w_carry_09_1_03),
        .ow_sum(w_sum_10_2_01),
        .ow_carry(w_carry_10_2_01)
    );
    wire w_sum_10_2_02, w_carry_10_2_02;
    math_adder_full FA_10_2_02 (
        .i_a(w_sum_10_1_01),
        .i_b(w_sum_10_1_02),
        .i_c(w_sum_10_1_03),
        .ow_sum(w_sum_10_2_02),
        .ow_carry(w_carry_10_2_02)
    );
    wire w_sum_11_2_01, w_carry_11_2_01;
    math_adder_full FA_11_2_01 (
        .i_a(w_carry_10_1_01),
        .i_b(w_carry_10_1_02),
        .i_c(w_carry_10_1_03),
        .ow_sum(w_sum_11_2_01),
        .ow_carry(w_carry_11_2_01)
    );
    wire w_sum_11_2_02, w_carry_11_2_02;
    math_adder_full FA_11_2_02 (
        .i_a(w_carry_10_1_04),
        .i_b(w_sum_11_1_01),
        .i_c(w_sum_11_1_02),
        .ow_sum(w_sum_11_2_02),
        .ow_carry(w_carry_11_2_02)
    );
    wire w_sum_11_2_03, w_carry_11_2_03;
    math_adder_half HA_11_2_03 (
        .i_a(w_sum_11_1_03),
        .i_b(w_sum_11_1_04),
        .ow_sum(w_sum_11_2_03),
        .ow_carry(w_carry_11_2_03)
    );
    wire w_sum_12_2_01, w_carry_12_2_01;
    math_adder_full FA_12_2_01 (
        .i_a(w_carry_11_1_01),
        .i_b(w_carry_11_1_02),
        .i_c(w_carry_11_1_03),
        .ow_sum(w_sum_12_2_01),
        .ow_carry(w_carry_12_2_01)
    );
    wire w_sum_12_2_02, w_carry_12_2_02;
    math_adder_full FA_12_2_02 (
        .i_a(w_carry_11_1_04),
        .i_b(w_sum_12_1_01),
        .i_c(w_sum_12_1_02),
        .ow_sum(w_sum_12_2_02),
        .ow_carry(w_carry_12_2_02)
    );
    wire w_sum_12_2_03, w_carry_12_2_03;
    math_adder_full FA_12_2_03 (
        .i_a(w_sum_12_1_03),
        .i_b(w_sum_12_1_04),
        .i_c(w_pp_12_00),
        .ow_sum(w_sum_12_2_03),
        .ow_carry(w_carry_12_2_03)
    );
    wire w_sum_13_2_01, w_carry_13_2_01;
    math_adder_full FA_13_2_01 (
        .i_a(w_carry_12_1_01),
        .i_b(w_carry_12_1_02),
        .i_c(w_carry_12_1_03),
        .ow_sum(w_sum_13_2_01),
        .ow_carry(w_carry_13_2_01)
    );
    wire w_sum_13_2_02, w_carry_13_2_02;
    math_adder_full FA_13_2_02 (
        .i_a(w_carry_12_1_04),
        .i_b(w_sum_13_1_01),
        .i_c(w_sum_13_1_02),
        .ow_sum(w_sum_13_2_02),
        .ow_carry(w_carry_13_2_02)
    );
    wire w_sum_13_2_03, w_carry_13_2_03;
    math_adder_full FA_13_2_03 (
        .i_a(w_sum_13_1_03),
        .i_b(w_sum_13_1_04),
        .i_c(w_sum_13_1_05),
        .ow_sum(w_sum_13_2_03),
        .ow_carry(w_carry_13_2_03)
    );
    wire w_sum_14_2_01, w_carry_14_2_01;
    math_adder_full FA_14_2_01 (
        .i_a(w_carry_13_1_01),
        .i_b(w_carry_13_1_02),
        .i_c(w_carry_13_1_03),
        .ow_sum(w_sum_14_2_01),
        .ow_carry(w_carry_14_2_01)
    );
    wire w_sum_14_2_02, w_carry_14_2_02;
    math_adder_full FA_14_2_02 (
        .i_a(w_carry_13_1_04),
        .i_b(w_carry_13_1_05),
        .i_c(w_sum_14_1_01),
        .ow_sum(w_sum_14_2_02),
        .ow_carry(w_carry_14_2_02)
    );
    wire w_sum_14_2_03, w_carry_14_2_03;
    math_adder_full FA_14_2_03 (
        .i_a(w_sum_14_1_02),
        .i_b(w_sum_14_1_03),
        .i_c(w_sum_14_1_04),
        .ow_sum(w_sum_14_2_03),
        .ow_carry(w_carry_14_2_03)
    );
    wire w_sum_15_2_01, w_carry_15_2_01;
    math_adder_full FA_15_2_01 (
        .i_a(w_carry_14_1_01),
        .i_b(w_carry_14_1_02),
        .i_c(w_carry_14_1_03),
        .ow_sum(w_sum_15_2_01),
        .ow_carry(w_carry_15_2_01)
    );
    wire w_sum_15_2_02, w_carry_15_2_02;
    math_adder_full FA_15_2_02 (
        .i_a(w_carry_14_1_04),
        .i_b(w_carry_14_1_05),
        .i_c(w_sum_15_1_01),
        .ow_sum(w_sum_15_2_02),
        .ow_carry(w_carry_15_2_02)
    );
    wire w_sum_15_2_03, w_carry_15_2_03;
    math_adder_full FA_15_2_03 (
        .i_a(w_sum_15_1_02),
        .i_b(w_sum_15_1_03),
        .i_c(w_sum_15_1_04),
        .ow_sum(w_sum_15_2_03),
        .ow_carry(w_carry_15_2_03)
    );
    wire w_sum_15_2_04, w_carry_15_2_04;
    math_adder_half HA_15_2_04 (
        .i_a(w_sum_15_1_05),
        .i_b(w_pp_15_00),
        .ow_sum(w_sum_15_2_04),
        .ow_carry(w_carry_15_2_04)
    );
    wire w_sum_16_2_01, w_carry_16_2_01;
    math_adder_full FA_16_2_01 (
        .i_a(w_carry_15_1_01),
        .i_b(w_carry_15_1_02),
        .i_c(w_carry_15_1_03),
        .ow_sum(w_sum_16_2_01),
        .ow_carry(w_carry_16_2_01)
    );
    wire w_sum_16_2_02, w_carry_16_2_02;
    math_adder_full FA_16_2_02 (
        .i_a(w_carry_15_1_04),
        .i_b(w_carry_15_1_05),
        .i_c(w_sum_16_1_01),
        .ow_sum(w_sum_16_2_02),
        .ow_carry(w_carry_16_2_02)
    );
    wire w_sum_16_2_03, w_carry_16_2_03;
    math_adder_full FA_16_2_03 (
        .i_a(w_sum_16_1_02),
        .i_b(w_sum_16_1_03),
        .i_c(w_sum_16_1_04),
        .ow_sum(w_sum_16_2_03),
        .ow_carry(w_carry_16_2_03)
    );
    wire w_sum_17_2_01, w_carry_17_2_01;
    math_adder_full FA_17_2_01 (
        .i_a(w_carry_16_1_01),
        .i_b(w_carry_16_1_02),
        .i_c(w_carry_16_1_03),
        .ow_sum(w_sum_17_2_01),
        .ow_carry(w_carry_17_2_01)
    );
    wire w_sum_17_2_02, w_carry_17_2_02;
    math_adder_full FA_17_2_02 (
        .i_a(w_carry_16_1_04),
        .i_b(w_carry_16_1_05),
        .i_c(w_sum_17_1_01),
        .ow_sum(w_sum_17_2_02),
        .ow_carry(w_carry_17_2_02)
    );
    wire w_sum_17_2_03, w_carry_17_2_03;
    math_adder_full FA_17_2_03 (
        .i_a(w_sum_17_1_02),
        .i_b(w_sum_17_1_03),
        .i_c(w_sum_17_1_04),
        .ow_sum(w_sum_17_2_03),
        .ow_carry(w_carry_17_2_03)
    );
    wire w_sum_18_2_01, w_carry_18_2_01;
    math_adder_full FA_18_2_01 (
        .i_a(w_carry_17_1_01),
        .i_b(w_carry_17_1_02),
        .i_c(w_carry_17_1_03),
        .ow_sum(w_sum_18_2_01),
        .ow_carry(w_carry_18_2_01)
    );
    wire w_sum_18_2_02, w_carry_18_2_02;
    math_adder_full FA_18_2_02 (
        .i_a(w_carry_17_1_04),
        .i_b(w_carry_17_1_05),
        .i_c(w_sum_18_1_01),
        .ow_sum(w_sum_18_2_02),
        .ow_carry(w_carry_18_2_02)
    );
    wire w_sum_18_2_03, w_carry_18_2_03;
    math_adder_full FA_18_2_03 (
        .i_a(w_sum_18_1_02),
        .i_b(w_sum_18_1_03),
        .i_c(w_sum_18_1_04),
        .ow_sum(w_sum_18_2_03),
        .ow_carry(w_carry_18_2_03)
    );
    wire w_sum_19_2_01, w_carry_19_2_01;
    math_adder_full FA_19_2_01 (
        .i_a(w_carry_18_1_01),
        .i_b(w_carry_18_1_02),
        .i_c(w_carry_18_1_03),
        .ow_sum(w_sum_19_2_01),
        .ow_carry(w_carry_19_2_01)
    );
    wire w_sum_19_2_02, w_carry_19_2_02;
    math_adder_full FA_19_2_02 (
        .i_a(w_carry_18_1_04),
        .i_b(w_sum_19_1_01),
        .i_c(w_sum_19_1_02),
        .ow_sum(w_sum_19_2_02),
        .ow_carry(w_carry_19_2_02)
    );
    wire w_sum_19_2_03, w_carry_19_2_03;
    math_adder_half HA_19_2_03 (
        .i_a(w_sum_19_1_03),
        .i_b(w_sum_19_1_04),
        .ow_sum(w_sum_19_2_03),
        .ow_carry(w_carry_19_2_03)
    );
    wire w_sum_20_2_01, w_carry_20_2_01;
    math_adder_full FA_20_2_01 (
        .i_a(w_carry_19_1_01),
        .i_b(w_carry_19_1_02),
        .i_c(w_carry_19_1_03),
        .ow_sum(w_sum_20_2_01),
        .ow_carry(w_carry_20_2_01)
    );
    wire w_sum_20_2_02, w_carry_20_2_02;
    math_adder_full FA_20_2_02 (
        .i_a(w_carry_19_1_04),
        .i_b(w_sum_20_1_01),
        .i_c(w_sum_20_1_02),
        .ow_sum(w_sum_20_2_02),
        .ow_carry(w_carry_20_2_02)
    );
    wire w_sum_20_2_03, w_carry_20_2_03;
    math_adder_half HA_20_2_03 (
        .i_a(w_sum_20_1_03),
        .i_b(w_sum_20_1_04),
        .ow_sum(w_sum_20_2_03),
        .ow_carry(w_carry_20_2_03)
    );
    wire w_sum_21_2_01, w_carry_21_2_01;
    math_adder_full FA_21_2_01 (
        .i_a(w_carry_20_1_01),
        .i_b(w_carry_20_1_02),
        .i_c(w_carry_20_1_03),
        .ow_sum(w_sum_21_2_01),
        .ow_carry(w_carry_21_2_01)
    );
    wire w_sum_21_2_02, w_carry_21_2_02;
    math_adder_full FA_21_2_02 (
        .i_a(w_carry_20_1_04),
        .i_b(w_sum_21_1_01),
        .i_c(w_sum_21_1_02),
        .ow_sum(w_sum_21_2_02),
        .ow_carry(w_carry_21_2_02)
    );
    wire w_sum_21_2_03, w_carry_21_2_03;
    math_adder_half HA_21_2_03 (
        .i_a(w_sum_21_1_03),
        .i_b(w_pp_15_06),
        .ow_sum(w_sum_21_2_03),
        .ow_carry(w_carry_21_2_03)
    );
    wire w_sum_22_2_01, w_carry_22_2_01;
    math_adder_full FA_22_2_01 (
        .i_a(w_carry_21_1_01),
        .i_b(w_carry_21_1_02),
        .i_c(w_carry_21_1_03),
        .ow_sum(w_sum_22_2_01),
        .ow_carry(w_carry_22_2_01)
    );
    wire w_sum_22_2_02, w_carry_22_2_02;
    math_adder_full FA_22_2_02 (
        .i_a(w_sum_22_1_01),
        .i_b(w_sum_22_1_02),
        .i_c(w_sum_22_1_03),
        .ow_sum(w_sum_22_2_02),
        .ow_carry(w_carry_22_2_02)
    );
    wire w_sum_23_2_01, w_carry_23_2_01;
    math_adder_full FA_23_2_01 (
        .i_a(w_carry_22_1_01),
        .i_b(w_carry_22_1_02),
        .i_c(w_carry_22_1_03),
        .ow_sum(w_sum_23_2_01),
        .ow_carry(w_carry_23_2_01)
    );
    wire w_sum_23_2_02, w_carry_23_2_02;
    math_adder_full FA_23_2_02 (
        .i_a(w_sum_23_1_01),
        .i_b(w_sum_23_1_02),
        .i_c(w_sum_23_1_03),
        .ow_sum(w_sum_23_2_02),
        .ow_carry(w_carry_23_2_02)
    );
    wire w_sum_24_2_01, w_carry_24_2_01;
    math_adder_full FA_24_2_01 (
        .i_a(w_carry_23_1_01),
        .i_b(w_carry_23_1_02),
        .i_c(w_carry_23_1_03),
        .ow_sum(w_sum_24_2_01),
        .ow_carry(w_carry_24_2_01)
    );
    wire w_sum_24_2_02, w_carry_24_2_02;
    math_adder_full FA_24_2_02 (
        .i_a(w_sum_24_1_01),
        .i_b(w_sum_24_1_02),
        .i_c(w_pp_15_09),
        .ow_sum(w_sum_24_2_02),
        .ow_carry(w_carry_24_2_02)
    );
    wire w_sum_25_2_01, w_carry_25_2_01;
    math_adder_full FA_25_2_01 (
        .i_a(w_carry_24_1_01),
        .i_b(w_carry_24_1_02),
        .i_c(w_sum_25_1_01),
        .ow_sum(w_sum_25_2_01),
        .ow_carry(w_carry_25_2_01)
    );
    wire w_sum_26_2_01, w_carry_26_2_01;
    math_adder_full FA_26_2_01 (
        .i_a(w_carry_25_1_01),
        .i_b(w_carry_25_1_02),
        .i_c(w_sum_26_1_01),
        .ow_sum(w_sum_26_2_01),
        .ow_carry(w_carry_26_2_01)
    );
    wire w_sum_27_2_01, w_carry_27_2_01;
    math_adder_full FA_27_2_01 (
        .i_a(w_carry_26_1_01),
        .i_b(w_carry_26_1_02),
        .i_c(w_sum_27_1_01),
        .ow_sum(w_sum_27_2_01),
        .ow_carry(w_carry_27_2_01)
    );
    wire w_sum_28_2_01, w_carry_28_2_01;
    math_adder_half HA_28_2_01 (
        .i_a(w_carry_27_1_01),
        .i_b(w_sum_28_1_01),
        .ow_sum(w_sum_28_2_01),
        .ow_carry(w_carry_28_2_01)
    );
    wire w_sum_29_2_01, w_carry_29_2_01;
    math_adder_half HA_29_2_01 (
        .i_a(w_carry_28_1_01),
        .i_b(w_sum_29_1_01),
        .ow_sum(w_sum_29_2_01),
        .ow_carry(w_carry_29_2_01)
    );
    wire w_sum_30_2_01, w_carry_30_2_01;
    math_adder_half HA_30_2_01 (
        .i_a(w_carry_29_1_01),
        .i_b(w_pp_15_15),
        .ow_sum(w_sum_30_2_01),
        .ow_carry(w_carry_30_2_01)
    );

    // Wallace reduction layer 3
    wire w_sum_03_3_01, w_carry_03_3_01;
    math_adder_half HA_03_3_01 (
        .i_a(w_carry_02_2_01),
        .i_b(w_sum_03_2_01),
        .ow_sum(w_sum_03_3_01),
        .ow_carry(w_carry_03_3_01)
    );
    wire w_sum_04_3_01, w_carry_04_3_01;
    math_adder_half HA_04_3_01 (
        .i_a(w_carry_03_2_01),
        .i_b(w_sum_04_2_01),
        .ow_sum(w_sum_04_3_01),
        .ow_carry(w_carry_04_3_01)
    );
    wire w_sum_05_3_01, w_carry_05_3_01;
    math_adder_full FA_05_3_01 (
        .i_a(w_carry_04_2_01),
        .i_b(w_sum_05_2_01),
        .i_c(w_sum_05_1_02),
        .ow_sum(w_sum_05_3_01),
        .ow_carry(w_carry_05_3_01)
    );
    wire w_sum_06_3_01, w_carry_06_3_01;
    math_adder_full FA_06_3_01 (
        .i_a(w_carry_05_2_01),
        .i_b(w_sum_06_2_01),
        .i_c(w_sum_06_2_02),
        .ow_sum(w_sum_06_3_01),
        .ow_carry(w_carry_06_3_01)
    );
    wire w_sum_07_3_01, w_carry_07_3_01;
    math_adder_full FA_07_3_01 (
        .i_a(w_carry_06_2_01),
        .i_b(w_carry_06_2_02),
        .i_c(w_sum_07_2_01),
        .ow_sum(w_sum_07_3_01),
        .ow_carry(w_carry_07_3_01)
    );
    wire w_sum_08_3_01, w_carry_08_3_01;
    math_adder_full FA_08_3_01 (
        .i_a(w_carry_07_2_01),
        .i_b(w_carry_07_2_02),
        .i_c(w_sum_08_2_01),
        .ow_sum(w_sum_08_3_01),
        .ow_carry(w_carry_08_3_01)
    );
    wire w_sum_09_3_01, w_carry_09_3_01;
    math_adder_full FA_09_3_01 (
        .i_a(w_carry_08_2_01),
        .i_b(w_carry_08_2_02),
        .i_c(w_sum_09_2_01),
        .ow_sum(w_sum_09_3_01),
        .ow_carry(w_carry_09_3_01)
    );
    wire w_sum_09_3_02, w_carry_09_3_02;
    math_adder_half HA_09_3_02 (
        .i_a(w_sum_09_2_02),
        .i_b(w_pp_09_00),
        .ow_sum(w_sum_09_3_02),
        .ow_carry(w_carry_09_3_02)
    );
    wire w_sum_10_3_01, w_carry_10_3_01;
    math_adder_full FA_10_3_01 (
        .i_a(w_carry_09_2_01),
        .i_b(w_carry_09_2_02),
        .i_c(w_sum_10_2_01),
        .ow_sum(w_sum_10_3_01),
        .ow_carry(w_carry_10_3_01)
    );
    wire w_sum_10_3_02, w_carry_10_3_02;
    math_adder_half HA_10_3_02 (
        .i_a(w_sum_10_2_02),
        .i_b(w_sum_10_1_04),
        .ow_sum(w_sum_10_3_02),
        .ow_carry(w_carry_10_3_02)
    );
    wire w_sum_11_3_01, w_carry_11_3_01;
    math_adder_full FA_11_3_01 (
        .i_a(w_carry_10_2_01),
        .i_b(w_carry_10_2_02),
        .i_c(w_sum_11_2_01),
        .ow_sum(w_sum_11_3_01),
        .ow_carry(w_carry_11_3_01)
    );
    wire w_sum_11_3_02, w_carry_11_3_02;
    math_adder_half HA_11_3_02 (
        .i_a(w_sum_11_2_02),
        .i_b(w_sum_11_2_03),
        .ow_sum(w_sum_11_3_02),
        .ow_carry(w_carry_11_3_02)
    );
    wire w_sum_12_3_01, w_carry_12_3_01;
    math_adder_full FA_12_3_01 (
        .i_a(w_carry_11_2_01),
        .i_b(w_carry_11_2_02),
        .i_c(w_carry_11_2_03),
        .ow_sum(w_sum_12_3_01),
        .ow_carry(w_carry_12_3_01)
    );
    wire w_sum_12_3_02, w_carry_12_3_02;
    math_adder_full FA_12_3_02 (
        .i_a(w_sum_12_2_01),
        .i_b(w_sum_12_2_02),
        .i_c(w_sum_12_2_03),
        .ow_sum(w_sum_12_3_02),
        .ow_carry(w_carry_12_3_02)
    );
    wire w_sum_13_3_01, w_carry_13_3_01;
    math_adder_full FA_13_3_01 (
        .i_a(w_carry_12_2_01),
        .i_b(w_carry_12_2_02),
        .i_c(w_carry_12_2_03),
        .ow_sum(w_sum_13_3_01),
        .ow_carry(w_carry_13_3_01)
    );
    wire w_sum_13_3_02, w_carry_13_3_02;
    math_adder_full FA_13_3_02 (
        .i_a(w_sum_13_2_01),
        .i_b(w_sum_13_2_02),
        .i_c(w_sum_13_2_03),
        .ow_sum(w_sum_13_3_02),
        .ow_carry(w_carry_13_3_02)
    );
    wire w_sum_14_3_01, w_carry_14_3_01;
    math_adder_full FA_14_3_01 (
        .i_a(w_carry_13_2_01),
        .i_b(w_carry_13_2_02),
        .i_c(w_carry_13_2_03),
        .ow_sum(w_sum_14_3_01),
        .ow_carry(w_carry_14_3_01)
    );
    wire w_sum_14_3_02, w_carry_14_3_02;
    math_adder_full FA_14_3_02 (
        .i_a(w_sum_14_2_01),
        .i_b(w_sum_14_2_02),
        .i_c(w_sum_14_2_03),
        .ow_sum(w_sum_14_3_02),
        .ow_carry(w_carry_14_3_02)
    );
    wire w_sum_15_3_01, w_carry_15_3_01;
    math_adder_full FA_15_3_01 (
        .i_a(w_carry_14_2_01),
        .i_b(w_carry_14_2_02),
        .i_c(w_carry_14_2_03),
        .ow_sum(w_sum_15_3_01),
        .ow_carry(w_carry_15_3_01)
    );
    wire w_sum_15_3_02, w_carry_15_3_02;
    math_adder_full FA_15_3_02 (
        .i_a(w_sum_15_2_01),
        .i_b(w_sum_15_2_02),
        .i_c(w_sum_15_2_03),
        .ow_sum(w_sum_15_3_02),
        .ow_carry(w_carry_15_3_02)
    );
    wire w_sum_16_3_01, w_carry_16_3_01;
    math_adder_full FA_16_3_01 (
        .i_a(w_carry_15_2_01),
        .i_b(w_carry_15_2_02),
        .i_c(w_carry_15_2_03),
        .ow_sum(w_sum_16_3_01),
        .ow_carry(w_carry_16_3_01)
    );
    wire w_sum_16_3_02, w_carry_16_3_02;
    math_adder_full FA_16_3_02 (
        .i_a(w_carry_15_2_04),
        .i_b(w_sum_16_2_01),
        .i_c(w_sum_16_2_02),
        .ow_sum(w_sum_16_3_02),
        .ow_carry(w_carry_16_3_02)
    );
    wire w_sum_16_3_03, w_carry_16_3_03;
    math_adder_half HA_16_3_03 (
        .i_a(w_sum_16_2_03),
        .i_b(w_sum_16_1_05),
        .ow_sum(w_sum_16_3_03),
        .ow_carry(w_carry_16_3_03)
    );
    wire w_sum_17_3_01, w_carry_17_3_01;
    math_adder_full FA_17_3_01 (
        .i_a(w_carry_16_2_01),
        .i_b(w_carry_16_2_02),
        .i_c(w_carry_16_2_03),
        .ow_sum(w_sum_17_3_01),
        .ow_carry(w_carry_17_3_01)
    );
    wire w_sum_17_3_02, w_carry_17_3_02;
    math_adder_full FA_17_3_02 (
        .i_a(w_sum_17_2_01),
        .i_b(w_sum_17_2_02),
        .i_c(w_sum_17_2_03),
        .ow_sum(w_sum_17_3_02),
        .ow_carry(w_carry_17_3_02)
    );
    wire w_sum_18_3_01, w_carry_18_3_01;
    math_adder_full FA_18_3_01 (
        .i_a(w_carry_17_2_01),
        .i_b(w_carry_17_2_02),
        .i_c(w_carry_17_2_03),
        .ow_sum(w_sum_18_3_01),
        .ow_carry(w_carry_18_3_01)
    );
    wire w_sum_18_3_02, w_carry_18_3_02;
    math_adder_full FA_18_3_02 (
        .i_a(w_sum_18_2_01),
        .i_b(w_sum_18_2_02),
        .i_c(w_sum_18_2_03),
        .ow_sum(w_sum_18_3_02),
        .ow_carry(w_carry_18_3_02)
    );
    wire w_sum_19_3_01, w_carry_19_3_01;
    math_adder_full FA_19_3_01 (
        .i_a(w_carry_18_2_01),
        .i_b(w_carry_18_2_02),
        .i_c(w_carry_18_2_03),
        .ow_sum(w_sum_19_3_01),
        .ow_carry(w_carry_19_3_01)
    );
    wire w_sum_19_3_02, w_carry_19_3_02;
    math_adder_full FA_19_3_02 (
        .i_a(w_sum_19_2_01),
        .i_b(w_sum_19_2_02),
        .i_c(w_sum_19_2_03),
        .ow_sum(w_sum_19_3_02),
        .ow_carry(w_carry_19_3_02)
    );
    wire w_sum_20_3_01, w_carry_20_3_01;
    math_adder_full FA_20_3_01 (
        .i_a(w_carry_19_2_01),
        .i_b(w_carry_19_2_02),
        .i_c(w_carry_19_2_03),
        .ow_sum(w_sum_20_3_01),
        .ow_carry(w_carry_20_3_01)
    );
    wire w_sum_20_3_02, w_carry_20_3_02;
    math_adder_full FA_20_3_02 (
        .i_a(w_sum_20_2_01),
        .i_b(w_sum_20_2_02),
        .i_c(w_sum_20_2_03),
        .ow_sum(w_sum_20_3_02),
        .ow_carry(w_carry_20_3_02)
    );
    wire w_sum_21_3_01, w_carry_21_3_01;
    math_adder_full FA_21_3_01 (
        .i_a(w_carry_20_2_01),
        .i_b(w_carry_20_2_02),
        .i_c(w_carry_20_2_03),
        .ow_sum(w_sum_21_3_01),
        .ow_carry(w_carry_21_3_01)
    );
    wire w_sum_21_3_02, w_carry_21_3_02;
    math_adder_full FA_21_3_02 (
        .i_a(w_sum_21_2_01),
        .i_b(w_sum_21_2_02),
        .i_c(w_sum_21_2_03),
        .ow_sum(w_sum_21_3_02),
        .ow_carry(w_carry_21_3_02)
    );
    wire w_sum_22_3_01, w_carry_22_3_01;
    math_adder_full FA_22_3_01 (
        .i_a(w_carry_21_2_01),
        .i_b(w_carry_21_2_02),
        .i_c(w_carry_21_2_03),
        .ow_sum(w_sum_22_3_01),
        .ow_carry(w_carry_22_3_01)
    );
    wire w_sum_22_3_02, w_carry_22_3_02;
    math_adder_half HA_22_3_02 (
        .i_a(w_sum_22_2_01),
        .i_b(w_sum_22_2_02),
        .ow_sum(w_sum_22_3_02),
        .ow_carry(w_carry_22_3_02)
    );
    wire w_sum_23_3_01, w_carry_23_3_01;
    math_adder_full FA_23_3_01 (
        .i_a(w_carry_22_2_01),
        .i_b(w_carry_22_2_02),
        .i_c(w_sum_23_2_01),
        .ow_sum(w_sum_23_3_01),
        .ow_carry(w_carry_23_3_01)
    );
    wire w_sum_24_3_01, w_carry_24_3_01;
    math_adder_full FA_24_3_01 (
        .i_a(w_carry_23_2_01),
        .i_b(w_carry_23_2_02),
        .i_c(w_sum_24_2_01),
        .ow_sum(w_sum_24_3_01),
        .ow_carry(w_carry_24_3_01)
    );
    wire w_sum_25_3_01, w_carry_25_3_01;
    math_adder_full FA_25_3_01 (
        .i_a(w_carry_24_2_01),
        .i_b(w_carry_24_2_02),
        .i_c(w_sum_25_2_01),
        .ow_sum(w_sum_25_3_01),
        .ow_carry(w_carry_25_3_01)
    );
    wire w_sum_26_3_01, w_carry_26_3_01;
    math_adder_full FA_26_3_01 (
        .i_a(w_carry_25_2_01),
        .i_b(w_sum_26_2_01),
        .i_c(w_sum_26_1_02),
        .ow_sum(w_sum_26_3_01),
        .ow_carry(w_carry_26_3_01)
    );
    wire w_sum_27_3_01, w_carry_27_3_01;
    math_adder_full FA_27_3_01 (
        .i_a(w_carry_26_2_01),
        .i_b(w_sum_27_2_01),
        .i_c(w_pp_15_12),
        .ow_sum(w_sum_27_3_01),
        .ow_carry(w_carry_27_3_01)
    );
    wire w_sum_28_3_01, w_carry_28_3_01;
    math_adder_half HA_28_3_01 (
        .i_a(w_carry_27_2_01),
        .i_b(w_sum_28_2_01),
        .ow_sum(w_sum_28_3_01),
        .ow_carry(w_carry_28_3_01)
    );
    wire w_sum_29_3_01, w_carry_29_3_01;
    math_adder_half HA_29_3_01 (
        .i_a(w_carry_28_2_01),
        .i_b(w_sum_29_2_01),
        .ow_sum(w_sum_29_3_01),
        .ow_carry(w_carry_29_3_01)
    );
    wire w_sum_30_3_01, w_carry_30_3_01;
    math_adder_half HA_30_3_01 (
        .i_a(w_carry_29_2_01),
        .i_b(w_sum_30_2_01),
        .ow_sum(w_sum_30_3_01),
        .ow_carry(w_carry_30_3_01)
    );

    // Wallace reduction layer 4
    wire w_sum_04_4_01, w_carry_04_4_01;
    math_adder_half HA_04_4_01 (
        .i_a(w_carry_03_3_01),
        .i_b(w_sum_04_3_01),
        .ow_sum(w_sum_04_4_01),
        .ow_carry(w_carry_04_4_01)
    );
    wire w_sum_05_4_01, w_carry_05_4_01;
    math_adder_half HA_05_4_01 (
        .i_a(w_carry_04_3_01),
        .i_b(w_sum_05_3_01),
        .ow_sum(w_sum_05_4_01),
        .ow_carry(w_carry_05_4_01)
    );
    wire w_sum_06_4_01, w_carry_06_4_01;
    math_adder_half HA_06_4_01 (
        .i_a(w_carry_05_3_01),
        .i_b(w_sum_06_3_01),
        .ow_sum(w_sum_06_4_01),
        .ow_carry(w_carry_06_4_01)
    );
    wire w_sum_07_4_01, w_carry_07_4_01;
    math_adder_full FA_07_4_01 (
        .i_a(w_carry_06_3_01),
        .i_b(w_sum_07_3_01),
        .i_c(w_sum_07_2_02),
        .ow_sum(w_sum_07_4_01),
        .ow_carry(w_carry_07_4_01)
    );
    wire w_sum_08_4_01, w_carry_08_4_01;
    math_adder_full FA_08_4_01 (
        .i_a(w_carry_07_3_01),
        .i_b(w_sum_08_3_01),
        .i_c(w_sum_08_2_02),
        .ow_sum(w_sum_08_4_01),
        .ow_carry(w_carry_08_4_01)
    );
    wire w_sum_09_4_01, w_carry_09_4_01;
    math_adder_full FA_09_4_01 (
        .i_a(w_carry_08_3_01),
        .i_b(w_sum_09_3_01),
        .i_c(w_sum_09_3_02),
        .ow_sum(w_sum_09_4_01),
        .ow_carry(w_carry_09_4_01)
    );
    wire w_sum_10_4_01, w_carry_10_4_01;
    math_adder_full FA_10_4_01 (
        .i_a(w_carry_09_3_01),
        .i_b(w_carry_09_3_02),
        .i_c(w_sum_10_3_01),
        .ow_sum(w_sum_10_4_01),
        .ow_carry(w_carry_10_4_01)
    );
    wire w_sum_11_4_01, w_carry_11_4_01;
    math_adder_full FA_11_4_01 (
        .i_a(w_carry_10_3_01),
        .i_b(w_carry_10_3_02),
        .i_c(w_sum_11_3_01),
        .ow_sum(w_sum_11_4_01),
        .ow_carry(w_carry_11_4_01)
    );
    wire w_sum_12_4_01, w_carry_12_4_01;
    math_adder_full FA_12_4_01 (
        .i_a(w_carry_11_3_01),
        .i_b(w_carry_11_3_02),
        .i_c(w_sum_12_3_01),
        .ow_sum(w_sum_12_4_01),
        .ow_carry(w_carry_12_4_01)
    );
    wire w_sum_13_4_01, w_carry_13_4_01;
    math_adder_full FA_13_4_01 (
        .i_a(w_carry_12_3_01),
        .i_b(w_carry_12_3_02),
        .i_c(w_sum_13_3_01),
        .ow_sum(w_sum_13_4_01),
        .ow_carry(w_carry_13_4_01)
    );
    wire w_sum_14_4_01, w_carry_14_4_01;
    math_adder_full FA_14_4_01 (
        .i_a(w_carry_13_3_01),
        .i_b(w_carry_13_3_02),
        .i_c(w_sum_14_3_01),
        .ow_sum(w_sum_14_4_01),
        .ow_carry(w_carry_14_4_01)
    );
    wire w_sum_14_4_02, w_carry_14_4_02;
    math_adder_half HA_14_4_02 (
        .i_a(w_sum_14_3_02),
        .i_b(w_sum_14_1_05),
        .ow_sum(w_sum_14_4_02),
        .ow_carry(w_carry_14_4_02)
    );
    wire w_sum_15_4_01, w_carry_15_4_01;
    math_adder_full FA_15_4_01 (
        .i_a(w_carry_14_3_01),
        .i_b(w_carry_14_3_02),
        .i_c(w_sum_15_3_01),
        .ow_sum(w_sum_15_4_01),
        .ow_carry(w_carry_15_4_01)
    );
    wire w_sum_15_4_02, w_carry_15_4_02;
    math_adder_half HA_15_4_02 (
        .i_a(w_sum_15_3_02),
        .i_b(w_sum_15_2_04),
        .ow_sum(w_sum_15_4_02),
        .ow_carry(w_carry_15_4_02)
    );
    wire w_sum_16_4_01, w_carry_16_4_01;
    math_adder_full FA_16_4_01 (
        .i_a(w_carry_15_3_01),
        .i_b(w_carry_15_3_02),
        .i_c(w_sum_16_3_01),
        .ow_sum(w_sum_16_4_01),
        .ow_carry(w_carry_16_4_01)
    );
    wire w_sum_16_4_02, w_carry_16_4_02;
    math_adder_half HA_16_4_02 (
        .i_a(w_sum_16_3_02),
        .i_b(w_sum_16_3_03),
        .ow_sum(w_sum_16_4_02),
        .ow_carry(w_carry_16_4_02)
    );
    wire w_sum_17_4_01, w_carry_17_4_01;
    math_adder_full FA_17_4_01 (
        .i_a(w_carry_16_3_01),
        .i_b(w_carry_16_3_02),
        .i_c(w_carry_16_3_03),
        .ow_sum(w_sum_17_4_01),
        .ow_carry(w_carry_17_4_01)
    );
    wire w_sum_17_4_02, w_carry_17_4_02;
    math_adder_full FA_17_4_02 (
        .i_a(w_sum_17_3_01),
        .i_b(w_sum_17_3_02),
        .i_c(w_sum_17_1_05),
        .ow_sum(w_sum_17_4_02),
        .ow_carry(w_carry_17_4_02)
    );
    wire w_sum_18_4_01, w_carry_18_4_01;
    math_adder_full FA_18_4_01 (
        .i_a(w_carry_17_3_01),
        .i_b(w_carry_17_3_02),
        .i_c(w_sum_18_3_01),
        .ow_sum(w_sum_18_4_01),
        .ow_carry(w_carry_18_4_01)
    );
    wire w_sum_18_4_02, w_carry_18_4_02;
    math_adder_half HA_18_4_02 (
        .i_a(w_sum_18_3_02),
        .i_b(w_pp_15_03),
        .ow_sum(w_sum_18_4_02),
        .ow_carry(w_carry_18_4_02)
    );
    wire w_sum_19_4_01, w_carry_19_4_01;
    math_adder_full FA_19_4_01 (
        .i_a(w_carry_18_3_01),
        .i_b(w_carry_18_3_02),
        .i_c(w_sum_19_3_01),
        .ow_sum(w_sum_19_4_01),
        .ow_carry(w_carry_19_4_01)
    );
    wire w_sum_20_4_01, w_carry_20_4_01;
    math_adder_full FA_20_4_01 (
        .i_a(w_carry_19_3_01),
        .i_b(w_carry_19_3_02),
        .i_c(w_sum_20_3_01),
        .ow_sum(w_sum_20_4_01),
        .ow_carry(w_carry_20_4_01)
    );
    wire w_sum_21_4_01, w_carry_21_4_01;
    math_adder_full FA_21_4_01 (
        .i_a(w_carry_20_3_01),
        .i_b(w_carry_20_3_02),
        .i_c(w_sum_21_3_01),
        .ow_sum(w_sum_21_4_01),
        .ow_carry(w_carry_21_4_01)
    );
    wire w_sum_22_4_01, w_carry_22_4_01;
    math_adder_full FA_22_4_01 (
        .i_a(w_carry_21_3_01),
        .i_b(w_carry_21_3_02),
        .i_c(w_sum_22_3_01),
        .ow_sum(w_sum_22_4_01),
        .ow_carry(w_carry_22_4_01)
    );
    wire w_sum_23_4_01, w_carry_23_4_01;
    math_adder_full FA_23_4_01 (
        .i_a(w_carry_22_3_01),
        .i_b(w_carry_22_3_02),
        .i_c(w_sum_23_3_01),
        .ow_sum(w_sum_23_4_01),
        .ow_carry(w_carry_23_4_01)
    );
    wire w_sum_24_4_01, w_carry_24_4_01;
    math_adder_full FA_24_4_01 (
        .i_a(w_carry_23_3_01),
        .i_b(w_sum_24_3_01),
        .i_c(w_sum_24_2_02),
        .ow_sum(w_sum_24_4_01),
        .ow_carry(w_carry_24_4_01)
    );
    wire w_sum_25_4_01, w_carry_25_4_01;
    math_adder_full FA_25_4_01 (
        .i_a(w_carry_24_3_01),
        .i_b(w_sum_25_3_01),
        .i_c(w_sum_25_1_02),
        .ow_sum(w_sum_25_4_01),
        .ow_carry(w_carry_25_4_01)
    );
    wire w_sum_26_4_01, w_carry_26_4_01;
    math_adder_half HA_26_4_01 (
        .i_a(w_carry_25_3_01),
        .i_b(w_sum_26_3_01),
        .ow_sum(w_sum_26_4_01),
        .ow_carry(w_carry_26_4_01)
    );
    wire w_sum_27_4_01, w_carry_27_4_01;
    math_adder_half HA_27_4_01 (
        .i_a(w_carry_26_3_01),
        .i_b(w_sum_27_3_01),
        .ow_sum(w_sum_27_4_01),
        .ow_carry(w_carry_27_4_01)
    );
    wire w_sum_28_4_01, w_carry_28_4_01;
    math_adder_half HA_28_4_01 (
        .i_a(w_carry_27_3_01),
        .i_b(w_sum_28_3_01),
        .ow_sum(w_sum_28_4_01),
        .ow_carry(w_carry_28_4_01)
    );
    wire w_sum_29_4_01, w_carry_29_4_01;
    math_adder_half HA_29_4_01 (
        .i_a(w_carry_28_3_01),
        .i_b(w_sum_29_3_01),
        .ow_sum(w_sum_29_4_01),
        .ow_carry(w_carry_29_4_01)
    );
    wire w_sum_30_4_01, w_carry_30_4_01;
    math_adder_half HA_30_4_01 (
        .i_a(w_carry_29_3_01),
        .i_b(w_sum_30_3_01),
        .ow_sum(w_sum_30_4_01),
        .ow_carry(w_carry_30_4_01)
    );
    wire w_sum_31_4_01, w_carry_31_4_01;
    math_adder_half HA_31_4_01 (
        .i_a(w_carry_30_3_01),
        .i_b(w_carry_30_2_01),
        .ow_sum(w_sum_31_4_01),
        .ow_carry(w_carry_31_4_01)
    );

    // Wallace reduction layer 5
    wire w_sum_05_5_01, w_carry_05_5_01;
    math_adder_half HA_05_5_01 (
        .i_a(w_carry_04_4_01),
        .i_b(w_sum_05_4_01),
        .ow_sum(w_sum_05_5_01),
        .ow_carry(w_carry_05_5_01)
    );
    wire w_sum_06_5_01, w_carry_06_5_01;
    math_adder_half HA_06_5_01 (
        .i_a(w_carry_05_4_01),
        .i_b(w_sum_06_4_01),
        .ow_sum(w_sum_06_5_01),
        .ow_carry(w_carry_06_5_01)
    );
    wire w_sum_07_5_01, w_carry_07_5_01;
    math_adder_half HA_07_5_01 (
        .i_a(w_carry_06_4_01),
        .i_b(w_sum_07_4_01),
        .ow_sum(w_sum_07_5_01),
        .ow_carry(w_carry_07_5_01)
    );
    wire w_sum_08_5_01, w_carry_08_5_01;
    math_adder_half HA_08_5_01 (
        .i_a(w_carry_07_4_01),
        .i_b(w_sum_08_4_01),
        .ow_sum(w_sum_08_5_01),
        .ow_carry(w_carry_08_5_01)
    );
    wire w_sum_09_5_01, w_carry_09_5_01;
    math_adder_half HA_09_5_01 (
        .i_a(w_carry_08_4_01),
        .i_b(w_sum_09_4_01),
        .ow_sum(w_sum_09_5_01),
        .ow_carry(w_carry_09_5_01)
    );
    wire w_sum_10_5_01, w_carry_10_5_01;
    math_adder_full FA_10_5_01 (
        .i_a(w_carry_09_4_01),
        .i_b(w_sum_10_4_01),
        .i_c(w_sum_10_3_02),
        .ow_sum(w_sum_10_5_01),
        .ow_carry(w_carry_10_5_01)
    );
    wire w_sum_11_5_01, w_carry_11_5_01;
    math_adder_full FA_11_5_01 (
        .i_a(w_carry_10_4_01),
        .i_b(w_sum_11_4_01),
        .i_c(w_sum_11_3_02),
        .ow_sum(w_sum_11_5_01),
        .ow_carry(w_carry_11_5_01)
    );
    wire w_sum_12_5_01, w_carry_12_5_01;
    math_adder_full FA_12_5_01 (
        .i_a(w_carry_11_4_01),
        .i_b(w_sum_12_4_01),
        .i_c(w_sum_12_3_02),
        .ow_sum(w_sum_12_5_01),
        .ow_carry(w_carry_12_5_01)
    );
    wire w_sum_13_5_01, w_carry_13_5_01;
    math_adder_full FA_13_5_01 (
        .i_a(w_carry_12_4_01),
        .i_b(w_sum_13_4_01),
        .i_c(w_sum_13_3_02),
        .ow_sum(w_sum_13_5_01),
        .ow_carry(w_carry_13_5_01)
    );
    wire w_sum_14_5_01, w_carry_14_5_01;
    math_adder_full FA_14_5_01 (
        .i_a(w_carry_13_4_01),
        .i_b(w_sum_14_4_01),
        .i_c(w_sum_14_4_02),
        .ow_sum(w_sum_14_5_01),
        .ow_carry(w_carry_14_5_01)
    );
    wire w_sum_15_5_01, w_carry_15_5_01;
    math_adder_full FA_15_5_01 (
        .i_a(w_carry_14_4_01),
        .i_b(w_carry_14_4_02),
        .i_c(w_sum_15_4_01),
        .ow_sum(w_sum_15_5_01),
        .ow_carry(w_carry_15_5_01)
    );
    wire w_sum_16_5_01, w_carry_16_5_01;
    math_adder_full FA_16_5_01 (
        .i_a(w_carry_15_4_01),
        .i_b(w_carry_15_4_02),
        .i_c(w_sum_16_4_01),
        .ow_sum(w_sum_16_5_01),
        .ow_carry(w_carry_16_5_01)
    );
    wire w_sum_17_5_01, w_carry_17_5_01;
    math_adder_full FA_17_5_01 (
        .i_a(w_carry_16_4_01),
        .i_b(w_carry_16_4_02),
        .i_c(w_sum_17_4_01),
        .ow_sum(w_sum_17_5_01),
        .ow_carry(w_carry_17_5_01)
    );
    wire w_sum_18_5_01, w_carry_18_5_01;
    math_adder_full FA_18_5_01 (
        .i_a(w_carry_17_4_01),
        .i_b(w_carry_17_4_02),
        .i_c(w_sum_18_4_01),
        .ow_sum(w_sum_18_5_01),
        .ow_carry(w_carry_18_5_01)
    );
    wire w_sum_19_5_01, w_carry_19_5_01;
    math_adder_full FA_19_5_01 (
        .i_a(w_carry_18_4_01),
        .i_b(w_carry_18_4_02),
        .i_c(w_sum_19_4_01),
        .ow_sum(w_sum_19_5_01),
        .ow_carry(w_carry_19_5_01)
    );
    wire w_sum_20_5_01, w_carry_20_5_01;
    math_adder_full FA_20_5_01 (
        .i_a(w_carry_19_4_01),
        .i_b(w_sum_20_4_01),
        .i_c(w_sum_20_3_02),
        .ow_sum(w_sum_20_5_01),
        .ow_carry(w_carry_20_5_01)
    );
    wire w_sum_21_5_01, w_carry_21_5_01;
    math_adder_full FA_21_5_01 (
        .i_a(w_carry_20_4_01),
        .i_b(w_sum_21_4_01),
        .i_c(w_sum_21_3_02),
        .ow_sum(w_sum_21_5_01),
        .ow_carry(w_carry_21_5_01)
    );
    wire w_sum_22_5_01, w_carry_22_5_01;
    math_adder_full FA_22_5_01 (
        .i_a(w_carry_21_4_01),
        .i_b(w_sum_22_4_01),
        .i_c(w_sum_22_3_02),
        .ow_sum(w_sum_22_5_01),
        .ow_carry(w_carry_22_5_01)
    );
    wire w_sum_23_5_01, w_carry_23_5_01;
    math_adder_full FA_23_5_01 (
        .i_a(w_carry_22_4_01),
        .i_b(w_sum_23_4_01),
        .i_c(w_sum_23_2_02),
        .ow_sum(w_sum_23_5_01),
        .ow_carry(w_carry_23_5_01)
    );
    wire w_sum_24_5_01, w_carry_24_5_01;
    math_adder_half HA_24_5_01 (
        .i_a(w_carry_23_4_01),
        .i_b(w_sum_24_4_01),
        .ow_sum(w_sum_24_5_01),
        .ow_carry(w_carry_24_5_01)
    );
    wire w_sum_25_5_01, w_carry_25_5_01;
    math_adder_half HA_25_5_01 (
        .i_a(w_carry_24_4_01),
        .i_b(w_sum_25_4_01),
        .ow_sum(w_sum_25_5_01),
        .ow_carry(w_carry_25_5_01)
    );
    wire w_sum_26_5_01, w_carry_26_5_01;
    math_adder_half HA_26_5_01 (
        .i_a(w_carry_25_4_01),
        .i_b(w_sum_26_4_01),
        .ow_sum(w_sum_26_5_01),
        .ow_carry(w_carry_26_5_01)
    );
    wire w_sum_27_5_01, w_carry_27_5_01;
    math_adder_half HA_27_5_01 (
        .i_a(w_carry_26_4_01),
        .i_b(w_sum_27_4_01),
        .ow_sum(w_sum_27_5_01),
        .ow_carry(w_carry_27_5_01)
    );
    wire w_sum_28_5_01, w_carry_28_5_01;
    math_adder_half HA_28_5_01 (
        .i_a(w_carry_27_4_01),
        .i_b(w_sum_28_4_01),
        .ow_sum(w_sum_28_5_01),
        .ow_carry(w_carry_28_5_01)
    );
    wire w_sum_29_5_01, w_carry_29_5_01;
    math_adder_half HA_29_5_01 (
        .i_a(w_carry_28_4_01),
        .i_b(w_sum_29_4_01),
        .ow_sum(w_sum_29_5_01),
        .ow_carry(w_carry_29_5_01)
    );
    wire w_sum_30_5_01, w_carry_30_5_01;
    math_adder_half HA_30_5_01 (
        .i_a(w_carry_29_4_01),
        .i_b(w_sum_30_4_01),
        .ow_sum(w_sum_30_5_01),
        .ow_carry(w_carry_30_5_01)
    );
    wire w_sum_31_5_01, w_carry_31_5_01;
    math_adder_half HA_31_5_01 (
        .i_a(w_carry_30_4_01),
        .i_b(w_sum_31_4_01),
        .ow_sum(w_sum_31_5_01),
        .ow_carry(w_carry_31_5_01)
    );

    // Wallace reduction layer 6
    wire w_sum_06_6_01, w_carry_06_6_01;
    math_adder_half HA_06_6_01 (
        .i_a(w_carry_05_5_01),
        .i_b(w_sum_06_5_01),
        .ow_sum(w_sum_06_6_01),
        .ow_carry(w_carry_06_6_01)
    );
    wire w_sum_07_6_01, w_carry_07_6_01;
    math_adder_half HA_07_6_01 (
        .i_a(w_carry_06_5_01),
        .i_b(w_sum_07_5_01),
        .ow_sum(w_sum_07_6_01),
        .ow_carry(w_carry_07_6_01)
    );
    wire w_sum_08_6_01, w_carry_08_6_01;
    math_adder_half HA_08_6_01 (
        .i_a(w_carry_07_5_01),
        .i_b(w_sum_08_5_01),
        .ow_sum(w_sum_08_6_01),
        .ow_carry(w_carry_08_6_01)
    );
    wire w_sum_09_6_01, w_carry_09_6_01;
    math_adder_half HA_09_6_01 (
        .i_a(w_carry_08_5_01),
        .i_b(w_sum_09_5_01),
        .ow_sum(w_sum_09_6_01),
        .ow_carry(w_carry_09_6_01)
    );
    wire w_sum_10_6_01, w_carry_10_6_01;
    math_adder_half HA_10_6_01 (
        .i_a(w_carry_09_5_01),
        .i_b(w_sum_10_5_01),
        .ow_sum(w_sum_10_6_01),
        .ow_carry(w_carry_10_6_01)
    );
    wire w_sum_11_6_01, w_carry_11_6_01;
    math_adder_half HA_11_6_01 (
        .i_a(w_carry_10_5_01),
        .i_b(w_sum_11_5_01),
        .ow_sum(w_sum_11_6_01),
        .ow_carry(w_carry_11_6_01)
    );
    wire w_sum_12_6_01, w_carry_12_6_01;
    math_adder_half HA_12_6_01 (
        .i_a(w_carry_11_5_01),
        .i_b(w_sum_12_5_01),
        .ow_sum(w_sum_12_6_01),
        .ow_carry(w_carry_12_6_01)
    );
    wire w_sum_13_6_01, w_carry_13_6_01;
    math_adder_half HA_13_6_01 (
        .i_a(w_carry_12_5_01),
        .i_b(w_sum_13_5_01),
        .ow_sum(w_sum_13_6_01),
        .ow_carry(w_carry_13_6_01)
    );
    wire w_sum_14_6_01, w_carry_14_6_01;
    math_adder_half HA_14_6_01 (
        .i_a(w_carry_13_5_01),
        .i_b(w_sum_14_5_01),
        .ow_sum(w_sum_14_6_01),
        .ow_carry(w_carry_14_6_01)
    );
    wire w_sum_15_6_01, w_carry_15_6_01;
    math_adder_full FA_15_6_01 (
        .i_a(w_carry_14_5_01),
        .i_b(w_sum_15_5_01),
        .i_c(w_sum_15_4_02),
        .ow_sum(w_sum_15_6_01),
        .ow_carry(w_carry_15_6_01)
    );
    wire w_sum_16_6_01, w_carry_16_6_01;
    math_adder_full FA_16_6_01 (
        .i_a(w_carry_15_5_01),
        .i_b(w_sum_16_5_01),
        .i_c(w_sum_16_4_02),
        .ow_sum(w_sum_16_6_01),
        .ow_carry(w_carry_16_6_01)
    );
    wire w_sum_17_6_01, w_carry_17_6_01;
    math_adder_full FA_17_6_01 (
        .i_a(w_carry_16_5_01),
        .i_b(w_sum_17_5_01),
        .i_c(w_sum_17_4_02),
        .ow_sum(w_sum_17_6_01),
        .ow_carry(w_carry_17_6_01)
    );
    wire w_sum_18_6_01, w_carry_18_6_01;
    math_adder_full FA_18_6_01 (
        .i_a(w_carry_17_5_01),
        .i_b(w_sum_18_5_01),
        .i_c(w_sum_18_4_02),
        .ow_sum(w_sum_18_6_01),
        .ow_carry(w_carry_18_6_01)
    );
    wire w_sum_19_6_01, w_carry_19_6_01;
    math_adder_full FA_19_6_01 (
        .i_a(w_carry_18_5_01),
        .i_b(w_sum_19_5_01),
        .i_c(w_sum_19_3_02),
        .ow_sum(w_sum_19_6_01),
        .ow_carry(w_carry_19_6_01)
    );
    wire w_sum_20_6_01, w_carry_20_6_01;
    math_adder_half HA_20_6_01 (
        .i_a(w_carry_19_5_01),
        .i_b(w_sum_20_5_01),
        .ow_sum(w_sum_20_6_01),
        .ow_carry(w_carry_20_6_01)
    );
    wire w_sum_21_6_01, w_carry_21_6_01;
    math_adder_half HA_21_6_01 (
        .i_a(w_carry_20_5_01),
        .i_b(w_sum_21_5_01),
        .ow_sum(w_sum_21_6_01),
        .ow_carry(w_carry_21_6_01)
    );
    wire w_sum_22_6_01, w_carry_22_6_01;
    math_adder_half HA_22_6_01 (
        .i_a(w_carry_21_5_01),
        .i_b(w_sum_22_5_01),
        .ow_sum(w_sum_22_6_01),
        .ow_carry(w_carry_22_6_01)
    );
    wire w_sum_23_6_01, w_carry_23_6_01;
    math_adder_half HA_23_6_01 (
        .i_a(w_carry_22_5_01),
        .i_b(w_sum_23_5_01),
        .ow_sum(w_sum_23_6_01),
        .ow_carry(w_carry_23_6_01)
    );
    wire w_sum_24_6_01, w_carry_24_6_01;
    math_adder_half HA_24_6_01 (
        .i_a(w_carry_23_5_01),
        .i_b(w_sum_24_5_01),
        .ow_sum(w_sum_24_6_01),
        .ow_carry(w_carry_24_6_01)
    );
    wire w_sum_25_6_01, w_carry_25_6_01;
    math_adder_half HA_25_6_01 (
        .i_a(w_carry_24_5_01),
        .i_b(w_sum_25_5_01),
        .ow_sum(w_sum_25_6_01),
        .ow_carry(w_carry_25_6_01)
    );
    wire w_sum_26_6_01, w_carry_26_6_01;
    math_adder_half HA_26_6_01 (
        .i_a(w_carry_25_5_01),
        .i_b(w_sum_26_5_01),
        .ow_sum(w_sum_26_6_01),
        .ow_carry(w_carry_26_6_01)
    );
    wire w_sum_27_6_01, w_carry_27_6_01;
    math_adder_half HA_27_6_01 (
        .i_a(w_carry_26_5_01),
        .i_b(w_sum_27_5_01),
        .ow_sum(w_sum_27_6_01),
        .ow_carry(w_carry_27_6_01)
    );
    wire w_sum_28_6_01, w_carry_28_6_01;
    math_adder_half HA_28_6_01 (
        .i_a(w_carry_27_5_01),
        .i_b(w_sum_28_5_01),
        .ow_sum(w_sum_28_6_01),
        .ow_carry(w_carry_28_6_01)
    );
    wire w_sum_29_6_01, w_carry_29_6_01;
    math_adder_half HA_29_6_01 (
        .i_a(w_carry_28_5_01),
        .i_b(w_sum_29_5_01),
        .ow_sum(w_sum_29_6_01),
        .ow_carry(w_carry_29_6_01)
    );
    wire w_sum_30_6_01, w_carry_30_6_01;
    math_adder_half HA_30_6_01 (
        .i_a(w_carry_29_5_01),
        .i_b(w_sum_30_5_01),
        .ow_sum(w_sum_30_6_01),
        .ow_carry(w_carry_30_6_01)
    );
    wire w_sum_31_6_01, w_carry_31_6_01;
    math_adder_half HA_31_6_01 (
        .i_a(w_carry_30_5_01),
        .i_b(w_sum_31_5_01),
        .ow_sum(w_sum_31_6_01),
        .ow_carry(w_carry_31_6_01)
    );

    // Final addition stage: two reduced rows into a Brent-Kung CPA
    wire [31:0] w_cpa_row0 = {
        w_carry_30_6_01,
        w_carry_29_6_01,
        w_carry_28_6_01,
        w_carry_27_6_01,
        w_carry_26_6_01,
        w_carry_25_6_01,
        w_carry_24_6_01,
        w_carry_23_6_01,
        w_carry_22_6_01,
        w_carry_21_6_01,
        w_carry_20_6_01,
        w_carry_19_6_01,
        w_carry_18_6_01,
        w_carry_17_6_01,
        w_carry_16_6_01,
        w_carry_15_6_01,
        w_carry_14_6_01,
        w_carry_13_6_01,
        w_carry_12_6_01,
        w_carry_11_6_01,
        w_carry_10_6_01,
        w_carry_09_6_01,
        w_carry_08_6_01,
        w_carry_07_6_01,
        w_carry_06_6_01,
        w_sum_06_6_01,
        w_sum_05_5_01,
        w_sum_04_4_01,
        w_sum_03_3_01,
        w_sum_02_2_01,
        w_sum_01_1_01,
        w_pp_00_00
    };
    wire [31:0] w_cpa_row1 = {
        w_sum_31_6_01,
        w_sum_30_6_01,
        w_sum_29_6_01,
        w_sum_28_6_01,
        w_sum_27_6_01,
        w_sum_26_6_01,
        w_sum_25_6_01,
        w_sum_24_6_01,
        w_sum_23_6_01,
        w_sum_22_6_01,
        w_sum_21_6_01,
        w_sum_20_6_01,
        w_sum_19_6_01,
        w_sum_18_6_01,
        w_sum_17_6_01,
        w_sum_16_6_01,
        w_sum_15_6_01,
        w_sum_14_6_01,
        w_sum_13_6_01,
        w_sum_12_6_01,
        w_sum_11_6_01,
        w_sum_10_6_01,
        w_sum_09_6_01,
        w_sum_08_6_01,
        w_sum_07_6_01,
        1'b0,
        1'b0,
        1'b0,
        1'b0,
        1'b0,
        1'b0,
        1'b0
    };

    /* verilator lint_off UNUSEDSIGNAL */
    wire w_cpa_carry_unused;
    /* verilator lint_on UNUSEDSIGNAL */
    math_adder_brent_kung_032 #(
        .N(32)
    ) u_final_cpa (
        .i_a(w_cpa_row0),
        .i_b(w_cpa_row1),
        .i_c(1'b0),
        .ow_sum(ow_product),
        .ow_carry(w_cpa_carry_unused)
    );

endmodule
