// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_multiplier_dadda_tree_016
// Purpose: Math Multiplier Dadda Tree 016 module
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_multiplier_dadda_tree_016 #(
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

    // Dadda reduction stage 1: max column height 13
    wire w_sum_13_01, w_carry_13_01;
    math_adder_half HA__13_01 (
        .i_a(w_pp_00_13),
        .i_b(w_pp_01_12),
        .ow_sum(w_sum_13_01),
        .ow_carry(w_carry_13_01)
    );
    wire w_sum_14_01, w_carry_14_01;
    math_adder_carry_save CSA_14_01 (
        .i_a(w_pp_00_14),
        .i_b(w_pp_01_13),
        .i_c(w_pp_02_12),
        .ow_sum(w_sum_14_01),
        .ow_carry(w_carry_14_01)
    );
    wire w_sum_14_02, w_carry_14_02;
    math_adder_half HA__14_02 (
        .i_a(w_pp_03_11),
        .i_b(w_pp_04_10),
        .ow_sum(w_sum_14_02),
        .ow_carry(w_carry_14_02)
    );
    wire w_sum_15_01, w_carry_15_01;
    math_adder_carry_save CSA_15_01 (
        .i_a(w_pp_00_15),
        .i_b(w_pp_01_14),
        .i_c(w_pp_02_13),
        .ow_sum(w_sum_15_01),
        .ow_carry(w_carry_15_01)
    );
    wire w_sum_15_02, w_carry_15_02;
    math_adder_carry_save CSA_15_02 (
        .i_a(w_pp_03_12),
        .i_b(w_pp_04_11),
        .i_c(w_pp_05_10),
        .ow_sum(w_sum_15_02),
        .ow_carry(w_carry_15_02)
    );
    wire w_sum_15_03, w_carry_15_03;
    math_adder_half HA__15_03 (
        .i_a(w_pp_06_09),
        .i_b(w_pp_07_08),
        .ow_sum(w_sum_15_03),
        .ow_carry(w_carry_15_03)
    );
    wire w_sum_16_01, w_carry_16_01;
    math_adder_carry_save CSA_16_01 (
        .i_a(w_pp_01_15),
        .i_b(w_pp_02_14),
        .i_c(w_pp_03_13),
        .ow_sum(w_sum_16_01),
        .ow_carry(w_carry_16_01)
    );
    wire w_sum_16_02, w_carry_16_02;
    math_adder_carry_save CSA_16_02 (
        .i_a(w_pp_04_12),
        .i_b(w_pp_05_11),
        .i_c(w_pp_06_10),
        .ow_sum(w_sum_16_02),
        .ow_carry(w_carry_16_02)
    );
    wire w_sum_16_03, w_carry_16_03;
    math_adder_half HA__16_03 (
        .i_a(w_pp_07_09),
        .i_b(w_pp_08_08),
        .ow_sum(w_sum_16_03),
        .ow_carry(w_carry_16_03)
    );
    wire w_sum_17_01, w_carry_17_01;
    math_adder_carry_save CSA_17_01 (
        .i_a(w_pp_02_15),
        .i_b(w_pp_03_14),
        .i_c(w_pp_04_13),
        .ow_sum(w_sum_17_01),
        .ow_carry(w_carry_17_01)
    );
    wire w_sum_17_02, w_carry_17_02;
    math_adder_carry_save CSA_17_02 (
        .i_a(w_pp_05_12),
        .i_b(w_pp_06_11),
        .i_c(w_pp_07_10),
        .ow_sum(w_sum_17_02),
        .ow_carry(w_carry_17_02)
    );
    wire w_sum_18_01, w_carry_18_01;
    math_adder_carry_save CSA_18_01 (
        .i_a(w_pp_03_15),
        .i_b(w_pp_04_14),
        .i_c(w_pp_05_13),
        .ow_sum(w_sum_18_01),
        .ow_carry(w_carry_18_01)
    );

    // Dadda reduction stage 2: max column height 9
    wire w_sum_09_01, w_carry_09_01;
    math_adder_half HA__09_01 (
        .i_a(w_pp_00_09),
        .i_b(w_pp_01_08),
        .ow_sum(w_sum_09_01),
        .ow_carry(w_carry_09_01)
    );
    wire w_sum_10_01, w_carry_10_01;
    math_adder_carry_save CSA_10_01 (
        .i_a(w_pp_00_10),
        .i_b(w_pp_01_09),
        .i_c(w_pp_02_08),
        .ow_sum(w_sum_10_01),
        .ow_carry(w_carry_10_01)
    );
    wire w_sum_10_02, w_carry_10_02;
    math_adder_half HA__10_02 (
        .i_a(w_pp_03_07),
        .i_b(w_pp_04_06),
        .ow_sum(w_sum_10_02),
        .ow_carry(w_carry_10_02)
    );
    wire w_sum_11_01, w_carry_11_01;
    math_adder_carry_save CSA_11_01 (
        .i_a(w_pp_00_11),
        .i_b(w_pp_01_10),
        .i_c(w_pp_02_09),
        .ow_sum(w_sum_11_01),
        .ow_carry(w_carry_11_01)
    );
    wire w_sum_11_02, w_carry_11_02;
    math_adder_carry_save CSA_11_02 (
        .i_a(w_pp_03_08),
        .i_b(w_pp_04_07),
        .i_c(w_pp_05_06),
        .ow_sum(w_sum_11_02),
        .ow_carry(w_carry_11_02)
    );
    wire w_sum_11_03, w_carry_11_03;
    math_adder_half HA__11_03 (
        .i_a(w_pp_06_05),
        .i_b(w_pp_07_04),
        .ow_sum(w_sum_11_03),
        .ow_carry(w_carry_11_03)
    );
    wire w_sum_12_01, w_carry_12_01;
    math_adder_carry_save CSA_12_01 (
        .i_a(w_pp_00_12),
        .i_b(w_pp_01_11),
        .i_c(w_pp_02_10),
        .ow_sum(w_sum_12_01),
        .ow_carry(w_carry_12_01)
    );
    wire w_sum_12_02, w_carry_12_02;
    math_adder_carry_save CSA_12_02 (
        .i_a(w_pp_03_09),
        .i_b(w_pp_04_08),
        .i_c(w_pp_05_07),
        .ow_sum(w_sum_12_02),
        .ow_carry(w_carry_12_02)
    );
    wire w_sum_12_03, w_carry_12_03;
    math_adder_carry_save CSA_12_03 (
        .i_a(w_pp_06_06),
        .i_b(w_pp_07_05),
        .i_c(w_pp_08_04),
        .ow_sum(w_sum_12_03),
        .ow_carry(w_carry_12_03)
    );
    wire w_sum_12_04, w_carry_12_04;
    math_adder_half HA__12_04 (
        .i_a(w_pp_09_03),
        .i_b(w_pp_10_02),
        .ow_sum(w_sum_12_04),
        .ow_carry(w_carry_12_04)
    );
    wire w_sum_13_02, w_carry_13_02;
    math_adder_carry_save CSA_13_02 (
        .i_a(w_pp_02_11),
        .i_b(w_pp_03_10),
        .i_c(w_pp_04_09),
        .ow_sum(w_sum_13_02),
        .ow_carry(w_carry_13_02)
    );
    wire w_sum_13_03, w_carry_13_03;
    math_adder_carry_save CSA_13_03 (
        .i_a(w_pp_05_08),
        .i_b(w_pp_06_07),
        .i_c(w_pp_07_06),
        .ow_sum(w_sum_13_03),
        .ow_carry(w_carry_13_03)
    );
    wire w_sum_13_04, w_carry_13_04;
    math_adder_carry_save CSA_13_04 (
        .i_a(w_pp_08_05),
        .i_b(w_pp_09_04),
        .i_c(w_pp_10_03),
        .ow_sum(w_sum_13_04),
        .ow_carry(w_carry_13_04)
    );
    wire w_sum_13_05, w_carry_13_05;
    math_adder_carry_save CSA_13_05 (
        .i_a(w_pp_11_02),
        .i_b(w_pp_12_01),
        .i_c(w_pp_13_00),
        .ow_sum(w_sum_13_05),
        .ow_carry(w_carry_13_05)
    );
    wire w_sum_14_03, w_carry_14_03;
    math_adder_carry_save CSA_14_03 (
        .i_a(w_pp_05_09),
        .i_b(w_pp_06_08),
        .i_c(w_pp_07_07),
        .ow_sum(w_sum_14_03),
        .ow_carry(w_carry_14_03)
    );
    wire w_sum_14_04, w_carry_14_04;
    math_adder_carry_save CSA_14_04 (
        .i_a(w_pp_08_06),
        .i_b(w_pp_09_05),
        .i_c(w_pp_10_04),
        .ow_sum(w_sum_14_04),
        .ow_carry(w_carry_14_04)
    );
    wire w_sum_14_05, w_carry_14_05;
    math_adder_carry_save CSA_14_05 (
        .i_a(w_pp_11_03),
        .i_b(w_pp_12_02),
        .i_c(w_pp_13_01),
        .ow_sum(w_sum_14_05),
        .ow_carry(w_carry_14_05)
    );
    wire w_sum_14_06, w_carry_14_06;
    math_adder_carry_save CSA_14_06 (
        .i_a(w_pp_14_00),
        .i_b(w_carry_13_01),
        .i_c(w_sum_14_01),
        .ow_sum(w_sum_14_06),
        .ow_carry(w_carry_14_06)
    );
    wire w_sum_15_04, w_carry_15_04;
    math_adder_carry_save CSA_15_04 (
        .i_a(w_pp_08_07),
        .i_b(w_pp_09_06),
        .i_c(w_pp_10_05),
        .ow_sum(w_sum_15_04),
        .ow_carry(w_carry_15_04)
    );
    wire w_sum_15_05, w_carry_15_05;
    math_adder_carry_save CSA_15_05 (
        .i_a(w_pp_11_04),
        .i_b(w_pp_12_03),
        .i_c(w_pp_13_02),
        .ow_sum(w_sum_15_05),
        .ow_carry(w_carry_15_05)
    );
    wire w_sum_15_06, w_carry_15_06;
    math_adder_carry_save CSA_15_06 (
        .i_a(w_pp_14_01),
        .i_b(w_pp_15_00),
        .i_c(w_carry_14_01),
        .ow_sum(w_sum_15_06),
        .ow_carry(w_carry_15_06)
    );
    wire w_sum_15_07, w_carry_15_07;
    math_adder_carry_save CSA_15_07 (
        .i_a(w_carry_14_02),
        .i_b(w_sum_15_01),
        .i_c(w_sum_15_02),
        .ow_sum(w_sum_15_07),
        .ow_carry(w_carry_15_07)
    );
    wire w_sum_16_04, w_carry_16_04;
    math_adder_carry_save CSA_16_04 (
        .i_a(w_pp_09_07),
        .i_b(w_pp_10_06),
        .i_c(w_pp_11_05),
        .ow_sum(w_sum_16_04),
        .ow_carry(w_carry_16_04)
    );
    wire w_sum_16_05, w_carry_16_05;
    math_adder_carry_save CSA_16_05 (
        .i_a(w_pp_12_04),
        .i_b(w_pp_13_03),
        .i_c(w_pp_14_02),
        .ow_sum(w_sum_16_05),
        .ow_carry(w_carry_16_05)
    );
    wire w_sum_16_06, w_carry_16_06;
    math_adder_carry_save CSA_16_06 (
        .i_a(w_pp_15_01),
        .i_b(w_carry_15_01),
        .i_c(w_carry_15_02),
        .ow_sum(w_sum_16_06),
        .ow_carry(w_carry_16_06)
    );
    wire w_sum_16_07, w_carry_16_07;
    math_adder_carry_save CSA_16_07 (
        .i_a(w_carry_15_03),
        .i_b(w_sum_16_01),
        .i_c(w_sum_16_02),
        .ow_sum(w_sum_16_07),
        .ow_carry(w_carry_16_07)
    );
    wire w_sum_17_03, w_carry_17_03;
    math_adder_carry_save CSA_17_03 (
        .i_a(w_pp_08_09),
        .i_b(w_pp_09_08),
        .i_c(w_pp_10_07),
        .ow_sum(w_sum_17_03),
        .ow_carry(w_carry_17_03)
    );
    wire w_sum_17_04, w_carry_17_04;
    math_adder_carry_save CSA_17_04 (
        .i_a(w_pp_11_06),
        .i_b(w_pp_12_05),
        .i_c(w_pp_13_04),
        .ow_sum(w_sum_17_04),
        .ow_carry(w_carry_17_04)
    );
    wire w_sum_17_05, w_carry_17_05;
    math_adder_carry_save CSA_17_05 (
        .i_a(w_pp_14_03),
        .i_b(w_pp_15_02),
        .i_c(w_carry_16_01),
        .ow_sum(w_sum_17_05),
        .ow_carry(w_carry_17_05)
    );
    wire w_sum_17_06, w_carry_17_06;
    math_adder_carry_save CSA_17_06 (
        .i_a(w_carry_16_02),
        .i_b(w_carry_16_03),
        .i_c(w_sum_17_01),
        .ow_sum(w_sum_17_06),
        .ow_carry(w_carry_17_06)
    );
    wire w_sum_18_02, w_carry_18_02;
    math_adder_carry_save CSA_18_02 (
        .i_a(w_pp_06_12),
        .i_b(w_pp_07_11),
        .i_c(w_pp_08_10),
        .ow_sum(w_sum_18_02),
        .ow_carry(w_carry_18_02)
    );
    wire w_sum_18_03, w_carry_18_03;
    math_adder_carry_save CSA_18_03 (
        .i_a(w_pp_09_09),
        .i_b(w_pp_10_08),
        .i_c(w_pp_11_07),
        .ow_sum(w_sum_18_03),
        .ow_carry(w_carry_18_03)
    );
    wire w_sum_18_04, w_carry_18_04;
    math_adder_carry_save CSA_18_04 (
        .i_a(w_pp_12_06),
        .i_b(w_pp_13_05),
        .i_c(w_pp_14_04),
        .ow_sum(w_sum_18_04),
        .ow_carry(w_carry_18_04)
    );
    wire w_sum_18_05, w_carry_18_05;
    math_adder_carry_save CSA_18_05 (
        .i_a(w_pp_15_03),
        .i_b(w_carry_17_01),
        .i_c(w_carry_17_02),
        .ow_sum(w_sum_18_05),
        .ow_carry(w_carry_18_05)
    );
    wire w_sum_19_01, w_carry_19_01;
    math_adder_carry_save CSA_19_01 (
        .i_a(w_pp_04_15),
        .i_b(w_pp_05_14),
        .i_c(w_pp_06_13),
        .ow_sum(w_sum_19_01),
        .ow_carry(w_carry_19_01)
    );
    wire w_sum_19_02, w_carry_19_02;
    math_adder_carry_save CSA_19_02 (
        .i_a(w_pp_07_12),
        .i_b(w_pp_08_11),
        .i_c(w_pp_09_10),
        .ow_sum(w_sum_19_02),
        .ow_carry(w_carry_19_02)
    );
    wire w_sum_19_03, w_carry_19_03;
    math_adder_carry_save CSA_19_03 (
        .i_a(w_pp_10_09),
        .i_b(w_pp_11_08),
        .i_c(w_pp_12_07),
        .ow_sum(w_sum_19_03),
        .ow_carry(w_carry_19_03)
    );
    wire w_sum_19_04, w_carry_19_04;
    math_adder_carry_save CSA_19_04 (
        .i_a(w_pp_13_06),
        .i_b(w_pp_14_05),
        .i_c(w_pp_15_04),
        .ow_sum(w_sum_19_04),
        .ow_carry(w_carry_19_04)
    );
    wire w_sum_20_01, w_carry_20_01;
    math_adder_carry_save CSA_20_01 (
        .i_a(w_pp_05_15),
        .i_b(w_pp_06_14),
        .i_c(w_pp_07_13),
        .ow_sum(w_sum_20_01),
        .ow_carry(w_carry_20_01)
    );
    wire w_sum_20_02, w_carry_20_02;
    math_adder_carry_save CSA_20_02 (
        .i_a(w_pp_08_12),
        .i_b(w_pp_09_11),
        .i_c(w_pp_10_10),
        .ow_sum(w_sum_20_02),
        .ow_carry(w_carry_20_02)
    );
    wire w_sum_20_03, w_carry_20_03;
    math_adder_carry_save CSA_20_03 (
        .i_a(w_pp_11_09),
        .i_b(w_pp_12_08),
        .i_c(w_pp_13_07),
        .ow_sum(w_sum_20_03),
        .ow_carry(w_carry_20_03)
    );
    wire w_sum_21_01, w_carry_21_01;
    math_adder_carry_save CSA_21_01 (
        .i_a(w_pp_06_15),
        .i_b(w_pp_07_14),
        .i_c(w_pp_08_13),
        .ow_sum(w_sum_21_01),
        .ow_carry(w_carry_21_01)
    );
    wire w_sum_21_02, w_carry_21_02;
    math_adder_carry_save CSA_21_02 (
        .i_a(w_pp_09_12),
        .i_b(w_pp_10_11),
        .i_c(w_pp_11_10),
        .ow_sum(w_sum_21_02),
        .ow_carry(w_carry_21_02)
    );
    wire w_sum_22_01, w_carry_22_01;
    math_adder_carry_save CSA_22_01 (
        .i_a(w_pp_07_15),
        .i_b(w_pp_08_14),
        .i_c(w_pp_09_13),
        .ow_sum(w_sum_22_01),
        .ow_carry(w_carry_22_01)
    );

    // Dadda reduction stage 3: max column height 6
    wire w_sum_06_01, w_carry_06_01;
    math_adder_half HA__06_01 (
        .i_a(w_pp_00_06),
        .i_b(w_pp_01_05),
        .ow_sum(w_sum_06_01),
        .ow_carry(w_carry_06_01)
    );
    wire w_sum_07_01, w_carry_07_01;
    math_adder_carry_save CSA_07_01 (
        .i_a(w_pp_00_07),
        .i_b(w_pp_01_06),
        .i_c(w_pp_02_05),
        .ow_sum(w_sum_07_01),
        .ow_carry(w_carry_07_01)
    );
    wire w_sum_07_02, w_carry_07_02;
    math_adder_half HA__07_02 (
        .i_a(w_pp_03_04),
        .i_b(w_pp_04_03),
        .ow_sum(w_sum_07_02),
        .ow_carry(w_carry_07_02)
    );
    wire w_sum_08_01, w_carry_08_01;
    math_adder_carry_save CSA_08_01 (
        .i_a(w_pp_00_08),
        .i_b(w_pp_01_07),
        .i_c(w_pp_02_06),
        .ow_sum(w_sum_08_01),
        .ow_carry(w_carry_08_01)
    );
    wire w_sum_08_02, w_carry_08_02;
    math_adder_carry_save CSA_08_02 (
        .i_a(w_pp_03_05),
        .i_b(w_pp_04_04),
        .i_c(w_pp_05_03),
        .ow_sum(w_sum_08_02),
        .ow_carry(w_carry_08_02)
    );
    wire w_sum_08_03, w_carry_08_03;
    math_adder_half HA__08_03 (
        .i_a(w_pp_06_02),
        .i_b(w_pp_07_01),
        .ow_sum(w_sum_08_03),
        .ow_carry(w_carry_08_03)
    );
    wire w_sum_09_02, w_carry_09_02;
    math_adder_carry_save CSA_09_02 (
        .i_a(w_pp_02_07),
        .i_b(w_pp_03_06),
        .i_c(w_pp_04_05),
        .ow_sum(w_sum_09_02),
        .ow_carry(w_carry_09_02)
    );
    wire w_sum_09_03, w_carry_09_03;
    math_adder_carry_save CSA_09_03 (
        .i_a(w_pp_05_04),
        .i_b(w_pp_06_03),
        .i_c(w_pp_07_02),
        .ow_sum(w_sum_09_03),
        .ow_carry(w_carry_09_03)
    );
    wire w_sum_09_04, w_carry_09_04;
    math_adder_carry_save CSA_09_04 (
        .i_a(w_pp_08_01),
        .i_b(w_pp_09_00),
        .i_c(w_sum_09_01),
        .ow_sum(w_sum_09_04),
        .ow_carry(w_carry_09_04)
    );
    wire w_sum_10_03, w_carry_10_03;
    math_adder_carry_save CSA_10_03 (
        .i_a(w_pp_05_05),
        .i_b(w_pp_06_04),
        .i_c(w_pp_07_03),
        .ow_sum(w_sum_10_03),
        .ow_carry(w_carry_10_03)
    );
    wire w_sum_10_04, w_carry_10_04;
    math_adder_carry_save CSA_10_04 (
        .i_a(w_pp_08_02),
        .i_b(w_pp_09_01),
        .i_c(w_pp_10_00),
        .ow_sum(w_sum_10_04),
        .ow_carry(w_carry_10_04)
    );
    wire w_sum_10_05, w_carry_10_05;
    math_adder_carry_save CSA_10_05 (
        .i_a(w_carry_09_01),
        .i_b(w_sum_10_01),
        .i_c(w_sum_10_02),
        .ow_sum(w_sum_10_05),
        .ow_carry(w_carry_10_05)
    );
    wire w_sum_11_04, w_carry_11_04;
    math_adder_carry_save CSA_11_04 (
        .i_a(w_pp_08_03),
        .i_b(w_pp_09_02),
        .i_c(w_pp_10_01),
        .ow_sum(w_sum_11_04),
        .ow_carry(w_carry_11_04)
    );
    wire w_sum_11_05, w_carry_11_05;
    math_adder_carry_save CSA_11_05 (
        .i_a(w_pp_11_00),
        .i_b(w_carry_10_01),
        .i_c(w_carry_10_02),
        .ow_sum(w_sum_11_05),
        .ow_carry(w_carry_11_05)
    );
    wire w_sum_11_06, w_carry_11_06;
    math_adder_carry_save CSA_11_06 (
        .i_a(w_sum_11_01),
        .i_b(w_sum_11_02),
        .i_c(w_sum_11_03),
        .ow_sum(w_sum_11_06),
        .ow_carry(w_carry_11_06)
    );
    wire w_sum_12_05, w_carry_12_05;
    math_adder_carry_save CSA_12_05 (
        .i_a(w_pp_11_01),
        .i_b(w_pp_12_00),
        .i_c(w_carry_11_01),
        .ow_sum(w_sum_12_05),
        .ow_carry(w_carry_12_05)
    );
    wire w_sum_12_06, w_carry_12_06;
    math_adder_carry_save CSA_12_06 (
        .i_a(w_carry_11_02),
        .i_b(w_carry_11_03),
        .i_c(w_sum_12_01),
        .ow_sum(w_sum_12_06),
        .ow_carry(w_carry_12_06)
    );
    wire w_sum_12_07, w_carry_12_07;
    math_adder_carry_save CSA_12_07 (
        .i_a(w_sum_12_02),
        .i_b(w_sum_12_03),
        .i_c(w_sum_12_04),
        .ow_sum(w_sum_12_07),
        .ow_carry(w_carry_12_07)
    );
    wire w_sum_13_06, w_carry_13_06;
    math_adder_carry_save CSA_13_06 (
        .i_a(w_sum_13_01),
        .i_b(w_carry_12_01),
        .i_c(w_carry_12_02),
        .ow_sum(w_sum_13_06),
        .ow_carry(w_carry_13_06)
    );
    wire w_sum_13_07, w_carry_13_07;
    math_adder_carry_save CSA_13_07 (
        .i_a(w_carry_12_03),
        .i_b(w_carry_12_04),
        .i_c(w_sum_13_02),
        .ow_sum(w_sum_13_07),
        .ow_carry(w_carry_13_07)
    );
    wire w_sum_13_08, w_carry_13_08;
    math_adder_carry_save CSA_13_08 (
        .i_a(w_sum_13_03),
        .i_b(w_sum_13_04),
        .i_c(w_sum_13_05),
        .ow_sum(w_sum_13_08),
        .ow_carry(w_carry_13_08)
    );
    wire w_sum_14_07, w_carry_14_07;
    math_adder_carry_save CSA_14_07 (
        .i_a(w_sum_14_02),
        .i_b(w_carry_13_02),
        .i_c(w_carry_13_03),
        .ow_sum(w_sum_14_07),
        .ow_carry(w_carry_14_07)
    );
    wire w_sum_14_08, w_carry_14_08;
    math_adder_carry_save CSA_14_08 (
        .i_a(w_carry_13_04),
        .i_b(w_carry_13_05),
        .i_c(w_sum_14_03),
        .ow_sum(w_sum_14_08),
        .ow_carry(w_carry_14_08)
    );
    wire w_sum_14_09, w_carry_14_09;
    math_adder_carry_save CSA_14_09 (
        .i_a(w_sum_14_04),
        .i_b(w_sum_14_05),
        .i_c(w_sum_14_06),
        .ow_sum(w_sum_14_09),
        .ow_carry(w_carry_14_09)
    );
    wire w_sum_15_08, w_carry_15_08;
    math_adder_carry_save CSA_15_08 (
        .i_a(w_sum_15_03),
        .i_b(w_carry_14_03),
        .i_c(w_carry_14_04),
        .ow_sum(w_sum_15_08),
        .ow_carry(w_carry_15_08)
    );
    wire w_sum_15_09, w_carry_15_09;
    math_adder_carry_save CSA_15_09 (
        .i_a(w_carry_14_05),
        .i_b(w_carry_14_06),
        .i_c(w_sum_15_04),
        .ow_sum(w_sum_15_09),
        .ow_carry(w_carry_15_09)
    );
    wire w_sum_15_10, w_carry_15_10;
    math_adder_carry_save CSA_15_10 (
        .i_a(w_sum_15_05),
        .i_b(w_sum_15_06),
        .i_c(w_sum_15_07),
        .ow_sum(w_sum_15_10),
        .ow_carry(w_carry_15_10)
    );
    wire w_sum_16_08, w_carry_16_08;
    math_adder_carry_save CSA_16_08 (
        .i_a(w_sum_16_03),
        .i_b(w_carry_15_04),
        .i_c(w_carry_15_05),
        .ow_sum(w_sum_16_08),
        .ow_carry(w_carry_16_08)
    );
    wire w_sum_16_09, w_carry_16_09;
    math_adder_carry_save CSA_16_09 (
        .i_a(w_carry_15_06),
        .i_b(w_carry_15_07),
        .i_c(w_sum_16_04),
        .ow_sum(w_sum_16_09),
        .ow_carry(w_carry_16_09)
    );
    wire w_sum_16_10, w_carry_16_10;
    math_adder_carry_save CSA_16_10 (
        .i_a(w_sum_16_05),
        .i_b(w_sum_16_06),
        .i_c(w_sum_16_07),
        .ow_sum(w_sum_16_10),
        .ow_carry(w_carry_16_10)
    );
    wire w_sum_17_07, w_carry_17_07;
    math_adder_carry_save CSA_17_07 (
        .i_a(w_sum_17_02),
        .i_b(w_carry_16_04),
        .i_c(w_carry_16_05),
        .ow_sum(w_sum_17_07),
        .ow_carry(w_carry_17_07)
    );
    wire w_sum_17_08, w_carry_17_08;
    math_adder_carry_save CSA_17_08 (
        .i_a(w_carry_16_06),
        .i_b(w_carry_16_07),
        .i_c(w_sum_17_03),
        .ow_sum(w_sum_17_08),
        .ow_carry(w_carry_17_08)
    );
    wire w_sum_17_09, w_carry_17_09;
    math_adder_carry_save CSA_17_09 (
        .i_a(w_sum_17_04),
        .i_b(w_sum_17_05),
        .i_c(w_sum_17_06),
        .ow_sum(w_sum_17_09),
        .ow_carry(w_carry_17_09)
    );
    wire w_sum_18_06, w_carry_18_06;
    math_adder_carry_save CSA_18_06 (
        .i_a(w_sum_18_01),
        .i_b(w_carry_17_03),
        .i_c(w_carry_17_04),
        .ow_sum(w_sum_18_06),
        .ow_carry(w_carry_18_06)
    );
    wire w_sum_18_07, w_carry_18_07;
    math_adder_carry_save CSA_18_07 (
        .i_a(w_carry_17_05),
        .i_b(w_carry_17_06),
        .i_c(w_sum_18_02),
        .ow_sum(w_sum_18_07),
        .ow_carry(w_carry_18_07)
    );
    wire w_sum_18_08, w_carry_18_08;
    math_adder_carry_save CSA_18_08 (
        .i_a(w_sum_18_03),
        .i_b(w_sum_18_04),
        .i_c(w_sum_18_05),
        .ow_sum(w_sum_18_08),
        .ow_carry(w_carry_18_08)
    );
    wire w_sum_19_05, w_carry_19_05;
    math_adder_carry_save CSA_19_05 (
        .i_a(w_carry_18_01),
        .i_b(w_carry_18_02),
        .i_c(w_carry_18_03),
        .ow_sum(w_sum_19_05),
        .ow_carry(w_carry_19_05)
    );
    wire w_sum_19_06, w_carry_19_06;
    math_adder_carry_save CSA_19_06 (
        .i_a(w_carry_18_04),
        .i_b(w_carry_18_05),
        .i_c(w_sum_19_01),
        .ow_sum(w_sum_19_06),
        .ow_carry(w_carry_19_06)
    );
    wire w_sum_19_07, w_carry_19_07;
    math_adder_carry_save CSA_19_07 (
        .i_a(w_sum_19_02),
        .i_b(w_sum_19_03),
        .i_c(w_sum_19_04),
        .ow_sum(w_sum_19_07),
        .ow_carry(w_carry_19_07)
    );
    wire w_sum_20_04, w_carry_20_04;
    math_adder_carry_save CSA_20_04 (
        .i_a(w_pp_14_06),
        .i_b(w_pp_15_05),
        .i_c(w_carry_19_01),
        .ow_sum(w_sum_20_04),
        .ow_carry(w_carry_20_04)
    );
    wire w_sum_20_05, w_carry_20_05;
    math_adder_carry_save CSA_20_05 (
        .i_a(w_carry_19_02),
        .i_b(w_carry_19_03),
        .i_c(w_carry_19_04),
        .ow_sum(w_sum_20_05),
        .ow_carry(w_carry_20_05)
    );
    wire w_sum_20_06, w_carry_20_06;
    math_adder_carry_save CSA_20_06 (
        .i_a(w_sum_20_01),
        .i_b(w_sum_20_02),
        .i_c(w_sum_20_03),
        .ow_sum(w_sum_20_06),
        .ow_carry(w_carry_20_06)
    );
    wire w_sum_21_03, w_carry_21_03;
    math_adder_carry_save CSA_21_03 (
        .i_a(w_pp_12_09),
        .i_b(w_pp_13_08),
        .i_c(w_pp_14_07),
        .ow_sum(w_sum_21_03),
        .ow_carry(w_carry_21_03)
    );
    wire w_sum_21_04, w_carry_21_04;
    math_adder_carry_save CSA_21_04 (
        .i_a(w_pp_15_06),
        .i_b(w_carry_20_01),
        .i_c(w_carry_20_02),
        .ow_sum(w_sum_21_04),
        .ow_carry(w_carry_21_04)
    );
    wire w_sum_21_05, w_carry_21_05;
    math_adder_carry_save CSA_21_05 (
        .i_a(w_carry_20_03),
        .i_b(w_sum_21_01),
        .i_c(w_sum_21_02),
        .ow_sum(w_sum_21_05),
        .ow_carry(w_carry_21_05)
    );
    wire w_sum_22_02, w_carry_22_02;
    math_adder_carry_save CSA_22_02 (
        .i_a(w_pp_10_12),
        .i_b(w_pp_11_11),
        .i_c(w_pp_12_10),
        .ow_sum(w_sum_22_02),
        .ow_carry(w_carry_22_02)
    );
    wire w_sum_22_03, w_carry_22_03;
    math_adder_carry_save CSA_22_03 (
        .i_a(w_pp_13_09),
        .i_b(w_pp_14_08),
        .i_c(w_pp_15_07),
        .ow_sum(w_sum_22_03),
        .ow_carry(w_carry_22_03)
    );
    wire w_sum_22_04, w_carry_22_04;
    math_adder_carry_save CSA_22_04 (
        .i_a(w_carry_21_01),
        .i_b(w_carry_21_02),
        .i_c(w_sum_22_01),
        .ow_sum(w_sum_22_04),
        .ow_carry(w_carry_22_04)
    );
    wire w_sum_23_01, w_carry_23_01;
    math_adder_carry_save CSA_23_01 (
        .i_a(w_pp_08_15),
        .i_b(w_pp_09_14),
        .i_c(w_pp_10_13),
        .ow_sum(w_sum_23_01),
        .ow_carry(w_carry_23_01)
    );
    wire w_sum_23_02, w_carry_23_02;
    math_adder_carry_save CSA_23_02 (
        .i_a(w_pp_11_12),
        .i_b(w_pp_12_11),
        .i_c(w_pp_13_10),
        .ow_sum(w_sum_23_02),
        .ow_carry(w_carry_23_02)
    );
    wire w_sum_23_03, w_carry_23_03;
    math_adder_carry_save CSA_23_03 (
        .i_a(w_pp_14_09),
        .i_b(w_pp_15_08),
        .i_c(w_carry_22_01),
        .ow_sum(w_sum_23_03),
        .ow_carry(w_carry_23_03)
    );
    wire w_sum_24_01, w_carry_24_01;
    math_adder_carry_save CSA_24_01 (
        .i_a(w_pp_09_15),
        .i_b(w_pp_10_14),
        .i_c(w_pp_11_13),
        .ow_sum(w_sum_24_01),
        .ow_carry(w_carry_24_01)
    );
    wire w_sum_24_02, w_carry_24_02;
    math_adder_carry_save CSA_24_02 (
        .i_a(w_pp_12_12),
        .i_b(w_pp_13_11),
        .i_c(w_pp_14_10),
        .ow_sum(w_sum_24_02),
        .ow_carry(w_carry_24_02)
    );
    wire w_sum_25_01, w_carry_25_01;
    math_adder_carry_save CSA_25_01 (
        .i_a(w_pp_10_15),
        .i_b(w_pp_11_14),
        .i_c(w_pp_12_13),
        .ow_sum(w_sum_25_01),
        .ow_carry(w_carry_25_01)
    );

    // Dadda reduction stage 4: max column height 4
    wire w_sum_04_01, w_carry_04_01;
    math_adder_half HA__04_01 (
        .i_a(w_pp_00_04),
        .i_b(w_pp_01_03),
        .ow_sum(w_sum_04_01),
        .ow_carry(w_carry_04_01)
    );
    wire w_sum_05_01, w_carry_05_01;
    math_adder_carry_save CSA_05_01 (
        .i_a(w_pp_00_05),
        .i_b(w_pp_01_04),
        .i_c(w_pp_02_03),
        .ow_sum(w_sum_05_01),
        .ow_carry(w_carry_05_01)
    );
    wire w_sum_05_02, w_carry_05_02;
    math_adder_half HA__05_02 (
        .i_a(w_pp_03_02),
        .i_b(w_pp_04_01),
        .ow_sum(w_sum_05_02),
        .ow_carry(w_carry_05_02)
    );
    wire w_sum_06_02, w_carry_06_02;
    math_adder_carry_save CSA_06_02 (
        .i_a(w_pp_02_04),
        .i_b(w_pp_03_03),
        .i_c(w_pp_04_02),
        .ow_sum(w_sum_06_02),
        .ow_carry(w_carry_06_02)
    );
    wire w_sum_06_03, w_carry_06_03;
    math_adder_carry_save CSA_06_03 (
        .i_a(w_pp_05_01),
        .i_b(w_pp_06_00),
        .i_c(w_sum_06_01),
        .ow_sum(w_sum_06_03),
        .ow_carry(w_carry_06_03)
    );
    wire w_sum_07_03, w_carry_07_03;
    math_adder_carry_save CSA_07_03 (
        .i_a(w_pp_05_02),
        .i_b(w_pp_06_01),
        .i_c(w_pp_07_00),
        .ow_sum(w_sum_07_03),
        .ow_carry(w_carry_07_03)
    );
    wire w_sum_07_04, w_carry_07_04;
    math_adder_carry_save CSA_07_04 (
        .i_a(w_carry_06_01),
        .i_b(w_sum_07_01),
        .i_c(w_sum_07_02),
        .ow_sum(w_sum_07_04),
        .ow_carry(w_carry_07_04)
    );
    wire w_sum_08_04, w_carry_08_04;
    math_adder_carry_save CSA_08_04 (
        .i_a(w_pp_08_00),
        .i_b(w_carry_07_01),
        .i_c(w_carry_07_02),
        .ow_sum(w_sum_08_04),
        .ow_carry(w_carry_08_04)
    );
    wire w_sum_08_05, w_carry_08_05;
    math_adder_carry_save CSA_08_05 (
        .i_a(w_sum_08_01),
        .i_b(w_sum_08_02),
        .i_c(w_sum_08_03),
        .ow_sum(w_sum_08_05),
        .ow_carry(w_carry_08_05)
    );
    wire w_sum_09_05, w_carry_09_05;
    math_adder_carry_save CSA_09_05 (
        .i_a(w_carry_08_01),
        .i_b(w_carry_08_02),
        .i_c(w_carry_08_03),
        .ow_sum(w_sum_09_05),
        .ow_carry(w_carry_09_05)
    );
    wire w_sum_09_06, w_carry_09_06;
    math_adder_carry_save CSA_09_06 (
        .i_a(w_sum_09_02),
        .i_b(w_sum_09_03),
        .i_c(w_sum_09_04),
        .ow_sum(w_sum_09_06),
        .ow_carry(w_carry_09_06)
    );
    wire w_sum_10_06, w_carry_10_06;
    math_adder_carry_save CSA_10_06 (
        .i_a(w_carry_09_02),
        .i_b(w_carry_09_03),
        .i_c(w_carry_09_04),
        .ow_sum(w_sum_10_06),
        .ow_carry(w_carry_10_06)
    );
    wire w_sum_10_07, w_carry_10_07;
    math_adder_carry_save CSA_10_07 (
        .i_a(w_sum_10_03),
        .i_b(w_sum_10_04),
        .i_c(w_sum_10_05),
        .ow_sum(w_sum_10_07),
        .ow_carry(w_carry_10_07)
    );
    wire w_sum_11_07, w_carry_11_07;
    math_adder_carry_save CSA_11_07 (
        .i_a(w_carry_10_03),
        .i_b(w_carry_10_04),
        .i_c(w_carry_10_05),
        .ow_sum(w_sum_11_07),
        .ow_carry(w_carry_11_07)
    );
    wire w_sum_11_08, w_carry_11_08;
    math_adder_carry_save CSA_11_08 (
        .i_a(w_sum_11_04),
        .i_b(w_sum_11_05),
        .i_c(w_sum_11_06),
        .ow_sum(w_sum_11_08),
        .ow_carry(w_carry_11_08)
    );
    wire w_sum_12_08, w_carry_12_08;
    math_adder_carry_save CSA_12_08 (
        .i_a(w_carry_11_04),
        .i_b(w_carry_11_05),
        .i_c(w_carry_11_06),
        .ow_sum(w_sum_12_08),
        .ow_carry(w_carry_12_08)
    );
    wire w_sum_12_09, w_carry_12_09;
    math_adder_carry_save CSA_12_09 (
        .i_a(w_sum_12_05),
        .i_b(w_sum_12_06),
        .i_c(w_sum_12_07),
        .ow_sum(w_sum_12_09),
        .ow_carry(w_carry_12_09)
    );
    wire w_sum_13_09, w_carry_13_09;
    math_adder_carry_save CSA_13_09 (
        .i_a(w_carry_12_05),
        .i_b(w_carry_12_06),
        .i_c(w_carry_12_07),
        .ow_sum(w_sum_13_09),
        .ow_carry(w_carry_13_09)
    );
    wire w_sum_13_10, w_carry_13_10;
    math_adder_carry_save CSA_13_10 (
        .i_a(w_sum_13_06),
        .i_b(w_sum_13_07),
        .i_c(w_sum_13_08),
        .ow_sum(w_sum_13_10),
        .ow_carry(w_carry_13_10)
    );
    wire w_sum_14_10, w_carry_14_10;
    math_adder_carry_save CSA_14_10 (
        .i_a(w_carry_13_06),
        .i_b(w_carry_13_07),
        .i_c(w_carry_13_08),
        .ow_sum(w_sum_14_10),
        .ow_carry(w_carry_14_10)
    );
    wire w_sum_14_11, w_carry_14_11;
    math_adder_carry_save CSA_14_11 (
        .i_a(w_sum_14_07),
        .i_b(w_sum_14_08),
        .i_c(w_sum_14_09),
        .ow_sum(w_sum_14_11),
        .ow_carry(w_carry_14_11)
    );
    wire w_sum_15_11, w_carry_15_11;
    math_adder_carry_save CSA_15_11 (
        .i_a(w_carry_14_07),
        .i_b(w_carry_14_08),
        .i_c(w_carry_14_09),
        .ow_sum(w_sum_15_11),
        .ow_carry(w_carry_15_11)
    );
    wire w_sum_15_12, w_carry_15_12;
    math_adder_carry_save CSA_15_12 (
        .i_a(w_sum_15_08),
        .i_b(w_sum_15_09),
        .i_c(w_sum_15_10),
        .ow_sum(w_sum_15_12),
        .ow_carry(w_carry_15_12)
    );
    wire w_sum_16_11, w_carry_16_11;
    math_adder_carry_save CSA_16_11 (
        .i_a(w_carry_15_08),
        .i_b(w_carry_15_09),
        .i_c(w_carry_15_10),
        .ow_sum(w_sum_16_11),
        .ow_carry(w_carry_16_11)
    );
    wire w_sum_16_12, w_carry_16_12;
    math_adder_carry_save CSA_16_12 (
        .i_a(w_sum_16_08),
        .i_b(w_sum_16_09),
        .i_c(w_sum_16_10),
        .ow_sum(w_sum_16_12),
        .ow_carry(w_carry_16_12)
    );
    wire w_sum_17_10, w_carry_17_10;
    math_adder_carry_save CSA_17_10 (
        .i_a(w_carry_16_08),
        .i_b(w_carry_16_09),
        .i_c(w_carry_16_10),
        .ow_sum(w_sum_17_10),
        .ow_carry(w_carry_17_10)
    );
    wire w_sum_17_11, w_carry_17_11;
    math_adder_carry_save CSA_17_11 (
        .i_a(w_sum_17_07),
        .i_b(w_sum_17_08),
        .i_c(w_sum_17_09),
        .ow_sum(w_sum_17_11),
        .ow_carry(w_carry_17_11)
    );
    wire w_sum_18_09, w_carry_18_09;
    math_adder_carry_save CSA_18_09 (
        .i_a(w_carry_17_07),
        .i_b(w_carry_17_08),
        .i_c(w_carry_17_09),
        .ow_sum(w_sum_18_09),
        .ow_carry(w_carry_18_09)
    );
    wire w_sum_18_10, w_carry_18_10;
    math_adder_carry_save CSA_18_10 (
        .i_a(w_sum_18_06),
        .i_b(w_sum_18_07),
        .i_c(w_sum_18_08),
        .ow_sum(w_sum_18_10),
        .ow_carry(w_carry_18_10)
    );
    wire w_sum_19_08, w_carry_19_08;
    math_adder_carry_save CSA_19_08 (
        .i_a(w_carry_18_06),
        .i_b(w_carry_18_07),
        .i_c(w_carry_18_08),
        .ow_sum(w_sum_19_08),
        .ow_carry(w_carry_19_08)
    );
    wire w_sum_19_09, w_carry_19_09;
    math_adder_carry_save CSA_19_09 (
        .i_a(w_sum_19_05),
        .i_b(w_sum_19_06),
        .i_c(w_sum_19_07),
        .ow_sum(w_sum_19_09),
        .ow_carry(w_carry_19_09)
    );
    wire w_sum_20_07, w_carry_20_07;
    math_adder_carry_save CSA_20_07 (
        .i_a(w_carry_19_05),
        .i_b(w_carry_19_06),
        .i_c(w_carry_19_07),
        .ow_sum(w_sum_20_07),
        .ow_carry(w_carry_20_07)
    );
    wire w_sum_20_08, w_carry_20_08;
    math_adder_carry_save CSA_20_08 (
        .i_a(w_sum_20_04),
        .i_b(w_sum_20_05),
        .i_c(w_sum_20_06),
        .ow_sum(w_sum_20_08),
        .ow_carry(w_carry_20_08)
    );
    wire w_sum_21_06, w_carry_21_06;
    math_adder_carry_save CSA_21_06 (
        .i_a(w_carry_20_04),
        .i_b(w_carry_20_05),
        .i_c(w_carry_20_06),
        .ow_sum(w_sum_21_06),
        .ow_carry(w_carry_21_06)
    );
    wire w_sum_21_07, w_carry_21_07;
    math_adder_carry_save CSA_21_07 (
        .i_a(w_sum_21_03),
        .i_b(w_sum_21_04),
        .i_c(w_sum_21_05),
        .ow_sum(w_sum_21_07),
        .ow_carry(w_carry_21_07)
    );
    wire w_sum_22_05, w_carry_22_05;
    math_adder_carry_save CSA_22_05 (
        .i_a(w_carry_21_03),
        .i_b(w_carry_21_04),
        .i_c(w_carry_21_05),
        .ow_sum(w_sum_22_05),
        .ow_carry(w_carry_22_05)
    );
    wire w_sum_22_06, w_carry_22_06;
    math_adder_carry_save CSA_22_06 (
        .i_a(w_sum_22_02),
        .i_b(w_sum_22_03),
        .i_c(w_sum_22_04),
        .ow_sum(w_sum_22_06),
        .ow_carry(w_carry_22_06)
    );
    wire w_sum_23_04, w_carry_23_04;
    math_adder_carry_save CSA_23_04 (
        .i_a(w_carry_22_02),
        .i_b(w_carry_22_03),
        .i_c(w_carry_22_04),
        .ow_sum(w_sum_23_04),
        .ow_carry(w_carry_23_04)
    );
    wire w_sum_23_05, w_carry_23_05;
    math_adder_carry_save CSA_23_05 (
        .i_a(w_sum_23_01),
        .i_b(w_sum_23_02),
        .i_c(w_sum_23_03),
        .ow_sum(w_sum_23_05),
        .ow_carry(w_carry_23_05)
    );
    wire w_sum_24_03, w_carry_24_03;
    math_adder_carry_save CSA_24_03 (
        .i_a(w_pp_15_09),
        .i_b(w_carry_23_01),
        .i_c(w_carry_23_02),
        .ow_sum(w_sum_24_03),
        .ow_carry(w_carry_24_03)
    );
    wire w_sum_24_04, w_carry_24_04;
    math_adder_carry_save CSA_24_04 (
        .i_a(w_carry_23_03),
        .i_b(w_sum_24_01),
        .i_c(w_sum_24_02),
        .ow_sum(w_sum_24_04),
        .ow_carry(w_carry_24_04)
    );
    wire w_sum_25_02, w_carry_25_02;
    math_adder_carry_save CSA_25_02 (
        .i_a(w_pp_13_12),
        .i_b(w_pp_14_11),
        .i_c(w_pp_15_10),
        .ow_sum(w_sum_25_02),
        .ow_carry(w_carry_25_02)
    );
    wire w_sum_25_03, w_carry_25_03;
    math_adder_carry_save CSA_25_03 (
        .i_a(w_carry_24_01),
        .i_b(w_carry_24_02),
        .i_c(w_sum_25_01),
        .ow_sum(w_sum_25_03),
        .ow_carry(w_carry_25_03)
    );
    wire w_sum_26_01, w_carry_26_01;
    math_adder_carry_save CSA_26_01 (
        .i_a(w_pp_11_15),
        .i_b(w_pp_12_14),
        .i_c(w_pp_13_13),
        .ow_sum(w_sum_26_01),
        .ow_carry(w_carry_26_01)
    );
    wire w_sum_26_02, w_carry_26_02;
    math_adder_carry_save CSA_26_02 (
        .i_a(w_pp_14_12),
        .i_b(w_pp_15_11),
        .i_c(w_carry_25_01),
        .ow_sum(w_sum_26_02),
        .ow_carry(w_carry_26_02)
    );
    wire w_sum_27_01, w_carry_27_01;
    math_adder_carry_save CSA_27_01 (
        .i_a(w_pp_12_15),
        .i_b(w_pp_13_14),
        .i_c(w_pp_14_13),
        .ow_sum(w_sum_27_01),
        .ow_carry(w_carry_27_01)
    );

    // Dadda reduction stage 5: max column height 3
    wire w_sum_03_01, w_carry_03_01;
    math_adder_half HA__03_01 (
        .i_a(w_pp_00_03),
        .i_b(w_pp_01_02),
        .ow_sum(w_sum_03_01),
        .ow_carry(w_carry_03_01)
    );
    wire w_sum_04_02, w_carry_04_02;
    math_adder_carry_save CSA_04_02 (
        .i_a(w_pp_02_02),
        .i_b(w_pp_03_01),
        .i_c(w_pp_04_00),
        .ow_sum(w_sum_04_02),
        .ow_carry(w_carry_04_02)
    );
    wire w_sum_05_03, w_carry_05_03;
    math_adder_carry_save CSA_05_03 (
        .i_a(w_pp_05_00),
        .i_b(w_carry_04_01),
        .i_c(w_sum_05_01),
        .ow_sum(w_sum_05_03),
        .ow_carry(w_carry_05_03)
    );
    wire w_sum_06_04, w_carry_06_04;
    math_adder_carry_save CSA_06_04 (
        .i_a(w_carry_05_01),
        .i_b(w_carry_05_02),
        .i_c(w_sum_06_02),
        .ow_sum(w_sum_06_04),
        .ow_carry(w_carry_06_04)
    );
    wire w_sum_07_05, w_carry_07_05;
    math_adder_carry_save CSA_07_05 (
        .i_a(w_carry_06_02),
        .i_b(w_carry_06_03),
        .i_c(w_sum_07_03),
        .ow_sum(w_sum_07_05),
        .ow_carry(w_carry_07_05)
    );
    wire w_sum_08_06, w_carry_08_06;
    math_adder_carry_save CSA_08_06 (
        .i_a(w_carry_07_03),
        .i_b(w_carry_07_04),
        .i_c(w_sum_08_04),
        .ow_sum(w_sum_08_06),
        .ow_carry(w_carry_08_06)
    );
    wire w_sum_09_07, w_carry_09_07;
    math_adder_carry_save CSA_09_07 (
        .i_a(w_carry_08_04),
        .i_b(w_carry_08_05),
        .i_c(w_sum_09_05),
        .ow_sum(w_sum_09_07),
        .ow_carry(w_carry_09_07)
    );
    wire w_sum_10_08, w_carry_10_08;
    math_adder_carry_save CSA_10_08 (
        .i_a(w_carry_09_05),
        .i_b(w_carry_09_06),
        .i_c(w_sum_10_06),
        .ow_sum(w_sum_10_08),
        .ow_carry(w_carry_10_08)
    );
    wire w_sum_11_09, w_carry_11_09;
    math_adder_carry_save CSA_11_09 (
        .i_a(w_carry_10_06),
        .i_b(w_carry_10_07),
        .i_c(w_sum_11_07),
        .ow_sum(w_sum_11_09),
        .ow_carry(w_carry_11_09)
    );
    wire w_sum_12_10, w_carry_12_10;
    math_adder_carry_save CSA_12_10 (
        .i_a(w_carry_11_07),
        .i_b(w_carry_11_08),
        .i_c(w_sum_12_08),
        .ow_sum(w_sum_12_10),
        .ow_carry(w_carry_12_10)
    );
    wire w_sum_13_11, w_carry_13_11;
    math_adder_carry_save CSA_13_11 (
        .i_a(w_carry_12_08),
        .i_b(w_carry_12_09),
        .i_c(w_sum_13_09),
        .ow_sum(w_sum_13_11),
        .ow_carry(w_carry_13_11)
    );
    wire w_sum_14_12, w_carry_14_12;
    math_adder_carry_save CSA_14_12 (
        .i_a(w_carry_13_09),
        .i_b(w_carry_13_10),
        .i_c(w_sum_14_10),
        .ow_sum(w_sum_14_12),
        .ow_carry(w_carry_14_12)
    );
    wire w_sum_15_13, w_carry_15_13;
    math_adder_carry_save CSA_15_13 (
        .i_a(w_carry_14_10),
        .i_b(w_carry_14_11),
        .i_c(w_sum_15_11),
        .ow_sum(w_sum_15_13),
        .ow_carry(w_carry_15_13)
    );
    wire w_sum_16_13, w_carry_16_13;
    math_adder_carry_save CSA_16_13 (
        .i_a(w_carry_15_11),
        .i_b(w_carry_15_12),
        .i_c(w_sum_16_11),
        .ow_sum(w_sum_16_13),
        .ow_carry(w_carry_16_13)
    );
    wire w_sum_17_12, w_carry_17_12;
    math_adder_carry_save CSA_17_12 (
        .i_a(w_carry_16_11),
        .i_b(w_carry_16_12),
        .i_c(w_sum_17_10),
        .ow_sum(w_sum_17_12),
        .ow_carry(w_carry_17_12)
    );
    wire w_sum_18_11, w_carry_18_11;
    math_adder_carry_save CSA_18_11 (
        .i_a(w_carry_17_10),
        .i_b(w_carry_17_11),
        .i_c(w_sum_18_09),
        .ow_sum(w_sum_18_11),
        .ow_carry(w_carry_18_11)
    );
    wire w_sum_19_10, w_carry_19_10;
    math_adder_carry_save CSA_19_10 (
        .i_a(w_carry_18_09),
        .i_b(w_carry_18_10),
        .i_c(w_sum_19_08),
        .ow_sum(w_sum_19_10),
        .ow_carry(w_carry_19_10)
    );
    wire w_sum_20_09, w_carry_20_09;
    math_adder_carry_save CSA_20_09 (
        .i_a(w_carry_19_08),
        .i_b(w_carry_19_09),
        .i_c(w_sum_20_07),
        .ow_sum(w_sum_20_09),
        .ow_carry(w_carry_20_09)
    );
    wire w_sum_21_08, w_carry_21_08;
    math_adder_carry_save CSA_21_08 (
        .i_a(w_carry_20_07),
        .i_b(w_carry_20_08),
        .i_c(w_sum_21_06),
        .ow_sum(w_sum_21_08),
        .ow_carry(w_carry_21_08)
    );
    wire w_sum_22_07, w_carry_22_07;
    math_adder_carry_save CSA_22_07 (
        .i_a(w_carry_21_06),
        .i_b(w_carry_21_07),
        .i_c(w_sum_22_05),
        .ow_sum(w_sum_22_07),
        .ow_carry(w_carry_22_07)
    );
    wire w_sum_23_06, w_carry_23_06;
    math_adder_carry_save CSA_23_06 (
        .i_a(w_carry_22_05),
        .i_b(w_carry_22_06),
        .i_c(w_sum_23_04),
        .ow_sum(w_sum_23_06),
        .ow_carry(w_carry_23_06)
    );
    wire w_sum_24_05, w_carry_24_05;
    math_adder_carry_save CSA_24_05 (
        .i_a(w_carry_23_04),
        .i_b(w_carry_23_05),
        .i_c(w_sum_24_03),
        .ow_sum(w_sum_24_05),
        .ow_carry(w_carry_24_05)
    );
    wire w_sum_25_04, w_carry_25_04;
    math_adder_carry_save CSA_25_04 (
        .i_a(w_carry_24_03),
        .i_b(w_carry_24_04),
        .i_c(w_sum_25_02),
        .ow_sum(w_sum_25_04),
        .ow_carry(w_carry_25_04)
    );
    wire w_sum_26_03, w_carry_26_03;
    math_adder_carry_save CSA_26_03 (
        .i_a(w_carry_25_02),
        .i_b(w_carry_25_03),
        .i_c(w_sum_26_01),
        .ow_sum(w_sum_26_03),
        .ow_carry(w_carry_26_03)
    );
    wire w_sum_27_02, w_carry_27_02;
    math_adder_carry_save CSA_27_02 (
        .i_a(w_pp_15_12),
        .i_b(w_carry_26_01),
        .i_c(w_carry_26_02),
        .ow_sum(w_sum_27_02),
        .ow_carry(w_carry_27_02)
    );
    wire w_sum_28_01, w_carry_28_01;
    math_adder_carry_save CSA_28_01 (
        .i_a(w_pp_13_15),
        .i_b(w_pp_14_14),
        .i_c(w_pp_15_13),
        .ow_sum(w_sum_28_01),
        .ow_carry(w_carry_28_01)
    );

    // Dadda reduction stage 6: max column height 2
    wire w_sum_02_01, w_carry_02_01;
    math_adder_half HA__02_01 (
        .i_a(w_pp_00_02),
        .i_b(w_pp_01_01),
        .ow_sum(w_sum_02_01),
        .ow_carry(w_carry_02_01)
    );
    wire w_sum_03_02, w_carry_03_02;
    math_adder_carry_save CSA_03_02 (
        .i_a(w_pp_02_01),
        .i_b(w_pp_03_00),
        .i_c(w_sum_03_01),
        .ow_sum(w_sum_03_02),
        .ow_carry(w_carry_03_02)
    );
    wire w_sum_04_03, w_carry_04_03;
    math_adder_carry_save CSA_04_03 (
        .i_a(w_sum_04_01),
        .i_b(w_carry_03_01),
        .i_c(w_sum_04_02),
        .ow_sum(w_sum_04_03),
        .ow_carry(w_carry_04_03)
    );
    wire w_sum_05_04, w_carry_05_04;
    math_adder_carry_save CSA_05_04 (
        .i_a(w_sum_05_02),
        .i_b(w_carry_04_02),
        .i_c(w_sum_05_03),
        .ow_sum(w_sum_05_04),
        .ow_carry(w_carry_05_04)
    );
    wire w_sum_06_05, w_carry_06_05;
    math_adder_carry_save CSA_06_05 (
        .i_a(w_sum_06_03),
        .i_b(w_carry_05_03),
        .i_c(w_sum_06_04),
        .ow_sum(w_sum_06_05),
        .ow_carry(w_carry_06_05)
    );
    wire w_sum_07_06, w_carry_07_06;
    math_adder_carry_save CSA_07_06 (
        .i_a(w_sum_07_04),
        .i_b(w_carry_06_04),
        .i_c(w_sum_07_05),
        .ow_sum(w_sum_07_06),
        .ow_carry(w_carry_07_06)
    );
    wire w_sum_08_07, w_carry_08_07;
    math_adder_carry_save CSA_08_07 (
        .i_a(w_sum_08_05),
        .i_b(w_carry_07_05),
        .i_c(w_sum_08_06),
        .ow_sum(w_sum_08_07),
        .ow_carry(w_carry_08_07)
    );
    wire w_sum_09_08, w_carry_09_08;
    math_adder_carry_save CSA_09_08 (
        .i_a(w_sum_09_06),
        .i_b(w_carry_08_06),
        .i_c(w_sum_09_07),
        .ow_sum(w_sum_09_08),
        .ow_carry(w_carry_09_08)
    );
    wire w_sum_10_09, w_carry_10_09;
    math_adder_carry_save CSA_10_09 (
        .i_a(w_sum_10_07),
        .i_b(w_carry_09_07),
        .i_c(w_sum_10_08),
        .ow_sum(w_sum_10_09),
        .ow_carry(w_carry_10_09)
    );
    wire w_sum_11_10, w_carry_11_10;
    math_adder_carry_save CSA_11_10 (
        .i_a(w_sum_11_08),
        .i_b(w_carry_10_08),
        .i_c(w_sum_11_09),
        .ow_sum(w_sum_11_10),
        .ow_carry(w_carry_11_10)
    );
    wire w_sum_12_11, w_carry_12_11;
    math_adder_carry_save CSA_12_11 (
        .i_a(w_sum_12_09),
        .i_b(w_carry_11_09),
        .i_c(w_sum_12_10),
        .ow_sum(w_sum_12_11),
        .ow_carry(w_carry_12_11)
    );
    wire w_sum_13_12, w_carry_13_12;
    math_adder_carry_save CSA_13_12 (
        .i_a(w_sum_13_10),
        .i_b(w_carry_12_10),
        .i_c(w_sum_13_11),
        .ow_sum(w_sum_13_12),
        .ow_carry(w_carry_13_12)
    );
    wire w_sum_14_13, w_carry_14_13;
    math_adder_carry_save CSA_14_13 (
        .i_a(w_sum_14_11),
        .i_b(w_carry_13_11),
        .i_c(w_sum_14_12),
        .ow_sum(w_sum_14_13),
        .ow_carry(w_carry_14_13)
    );
    wire w_sum_15_14, w_carry_15_14;
    math_adder_carry_save CSA_15_14 (
        .i_a(w_sum_15_12),
        .i_b(w_carry_14_12),
        .i_c(w_sum_15_13),
        .ow_sum(w_sum_15_14),
        .ow_carry(w_carry_15_14)
    );
    wire w_sum_16_14, w_carry_16_14;
    math_adder_carry_save CSA_16_14 (
        .i_a(w_sum_16_12),
        .i_b(w_carry_15_13),
        .i_c(w_sum_16_13),
        .ow_sum(w_sum_16_14),
        .ow_carry(w_carry_16_14)
    );
    wire w_sum_17_13, w_carry_17_13;
    math_adder_carry_save CSA_17_13 (
        .i_a(w_sum_17_11),
        .i_b(w_carry_16_13),
        .i_c(w_sum_17_12),
        .ow_sum(w_sum_17_13),
        .ow_carry(w_carry_17_13)
    );
    wire w_sum_18_12, w_carry_18_12;
    math_adder_carry_save CSA_18_12 (
        .i_a(w_sum_18_10),
        .i_b(w_carry_17_12),
        .i_c(w_sum_18_11),
        .ow_sum(w_sum_18_12),
        .ow_carry(w_carry_18_12)
    );
    wire w_sum_19_11, w_carry_19_11;
    math_adder_carry_save CSA_19_11 (
        .i_a(w_sum_19_09),
        .i_b(w_carry_18_11),
        .i_c(w_sum_19_10),
        .ow_sum(w_sum_19_11),
        .ow_carry(w_carry_19_11)
    );
    wire w_sum_20_10, w_carry_20_10;
    math_adder_carry_save CSA_20_10 (
        .i_a(w_sum_20_08),
        .i_b(w_carry_19_10),
        .i_c(w_sum_20_09),
        .ow_sum(w_sum_20_10),
        .ow_carry(w_carry_20_10)
    );
    wire w_sum_21_09, w_carry_21_09;
    math_adder_carry_save CSA_21_09 (
        .i_a(w_sum_21_07),
        .i_b(w_carry_20_09),
        .i_c(w_sum_21_08),
        .ow_sum(w_sum_21_09),
        .ow_carry(w_carry_21_09)
    );
    wire w_sum_22_08, w_carry_22_08;
    math_adder_carry_save CSA_22_08 (
        .i_a(w_sum_22_06),
        .i_b(w_carry_21_08),
        .i_c(w_sum_22_07),
        .ow_sum(w_sum_22_08),
        .ow_carry(w_carry_22_08)
    );
    wire w_sum_23_07, w_carry_23_07;
    math_adder_carry_save CSA_23_07 (
        .i_a(w_sum_23_05),
        .i_b(w_carry_22_07),
        .i_c(w_sum_23_06),
        .ow_sum(w_sum_23_07),
        .ow_carry(w_carry_23_07)
    );
    wire w_sum_24_06, w_carry_24_06;
    math_adder_carry_save CSA_24_06 (
        .i_a(w_sum_24_04),
        .i_b(w_carry_23_06),
        .i_c(w_sum_24_05),
        .ow_sum(w_sum_24_06),
        .ow_carry(w_carry_24_06)
    );
    wire w_sum_25_05, w_carry_25_05;
    math_adder_carry_save CSA_25_05 (
        .i_a(w_sum_25_03),
        .i_b(w_carry_24_05),
        .i_c(w_sum_25_04),
        .ow_sum(w_sum_25_05),
        .ow_carry(w_carry_25_05)
    );
    wire w_sum_26_04, w_carry_26_04;
    math_adder_carry_save CSA_26_04 (
        .i_a(w_sum_26_02),
        .i_b(w_carry_25_04),
        .i_c(w_sum_26_03),
        .ow_sum(w_sum_26_04),
        .ow_carry(w_carry_26_04)
    );
    wire w_sum_27_03, w_carry_27_03;
    math_adder_carry_save CSA_27_03 (
        .i_a(w_sum_27_01),
        .i_b(w_carry_26_03),
        .i_c(w_sum_27_02),
        .ow_sum(w_sum_27_03),
        .ow_carry(w_carry_27_03)
    );
    wire w_sum_28_02, w_carry_28_02;
    math_adder_carry_save CSA_28_02 (
        .i_a(w_carry_27_01),
        .i_b(w_carry_27_02),
        .i_c(w_sum_28_01),
        .ow_sum(w_sum_28_02),
        .ow_carry(w_carry_28_02)
    );
    wire w_sum_29_01, w_carry_29_01;
    math_adder_carry_save CSA_29_01 (
        .i_a(w_pp_14_15),
        .i_b(w_pp_15_14),
        .i_c(w_carry_28_01),
        .ow_sum(w_sum_29_01),
        .ow_carry(w_carry_29_01)
    );

    // Final addition stage: two reduced rows into a Brent-Kung CPA
    wire [31:0] w_cpa_row0 = {
        1'b0,
        w_pp_15_15,
        w_carry_28_02,
        w_carry_27_03,
        w_carry_26_04,
        w_carry_25_05,
        w_carry_24_06,
        w_carry_23_07,
        w_carry_22_08,
        w_carry_21_09,
        w_carry_20_10,
        w_carry_19_11,
        w_carry_18_12,
        w_carry_17_13,
        w_carry_16_14,
        w_carry_15_14,
        w_carry_14_13,
        w_carry_13_12,
        w_carry_12_11,
        w_carry_11_10,
        w_carry_10_09,
        w_carry_09_08,
        w_carry_08_07,
        w_carry_07_06,
        w_carry_06_05,
        w_carry_05_04,
        w_carry_04_03,
        w_carry_03_02,
        w_carry_02_01,
        w_pp_02_00,
        w_pp_00_01,
        w_pp_00_00
    };
    wire [31:0] w_cpa_row1 = {
        1'b0,
        w_carry_29_01,
        w_sum_29_01,
        w_sum_28_02,
        w_sum_27_03,
        w_sum_26_04,
        w_sum_25_05,
        w_sum_24_06,
        w_sum_23_07,
        w_sum_22_08,
        w_sum_21_09,
        w_sum_20_10,
        w_sum_19_11,
        w_sum_18_12,
        w_sum_17_13,
        w_sum_16_14,
        w_sum_15_14,
        w_sum_14_13,
        w_sum_13_12,
        w_sum_12_11,
        w_sum_11_10,
        w_sum_10_09,
        w_sum_09_08,
        w_sum_08_07,
        w_sum_07_06,
        w_sum_06_05,
        w_sum_05_04,
        w_sum_04_03,
        w_sum_03_02,
        w_sum_02_01,
        w_pp_01_00,
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
