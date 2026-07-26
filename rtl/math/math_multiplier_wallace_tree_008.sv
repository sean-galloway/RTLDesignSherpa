// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_multiplier_wallace_tree_008
// Purpose: Math Multiplier Wallace Tree 008 module
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_multiplier_wallace_tree_008 #(
    parameter int N = 8
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);

    // Partial Products
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

    // Partial products reduction using Wallace tree
    // Wallace reduction layer 1
    wire w_sum_01_1_01, w_carry_01_1_01;
    math_adder_half HA_01_1_01 (
        .i_a(w_pp_0_1),
        .i_b(w_pp_1_0),
        .ow_sum(w_sum_01_1_01),
        .ow_carry(w_carry_01_1_01)
    );
    wire w_sum_02_1_01, w_carry_02_1_01;
    math_adder_full FA_02_1_01 (
        .i_a(w_pp_0_2),
        .i_b(w_pp_1_1),
        .i_c(w_pp_2_0),
        .ow_sum(w_sum_02_1_01),
        .ow_carry(w_carry_02_1_01)
    );
    wire w_sum_03_1_01, w_carry_03_1_01;
    math_adder_full FA_03_1_01 (
        .i_a(w_pp_0_3),
        .i_b(w_pp_1_2),
        .i_c(w_pp_2_1),
        .ow_sum(w_sum_03_1_01),
        .ow_carry(w_carry_03_1_01)
    );
    wire w_sum_04_1_01, w_carry_04_1_01;
    math_adder_full FA_04_1_01 (
        .i_a(w_pp_0_4),
        .i_b(w_pp_1_3),
        .i_c(w_pp_2_2),
        .ow_sum(w_sum_04_1_01),
        .ow_carry(w_carry_04_1_01)
    );
    wire w_sum_04_1_02, w_carry_04_1_02;
    math_adder_half HA_04_1_02 (
        .i_a(w_pp_3_1),
        .i_b(w_pp_4_0),
        .ow_sum(w_sum_04_1_02),
        .ow_carry(w_carry_04_1_02)
    );
    wire w_sum_05_1_01, w_carry_05_1_01;
    math_adder_full FA_05_1_01 (
        .i_a(w_pp_0_5),
        .i_b(w_pp_1_4),
        .i_c(w_pp_2_3),
        .ow_sum(w_sum_05_1_01),
        .ow_carry(w_carry_05_1_01)
    );
    wire w_sum_05_1_02, w_carry_05_1_02;
    math_adder_full FA_05_1_02 (
        .i_a(w_pp_3_2),
        .i_b(w_pp_4_1),
        .i_c(w_pp_5_0),
        .ow_sum(w_sum_05_1_02),
        .ow_carry(w_carry_05_1_02)
    );
    wire w_sum_06_1_01, w_carry_06_1_01;
    math_adder_full FA_06_1_01 (
        .i_a(w_pp_0_6),
        .i_b(w_pp_1_5),
        .i_c(w_pp_2_4),
        .ow_sum(w_sum_06_1_01),
        .ow_carry(w_carry_06_1_01)
    );
    wire w_sum_06_1_02, w_carry_06_1_02;
    math_adder_full FA_06_1_02 (
        .i_a(w_pp_3_3),
        .i_b(w_pp_4_2),
        .i_c(w_pp_5_1),
        .ow_sum(w_sum_06_1_02),
        .ow_carry(w_carry_06_1_02)
    );
    wire w_sum_07_1_01, w_carry_07_1_01;
    math_adder_full FA_07_1_01 (
        .i_a(w_pp_0_7),
        .i_b(w_pp_1_6),
        .i_c(w_pp_2_5),
        .ow_sum(w_sum_07_1_01),
        .ow_carry(w_carry_07_1_01)
    );
    wire w_sum_07_1_02, w_carry_07_1_02;
    math_adder_full FA_07_1_02 (
        .i_a(w_pp_3_4),
        .i_b(w_pp_4_3),
        .i_c(w_pp_5_2),
        .ow_sum(w_sum_07_1_02),
        .ow_carry(w_carry_07_1_02)
    );
    wire w_sum_07_1_03, w_carry_07_1_03;
    math_adder_half HA_07_1_03 (
        .i_a(w_pp_6_1),
        .i_b(w_pp_7_0),
        .ow_sum(w_sum_07_1_03),
        .ow_carry(w_carry_07_1_03)
    );
    wire w_sum_08_1_01, w_carry_08_1_01;
    math_adder_full FA_08_1_01 (
        .i_a(w_pp_1_7),
        .i_b(w_pp_2_6),
        .i_c(w_pp_3_5),
        .ow_sum(w_sum_08_1_01),
        .ow_carry(w_carry_08_1_01)
    );
    wire w_sum_08_1_02, w_carry_08_1_02;
    math_adder_full FA_08_1_02 (
        .i_a(w_pp_4_4),
        .i_b(w_pp_5_3),
        .i_c(w_pp_6_2),
        .ow_sum(w_sum_08_1_02),
        .ow_carry(w_carry_08_1_02)
    );
    wire w_sum_09_1_01, w_carry_09_1_01;
    math_adder_full FA_09_1_01 (
        .i_a(w_pp_2_7),
        .i_b(w_pp_3_6),
        .i_c(w_pp_4_5),
        .ow_sum(w_sum_09_1_01),
        .ow_carry(w_carry_09_1_01)
    );
    wire w_sum_09_1_02, w_carry_09_1_02;
    math_adder_full FA_09_1_02 (
        .i_a(w_pp_5_4),
        .i_b(w_pp_6_3),
        .i_c(w_pp_7_2),
        .ow_sum(w_sum_09_1_02),
        .ow_carry(w_carry_09_1_02)
    );
    wire w_sum_10_1_01, w_carry_10_1_01;
    math_adder_full FA_10_1_01 (
        .i_a(w_pp_3_7),
        .i_b(w_pp_4_6),
        .i_c(w_pp_5_5),
        .ow_sum(w_sum_10_1_01),
        .ow_carry(w_carry_10_1_01)
    );
    wire w_sum_10_1_02, w_carry_10_1_02;
    math_adder_half HA_10_1_02 (
        .i_a(w_pp_6_4),
        .i_b(w_pp_7_3),
        .ow_sum(w_sum_10_1_02),
        .ow_carry(w_carry_10_1_02)
    );
    wire w_sum_11_1_01, w_carry_11_1_01;
    math_adder_full FA_11_1_01 (
        .i_a(w_pp_4_7),
        .i_b(w_pp_5_6),
        .i_c(w_pp_6_5),
        .ow_sum(w_sum_11_1_01),
        .ow_carry(w_carry_11_1_01)
    );
    wire w_sum_12_1_01, w_carry_12_1_01;
    math_adder_full FA_12_1_01 (
        .i_a(w_pp_5_7),
        .i_b(w_pp_6_6),
        .i_c(w_pp_7_5),
        .ow_sum(w_sum_12_1_01),
        .ow_carry(w_carry_12_1_01)
    );
    wire w_sum_13_1_01, w_carry_13_1_01;
    math_adder_half HA_13_1_01 (
        .i_a(w_pp_6_7),
        .i_b(w_pp_7_6),
        .ow_sum(w_sum_13_1_01),
        .ow_carry(w_carry_13_1_01)
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
        .i_c(w_pp_3_0),
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
        .i_b(w_pp_6_0),
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
        .i_c(w_pp_7_1),
        .ow_sum(w_sum_08_2_02),
        .ow_carry(w_carry_08_2_02)
    );
    wire w_sum_09_2_01, w_carry_09_2_01;
    math_adder_full FA_09_2_01 (
        .i_a(w_carry_08_1_01),
        .i_b(w_carry_08_1_02),
        .i_c(w_sum_09_1_01),
        .ow_sum(w_sum_09_2_01),
        .ow_carry(w_carry_09_2_01)
    );
    wire w_sum_10_2_01, w_carry_10_2_01;
    math_adder_full FA_10_2_01 (
        .i_a(w_carry_09_1_01),
        .i_b(w_carry_09_1_02),
        .i_c(w_sum_10_1_01),
        .ow_sum(w_sum_10_2_01),
        .ow_carry(w_carry_10_2_01)
    );
    wire w_sum_11_2_01, w_carry_11_2_01;
    math_adder_full FA_11_2_01 (
        .i_a(w_carry_10_1_01),
        .i_b(w_carry_10_1_02),
        .i_c(w_sum_11_1_01),
        .ow_sum(w_sum_11_2_01),
        .ow_carry(w_carry_11_2_01)
    );
    wire w_sum_12_2_01, w_carry_12_2_01;
    math_adder_half HA_12_2_01 (
        .i_a(w_carry_11_1_01),
        .i_b(w_sum_12_1_01),
        .ow_sum(w_sum_12_2_01),
        .ow_carry(w_carry_12_2_01)
    );
    wire w_sum_13_2_01, w_carry_13_2_01;
    math_adder_half HA_13_2_01 (
        .i_a(w_carry_12_1_01),
        .i_b(w_sum_13_1_01),
        .ow_sum(w_sum_13_2_01),
        .ow_carry(w_carry_13_2_01)
    );
    wire w_sum_14_2_01, w_carry_14_2_01;
    math_adder_half HA_14_2_01 (
        .i_a(w_carry_13_1_01),
        .i_b(w_pp_7_7),
        .ow_sum(w_sum_14_2_01),
        .ow_carry(w_carry_14_2_01)
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
    wire w_sum_10_3_01, w_carry_10_3_01;
    math_adder_full FA_10_3_01 (
        .i_a(w_carry_09_2_01),
        .i_b(w_sum_10_2_01),
        .i_c(w_sum_10_1_02),
        .ow_sum(w_sum_10_3_01),
        .ow_carry(w_carry_10_3_01)
    );
    wire w_sum_11_3_01, w_carry_11_3_01;
    math_adder_full FA_11_3_01 (
        .i_a(w_carry_10_2_01),
        .i_b(w_sum_11_2_01),
        .i_c(w_pp_7_4),
        .ow_sum(w_sum_11_3_01),
        .ow_carry(w_carry_11_3_01)
    );
    wire w_sum_12_3_01, w_carry_12_3_01;
    math_adder_half HA_12_3_01 (
        .i_a(w_carry_11_2_01),
        .i_b(w_sum_12_2_01),
        .ow_sum(w_sum_12_3_01),
        .ow_carry(w_carry_12_3_01)
    );
    wire w_sum_13_3_01, w_carry_13_3_01;
    math_adder_half HA_13_3_01 (
        .i_a(w_carry_12_2_01),
        .i_b(w_sum_13_2_01),
        .ow_sum(w_sum_13_3_01),
        .ow_carry(w_carry_13_3_01)
    );
    wire w_sum_14_3_01, w_carry_14_3_01;
    math_adder_half HA_14_3_01 (
        .i_a(w_carry_13_2_01),
        .i_b(w_sum_14_2_01),
        .ow_sum(w_sum_14_3_01),
        .ow_carry(w_carry_14_3_01)
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
        .i_c(w_sum_09_1_02),
        .ow_sum(w_sum_09_4_01),
        .ow_carry(w_carry_09_4_01)
    );
    wire w_sum_10_4_01, w_carry_10_4_01;
    math_adder_half HA_10_4_01 (
        .i_a(w_carry_09_3_01),
        .i_b(w_sum_10_3_01),
        .ow_sum(w_sum_10_4_01),
        .ow_carry(w_carry_10_4_01)
    );
    wire w_sum_11_4_01, w_carry_11_4_01;
    math_adder_half HA_11_4_01 (
        .i_a(w_carry_10_3_01),
        .i_b(w_sum_11_3_01),
        .ow_sum(w_sum_11_4_01),
        .ow_carry(w_carry_11_4_01)
    );
    wire w_sum_12_4_01, w_carry_12_4_01;
    math_adder_half HA_12_4_01 (
        .i_a(w_carry_11_3_01),
        .i_b(w_sum_12_3_01),
        .ow_sum(w_sum_12_4_01),
        .ow_carry(w_carry_12_4_01)
    );
    wire w_sum_13_4_01, w_carry_13_4_01;
    math_adder_half HA_13_4_01 (
        .i_a(w_carry_12_3_01),
        .i_b(w_sum_13_3_01),
        .ow_sum(w_sum_13_4_01),
        .ow_carry(w_carry_13_4_01)
    );
    wire w_sum_14_4_01, w_carry_14_4_01;
    math_adder_half HA_14_4_01 (
        .i_a(w_carry_13_3_01),
        .i_b(w_sum_14_3_01),
        .ow_sum(w_sum_14_4_01),
        .ow_carry(w_carry_14_4_01)
    );
    wire w_sum_15_4_01, w_carry_15_4_01;
    math_adder_half HA_15_4_01 (
        .i_a(w_carry_14_3_01),
        .i_b(w_carry_14_2_01),
        .ow_sum(w_sum_15_4_01),
        .ow_carry(w_carry_15_4_01)
    );

    // Final addition stage: two reduced rows into a Brent-Kung CPA
    wire [15:0] w_cpa_row0 = {
        w_carry_14_4_01,
        w_carry_13_4_01,
        w_carry_12_4_01,
        w_carry_11_4_01,
        w_carry_10_4_01,
        w_carry_09_4_01,
        w_carry_08_4_01,
        w_carry_07_4_01,
        w_carry_06_4_01,
        w_carry_05_4_01,
        w_carry_04_4_01,
        w_sum_04_4_01,
        w_sum_03_3_01,
        w_sum_02_2_01,
        w_sum_01_1_01,
        w_pp_0_0
    };
    wire [15:0] w_cpa_row1 = {
        w_sum_15_4_01,
        w_sum_14_4_01,
        w_sum_13_4_01,
        w_sum_12_4_01,
        w_sum_11_4_01,
        w_sum_10_4_01,
        w_sum_09_4_01,
        w_sum_08_4_01,
        w_sum_07_4_01,
        w_sum_06_4_01,
        w_sum_05_4_01,
        1'b0,
        1'b0,
        1'b0,
        1'b0,
        1'b0
    };

    /* verilator lint_off UNUSEDSIGNAL */
    wire w_cpa_carry_unused;
    /* verilator lint_on UNUSEDSIGNAL */
    math_adder_brent_kung_016 #(
        .N(16)
    ) u_final_cpa (
        .i_a(w_cpa_row0),
        .i_b(w_cpa_row1),
        .i_c(1'b0),
        .ow_sum(ow_product),
        .ow_carry(w_cpa_carry_unused)
    );

endmodule
