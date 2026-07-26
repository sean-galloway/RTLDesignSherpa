// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_multiplier_dadda_tree_008
// Purpose: Math Multiplier Dadda Tree 008 module
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_multiplier_dadda_tree_008 #(
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

    // Dadda reduction stage 1: max column height 6
    wire w_sum_06_01, w_carry_06_01;
    math_adder_half HA__06_01 (
        .i_a(w_pp_0_6),
        .i_b(w_pp_1_5),
        .ow_sum(w_sum_06_01),
        .ow_carry(w_carry_06_01)
    );
    wire w_sum_07_01, w_carry_07_01;
    math_adder_carry_save CSA_07_01 (
        .i_a(w_pp_0_7),
        .i_b(w_pp_1_6),
        .i_c(w_pp_2_5),
        .ow_sum(w_sum_07_01),
        .ow_carry(w_carry_07_01)
    );
    wire w_sum_07_02, w_carry_07_02;
    math_adder_half HA__07_02 (
        .i_a(w_pp_3_4),
        .i_b(w_pp_4_3),
        .ow_sum(w_sum_07_02),
        .ow_carry(w_carry_07_02)
    );
    wire w_sum_08_01, w_carry_08_01;
    math_adder_carry_save CSA_08_01 (
        .i_a(w_pp_1_7),
        .i_b(w_pp_2_6),
        .i_c(w_pp_3_5),
        .ow_sum(w_sum_08_01),
        .ow_carry(w_carry_08_01)
    );
    wire w_sum_08_02, w_carry_08_02;
    math_adder_half HA__08_02 (
        .i_a(w_pp_4_4),
        .i_b(w_pp_5_3),
        .ow_sum(w_sum_08_02),
        .ow_carry(w_carry_08_02)
    );
    wire w_sum_09_01, w_carry_09_01;
    math_adder_carry_save CSA_09_01 (
        .i_a(w_pp_2_7),
        .i_b(w_pp_3_6),
        .i_c(w_pp_4_5),
        .ow_sum(w_sum_09_01),
        .ow_carry(w_carry_09_01)
    );

    // Dadda reduction stage 2: max column height 4
    wire w_sum_04_01, w_carry_04_01;
    math_adder_half HA__04_01 (
        .i_a(w_pp_0_4),
        .i_b(w_pp_1_3),
        .ow_sum(w_sum_04_01),
        .ow_carry(w_carry_04_01)
    );
    wire w_sum_05_01, w_carry_05_01;
    math_adder_carry_save CSA_05_01 (
        .i_a(w_pp_0_5),
        .i_b(w_pp_1_4),
        .i_c(w_pp_2_3),
        .ow_sum(w_sum_05_01),
        .ow_carry(w_carry_05_01)
    );
    wire w_sum_05_02, w_carry_05_02;
    math_adder_half HA__05_02 (
        .i_a(w_pp_3_2),
        .i_b(w_pp_4_1),
        .ow_sum(w_sum_05_02),
        .ow_carry(w_carry_05_02)
    );
    wire w_sum_06_02, w_carry_06_02;
    math_adder_carry_save CSA_06_02 (
        .i_a(w_pp_2_4),
        .i_b(w_pp_3_3),
        .i_c(w_pp_4_2),
        .ow_sum(w_sum_06_02),
        .ow_carry(w_carry_06_02)
    );
    wire w_sum_06_03, w_carry_06_03;
    math_adder_carry_save CSA_06_03 (
        .i_a(w_pp_5_1),
        .i_b(w_pp_6_0),
        .i_c(w_sum_06_01),
        .ow_sum(w_sum_06_03),
        .ow_carry(w_carry_06_03)
    );
    wire w_sum_07_03, w_carry_07_03;
    math_adder_carry_save CSA_07_03 (
        .i_a(w_pp_5_2),
        .i_b(w_pp_6_1),
        .i_c(w_pp_7_0),
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
    wire w_sum_08_03, w_carry_08_03;
    math_adder_carry_save CSA_08_03 (
        .i_a(w_pp_6_2),
        .i_b(w_pp_7_1),
        .i_c(w_carry_07_01),
        .ow_sum(w_sum_08_03),
        .ow_carry(w_carry_08_03)
    );
    wire w_sum_08_04, w_carry_08_04;
    math_adder_carry_save CSA_08_04 (
        .i_a(w_carry_07_02),
        .i_b(w_sum_08_01),
        .i_c(w_sum_08_02),
        .ow_sum(w_sum_08_04),
        .ow_carry(w_carry_08_04)
    );
    wire w_sum_09_02, w_carry_09_02;
    math_adder_carry_save CSA_09_02 (
        .i_a(w_pp_5_4),
        .i_b(w_pp_6_3),
        .i_c(w_pp_7_2),
        .ow_sum(w_sum_09_02),
        .ow_carry(w_carry_09_02)
    );
    wire w_sum_09_03, w_carry_09_03;
    math_adder_carry_save CSA_09_03 (
        .i_a(w_carry_08_01),
        .i_b(w_carry_08_02),
        .i_c(w_sum_09_01),
        .ow_sum(w_sum_09_03),
        .ow_carry(w_carry_09_03)
    );
    wire w_sum_10_01, w_carry_10_01;
    math_adder_carry_save CSA_10_01 (
        .i_a(w_pp_3_7),
        .i_b(w_pp_4_6),
        .i_c(w_pp_5_5),
        .ow_sum(w_sum_10_01),
        .ow_carry(w_carry_10_01)
    );
    wire w_sum_10_02, w_carry_10_02;
    math_adder_carry_save CSA_10_02 (
        .i_a(w_pp_6_4),
        .i_b(w_pp_7_3),
        .i_c(w_carry_09_01),
        .ow_sum(w_sum_10_02),
        .ow_carry(w_carry_10_02)
    );
    wire w_sum_11_01, w_carry_11_01;
    math_adder_carry_save CSA_11_01 (
        .i_a(w_pp_4_7),
        .i_b(w_pp_5_6),
        .i_c(w_pp_6_5),
        .ow_sum(w_sum_11_01),
        .ow_carry(w_carry_11_01)
    );

    // Dadda reduction stage 3: max column height 3
    wire w_sum_03_01, w_carry_03_01;
    math_adder_half HA__03_01 (
        .i_a(w_pp_0_3),
        .i_b(w_pp_1_2),
        .ow_sum(w_sum_03_01),
        .ow_carry(w_carry_03_01)
    );
    wire w_sum_04_02, w_carry_04_02;
    math_adder_carry_save CSA_04_02 (
        .i_a(w_pp_2_2),
        .i_b(w_pp_3_1),
        .i_c(w_pp_4_0),
        .ow_sum(w_sum_04_02),
        .ow_carry(w_carry_04_02)
    );
    wire w_sum_05_03, w_carry_05_03;
    math_adder_carry_save CSA_05_03 (
        .i_a(w_pp_5_0),
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
    wire w_sum_08_05, w_carry_08_05;
    math_adder_carry_save CSA_08_05 (
        .i_a(w_carry_07_03),
        .i_b(w_carry_07_04),
        .i_c(w_sum_08_03),
        .ow_sum(w_sum_08_05),
        .ow_carry(w_carry_08_05)
    );
    wire w_sum_09_04, w_carry_09_04;
    math_adder_carry_save CSA_09_04 (
        .i_a(w_carry_08_03),
        .i_b(w_carry_08_04),
        .i_c(w_sum_09_02),
        .ow_sum(w_sum_09_04),
        .ow_carry(w_carry_09_04)
    );
    wire w_sum_10_03, w_carry_10_03;
    math_adder_carry_save CSA_10_03 (
        .i_a(w_carry_09_02),
        .i_b(w_carry_09_03),
        .i_c(w_sum_10_01),
        .ow_sum(w_sum_10_03),
        .ow_carry(w_carry_10_03)
    );
    wire w_sum_11_02, w_carry_11_02;
    math_adder_carry_save CSA_11_02 (
        .i_a(w_pp_7_4),
        .i_b(w_carry_10_01),
        .i_c(w_carry_10_02),
        .ow_sum(w_sum_11_02),
        .ow_carry(w_carry_11_02)
    );
    wire w_sum_12_01, w_carry_12_01;
    math_adder_carry_save CSA_12_01 (
        .i_a(w_pp_5_7),
        .i_b(w_pp_6_6),
        .i_c(w_pp_7_5),
        .ow_sum(w_sum_12_01),
        .ow_carry(w_carry_12_01)
    );

    // Dadda reduction stage 4: max column height 2
    wire w_sum_02_01, w_carry_02_01;
    math_adder_half HA__02_01 (
        .i_a(w_pp_0_2),
        .i_b(w_pp_1_1),
        .ow_sum(w_sum_02_01),
        .ow_carry(w_carry_02_01)
    );
    wire w_sum_03_02, w_carry_03_02;
    math_adder_carry_save CSA_03_02 (
        .i_a(w_pp_2_1),
        .i_b(w_pp_3_0),
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
    wire w_sum_08_06, w_carry_08_06;
    math_adder_carry_save CSA_08_06 (
        .i_a(w_sum_08_04),
        .i_b(w_carry_07_05),
        .i_c(w_sum_08_05),
        .ow_sum(w_sum_08_06),
        .ow_carry(w_carry_08_06)
    );
    wire w_sum_09_05, w_carry_09_05;
    math_adder_carry_save CSA_09_05 (
        .i_a(w_sum_09_03),
        .i_b(w_carry_08_05),
        .i_c(w_sum_09_04),
        .ow_sum(w_sum_09_05),
        .ow_carry(w_carry_09_05)
    );
    wire w_sum_10_04, w_carry_10_04;
    math_adder_carry_save CSA_10_04 (
        .i_a(w_sum_10_02),
        .i_b(w_carry_09_04),
        .i_c(w_sum_10_03),
        .ow_sum(w_sum_10_04),
        .ow_carry(w_carry_10_04)
    );
    wire w_sum_11_03, w_carry_11_03;
    math_adder_carry_save CSA_11_03 (
        .i_a(w_sum_11_01),
        .i_b(w_carry_10_03),
        .i_c(w_sum_11_02),
        .ow_sum(w_sum_11_03),
        .ow_carry(w_carry_11_03)
    );
    wire w_sum_12_02, w_carry_12_02;
    math_adder_carry_save CSA_12_02 (
        .i_a(w_carry_11_01),
        .i_b(w_carry_11_02),
        .i_c(w_sum_12_01),
        .ow_sum(w_sum_12_02),
        .ow_carry(w_carry_12_02)
    );
    wire w_sum_13_01, w_carry_13_01;
    math_adder_carry_save CSA_13_01 (
        .i_a(w_pp_6_7),
        .i_b(w_pp_7_6),
        .i_c(w_carry_12_01),
        .ow_sum(w_sum_13_01),
        .ow_carry(w_carry_13_01)
    );

    // Final addition stage: two reduced rows into a Brent-Kung CPA
    wire [15:0] w_cpa_row0 = {
        1'b0,
        w_pp_7_7,
        w_carry_12_02,
        w_carry_11_03,
        w_carry_10_04,
        w_carry_09_05,
        w_carry_08_06,
        w_carry_07_06,
        w_carry_06_05,
        w_carry_05_04,
        w_carry_04_03,
        w_carry_03_02,
        w_carry_02_01,
        w_pp_2_0,
        w_pp_0_1,
        w_pp_0_0
    };
    wire [15:0] w_cpa_row1 = {
        1'b0,
        w_carry_13_01,
        w_sum_13_01,
        w_sum_12_02,
        w_sum_11_03,
        w_sum_10_04,
        w_sum_09_05,
        w_sum_08_06,
        w_sum_07_06,
        w_sum_06_05,
        w_sum_05_04,
        w_sum_04_03,
        w_sum_03_02,
        w_sum_02_01,
        w_pp_1_0,
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
