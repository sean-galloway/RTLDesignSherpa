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
    wire w_sum_01_2, w_carry_01_2;
    math_adder_half HA_01_2 (
        .i_a(w_pp_0_1),
        .i_b(w_pp_1_0),
        .ow_sum(w_sum_01_2),
        .ow_carry(w_carry_01_2)
    );
    wire w_sum_02_4, w_carry_02_4;

    math_adder_full FA_02_4 (
        .i_a(w_pp_0_2),
        .i_b(w_pp_1_1),
        .i_c(w_pp_2_0),
        .ow_sum(w_sum_02_4),
        .ow_carry(w_carry_02_4)
    );
    wire w_sum_02_2, w_carry_02_2;
    math_adder_half HA_02_2 (
        .i_a(w_carry_01_2),
        .i_b(w_sum_02_4),
        .ow_sum(w_sum_02_2),
        .ow_carry(w_carry_02_2)
    );
    wire w_sum_03_6, w_carry_03_6;

    math_adder_full FA_03_6 (
        .i_a(w_pp_0_3),
        .i_b(w_pp_1_2),
        .i_c(w_pp_2_1),
        .ow_sum(w_sum_03_6),
        .ow_carry(w_carry_03_6)
    );
    wire w_sum_03_4, w_carry_03_4;

    math_adder_full FA_03_4 (
        .i_a(w_pp_3_0),
        .i_b(w_carry_02_4),
        .i_c(w_carry_02_2),
        .ow_sum(w_sum_03_4),
        .ow_carry(w_carry_03_4)
    );
    wire w_sum_03_2, w_carry_03_2;
    math_adder_half HA_03_2 (
        .i_a(w_sum_03_6),
        .i_b(w_sum_03_4),
        .ow_sum(w_sum_03_2),
        .ow_carry(w_carry_03_2)
    );
    wire w_sum_04_8, w_carry_04_8;

    math_adder_full FA_04_8 (
        .i_a(w_pp_0_4),
        .i_b(w_pp_1_3),
        .i_c(w_pp_2_2),
        .ow_sum(w_sum_04_8),
        .ow_carry(w_carry_04_8)
    );
    wire w_sum_04_6, w_carry_04_6;

    math_adder_full FA_04_6 (
        .i_a(w_pp_3_1),
        .i_b(w_pp_4_0),
        .i_c(w_carry_03_6),
        .ow_sum(w_sum_04_6),
        .ow_carry(w_carry_04_6)
    );
    wire w_sum_04_4, w_carry_04_4;

    math_adder_full FA_04_4 (
        .i_a(w_carry_03_4),
        .i_b(w_carry_03_2),
        .i_c(w_sum_04_8),
        .ow_sum(w_sum_04_4),
        .ow_carry(w_carry_04_4)
    );
    wire w_sum_04_2, w_carry_04_2;
    math_adder_half HA_04_2 (
        .i_a(w_sum_04_6),
        .i_b(w_sum_04_4),
        .ow_sum(w_sum_04_2),
        .ow_carry(w_carry_04_2)
    );
    wire w_sum_05_10, w_carry_05_10;

    math_adder_full FA_05_10 (
        .i_a(w_pp_0_5),
        .i_b(w_pp_1_4),
        .i_c(w_pp_2_3),
        .ow_sum(w_sum_05_10),
        .ow_carry(w_carry_05_10)
    );
    wire w_sum_05_8, w_carry_05_8;

    math_adder_full FA_05_8 (
        .i_a(w_pp_3_2),
        .i_b(w_pp_4_1),
        .i_c(w_pp_5_0),
        .ow_sum(w_sum_05_8),
        .ow_carry(w_carry_05_8)
    );
    wire w_sum_05_6, w_carry_05_6;

    math_adder_full FA_05_6 (
        .i_a(w_carry_04_8),
        .i_b(w_carry_04_6),
        .i_c(w_carry_04_4),
        .ow_sum(w_sum_05_6),
        .ow_carry(w_carry_05_6)
    );
    wire w_sum_05_4, w_carry_05_4;

    math_adder_full FA_05_4 (
        .i_a(w_carry_04_2),
        .i_b(w_sum_05_10),
        .i_c(w_sum_05_8),
        .ow_sum(w_sum_05_4),
        .ow_carry(w_carry_05_4)
    );
    wire w_sum_05_2, w_carry_05_2;
    math_adder_half HA_05_2 (
        .i_a(w_sum_05_6),
        .i_b(w_sum_05_4),
        .ow_sum(w_sum_05_2),
        .ow_carry(w_carry_05_2)
    );
    wire w_sum_06_12, w_carry_06_12;

    math_adder_full FA_06_12 (
        .i_a(w_pp_0_6),
        .i_b(w_pp_1_5),
        .i_c(w_pp_2_4),
        .ow_sum(w_sum_06_12),
        .ow_carry(w_carry_06_12)
    );
    wire w_sum_06_10, w_carry_06_10;

    math_adder_full FA_06_10 (
        .i_a(w_pp_3_3),
        .i_b(w_pp_4_2),
        .i_c(w_pp_5_1),
        .ow_sum(w_sum_06_10),
        .ow_carry(w_carry_06_10)
    );
    wire w_sum_06_8, w_carry_06_8;

    math_adder_full FA_06_8 (
        .i_a(w_pp_6_0),
        .i_b(w_carry_05_10),
        .i_c(w_carry_05_8),
        .ow_sum(w_sum_06_8),
        .ow_carry(w_carry_06_8)
    );
    wire w_sum_06_6, w_carry_06_6;

    math_adder_full FA_06_6 (
        .i_a(w_carry_05_6),
        .i_b(w_carry_05_4),
        .i_c(w_carry_05_2),
        .ow_sum(w_sum_06_6),
        .ow_carry(w_carry_06_6)
    );
    wire w_sum_06_4, w_carry_06_4;

    math_adder_full FA_06_4 (
        .i_a(w_sum_06_12),
        .i_b(w_sum_06_10),
        .i_c(w_sum_06_8),
        .ow_sum(w_sum_06_4),
        .ow_carry(w_carry_06_4)
    );
    wire w_sum_06_2, w_carry_06_2;
    math_adder_half HA_06_2 (
        .i_a(w_sum_06_6),
        .i_b(w_sum_06_4),
        .ow_sum(w_sum_06_2),
        .ow_carry(w_carry_06_2)
    );
    wire w_sum_07_14, w_carry_07_14;

    math_adder_full FA_07_14 (
        .i_a(w_pp_0_7),
        .i_b(w_pp_1_6),
        .i_c(w_pp_2_5),
        .ow_sum(w_sum_07_14),
        .ow_carry(w_carry_07_14)
    );
    wire w_sum_07_12, w_carry_07_12;

    math_adder_full FA_07_12 (
        .i_a(w_pp_3_4),
        .i_b(w_pp_4_3),
        .i_c(w_pp_5_2),
        .ow_sum(w_sum_07_12),
        .ow_carry(w_carry_07_12)
    );
    wire w_sum_07_10, w_carry_07_10;

    math_adder_full FA_07_10 (
        .i_a(w_pp_6_1),
        .i_b(w_pp_7_0),
        .i_c(w_carry_06_12),
        .ow_sum(w_sum_07_10),
        .ow_carry(w_carry_07_10)
    );
    wire w_sum_07_8, w_carry_07_8;

    math_adder_full FA_07_8 (
        .i_a(w_carry_06_10),
        .i_b(w_carry_06_8),
        .i_c(w_carry_06_6),
        .ow_sum(w_sum_07_8),
        .ow_carry(w_carry_07_8)
    );
    wire w_sum_07_6, w_carry_07_6;

    math_adder_full FA_07_6 (
        .i_a(w_carry_06_4),
        .i_b(w_carry_06_2),
        .i_c(w_sum_07_14),
        .ow_sum(w_sum_07_6),
        .ow_carry(w_carry_07_6)
    );
    wire w_sum_07_4, w_carry_07_4;

    math_adder_full FA_07_4 (
        .i_a(w_sum_07_12),
        .i_b(w_sum_07_10),
        .i_c(w_sum_07_8),
        .ow_sum(w_sum_07_4),
        .ow_carry(w_carry_07_4)
    );
    wire w_sum_07_2, w_carry_07_2;
    math_adder_half HA_07_2 (
        .i_a(w_sum_07_6),
        .i_b(w_sum_07_4),
        .ow_sum(w_sum_07_2),
        .ow_carry(w_carry_07_2)
    );
    wire w_sum_08_14, w_carry_08_14;

    math_adder_full FA_08_14 (
        .i_a(w_pp_1_7),
        .i_b(w_pp_2_6),
        .i_c(w_pp_3_5),
        .ow_sum(w_sum_08_14),
        .ow_carry(w_carry_08_14)
    );
    wire w_sum_08_12, w_carry_08_12;

    math_adder_full FA_08_12 (
        .i_a(w_pp_4_4),
        .i_b(w_pp_5_3),
        .i_c(w_pp_6_2),
        .ow_sum(w_sum_08_12),
        .ow_carry(w_carry_08_12)
    );
    wire w_sum_08_10, w_carry_08_10;

    math_adder_full FA_08_10 (
        .i_a(w_pp_7_1),
        .i_b(w_carry_07_14),
        .i_c(w_carry_07_12),
        .ow_sum(w_sum_08_10),
        .ow_carry(w_carry_08_10)
    );
    wire w_sum_08_8, w_carry_08_8;

    math_adder_full FA_08_8 (
        .i_a(w_carry_07_10),
        .i_b(w_carry_07_8),
        .i_c(w_carry_07_6),
        .ow_sum(w_sum_08_8),
        .ow_carry(w_carry_08_8)
    );
    wire w_sum_08_6, w_carry_08_6;

    math_adder_full FA_08_6 (
        .i_a(w_carry_07_4),
        .i_b(w_carry_07_2),
        .i_c(w_sum_08_14),
        .ow_sum(w_sum_08_6),
        .ow_carry(w_carry_08_6)
    );
    wire w_sum_08_4, w_carry_08_4;

    math_adder_full FA_08_4 (
        .i_a(w_sum_08_12),
        .i_b(w_sum_08_10),
        .i_c(w_sum_08_8),
        .ow_sum(w_sum_08_4),
        .ow_carry(w_carry_08_4)
    );
    wire w_sum_08_2, w_carry_08_2;
    math_adder_half HA_08_2 (
        .i_a(w_sum_08_6),
        .i_b(w_sum_08_4),
        .ow_sum(w_sum_08_2),
        .ow_carry(w_carry_08_2)
    );
    wire w_sum_09_13, w_carry_09_13;

    math_adder_full FA_09_13 (
        .i_a(w_pp_2_7),
        .i_b(w_pp_3_6),
        .i_c(w_pp_4_5),
        .ow_sum(w_sum_09_13),
        .ow_carry(w_carry_09_13)
    );
    wire w_sum_09_11, w_carry_09_11;

    math_adder_full FA_09_11 (
        .i_a(w_pp_5_4),
        .i_b(w_pp_6_3),
        .i_c(w_pp_7_2),
        .ow_sum(w_sum_09_11),
        .ow_carry(w_carry_09_11)
    );
    wire w_sum_09_9, w_carry_09_9;

    math_adder_full FA_09_9 (
        .i_a(w_carry_08_14),
        .i_b(w_carry_08_12),
        .i_c(w_carry_08_10),
        .ow_sum(w_sum_09_9),
        .ow_carry(w_carry_09_9)
    );
    wire w_sum_09_7, w_carry_09_7;

    math_adder_full FA_09_7 (
        .i_a(w_carry_08_8),
        .i_b(w_carry_08_6),
        .i_c(w_carry_08_4),
        .ow_sum(w_sum_09_7),
        .ow_carry(w_carry_09_7)
    );
    wire w_sum_09_5, w_carry_09_5;

    math_adder_full FA_09_5 (
        .i_a(w_carry_08_2),
        .i_b(w_sum_09_13),
        .i_c(w_sum_09_11),
        .ow_sum(w_sum_09_5),
        .ow_carry(w_carry_09_5)
    );
    wire w_sum_09_3, w_carry_09_3;

    math_adder_full FA_09_3 (
        .i_a(w_sum_09_9),
        .i_b(w_sum_09_7),
        .i_c(w_sum_09_5),
        .ow_sum(w_sum_09_3),
        .ow_carry(w_carry_09_3)
    );
    wire w_sum_10_11, w_carry_10_11;

    math_adder_full FA_10_11 (
        .i_a(w_pp_3_7),
        .i_b(w_pp_4_6),
        .i_c(w_pp_5_5),
        .ow_sum(w_sum_10_11),
        .ow_carry(w_carry_10_11)
    );
    wire w_sum_10_9, w_carry_10_9;

    math_adder_full FA_10_9 (
        .i_a(w_pp_6_4),
        .i_b(w_pp_7_3),
        .i_c(w_carry_09_13),
        .ow_sum(w_sum_10_9),
        .ow_carry(w_carry_10_9)
    );
    wire w_sum_10_7, w_carry_10_7;

    math_adder_full FA_10_7 (
        .i_a(w_carry_09_11),
        .i_b(w_carry_09_9),
        .i_c(w_carry_09_7),
        .ow_sum(w_sum_10_7),
        .ow_carry(w_carry_10_7)
    );
    wire w_sum_10_5, w_carry_10_5;

    math_adder_full FA_10_5 (
        .i_a(w_carry_09_5),
        .i_b(w_carry_09_3),
        .i_c(w_sum_10_11),
        .ow_sum(w_sum_10_5),
        .ow_carry(w_carry_10_5)
    );
    wire w_sum_10_3, w_carry_10_3;

    math_adder_full FA_10_3 (
        .i_a(w_sum_10_9),
        .i_b(w_sum_10_7),
        .i_c(w_sum_10_5),
        .ow_sum(w_sum_10_3),
        .ow_carry(w_carry_10_3)
    );
    wire w_sum_11_9, w_carry_11_9;

    math_adder_full FA_11_9 (
        .i_a(w_pp_4_7),
        .i_b(w_pp_5_6),
        .i_c(w_pp_6_5),
        .ow_sum(w_sum_11_9),
        .ow_carry(w_carry_11_9)
    );
    wire w_sum_11_7, w_carry_11_7;

    math_adder_full FA_11_7 (
        .i_a(w_pp_7_4),
        .i_b(w_carry_10_11),
        .i_c(w_carry_10_9),
        .ow_sum(w_sum_11_7),
        .ow_carry(w_carry_11_7)
    );
    wire w_sum_11_5, w_carry_11_5;

    math_adder_full FA_11_5 (
        .i_a(w_carry_10_7),
        .i_b(w_carry_10_5),
        .i_c(w_carry_10_3),
        .ow_sum(w_sum_11_5),
        .ow_carry(w_carry_11_5)
    );
    wire w_sum_11_3, w_carry_11_3;

    math_adder_full FA_11_3 (
        .i_a(w_sum_11_9),
        .i_b(w_sum_11_7),
        .i_c(w_sum_11_5),
        .ow_sum(w_sum_11_3),
        .ow_carry(w_carry_11_3)
    );
    wire w_sum_12_7, w_carry_12_7;

    math_adder_full FA_12_7 (
        .i_a(w_pp_5_7),
        .i_b(w_pp_6_6),
        .i_c(w_pp_7_5),
        .ow_sum(w_sum_12_7),
        .ow_carry(w_carry_12_7)
    );
    wire w_sum_12_5, w_carry_12_5;

    math_adder_full FA_12_5 (
        .i_a(w_carry_11_9),
        .i_b(w_carry_11_7),
        .i_c(w_carry_11_5),
        .ow_sum(w_sum_12_5),
        .ow_carry(w_carry_12_5)
    );
    wire w_sum_12_3, w_carry_12_3;

    math_adder_full FA_12_3 (
        .i_a(w_carry_11_3),
        .i_b(w_sum_12_7),
        .i_c(w_sum_12_5),
        .ow_sum(w_sum_12_3),
        .ow_carry(w_carry_12_3)
    );
    wire w_sum_13_5, w_carry_13_5;

    math_adder_full FA_13_5 (
        .i_a(w_pp_6_7),
        .i_b(w_pp_7_6),
        .i_c(w_carry_12_7),
        .ow_sum(w_sum_13_5),
        .ow_carry(w_carry_13_5)
    );
    wire w_sum_13_3, w_carry_13_3;

    math_adder_full FA_13_3 (
        .i_a(w_carry_12_5),
        .i_b(w_carry_12_3),
        .i_c(w_sum_13_5),
        .ow_sum(w_sum_13_3),
        .ow_carry(w_carry_13_3)
    );
    wire w_sum_14_3, w_carry_14_3;

    math_adder_full FA_14_3 (
        .i_a(w_pp_7_7),
        .i_b(w_carry_13_5),
        .i_c(w_carry_13_3),
        .ow_sum(w_sum_14_3),
        .ow_carry(w_carry_14_3)
    );

    // Final addition stage
    wire w_sum_00 = w_pp_0_0;
    wire w_carry_00 = 1'b0;
    wire w_sum_01 = w_sum_01_2;
    wire w_carry_01 = 1'b0;
    wire w_sum_02 = w_sum_02_2;
    wire w_carry_02 = 1'b0;
    wire w_sum_03 = w_sum_03_2;
    wire w_carry_03 = 1'b0;
    wire w_sum_04 = w_sum_04_2;
    wire w_carry_04 = 1'b0;
    wire w_sum_05 = w_sum_05_2;
    wire w_carry_05 = 1'b0;
    wire w_sum_06 = w_sum_06_2;
    wire w_carry_06 = 1'b0;
    wire w_sum_07 = w_sum_07_2;
    wire w_carry_07 = 1'b0;
    wire w_sum_08 = w_sum_08_2;
    wire w_carry_08 = 1'b0;
    wire w_sum_09 = w_sum_09_3;
    wire w_carry_09 = 1'b0;
    wire w_sum_10 = w_sum_10_3;
    wire w_carry_10 = 1'b0;
    wire w_sum_11 = w_sum_11_3;
    wire w_carry_11 = 1'b0;
    wire w_sum_12 = w_sum_12_3;
    wire w_carry_12 = 1'b0;
    wire w_sum_13 = w_sum_13_3;
    wire w_carry_13 = 1'b0;
    wire w_sum_14 = w_sum_14_3;
    wire w_carry_14 = 1'b0;
    wire w_sum_15 = w_carry_14_3;
    wire w_carry_15 = 1'b0;

    // Final product assignment
    assign ow_product[0]  = w_sum_00;
    assign ow_product[1]  = w_sum_01;
    assign ow_product[2]  = w_sum_02;
    assign ow_product[3]  = w_sum_03;
    assign ow_product[4]  = w_sum_04;
    assign ow_product[5]  = w_sum_05;
    assign ow_product[6]  = w_sum_06;
    assign ow_product[7]  = w_sum_07;
    assign ow_product[8]  = w_sum_08;
    assign ow_product[9]  = w_sum_09;
    assign ow_product[10] = w_sum_10;
    assign ow_product[11] = w_sum_11;
    assign ow_product[12] = w_sum_12;
    assign ow_product[13] = w_sum_13;
    assign ow_product[14] = w_sum_14;
    assign ow_product[15] = w_sum_15;

endmodule
