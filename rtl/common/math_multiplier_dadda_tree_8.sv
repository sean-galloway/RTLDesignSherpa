`timescale 1ns / 1ps

module math_multiplier_dadda_tree_8 (
    input  [7:0] i_multiplier,
    input  [7:0] i_multiplicand,
    output [15:0] ow_product
);

// Partial products generation
wire w_pp_0_0 = i_multiplier[ 0] & i_multiplicand[ 0];
wire w_pp_0_1 = i_multiplier[ 0] & i_multiplicand[ 1];
wire w_pp_0_2 = i_multiplier[ 0] & i_multiplicand[ 2];
wire w_pp_0_3 = i_multiplier[ 0] & i_multiplicand[ 3];
wire w_pp_0_4 = i_multiplier[ 0] & i_multiplicand[ 4];
wire w_pp_0_5 = i_multiplier[ 0] & i_multiplicand[ 5];
wire w_pp_0_6 = i_multiplier[ 0] & i_multiplicand[ 6];
wire w_pp_0_7 = i_multiplier[ 0] & i_multiplicand[ 7];
wire w_pp_1_0 = i_multiplier[ 1] & i_multiplicand[ 0];
wire w_pp_1_1 = i_multiplier[ 1] & i_multiplicand[ 1];
wire w_pp_1_2 = i_multiplier[ 1] & i_multiplicand[ 2];
wire w_pp_1_3 = i_multiplier[ 1] & i_multiplicand[ 3];
wire w_pp_1_4 = i_multiplier[ 1] & i_multiplicand[ 4];
wire w_pp_1_5 = i_multiplier[ 1] & i_multiplicand[ 5];
wire w_pp_1_6 = i_multiplier[ 1] & i_multiplicand[ 6];
wire w_pp_1_7 = i_multiplier[ 1] & i_multiplicand[ 7];
wire w_pp_2_0 = i_multiplier[ 2] & i_multiplicand[ 0];
wire w_pp_2_1 = i_multiplier[ 2] & i_multiplicand[ 1];
wire w_pp_2_2 = i_multiplier[ 2] & i_multiplicand[ 2];
wire w_pp_2_3 = i_multiplier[ 2] & i_multiplicand[ 3];
wire w_pp_2_4 = i_multiplier[ 2] & i_multiplicand[ 4];
wire w_pp_2_5 = i_multiplier[ 2] & i_multiplicand[ 5];
wire w_pp_2_6 = i_multiplier[ 2] & i_multiplicand[ 6];
wire w_pp_2_7 = i_multiplier[ 2] & i_multiplicand[ 7];
wire w_pp_3_0 = i_multiplier[ 3] & i_multiplicand[ 0];
wire w_pp_3_1 = i_multiplier[ 3] & i_multiplicand[ 1];
wire w_pp_3_2 = i_multiplier[ 3] & i_multiplicand[ 2];
wire w_pp_3_3 = i_multiplier[ 3] & i_multiplicand[ 3];
wire w_pp_3_4 = i_multiplier[ 3] & i_multiplicand[ 4];
wire w_pp_3_5 = i_multiplier[ 3] & i_multiplicand[ 5];
wire w_pp_3_6 = i_multiplier[ 3] & i_multiplicand[ 6];
wire w_pp_3_7 = i_multiplier[ 3] & i_multiplicand[ 7];
wire w_pp_4_0 = i_multiplier[ 4] & i_multiplicand[ 0];
wire w_pp_4_1 = i_multiplier[ 4] & i_multiplicand[ 1];
wire w_pp_4_2 = i_multiplier[ 4] & i_multiplicand[ 2];
wire w_pp_4_3 = i_multiplier[ 4] & i_multiplicand[ 3];
wire w_pp_4_4 = i_multiplier[ 4] & i_multiplicand[ 4];
wire w_pp_4_5 = i_multiplier[ 4] & i_multiplicand[ 5];
wire w_pp_4_6 = i_multiplier[ 4] & i_multiplicand[ 6];
wire w_pp_4_7 = i_multiplier[ 4] & i_multiplicand[ 7];
wire w_pp_5_0 = i_multiplier[ 5] & i_multiplicand[ 0];
wire w_pp_5_1 = i_multiplier[ 5] & i_multiplicand[ 1];
wire w_pp_5_2 = i_multiplier[ 5] & i_multiplicand[ 2];
wire w_pp_5_3 = i_multiplier[ 5] & i_multiplicand[ 3];
wire w_pp_5_4 = i_multiplier[ 5] & i_multiplicand[ 4];
wire w_pp_5_5 = i_multiplier[ 5] & i_multiplicand[ 5];
wire w_pp_5_6 = i_multiplier[ 5] & i_multiplicand[ 6];
wire w_pp_5_7 = i_multiplier[ 5] & i_multiplicand[ 7];
wire w_pp_6_0 = i_multiplier[ 6] & i_multiplicand[ 0];
wire w_pp_6_1 = i_multiplier[ 6] & i_multiplicand[ 1];
wire w_pp_6_2 = i_multiplier[ 6] & i_multiplicand[ 2];
wire w_pp_6_3 = i_multiplier[ 6] & i_multiplicand[ 3];
wire w_pp_6_4 = i_multiplier[ 6] & i_multiplicand[ 4];
wire w_pp_6_5 = i_multiplier[ 6] & i_multiplicand[ 5];
wire w_pp_6_6 = i_multiplier[ 6] & i_multiplicand[ 6];
wire w_pp_6_7 = i_multiplier[ 6] & i_multiplicand[ 7];
wire w_pp_7_0 = i_multiplier[ 7] & i_multiplicand[ 0];
wire w_pp_7_1 = i_multiplier[ 7] & i_multiplicand[ 1];
wire w_pp_7_2 = i_multiplier[ 7] & i_multiplicand[ 2];
wire w_pp_7_3 = i_multiplier[ 7] & i_multiplicand[ 3];
wire w_pp_7_4 = i_multiplier[ 7] & i_multiplicand[ 4];
wire w_pp_7_5 = i_multiplier[ 7] & i_multiplicand[ 5];
wire w_pp_7_6 = i_multiplier[ 7] & i_multiplicand[ 6];
wire w_pp_7_7 = i_multiplier[ 7] & i_multiplicand[ 7];

// Stage: 0, Max Height: 6
wire w_sum_0, w_carry_0;
math_adder_half HA_0(.i_a(w_pp_0_6), .i_b(w_pp_1_5), .ow_sum(w_sum_0), .ow_carry(w_carry_0));
wire w_sum_1, w_carry_1;
math_adder_carry_save CSA_1(.i_a(w_pp_0_7), .i_b(w_pp_1_6), .i_c(w_pp_2_5), .ow_sum(w_sum_1), .ow_carry(w_carry_1));
wire w_sum_2, w_carry_2;
math_adder_half HA_2(.i_a(w_pp_3_4), .i_b(w_pp_4_3), .ow_sum(w_sum_2), .ow_carry(w_carry_2));
wire w_sum_3, w_carry_3;
math_adder_carry_save CSA_3(.i_a(w_pp_1_7), .i_b(w_pp_2_6), .i_c(w_pp_3_5), .ow_sum(w_sum_3), .ow_carry(w_carry_3));
wire w_sum_4, w_carry_4;
math_adder_half HA_4(.i_a(w_pp_4_4), .i_b(w_pp_5_3), .ow_sum(w_sum_4), .ow_carry(w_carry_4));
wire w_sum_5, w_carry_5;
math_adder_carry_save CSA_5(.i_a(w_pp_2_7), .i_b(w_pp_3_6), .i_c(w_pp_4_5), .ow_sum(w_sum_5), .ow_carry(w_carry_5));
// Stage: 1, Max Height: 4
wire w_sum_6, w_carry_6;
math_adder_half HA_6(.i_a(w_pp_0_4), .i_b(w_pp_1_3), .ow_sum(w_sum_6), .ow_carry(w_carry_6));
wire w_sum_7, w_carry_7;
math_adder_carry_save CSA_7(.i_a(w_pp_0_5), .i_b(w_pp_1_4), .i_c(w_pp_2_3), .ow_sum(w_sum_7), .ow_carry(w_carry_7));
wire w_sum_8, w_carry_8;
math_adder_half HA_8(.i_a(w_pp_3_2), .i_b(w_pp_4_1), .ow_sum(w_sum_8), .ow_carry(w_carry_8));
wire w_sum_9, w_carry_9;
math_adder_carry_save CSA_9(.i_a(w_pp_2_4), .i_b(w_pp_3_3), .i_c(w_pp_4_2), .ow_sum(w_sum_9), .ow_carry(w_carry_9));
wire w_sum_10, w_carry_10;
math_adder_carry_save CSA_10(.i_a(w_pp_5_1), .i_b(w_pp_6_0), .i_c(w_sum_0), .ow_sum(w_sum_10), .ow_carry(w_carry_10));
wire w_sum_11, w_carry_11;
math_adder_carry_save CSA_11(.i_a(w_pp_5_2), .i_b(w_pp_6_1), .i_c(w_pp_7_0), .ow_sum(w_sum_11), .ow_carry(w_carry_11));
wire w_sum_12, w_carry_12;
math_adder_carry_save CSA_12(.i_a(w_carry_0), .i_b(w_sum_1), .i_c(w_sum_2), .ow_sum(w_sum_12), .ow_carry(w_carry_12));
wire w_sum_13, w_carry_13;
math_adder_carry_save CSA_13(.i_a(w_pp_6_2), .i_b(w_pp_7_1), .i_c(w_carry_1), .ow_sum(w_sum_13), .ow_carry(w_carry_13));
wire w_sum_14, w_carry_14;
math_adder_carry_save CSA_14(.i_a(w_carry_2), .i_b(w_sum_3), .i_c(w_sum_4), .ow_sum(w_sum_14), .ow_carry(w_carry_14));
wire w_sum_15, w_carry_15;
math_adder_carry_save CSA_15(.i_a(w_pp_5_4), .i_b(w_pp_6_3), .i_c(w_pp_7_2), .ow_sum(w_sum_15), .ow_carry(w_carry_15));
wire w_sum_16, w_carry_16;
math_adder_carry_save CSA_16(.i_a(w_carry_3), .i_b(w_carry_4), .i_c(w_sum_5), .ow_sum(w_sum_16), .ow_carry(w_carry_16));
wire w_sum_17, w_carry_17;
math_adder_carry_save CSA_17(.i_a(w_pp_3_7), .i_b(w_pp_4_6), .i_c(w_pp_5_5), .ow_sum(w_sum_17), .ow_carry(w_carry_17));
wire w_sum_18, w_carry_18;
math_adder_carry_save CSA_18(.i_a(w_pp_6_4), .i_b(w_pp_7_3), .i_c(w_carry_5), .ow_sum(w_sum_18), .ow_carry(w_carry_18));
wire w_sum_19, w_carry_19;
math_adder_carry_save CSA_19(.i_a(w_pp_4_7), .i_b(w_pp_5_6), .i_c(w_pp_6_5), .ow_sum(w_sum_19), .ow_carry(w_carry_19));
// Stage: 2, Max Height: 3
wire w_sum_20, w_carry_20;
math_adder_half HA_20(.i_a(w_pp_0_3), .i_b(w_pp_1_2), .ow_sum(w_sum_20), .ow_carry(w_carry_20));
wire w_sum_21, w_carry_21;
math_adder_carry_save CSA_21(.i_a(w_pp_2_2), .i_b(w_pp_3_1), .i_c(w_pp_4_0), .ow_sum(w_sum_21), .ow_carry(w_carry_21));
wire w_sum_22, w_carry_22;
math_adder_carry_save CSA_22(.i_a(w_pp_5_0), .i_b(w_carry_6), .i_c(w_sum_7), .ow_sum(w_sum_22), .ow_carry(w_carry_22));
wire w_sum_23, w_carry_23;
math_adder_carry_save CSA_23(.i_a(w_carry_7), .i_b(w_carry_8), .i_c(w_sum_9), .ow_sum(w_sum_23), .ow_carry(w_carry_23));
wire w_sum_24, w_carry_24;
math_adder_carry_save CSA_24(.i_a(w_carry_9), .i_b(w_carry_10), .i_c(w_sum_11), .ow_sum(w_sum_24), .ow_carry(w_carry_24));
wire w_sum_25, w_carry_25;
math_adder_carry_save CSA_25(.i_a(w_carry_11), .i_b(w_carry_12), .i_c(w_sum_13), .ow_sum(w_sum_25), .ow_carry(w_carry_25));
wire w_sum_26, w_carry_26;
math_adder_carry_save CSA_26(.i_a(w_carry_13), .i_b(w_carry_14), .i_c(w_sum_15), .ow_sum(w_sum_26), .ow_carry(w_carry_26));
wire w_sum_27, w_carry_27;
math_adder_carry_save CSA_27(.i_a(w_carry_15), .i_b(w_carry_16), .i_c(w_sum_17), .ow_sum(w_sum_27), .ow_carry(w_carry_27));
wire w_sum_28, w_carry_28;
math_adder_carry_save CSA_28(.i_a(w_pp_7_4), .i_b(w_carry_17), .i_c(w_carry_18), .ow_sum(w_sum_28), .ow_carry(w_carry_28));
wire w_sum_29, w_carry_29;
math_adder_carry_save CSA_29(.i_a(w_pp_5_7), .i_b(w_pp_6_6), .i_c(w_pp_7_5), .ow_sum(w_sum_29), .ow_carry(w_carry_29));
// Stage: 3, Max Height: 2
wire w_sum_30, w_carry_30;
math_adder_half HA_30(.i_a(w_pp_0_2), .i_b(w_pp_1_1), .ow_sum(w_sum_30), .ow_carry(w_carry_30));
wire w_sum_31, w_carry_31;
math_adder_carry_save CSA_31(.i_a(w_pp_2_1), .i_b(w_pp_3_0), .i_c(w_sum_20), .ow_sum(w_sum_31), .ow_carry(w_carry_31));
wire w_sum_32, w_carry_32;
math_adder_carry_save CSA_32(.i_a(w_sum_6), .i_b(w_carry_20), .i_c(w_sum_21), .ow_sum(w_sum_32), .ow_carry(w_carry_32));
wire w_sum_33, w_carry_33;
math_adder_carry_save CSA_33(.i_a(w_sum_8), .i_b(w_carry_21), .i_c(w_sum_22), .ow_sum(w_sum_33), .ow_carry(w_carry_33));
wire w_sum_34, w_carry_34;
math_adder_carry_save CSA_34(.i_a(w_sum_10), .i_b(w_carry_22), .i_c(w_sum_23), .ow_sum(w_sum_34), .ow_carry(w_carry_34));
wire w_sum_35, w_carry_35;
math_adder_carry_save CSA_35(.i_a(w_sum_12), .i_b(w_carry_23), .i_c(w_sum_24), .ow_sum(w_sum_35), .ow_carry(w_carry_35));
wire w_sum_36, w_carry_36;
math_adder_carry_save CSA_36(.i_a(w_sum_14), .i_b(w_carry_24), .i_c(w_sum_25), .ow_sum(w_sum_36), .ow_carry(w_carry_36));
wire w_sum_37, w_carry_37;
math_adder_carry_save CSA_37(.i_a(w_sum_16), .i_b(w_carry_25), .i_c(w_sum_26), .ow_sum(w_sum_37), .ow_carry(w_carry_37));
wire w_sum_38, w_carry_38;
math_adder_carry_save CSA_38(.i_a(w_sum_18), .i_b(w_carry_26), .i_c(w_sum_27), .ow_sum(w_sum_38), .ow_carry(w_carry_38));
wire w_sum_39, w_carry_39;
math_adder_carry_save CSA_39(.i_a(w_sum_19), .i_b(w_carry_27), .i_c(w_sum_28), .ow_sum(w_sum_39), .ow_carry(w_carry_39));
wire w_sum_40, w_carry_40;
math_adder_carry_save CSA_40(.i_a(w_carry_19), .i_b(w_carry_28), .i_c(w_sum_29), .ow_sum(w_sum_40), .ow_carry(w_carry_40));
wire w_sum_41, w_carry_41;
math_adder_carry_save CSA_41(.i_a(w_pp_6_7), .i_b(w_pp_7_6), .i_c(w_carry_29), .ow_sum(w_sum_41), .ow_carry(w_carry_41));

// Final addition stage
wire ow_sum_00, ow_carry_00;
assign ow_sum_00 = w_pp_0_0;
assign ow_carry_00 = 1'b0;
wire ow_sum_01, ow_carry_01;
math_adder_full FA_01(.i_a(w_pp_0_1), .i_b(w_pp_1_0), .i_c(ow_carry_00), .ow_sum(ow_sum_01), .ow_carry(ow_carry_01));
wire ow_sum_02, ow_carry_02;
math_adder_full FA_02(.i_a(w_pp_2_0), .i_b(w_sum_30), .i_c(ow_carry_01), .ow_sum(ow_sum_02), .ow_carry(ow_carry_02));
wire ow_sum_03, ow_carry_03;
math_adder_full FA_03(.i_a(w_carry_30), .i_b(w_sum_31), .i_c(ow_carry_02), .ow_sum(ow_sum_03), .ow_carry(ow_carry_03));
wire ow_sum_04, ow_carry_04;
math_adder_full FA_04(.i_a(w_carry_31), .i_b(w_sum_32), .i_c(ow_carry_03), .ow_sum(ow_sum_04), .ow_carry(ow_carry_04));
wire ow_sum_05, ow_carry_05;
math_adder_full FA_05(.i_a(w_carry_32), .i_b(w_sum_33), .i_c(ow_carry_04), .ow_sum(ow_sum_05), .ow_carry(ow_carry_05));
wire ow_sum_06, ow_carry_06;
math_adder_full FA_06(.i_a(w_carry_33), .i_b(w_sum_34), .i_c(ow_carry_05), .ow_sum(ow_sum_06), .ow_carry(ow_carry_06));
wire ow_sum_07, ow_carry_07;
math_adder_full FA_07(.i_a(w_carry_34), .i_b(w_sum_35), .i_c(ow_carry_06), .ow_sum(ow_sum_07), .ow_carry(ow_carry_07));
wire ow_sum_08, ow_carry_08;
math_adder_full FA_08(.i_a(w_carry_35), .i_b(w_sum_36), .i_c(ow_carry_07), .ow_sum(ow_sum_08), .ow_carry(ow_carry_08));
wire ow_sum_09, ow_carry_09;
math_adder_full FA_09(.i_a(w_carry_36), .i_b(w_sum_37), .i_c(ow_carry_08), .ow_sum(ow_sum_09), .ow_carry(ow_carry_09));
wire ow_sum_10, ow_carry_10;
math_adder_full FA_10(.i_a(w_carry_37), .i_b(w_sum_38), .i_c(ow_carry_09), .ow_sum(ow_sum_10), .ow_carry(ow_carry_10));
wire ow_sum_11, ow_carry_11;
math_adder_full FA_11(.i_a(w_carry_38), .i_b(w_sum_39), .i_c(ow_carry_10), .ow_sum(ow_sum_11), .ow_carry(ow_carry_11));
wire ow_sum_12, ow_carry_12;
math_adder_full FA_12(.i_a(w_carry_39), .i_b(w_sum_40), .i_c(ow_carry_11), .ow_sum(ow_sum_12), .ow_carry(ow_carry_12));
wire ow_sum_13, ow_carry_13;
math_adder_full FA_13(.i_a(w_carry_40), .i_b(w_sum_41), .i_c(ow_carry_12), .ow_sum(ow_sum_13), .ow_carry(ow_carry_13));
wire ow_sum_14, ow_carry_14;
math_adder_full FA_14(.i_a(w_pp_7_7), .i_b(w_carry_41), .i_c(ow_carry_13), .ow_sum(ow_sum_14), .ow_carry(ow_carry_14));
wire ow_sum_15, ow_carry_15;
assign ow_sum_15 = ow_carry_14;
assign ow_carry_15 = 1'b0;

// Final product assignment
assign ow_product[ 0] = ow_sum_00;
assign ow_product[ 1] = ow_sum_01;
assign ow_product[ 2] = ow_sum_02;
assign ow_product[ 3] = ow_sum_03;
assign ow_product[ 4] = ow_sum_04;
assign ow_product[ 5] = ow_sum_05;
assign ow_product[ 6] = ow_sum_06;
assign ow_product[ 7] = ow_sum_07;
assign ow_product[ 8] = ow_sum_08;
assign ow_product[ 9] = ow_sum_09;
assign ow_product[10] = ow_sum_10;
assign ow_product[11] = ow_sum_11;
assign ow_product[12] = ow_sum_12;
assign ow_product[13] = ow_sum_13;
assign ow_product[14] = ow_sum_14;
assign ow_product[15] = ow_sum_15;


    // Debug purposes
    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, math_multiplier_dadda_tree_8);
    end
    // synopsys translate_off
        
endmodule : math_multiplier_dadda_tree_8
