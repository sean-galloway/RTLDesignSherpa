// Yosys-compatible version of math_fp8_e5m2_min_tree_8
// Flattens unpacked array port and inlines function automatic

`timescale 1ns / 1ps

module math_fp8_e5m2_min_tree_8 (
    input  logic [7:0] i_data_0, i_data_1, i_data_2, i_data_3,
    input  logic [7:0] i_data_4, i_data_5, i_data_6, i_data_7,
    output logic [7:0] ow_min,
    output logic [7:0] ow_min_idx
);

// Level 0: 8 -> 4
wire w_l0_0_a_nan = (i_data_0[6:2] == 5'h1F) & (i_data_0[1:0] != 2'h0);
wire w_l0_0_b_nan = (i_data_1[6:2] == 5'h1F) & (i_data_1[1:0] != 2'h0);
wire w_l0_0_a_sel = w_l0_0_a_nan ? 1'b0 : w_l0_0_b_nan ? 1'b1 :
    (i_data_0[7] != i_data_1[7]) ? i_data_0[7] :
    (i_data_0[7] == 1'b0) ? (i_data_0[6:0] <= i_data_1[6:0]) :
    (i_data_0[6:0] >= i_data_1[6:0]);
wire [7:0] w_l0_0_result = w_l0_0_a_sel ? i_data_0 : i_data_1;

wire w_l0_1_a_nan = (i_data_2[6:2] == 5'h1F) & (i_data_2[1:0] != 2'h0);
wire w_l0_1_b_nan = (i_data_3[6:2] == 5'h1F) & (i_data_3[1:0] != 2'h0);
wire w_l0_1_a_sel = w_l0_1_a_nan ? 1'b0 : w_l0_1_b_nan ? 1'b1 :
    (i_data_2[7] != i_data_3[7]) ? i_data_2[7] :
    (i_data_2[7] == 1'b0) ? (i_data_2[6:0] <= i_data_3[6:0]) :
    (i_data_2[6:0] >= i_data_3[6:0]);
wire [7:0] w_l0_1_result = w_l0_1_a_sel ? i_data_2 : i_data_3;

wire w_l0_2_a_nan = (i_data_4[6:2] == 5'h1F) & (i_data_4[1:0] != 2'h0);
wire w_l0_2_b_nan = (i_data_5[6:2] == 5'h1F) & (i_data_5[1:0] != 2'h0);
wire w_l0_2_a_sel = w_l0_2_a_nan ? 1'b0 : w_l0_2_b_nan ? 1'b1 :
    (i_data_4[7] != i_data_5[7]) ? i_data_4[7] :
    (i_data_4[7] == 1'b0) ? (i_data_4[6:0] <= i_data_5[6:0]) :
    (i_data_4[6:0] >= i_data_5[6:0]);
wire [7:0] w_l0_2_result = w_l0_2_a_sel ? i_data_4 : i_data_5;

wire w_l0_3_a_nan = (i_data_6[6:2] == 5'h1F) & (i_data_6[1:0] != 2'h0);
wire w_l0_3_b_nan = (i_data_7[6:2] == 5'h1F) & (i_data_7[1:0] != 2'h0);
wire w_l0_3_a_sel = w_l0_3_a_nan ? 1'b0 : w_l0_3_b_nan ? 1'b1 :
    (i_data_6[7] != i_data_7[7]) ? i_data_6[7] :
    (i_data_6[7] == 1'b0) ? (i_data_6[6:0] <= i_data_7[6:0]) :
    (i_data_6[6:0] >= i_data_7[6:0]);
wire [7:0] w_l0_3_result = w_l0_3_a_sel ? i_data_6 : i_data_7;

// Level 1: 4 -> 2
wire w_l1_0_a_nan = (w_l0_0_result[6:2] == 5'h1F) & (w_l0_0_result[1:0] != 2'h0);
wire w_l1_0_b_nan = (w_l0_1_result[6:2] == 5'h1F) & (w_l0_1_result[1:0] != 2'h0);
wire w_l1_0_a_sel = w_l1_0_a_nan ? 1'b0 : w_l1_0_b_nan ? 1'b1 :
    (w_l0_0_result[7] != w_l0_1_result[7]) ? w_l0_0_result[7] :
    (w_l0_0_result[7] == 1'b0) ? (w_l0_0_result[6:0] <= w_l0_1_result[6:0]) :
    (w_l0_0_result[6:0] >= w_l0_1_result[6:0]);
wire [7:0] w_l1_0_result = w_l1_0_a_sel ? w_l0_0_result : w_l0_1_result;

wire w_l1_1_a_nan = (w_l0_2_result[6:2] == 5'h1F) & (w_l0_2_result[1:0] != 2'h0);
wire w_l1_1_b_nan = (w_l0_3_result[6:2] == 5'h1F) & (w_l0_3_result[1:0] != 2'h0);
wire w_l1_1_a_sel = w_l1_1_a_nan ? 1'b0 : w_l1_1_b_nan ? 1'b1 :
    (w_l0_2_result[7] != w_l0_3_result[7]) ? w_l0_2_result[7] :
    (w_l0_2_result[7] == 1'b0) ? (w_l0_2_result[6:0] <= w_l0_3_result[6:0]) :
    (w_l0_2_result[6:0] >= w_l0_3_result[6:0]);
wire [7:0] w_l1_1_result = w_l1_1_a_sel ? w_l0_2_result : w_l0_3_result;

// Level 2: 2 -> 1
wire w_l2_0_a_nan = (w_l1_0_result[6:2] == 5'h1F) & (w_l1_0_result[1:0] != 2'h0);
wire w_l2_0_b_nan = (w_l1_1_result[6:2] == 5'h1F) & (w_l1_1_result[1:0] != 2'h0);
wire w_l2_0_a_sel = w_l2_0_a_nan ? 1'b0 : w_l2_0_b_nan ? 1'b1 :
    (w_l1_0_result[7] != w_l1_1_result[7]) ? w_l1_0_result[7] :
    (w_l1_0_result[7] == 1'b0) ? (w_l1_0_result[6:0] <= w_l1_1_result[6:0]) :
    (w_l1_0_result[6:0] >= w_l1_1_result[6:0]);
wire [7:0] w_l2_0_result = w_l2_0_a_sel ? w_l1_0_result : w_l1_1_result;

assign ow_min = w_l2_0_result;

// One-hot index
assign ow_min_idx[0] = (i_data_0 == ow_min);
assign ow_min_idx[1] = (i_data_1 == ow_min);
assign ow_min_idx[2] = (i_data_2 == ow_min);
assign ow_min_idx[3] = (i_data_3 == ow_min);
assign ow_min_idx[4] = (i_data_4 == ow_min);
assign ow_min_idx[5] = (i_data_5 == ow_min);
assign ow_min_idx[6] = (i_data_6 == ow_min);
assign ow_min_idx[7] = (i_data_7 == ow_min);

endmodule
