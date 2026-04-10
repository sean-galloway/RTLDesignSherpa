// Yosys-compatible version of math_fp16_max_tree_8
// Flattens unpacked array port and inlines function automatic

`timescale 1ns / 1ps

module math_fp16_max_tree_8 (
    input  logic [15:0] i_data_0, i_data_1, i_data_2, i_data_3,
    input  logic [15:0] i_data_4, i_data_5, i_data_6, i_data_7,
    output logic [15:0] ow_max,
    output logic [7:0] ow_max_idx
);

// Level 0: 8 -> 4
wire w_l0_0_a_nan = (i_data_0[14:10] == 5'h1F) & (i_data_0[9:0] != 10'h0);
wire w_l0_0_b_nan = (i_data_1[14:10] == 5'h1F) & (i_data_1[9:0] != 10'h0);
wire w_l0_0_a_sel = w_l0_0_a_nan ? 1'b0 : w_l0_0_b_nan ? 1'b1 :
    (i_data_0[15] != i_data_1[15]) ? ~i_data_0[15] :
    (i_data_0[15] == 1'b0) ? (i_data_0[14:0] >= i_data_1[14:0]) :
    (i_data_0[14:0] <= i_data_1[14:0]);
wire [15:0] w_l0_0_result = w_l0_0_a_sel ? i_data_0 : i_data_1;

wire w_l0_1_a_nan = (i_data_2[14:10] == 5'h1F) & (i_data_2[9:0] != 10'h0);
wire w_l0_1_b_nan = (i_data_3[14:10] == 5'h1F) & (i_data_3[9:0] != 10'h0);
wire w_l0_1_a_sel = w_l0_1_a_nan ? 1'b0 : w_l0_1_b_nan ? 1'b1 :
    (i_data_2[15] != i_data_3[15]) ? ~i_data_2[15] :
    (i_data_2[15] == 1'b0) ? (i_data_2[14:0] >= i_data_3[14:0]) :
    (i_data_2[14:0] <= i_data_3[14:0]);
wire [15:0] w_l0_1_result = w_l0_1_a_sel ? i_data_2 : i_data_3;

wire w_l0_2_a_nan = (i_data_4[14:10] == 5'h1F) & (i_data_4[9:0] != 10'h0);
wire w_l0_2_b_nan = (i_data_5[14:10] == 5'h1F) & (i_data_5[9:0] != 10'h0);
wire w_l0_2_a_sel = w_l0_2_a_nan ? 1'b0 : w_l0_2_b_nan ? 1'b1 :
    (i_data_4[15] != i_data_5[15]) ? ~i_data_4[15] :
    (i_data_4[15] == 1'b0) ? (i_data_4[14:0] >= i_data_5[14:0]) :
    (i_data_4[14:0] <= i_data_5[14:0]);
wire [15:0] w_l0_2_result = w_l0_2_a_sel ? i_data_4 : i_data_5;

wire w_l0_3_a_nan = (i_data_6[14:10] == 5'h1F) & (i_data_6[9:0] != 10'h0);
wire w_l0_3_b_nan = (i_data_7[14:10] == 5'h1F) & (i_data_7[9:0] != 10'h0);
wire w_l0_3_a_sel = w_l0_3_a_nan ? 1'b0 : w_l0_3_b_nan ? 1'b1 :
    (i_data_6[15] != i_data_7[15]) ? ~i_data_6[15] :
    (i_data_6[15] == 1'b0) ? (i_data_6[14:0] >= i_data_7[14:0]) :
    (i_data_6[14:0] <= i_data_7[14:0]);
wire [15:0] w_l0_3_result = w_l0_3_a_sel ? i_data_6 : i_data_7;

// Level 1: 4 -> 2
wire w_l1_0_a_nan = (w_l0_0_result[14:10] == 5'h1F) & (w_l0_0_result[9:0] != 10'h0);
wire w_l1_0_b_nan = (w_l0_1_result[14:10] == 5'h1F) & (w_l0_1_result[9:0] != 10'h0);
wire w_l1_0_a_sel = w_l1_0_a_nan ? 1'b0 : w_l1_0_b_nan ? 1'b1 :
    (w_l0_0_result[15] != w_l0_1_result[15]) ? ~w_l0_0_result[15] :
    (w_l0_0_result[15] == 1'b0) ? (w_l0_0_result[14:0] >= w_l0_1_result[14:0]) :
    (w_l0_0_result[14:0] <= w_l0_1_result[14:0]);
wire [15:0] w_l1_0_result = w_l1_0_a_sel ? w_l0_0_result : w_l0_1_result;

wire w_l1_1_a_nan = (w_l0_2_result[14:10] == 5'h1F) & (w_l0_2_result[9:0] != 10'h0);
wire w_l1_1_b_nan = (w_l0_3_result[14:10] == 5'h1F) & (w_l0_3_result[9:0] != 10'h0);
wire w_l1_1_a_sel = w_l1_1_a_nan ? 1'b0 : w_l1_1_b_nan ? 1'b1 :
    (w_l0_2_result[15] != w_l0_3_result[15]) ? ~w_l0_2_result[15] :
    (w_l0_2_result[15] == 1'b0) ? (w_l0_2_result[14:0] >= w_l0_3_result[14:0]) :
    (w_l0_2_result[14:0] <= w_l0_3_result[14:0]);
wire [15:0] w_l1_1_result = w_l1_1_a_sel ? w_l0_2_result : w_l0_3_result;

// Level 2: 2 -> 1
wire w_l2_0_a_nan = (w_l1_0_result[14:10] == 5'h1F) & (w_l1_0_result[9:0] != 10'h0);
wire w_l2_0_b_nan = (w_l1_1_result[14:10] == 5'h1F) & (w_l1_1_result[9:0] != 10'h0);
wire w_l2_0_a_sel = w_l2_0_a_nan ? 1'b0 : w_l2_0_b_nan ? 1'b1 :
    (w_l1_0_result[15] != w_l1_1_result[15]) ? ~w_l1_0_result[15] :
    (w_l1_0_result[15] == 1'b0) ? (w_l1_0_result[14:0] >= w_l1_1_result[14:0]) :
    (w_l1_0_result[14:0] <= w_l1_1_result[14:0]);
wire [15:0] w_l2_0_result = w_l2_0_a_sel ? w_l1_0_result : w_l1_1_result;

assign ow_max = w_l2_0_result;

// One-hot index
assign ow_max_idx[0] = (i_data_0 == ow_max);
assign ow_max_idx[1] = (i_data_1 == ow_max);
assign ow_max_idx[2] = (i_data_2 == ow_max);
assign ow_max_idx[3] = (i_data_3 == ow_max);
assign ow_max_idx[4] = (i_data_4 == ow_max);
assign ow_max_idx[5] = (i_data_5 == ow_max);
assign ow_max_idx[6] = (i_data_6 == ow_max);
assign ow_max_idx[7] = (i_data_7 == ow_max);

endmodule
