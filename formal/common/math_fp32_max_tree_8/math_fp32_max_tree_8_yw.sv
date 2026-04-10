// Yosys-compatible version of math_fp32_max_tree_8
// Flattens unpacked array port and inlines function automatic

`timescale 1ns / 1ps

module math_fp32_max_tree_8 (
    input  logic [31:0] i_data_0, i_data_1, i_data_2, i_data_3,
    input  logic [31:0] i_data_4, i_data_5, i_data_6, i_data_7,
    output logic [31:0] ow_max,
    output logic [7:0] ow_max_idx
);

// Level 0: 8 -> 4
wire w_l0_0_a_nan = (i_data_0[30:23] == 8'hFF) & (i_data_0[22:0] != 23'h0);
wire w_l0_0_b_nan = (i_data_1[30:23] == 8'hFF) & (i_data_1[22:0] != 23'h0);
wire w_l0_0_a_sel = w_l0_0_a_nan ? 1'b0 : w_l0_0_b_nan ? 1'b1 :
    (i_data_0[31] != i_data_1[31]) ? ~i_data_0[31] :
    (i_data_0[31] == 1'b0) ? (i_data_0[30:0] >= i_data_1[30:0]) :
    (i_data_0[30:0] <= i_data_1[30:0]);
wire [31:0] w_l0_0_result = w_l0_0_a_sel ? i_data_0 : i_data_1;

wire w_l0_1_a_nan = (i_data_2[30:23] == 8'hFF) & (i_data_2[22:0] != 23'h0);
wire w_l0_1_b_nan = (i_data_3[30:23] == 8'hFF) & (i_data_3[22:0] != 23'h0);
wire w_l0_1_a_sel = w_l0_1_a_nan ? 1'b0 : w_l0_1_b_nan ? 1'b1 :
    (i_data_2[31] != i_data_3[31]) ? ~i_data_2[31] :
    (i_data_2[31] == 1'b0) ? (i_data_2[30:0] >= i_data_3[30:0]) :
    (i_data_2[30:0] <= i_data_3[30:0]);
wire [31:0] w_l0_1_result = w_l0_1_a_sel ? i_data_2 : i_data_3;

wire w_l0_2_a_nan = (i_data_4[30:23] == 8'hFF) & (i_data_4[22:0] != 23'h0);
wire w_l0_2_b_nan = (i_data_5[30:23] == 8'hFF) & (i_data_5[22:0] != 23'h0);
wire w_l0_2_a_sel = w_l0_2_a_nan ? 1'b0 : w_l0_2_b_nan ? 1'b1 :
    (i_data_4[31] != i_data_5[31]) ? ~i_data_4[31] :
    (i_data_4[31] == 1'b0) ? (i_data_4[30:0] >= i_data_5[30:0]) :
    (i_data_4[30:0] <= i_data_5[30:0]);
wire [31:0] w_l0_2_result = w_l0_2_a_sel ? i_data_4 : i_data_5;

wire w_l0_3_a_nan = (i_data_6[30:23] == 8'hFF) & (i_data_6[22:0] != 23'h0);
wire w_l0_3_b_nan = (i_data_7[30:23] == 8'hFF) & (i_data_7[22:0] != 23'h0);
wire w_l0_3_a_sel = w_l0_3_a_nan ? 1'b0 : w_l0_3_b_nan ? 1'b1 :
    (i_data_6[31] != i_data_7[31]) ? ~i_data_6[31] :
    (i_data_6[31] == 1'b0) ? (i_data_6[30:0] >= i_data_7[30:0]) :
    (i_data_6[30:0] <= i_data_7[30:0]);
wire [31:0] w_l0_3_result = w_l0_3_a_sel ? i_data_6 : i_data_7;

// Level 1: 4 -> 2
wire w_l1_0_a_nan = (w_l0_0_result[30:23] == 8'hFF) & (w_l0_0_result[22:0] != 23'h0);
wire w_l1_0_b_nan = (w_l0_1_result[30:23] == 8'hFF) & (w_l0_1_result[22:0] != 23'h0);
wire w_l1_0_a_sel = w_l1_0_a_nan ? 1'b0 : w_l1_0_b_nan ? 1'b1 :
    (w_l0_0_result[31] != w_l0_1_result[31]) ? ~w_l0_0_result[31] :
    (w_l0_0_result[31] == 1'b0) ? (w_l0_0_result[30:0] >= w_l0_1_result[30:0]) :
    (w_l0_0_result[30:0] <= w_l0_1_result[30:0]);
wire [31:0] w_l1_0_result = w_l1_0_a_sel ? w_l0_0_result : w_l0_1_result;

wire w_l1_1_a_nan = (w_l0_2_result[30:23] == 8'hFF) & (w_l0_2_result[22:0] != 23'h0);
wire w_l1_1_b_nan = (w_l0_3_result[30:23] == 8'hFF) & (w_l0_3_result[22:0] != 23'h0);
wire w_l1_1_a_sel = w_l1_1_a_nan ? 1'b0 : w_l1_1_b_nan ? 1'b1 :
    (w_l0_2_result[31] != w_l0_3_result[31]) ? ~w_l0_2_result[31] :
    (w_l0_2_result[31] == 1'b0) ? (w_l0_2_result[30:0] >= w_l0_3_result[30:0]) :
    (w_l0_2_result[30:0] <= w_l0_3_result[30:0]);
wire [31:0] w_l1_1_result = w_l1_1_a_sel ? w_l0_2_result : w_l0_3_result;

// Level 2: 2 -> 1
wire w_l2_0_a_nan = (w_l1_0_result[30:23] == 8'hFF) & (w_l1_0_result[22:0] != 23'h0);
wire w_l2_0_b_nan = (w_l1_1_result[30:23] == 8'hFF) & (w_l1_1_result[22:0] != 23'h0);
wire w_l2_0_a_sel = w_l2_0_a_nan ? 1'b0 : w_l2_0_b_nan ? 1'b1 :
    (w_l1_0_result[31] != w_l1_1_result[31]) ? ~w_l1_0_result[31] :
    (w_l1_0_result[31] == 1'b0) ? (w_l1_0_result[30:0] >= w_l1_1_result[30:0]) :
    (w_l1_0_result[30:0] <= w_l1_1_result[30:0]);
wire [31:0] w_l2_0_result = w_l2_0_a_sel ? w_l1_0_result : w_l1_1_result;

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
