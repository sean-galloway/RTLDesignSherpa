// Yosys-compatible version of math_fp16_clamp
// Replaces function automatic with inline combinational logic

`timescale 1ns / 1ps

module math_fp16_clamp (
    input  logic [15:0] i_x,
    input  logic [15:0] i_min,
    input  logic [15:0] i_max,
    output logic [15:0] ow_result
);

wire [4:0] w_exp_x = i_x[14:10];
wire [9:0] w_mant_x = i_x[9:0];
wire [4:0] w_exp_min = i_min[14:10];
wire [9:0] w_mant_min = i_min[9:0];
wire [4:0] w_exp_max = i_max[14:10];
wire [9:0] w_mant_max = i_max[9:0];

wire w_x_is_nan = (w_exp_x == 5'h1F) & (w_mant_x != 10'h0);
wire w_min_is_nan = (w_exp_min == 5'h1F) & (w_mant_min != 10'h0);
wire w_max_is_nan = (w_exp_max == 5'h1F) & (w_mant_max != 10'h0);
wire w_any_nan = w_x_is_nan | w_min_is_nan | w_max_is_nan;

wire w_x_lt_min = (i_x[15] != i_min[15]) ? i_x[15] :
                  (i_x[15] == 1'b0) ? (i_x[14:0] < i_min[14:0]) :
                                       (i_x[14:0] > i_min[14:0]);

wire w_x_gt_max = (i_max[15] != i_x[15]) ? i_max[15] :
                  (i_max[15] == 1'b0) ? (i_max[14:0] < i_x[14:0]) :
                                         (i_max[14:0] > i_x[14:0]);

assign ow_result = w_any_nan  ? i_x :
                   w_x_lt_min ? i_min :
                   w_x_gt_max ? i_max :
                   i_x;

endmodule
