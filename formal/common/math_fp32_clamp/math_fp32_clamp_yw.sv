// Yosys-compatible version of math_fp32_clamp

`timescale 1ns / 1ps

module math_fp32_clamp (
    input  logic [31:0] i_x,
    input  logic [31:0] i_min,
    input  logic [31:0] i_max,
    output logic [31:0] ow_result
);

wire [7:0]  w_exp_x = i_x[30:23];
wire [22:0] w_mant_x = i_x[22:0];
wire [7:0]  w_exp_min = i_min[30:23];
wire [22:0] w_mant_min = i_min[22:0];
wire [7:0]  w_exp_max = i_max[30:23];
wire [22:0] w_mant_max = i_max[22:0];

wire w_x_is_nan = (w_exp_x == 8'hFF) & (w_mant_x != 23'h0);
wire w_min_is_nan = (w_exp_min == 8'hFF) & (w_mant_min != 23'h0);
wire w_max_is_nan = (w_exp_max == 8'hFF) & (w_mant_max != 23'h0);
wire w_any_nan = w_x_is_nan | w_min_is_nan | w_max_is_nan;

wire w_x_lt_min = (i_x[31] != i_min[31]) ? i_x[31] :
                  (i_x[31] == 1'b0) ? (i_x[30:0] < i_min[30:0]) :
                                       (i_x[30:0] > i_min[30:0]);

wire w_x_gt_max = (i_max[31] != i_x[31]) ? i_max[31] :
                  (i_max[31] == 1'b0) ? (i_max[30:0] < i_x[30:0]) :
                                         (i_max[30:0] > i_x[30:0]);

assign ow_result = w_any_nan  ? i_x :
                   w_x_lt_min ? i_min :
                   w_x_gt_max ? i_max :
                   i_x;

endmodule
