// Yosys-compatible version of math_fp8_e5m2_clamp

`timescale 1ns / 1ps

module math_fp8_e5m2_clamp (
    input  logic [7:0] i_x,
    input  logic [7:0] i_min,
    input  logic [7:0] i_max,
    output logic [7:0] ow_result
);

wire [4:0] w_exp_x = i_x[6:2];
wire [1:0] w_mant_x = i_x[1:0];
wire [4:0] w_exp_min = i_min[6:2];
wire [1:0] w_mant_min = i_min[1:0];
wire [4:0] w_exp_max = i_max[6:2];
wire [1:0] w_mant_max = i_max[1:0];

wire w_x_is_nan = (w_exp_x == 5'h1F) & (w_mant_x != 2'h0);
wire w_min_is_nan = (w_exp_min == 5'h1F) & (w_mant_min != 2'h0);
wire w_max_is_nan = (w_exp_max == 5'h1F) & (w_mant_max != 2'h0);
wire w_any_nan = w_x_is_nan | w_min_is_nan | w_max_is_nan;

wire w_x_lt_min = (i_x[7] != i_min[7]) ? i_x[7] :
                  (i_x[7] == 1'b0) ? (i_x[6:0] < i_min[6:0]) :
                                      (i_x[6:0] > i_min[6:0]);

wire w_x_gt_max = (i_max[7] != i_x[7]) ? i_max[7] :
                  (i_max[7] == 1'b0) ? (i_max[6:0] < i_x[6:0]) :
                                        (i_max[6:0] > i_x[6:0]);

assign ow_result = w_any_nan  ? i_x :
                   w_x_lt_min ? i_min :
                   w_x_gt_max ? i_max :
                   i_x;

endmodule
