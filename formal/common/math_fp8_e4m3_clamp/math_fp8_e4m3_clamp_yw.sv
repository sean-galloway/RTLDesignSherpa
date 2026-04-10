// Yosys-compatible version of math_fp8_e4m3_clamp

`timescale 1ns / 1ps

module math_fp8_e4m3_clamp (
    input  logic [7:0] i_x,
    input  logic [7:0] i_min,
    input  logic [7:0] i_max,
    output logic [7:0] ow_result
);

wire [3:0] w_exp_x = i_x[6:3];
wire [2:0] w_mant_x = i_x[2:0];
wire [3:0] w_exp_min = i_min[6:3];
wire [2:0] w_mant_min = i_min[2:0];
wire [3:0] w_exp_max = i_max[6:3];
wire [2:0] w_mant_max = i_max[2:0];

// E4M3: NaN is only exp=F, mant=7
wire w_x_is_nan = (w_exp_x == 4'hF) & (w_mant_x == 3'h7);
wire w_min_is_nan = (w_exp_min == 4'hF) & (w_mant_min == 3'h7);
wire w_max_is_nan = (w_exp_max == 4'hF) & (w_mant_max == 3'h7);
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
