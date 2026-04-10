// Yosys-compatible version of math_bf16_clamp
// Replaces function automatic with inline combinational logic
// (Yosys does not support function automatic with begin/end/return blocks)

`timescale 1ns / 1ps

module math_bf16_clamp (
    input  logic [15:0] i_x,
    input  logic [15:0] i_min,
    input  logic [15:0] i_max,
    output logic [15:0] ow_result
);

// Field extraction
wire w_sign_x = i_x[15];
wire [7:0] w_exp_x = i_x[14:7];
wire [6:0] w_mant_x = i_x[6:0];

wire w_sign_min = i_min[15];
wire [7:0] w_exp_min = i_min[14:7];
wire [6:0] w_mant_min = i_min[6:0];

wire w_sign_max = i_max[15];
wire [7:0] w_exp_max = i_max[14:7];
wire [6:0] w_mant_max = i_max[6:0];

// NaN detection
wire w_x_is_nan = (w_exp_x == 8'hFF) & (w_mant_x != 7'h0);
wire w_min_is_nan = (w_exp_min == 8'hFF) & (w_mant_min != 7'h0);
wire w_max_is_nan = (w_exp_max == 8'hFF) & (w_mant_max != 7'h0);
wire w_any_nan = w_x_is_nan | w_min_is_nan | w_max_is_nan;

// Inline fp_less_than(i_x, i_min)
wire w_x_lt_min = (i_x[15] != i_min[15]) ? i_x[15] :
                  (i_x[15] == 1'b0) ? (i_x[14:0] < i_min[14:0]) :
                                       (i_x[14:0] > i_min[14:0]);

// Inline fp_less_than(i_max, i_x)
wire w_x_gt_max = (i_max[15] != i_x[15]) ? i_max[15] :
                  (i_max[15] == 1'b0) ? (i_max[14:0] < i_x[14:0]) :
                                         (i_max[14:0] > i_x[14:0]);

// Result selection
assign ow_result = w_any_nan  ? i_x :
                   w_x_lt_min ? i_min :
                   w_x_gt_max ? i_max :
                   i_x;

endmodule
