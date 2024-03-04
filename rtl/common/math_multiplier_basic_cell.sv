`timescale 1ns / 1ps

module math_multiplier_basic_cell
(
    input  logic i_i,
    input  logic i_j,
    input  logic i_c,
    input  logic i_p,
    output logic ow_c,
    output logic ow_p
);

    logic w_p;

    assign w_p  = i_i & i_j;
    assign ow_c = (i_c & i_p) | (i_c & w_p) | (i_p & w_p);
    assign ow_p = i_c ^ w_p ^ i_p;

endmodule : math_multiplier_basic_cell
