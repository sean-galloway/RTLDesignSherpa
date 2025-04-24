`timescale 1ns / 1ps

module math_multiplier_basic_cell
(
    input  logic i_i,
    input  logic i_j,
    input  logic i_c,
    input  logic i_p,
    /* verilator lint_off UNOPTFLAT */
    output logic ow_c,
    output logic ow_p
    /* verilator lint_on UNOPTFLAT */
);

    logic w_p;
    logic w_sum, w_carry;

    assign w_p     = i_i & i_j;
    assign w_sum   = i_c ^ i_p ^ w_p;
    assign w_carry = (i_c & i_p) | (i_c & w_p) | (i_p & w_p);

    // Explicit output buffering to break any feedback path through ports
    always_comb begin
        ow_p = w_sum;
        ow_c = w_carry;
    end

endmodule : math_multiplier_basic_cell
