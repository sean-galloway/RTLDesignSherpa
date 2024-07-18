`timescale 1ns / 1ps

module math_adder_half #(parameter int N=1)(
    input  logic i_a,
    input  logic i_b,
    output logic ow_sum,
    output logic ow_carry
);

    assign ow_sum   = i_a ^ i_b;
    assign ow_carry = i_a & i_b;

endmodule : math_adder_half
