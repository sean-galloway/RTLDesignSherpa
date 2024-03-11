`timescale 1ns / 1ps

// Simple Full Adder implemented
module math_adder_full (
    input  logic i_a,
    input  logic i_b,
    input  logic i_c,
    output logic ow_sum,
    output logic ow_carry
);

    assign ow_sum   = i_a ^ i_b ^ i_c;  // XOR gate for sum output
    assign ow_carry = (i_a & i_b) | (i_c & (i_a ^ i_b));  // OR gate for carry output

endmodule : math_adder_full
