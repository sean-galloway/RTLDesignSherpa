`timescale 1ns / 1ps

// Simple Full Adder implemented
module math_adder_full (
    input  i_a,
    input  i_b,
    input  i_c,
    output ow_sum,
    output ow_carry
);

    assign ow_sum   = i_a ^ i_b ^ i_c;  // XOR gate for sum output
    assign ow_carry = (i_a & i_b) | (i_c & (i_a ^ i_b));  // OR gate for carry output

endmodule : math_adder_full
