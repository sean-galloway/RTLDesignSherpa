`timescale 1ns / 1ps

module math_adder_half (
    input  i_a,
    i_b,
    output ow_sum,
    ow_carry
);

    assign ow_sum   = i_a ^ i_b;
    assign ow_carry = i_a & i_b;

endmodule : math_adder_half
