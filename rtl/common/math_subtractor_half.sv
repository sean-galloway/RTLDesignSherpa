`timescale 1ns / 1ps

module math_subtractor_half (
    input  i_a,
    i_b,
    output o_d,
    o_b
);

    assign o_d = i_a ^ i_b;
    assign o_b = ~i_a & i_b;

endmodule : math_subtractor_half
