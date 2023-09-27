`timescale 1ns / 1ps

module math_adder_brent_kung_pg (
    input  logic i_a,
    input  logic i_b,
    output logic ow_g,
    output logic ow_p
);

    assign ow_g = i_a & i_b;
    assign ow_p = i_a ^ i_b;
endmodule
