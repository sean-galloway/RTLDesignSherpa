`timescale 1ns / 1ps

module math_adder_brent_kung_gray (
    input  logic i_g,
    input  logic i_p,
    input  logic i_g_km1,
    output logic ow_g
);

    assign ow_g = i_g | (i_p & i_g_km1);
endmodule
