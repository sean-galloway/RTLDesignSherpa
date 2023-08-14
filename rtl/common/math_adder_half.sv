`timescale 1ns / 1ps

module math_adder_half (input i_a, i_b, output ow_sum, ow_c);

    assign ow_sum = i_a ^ i_b;
    assign ow_c   = i_a & i_b;

endmodule : math_adder_half