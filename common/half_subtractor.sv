`timescale 1ns / 1ps

module half_subtractor(input a, b, output d, b_out);
    assign d = a ^ b;
    assign b_out = ~a & b;
endmodule