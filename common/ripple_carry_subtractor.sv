`timescale 1ns / 1ps

module ripple_carry_subtractor #(parameter SIZE = 4) (
    input [SIZE-1:0]  a, b,
    input             b_in,
    output [SIZE-1:0] d, b_out);


    full_subtractor fs0(.a(a[0]), .b(b[0]), .b_in(b_in), .d(d[0]), .b_out(b_out[0]));

    genvar i;
    generate
        for(i = 1; i<SIZE; i++) begin
            full_subtractor fs(.a(a[i]), .b(b[i]), .b_in(b_out[i-1]), .d(d[i]), .b_out(b_out[i]));
        end
    endgenerate

endmodule : ripple_carry_subtractor