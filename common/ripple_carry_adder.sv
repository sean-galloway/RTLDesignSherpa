`timescale 1ns / 1ps

module ripple_carry_adder #(parameter WIDTH = 4) (
    input [WIDTH-1:0]  a, b,
    input             c_in,
    output [WIDTH-1:0] sum, c_out);


    full_adder fa0(.a(a[0]), .b(b[0]), .c_in(c_in), .sum(sum[0]), .c_out(c_out[0]));

    genvar i;
    generate
        for(i = 1; i<WIDTH; i++) begin
            full_adder fa(.a(a[i]), .b(b[i]), .c_in(c_out[i-1]), .sum(sum[i]), .c_out(c_out[i]));
        end
    endgenerate

endmodule : ripple_carry_adder