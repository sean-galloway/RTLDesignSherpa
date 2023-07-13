`timescale 1ns / 1ps

module half_adder(input a, b, output sum, c_out);

    assign sum = a ^ b;
    assign c_out = a & b;

endmodule : half_adder