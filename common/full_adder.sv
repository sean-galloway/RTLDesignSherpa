`timescale 1ns / 1ps

// Simple Full Adder implemented
module full_adder(
    input  a,
    input  b,
    input  c_in,
    output sum,
    output c_out
    );

    assign sum = a ^ b ^ c_in;                  // XOR gate for sum output
    assign c_out = (a & b) | (c_in & (a ^ b));  // OR gate for carry output

endmodule : full_adder