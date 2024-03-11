`timescale 1ns / 1ps

// Carry Save Adder
module math_adder_carry_save (
    input  logic i_a,
    input  logic i_b,
    input  logic i_c,
    output logic ow_sum,
    output logic ow_carry
);

    assign ow_sum   = i_a ^ i_b ^ i_c;  // XOR gate for sum output
    assign ow_carry = i_a & i_b | i_a & i_c | i_b & i_c;  // OR gate for carry output

endmodule : math_adder_carry_save
