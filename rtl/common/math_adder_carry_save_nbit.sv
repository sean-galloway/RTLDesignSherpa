`timescale 1ns / 1ps

module math_adder_carry_save_nbit #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic [N-1:0] i_c,      // Carry from a previous operation
    output logic [N-1:0] ow_sum,
    output logic [N-1:0] ow_carry  // Saved carries
);

    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_carry_save
            // Sum
            assign ow_sum[i]   = i_a[i] ^ i_b[i] ^ i_c[i];

            // Carry out is the majority function
            assign ow_carry[i] = (i_a[i] & i_b[i]) | (i_a[i] & i_c[i]) | (i_b[i] & i_c[i]);
        end
    endgenerate

endmodule : math_adder_carry_save_nbit
