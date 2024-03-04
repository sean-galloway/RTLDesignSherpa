`timescale 1ns / 1ps

// Parameterized CLA
module math_adder_carry_lookahead #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
);

    wire [N-1:0] w_p, w_g;
    wire [N:0] w_c;

    // Generate and propagate signals
    generate
        genvar i;
        for (i = 0; i < N; i++) begin : gen_g_p
            assign w_g[i] = i_a[i] & i_b[i];
            assign w_p[i] = i_a[i] | i_b[i];
        end
    endgenerate

    // Calculate carry bits
    assign w_c[0] = i_c;
    generate
        for (i = 1; i <= N; i++) begin : gen_carry
            assign w_c[i] = w_g[i-1] | (w_p[i-1] & w_c[i-1]);
        end
    endgenerate

    // Calculate sum bits
    generate
        for (i = 0; i < N; i++) begin : gen_sum
            assign ow_sum[i] = i_a[i] ^ i_b[i] ^ w_c[i];
        end
    endgenerate

    // assign carry-out
    assign ow_carry = w_c[N];

endmodule : math_adder_carry_lookahead
