`timescale 1ns / 1ps

module math_subtractor_carry_lookahead #(
    parameter int N = 4  // Width of input and output data
) (
    input  logic [N-1:0] i_a,            // Input a
    input  logic [N-1:0] i_b,            // Input b
    input  logic         i_borrow_in,    // Borrow in
    output logic [N-1:0] ow_difference,  // Output difference (a - b)
    output logic         ow_carry_out    // Borrow out (carry out) after subtraction
);

    logic [N-1:0] w_g, w_p, w_k;
    logic [N:0] w_lookahead_borrow;

    // Generate and Kill (Borrow) signals
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_borrow_kill
            assign w_g[i] = ~i_a[i] & i_b[i];  // Borrow generate
            assign w_p[i] = ~i_a[i] | i_b[i];  // Borrow propagate
            assign w_k[i] = i_a[i] & i_b[i];  // Kill signal
        end
    endgenerate

    // Borrow lookahead calculation
    assign w_lookahead_borrow[0] = i_borrow_in;  // Taking the external borrow-in into account
    generate
        for (i = 1; i <= N; i++) begin : gen_borrow_calc
            assign w_lookahead_borrow[i] = w_g[i-1] | (w_p[i-1] & w_lookahead_borrow[i-1]);
        end
    endgenerate

    // Difference calculation
    generate
        for (i = 0; i < N; i++) begin : gen_diff_calc
            assign ow_difference[i] = i_a[i] ^ i_b[i] ^ w_lookahead_borrow[i];
        end
    endgenerate

    // Final borrow out (carry out)
    assign ow_carry_out = w_lookahead_borrow[N];

endmodule : math_subtractor_carry_lookahead
