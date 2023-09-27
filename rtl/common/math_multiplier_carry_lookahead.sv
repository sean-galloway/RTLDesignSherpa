`timescale 1ns / 1ps

module math_multiplier_carry_lookahead #(
    parameter int N = 4
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);

    // Generate partial products
    logic [N-1:0] w_partial_products[N-1];
    genvar i, j;
    generate
        for (i = 0; i < N; i++) begin : gen_partial_outer
            for (j = 0; j < N; j++) begin : gen_partial
                assign w_partial_products[i][j] = i_multiplier[i] & i_multiplicand[j];
            end
        end
    endgenerate

    // In the carry lookahead logic, we need to compute propagate and generate signals
    logic w_generate [N-1];
    logic w_propagate[N-1];
    logic w_carry    [  N];

    assign w_carry[0] = 1'b0;
    for (i = 0; i < N; i++) begin : gen_g_p
        assign w_generate[i]  = i_multiplier[i] & i_multiplicand[i];
        assign w_propagate[i] = i_multiplier[i] ^ i_multiplicand[i];
    end

    // Compute carries using lookahead logic
    generate
        for (i = 0; i < N; i++) begin : gen_carry_lookahead
            assign w_carry[i+1] = w_generate[i] | (w_propagate[i] & w_carry[i]);
        end
    endgenerate

    // Compute the product bits
    logic [2*N-1:0] w_sum;
    generate
        for (i = 0; i < N; i++) begin : gen_products
            assign w_sum[i] = w_propagate[i] ^ w_carry[i];
        end
        for (i = N; i < 2 * N; i++) begin : gen_extended_products
            assign w_sum[i] = w_carry[i-N+1];
        end
    endgenerate

    assign ow_product = w_sum;

endmodule : math_multiplier_carry_lookahead
