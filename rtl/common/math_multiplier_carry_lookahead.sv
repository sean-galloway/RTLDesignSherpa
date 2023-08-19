`timescale 1ns / 1ps

module math_multiplier_carry_lookahead #(parameter N=4) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    output logic [2*N-1:0] ow_product
);

    // Generate partial products
    logic [N-1:0] w_partial_products[N-1:0];
    genvar i, j;
    generate
        for (i = 0; i < N; i++) begin : GEN_PARTIAL
            for (j = 0; j < N; j++) begin
                assign w_partial_products[i][j] = i_a[i] & i_b[j];
            end
        end
    endgenerate

    // In the carry lookahead logic, we need to compute propagate and generate signals
    logic w_generate[N-1:0];
    logic w_propagate[N-1:0];
    logic w_carry[N:0];

    assign w_carry[0] = 1'b0;
    for (i = 0; i < N; i++) begin
        assign w_generate[i] = i_a[i] & i_b[i];
        assign w_propagate[i] = i_a[i] ^ i_b[i];
    end

    // Compute carries using lookahead logic
    generate
        for (i = 0; i < N; i++) begin : GEN_CARRY_LOOKAHEAD
            assign w_carry[i+1] = w_generate[i] | (w_propagate[i] & w_carry[i]);
        end
    endgenerate

    // Compute the product bits
    logic [2*N-1:0] w_sum;
    generate
        for (i = 0; i < N; i++) begin : GEN_PRODUCT_BITS
            assign w_sum[i] = w_propagate[i] ^ w_carry[i];
        end
        for (i = N; i < 2*N; i++) begin : GEN_EXTENDED_PRODUCT_BITS
            assign w_sum[i] = w_carry[i-N+1];
        end
    endgenerate

    assign ow_product = w_sum;

endmodule : math_multiplier_carry_lookahead
