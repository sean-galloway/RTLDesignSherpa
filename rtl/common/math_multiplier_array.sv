`timescale 1ns / 1ps

module math_multiplier_array #(
    parameter int N = 4
) (
    input  logic [  N-1:0] i_multiplier,
    input  logic [  N-1:0] i_multiplicand,
    output logic [2*N-1:0] ow_product
);

    wire [N*(N-1)-1:0] w_sum;
    wire [N-1:0] w_and, w_o_c;

    assign w_and[N-1:0] = i_multiplier & {N{i_multiplicand[0]}};

    // First full adder
    math_adder_full_nbit #(
        .N(N)
    ) fa_first (
        .i_a(w_and[N-1:0] >> 1),
        .i_b(i_multiplier & {N{i_multiplicand[1]}}),
        .i_c(1'b0),
        .ow_sum(w_sum[N-1:0]),
        .ow_carry(w_o_c[0])
    );

    assign ow_product[1:0] = {w_sum[0], w_and[0]};

    // Iterative full adders
    genvar i;
    generate
        for (i = 2; i < N - 1; i++) begin : gen_full_adder
            math_adder_full_nbit #(
                .N(N)
            ) fa_i (
                .i_a({w_o_c[i-2], {(N - 1) {1'b0}}} | w_sum[N*(i-1)-1:N*(i-2)] >> 1),
                .i_b(i_multiplier & {N{i_multiplicand[i]}}),
                .i_c(1'b0),
                .ow_sum(w_sum[N*i-1:N*(i-1)]),
                .ow_carry(w_o_c[i-1])
            );

            assign ow_product[i] = w_sum[N*(i-1)];
        end
    endgenerate

    // Last full adder
    math_adder_full_nbit #(
        .N(N)
    ) fa_last (
        .i_a({w_o_c[N-3], {(N - 1) {1'b0}}} | w_sum[N*(N-2)-1:N*(N-3)] >> 1),
        .i_b(i_multiplier & {N{i_multiplicand[N-1]}}),
        .i_c(1'b0),
        .ow_sum(w_sum[N*(N-1)-1:N*(N-2)]),
        .ow_carry(w_o_c[N-2])
    );

    assign ow_product[N*2-1:N*2-N-1] = {w_o_c[N-2], w_sum[N*(N-1)-1:N*(N-2)]};

endmodule

