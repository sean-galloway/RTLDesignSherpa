`timescale 1ns / 1ps

module booths_multiplier #(parameter N=4) (
    input signed [N-1:0] a,
    input signed [N-1:0] b,
    output signed [2*N-1:0] product
);

    wire signed [2*N-1:0] partial_products [0:N-1][0:N-1];

    genvar i, j, k;
    generate
        for (i = 0; i < N; i = i + 1) begin : ROW_GEN
            for (j = 0; j < N; j = j + 1) begin : COL_GEN
                if (i >= j) begin
                    if (j == 0) begin
                        half_adder ha(.a(a[i]), .b(b[j]), .sum(partial_products[i][j]), .c_out(/*carry_out*/));
                    end
                    else begin
                        wire signed [2*N-1:0] fa_output;
                        assign partial_products[i][j] = fa_output[N-1:0];
                        assign partial_products[i][j-1] = fa_output[2*N-1:N];
                        for (k = 0; k < N-1; k = k + 1) begin : FA_CHAIN
                            full_adder fa(.a(partial_products[i][j-k-1]), .b(a[i]), .c_in(b[j-k-1]), .sum(fa_output[N+k]), .c_out(fa_output[N+k+1]));
                        end
                    end
                end
            end
        end
    endgenerate

    assign product = partial_products[0][N-1];
    generate
        for (i = 1; i < N; i = i + 1) begin : SUM_GEN
            assign product = product + partial_products[i][N-1-i];
        end
    endgenerate

endmodule : booths_multiplier
