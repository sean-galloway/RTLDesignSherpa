`timescale 1ns / 1ps

// Simple Array Multiplier
module array_multipler #(parameter N=4) (
    input [N-1:0] a,
    input [N-1:0] b,
    output [2*N-1:0] product
);

    wire [N-1:0] partial_products [0:N-1][0:N-1];

    genvar i, j;
    generate
        for (i = 0; i < N; i = i + 1) begin : ROW_GEN
            for (j = 0; j < N; j = j + 1) begin : COL_GEN
                if (i >= j) begin
                    if (j == 0) begin
                        half_adder HA(.a(a[i]), .b(b[j]), .sum(partial_products[i][j]), .c_out()/*carry*/);
                    end
                    else begin
                        full_adder FA(.a(a[i]), .b(b[j]), .c_in(partial_products[i][j-1]), .sum(partial_products[i][j]), .c_out()/*carry*/);
                    end
                end
            end
        end
    endgenerate

    generate
        genvar k;
        assign product = {partial_products[0][N-1]};
        for (k = 1; k < N; k = k + 1) begin : CONCAT_GEN
            assign product = {product, partial_products[k][N-k-1]};
        end
    endgenerate

endmodule : array_multipler
