// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for encoder (yosys-compatible)

module formal_encoder #(
    parameter int N = 8,
    parameter int M = $clog2(N)
) (
    input logic clk
);

    (* anyconst *) logic [N-1:0] decoded;

    logic [M-1:0] data;

    encoder #(.N(N)) dut (
        .decoded(decoded),
        .data   (data)
    );

    // When input is one-hot, output equals the index of the set bit
    always @(posedge clk)
        if ($onehot(decoded))
assert (decoded[data]);

    // For each specific one-hot position, output must equal i
    generate
        genvar i;
        for (i = 0; i < N; i++) begin : gen_bit_check
            always @(posedge clk)
                if (decoded == (N'(1) << i))
assert (data == M'(i));
        end
    endgenerate

    // When input is all zeros, output is zero
    always @(posedge clk)
        if (decoded == '0)
assert (data == '0);

    // Output is always in valid range
    always @(posedge clk)
assert (data < N);

    // When input is one-hot, the set bit position matches data
    always @(posedge clk)
        if ($onehot(decoded))
assert ((N'(1) << data) == decoded);

    // Cover: each index value
    generate
        for (i = 0; i < N; i++) begin : gen_cover
            always @(posedge clk)
cover (data == M'(i) && $onehot(decoded));
        end
    endgenerate

endmodule
