// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for reverse_vector
// Proves bit reversal properties:
//   1. output[i] == input[WIDTH-1-i] for all i
//   2. Double reversal is identity
//   3. Boundary checks: output[0] == input[WIDTH-1] and vice versa

module formal_reverse_vector #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] vector_in;

    logic [WIDTH-1:0] vector_rev;

    reverse_vector #(
        .WIDTH(WIDTH)
    ) dut (
        .vector_in (vector_in),
        .vector_rev(vector_rev)
    );

    // Second instance for double-reversal identity proof
    logic [WIDTH-1:0] vector_double_rev;

    reverse_vector #(
        .WIDTH(WIDTH)
    ) dut_double (
        .vector_in (vector_rev),
        .vector_rev(vector_double_rev)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Primary property: each bit is correctly reversed
    generate
        genvar i;
        for (i = 0; i < WIDTH; i++) begin : gen_bit_check
            always @(posedge clk)
                assert (vector_rev[i] == vector_in[(WIDTH-1)-i]);
        end
    endgenerate

    // Double reversal is identity
    always @(posedge clk)
        ap_double_reverse: assert (vector_double_rev == vector_in);

    // Boundary: output[0] == input[WIDTH-1]
    always @(posedge clk)
        ap_lsb_to_msb: assert (vector_rev[0] == vector_in[WIDTH-1]);

    // Boundary: output[WIDTH-1] == input[0]
    always @(posedge clk)
        ap_msb_to_lsb: assert (vector_rev[WIDTH-1] == vector_in[0]);

    // Palindrome: if input is a palindrome, output equals input
    always @(posedge clk)
        if (vector_in == vector_rev)
            ap_palindrome: assert (vector_rev == vector_in);

    // All zeros reverses to all zeros
    always @(posedge clk)
        ap_all_zeros: assert (!(vector_in == '0) || (vector_rev == '0));

    // All ones reverses to all ones
    always @(posedge clk)
        ap_all_ones: assert (!(vector_in == {WIDTH{1'b1}}) || (vector_rev == {WIDTH{1'b1}}));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zeros: cover (vector_in == '0 && vector_rev == '0);

    // Cover: all ones
    always @(posedge clk)
        cp_all_ones: cover (vector_in == {WIDTH{1'b1}} && vector_rev == {WIDTH{1'b1}});

    // Cover: single bit set in input appears reversed in output
    always @(posedge clk)
        cp_single_bit: cover (vector_in == {{(WIDTH-1){1'b0}}, 1'b1} &&
                              vector_rev == {1'b1, {(WIDTH-1){1'b0}}});

    // Cover: input != output (non-palindrome)
    always @(posedge clk)
        cp_non_palindrome: cover (vector_in != vector_rev);

endmodule
