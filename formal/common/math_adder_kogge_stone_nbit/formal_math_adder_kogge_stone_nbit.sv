// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_kogge_stone_nbit (parameterized Kogge-Stone adder)
// Proves: {carry, sum} == a + b (no carry-in port on this module)

module formal_math_adder_kogge_stone_nbit #(
    parameter int N = 8
) (
    input logic clk
);

    (* anyconst *) logic [N-1:0] a;
    (* anyconst *) logic [N-1:0] b;

    logic [N-1:0] sum;
    logic         carry;

    math_adder_kogge_stone_nbit #(.N(N)) dut (
        .i_a     (a),
        .i_b     (b),
        .ow_sum  (sum),
        .ow_carry(carry)
    );

    // Reference: (N+1)-bit result of a + b (no carry-in)
    wire [N:0] ref_result = {1'b0, a} + {1'b0, b};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: {carry, sum} == a + b
    always @(posedge clk)
        ap_adder_correct: assert ({carry, sum} == ref_result);

    // Carry matches overflow bit
    always @(posedge clk)
        ap_carry_overflow: assert (carry == ref_result[N]);

    // Sum matches lower N bits
    always @(posedge clk)
        ap_sum_lower: assert (sum == ref_result[N-1:0]);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no carry with non-zero inputs
    always @(posedge clk)
        cp_no_carry: cover (carry == 1'b0 && a != '0 && b != '0);

    // Cover: carry generated
    always @(posedge clk)
        cp_carry_gen: cover (carry == 1'b1);

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zeros: cover (a == '0 && b == '0);

    // Cover: all ones
    always @(posedge clk)
        cp_all_ones: cover (a == {N{1'b1}} && b == {N{1'b1}});

    // Cover: maximum sum without carry (a + b = 2^N - 1)
    always @(posedge clk)
        cp_max_no_carry: cover (carry == 1'b0 && sum == {N{1'b1}});

endmodule
