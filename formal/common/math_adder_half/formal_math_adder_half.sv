// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_half (1-bit half adder)
// Proves: sum == a^b, carry == a&b

module formal_math_adder_half (
    input logic clk
);

    (* anyconst *) logic a;
    (* anyconst *) logic b;

    logic sum;
    logic carry;

    math_adder_half #(.N(1)) dut (
        .i_a     (a),
        .i_b     (b),
        .ow_sum  (sum),
        .ow_carry(carry)
    );

    // Reference: 2-bit result of a + b
    wire [1:0] ref_result = {1'b0, a} + {1'b0, b};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: {carry, sum} == a + b
    always @(posedge clk)
        ap_adder_correct: assert ({carry, sum} == ref_result);

    // Sum is XOR of inputs
    always @(posedge clk)
        ap_sum_is_xor: assert (sum == (a ^ b));

    // Carry is AND of inputs
    always @(posedge clk)
        ap_carry_is_and: assert (carry == (a & b));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: both zero (0+0)
    always @(posedge clk)
        cp_both_zero: cover (a == 1'b0 && b == 1'b0);

    // Cover: sum without carry (0+1)
    always @(posedge clk)
        cp_sum_no_carry: cover (sum == 1'b1 && carry == 1'b0);

    // Cover: carry generated (1+1)
    always @(posedge clk)
        cp_carry_gen: cover (carry == 1'b1 && sum == 1'b0);

    // Cover: one of each input combination
    always @(posedge clk)
        cp_a_only: cover (a == 1'b1 && b == 1'b0);

endmodule
