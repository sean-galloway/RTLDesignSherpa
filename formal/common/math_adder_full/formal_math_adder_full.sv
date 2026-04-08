// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_full (1-bit full adder)
// Proves: {carry, sum} == a + b + cin for all input combinations

module formal_math_adder_full (
    input logic clk
);

    (* anyconst *) logic a;
    (* anyconst *) logic b;
    (* anyconst *) logic cin;

    logic sum;
    logic carry;

    math_adder_full #(.N(1)) dut (
        .i_a     (a),
        .i_b     (b),
        .i_c     (cin),
        .ow_sum  (sum),
        .ow_carry(carry)
    );

    // Reference: 2-bit result of a + b + cin
    wire [1:0] ref_result = {1'b0, a} + {1'b0, b} + {1'b0, cin};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: {carry, sum} == a + b + cin
    always @(posedge clk)
        ap_adder_correct: assert ({carry, sum} == ref_result);

    // Sum is XOR of all inputs
    always @(posedge clk)
        ap_sum_is_xor: assert (sum == (a ^ b ^ cin));

    // Carry is majority function
    always @(posedge clk)
        ap_carry_is_majority: assert (carry == ((a & b) | (b & cin) | (a & cin)));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no carry (0+0+0)
    always @(posedge clk)
        cp_no_carry: cover (carry == 1'b0 && sum == 1'b0);

    // Cover: carry generated (1+1+0)
    always @(posedge clk)
        cp_carry_gen: cover (carry == 1'b1 && sum == 1'b0);

    // Cover: all ones input (1+1+1)
    always @(posedge clk)
        cp_all_ones: cover (a == 1'b1 && b == 1'b1 && cin == 1'b1);

    // Cover: sum=1, carry=0
    always @(posedge clk)
        cp_sum_only: cover (carry == 1'b0 && sum == 1'b1);

endmodule
