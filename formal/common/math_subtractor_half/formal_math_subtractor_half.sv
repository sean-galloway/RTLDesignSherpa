// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_subtractor_half (1-bit half subtractor)
// Proves: diff == a^b, borrow == ~a&b

module formal_math_subtractor_half (
    input logic clk
);

    (* anyconst *) logic a;
    (* anyconst *) logic b;

    logic diff;
    logic borrow;

    math_subtractor_half dut (
        .i_a(a),
        .i_b(b),
        .o_d(diff),
        .o_b(borrow)
    );

    // Reference: 2-bit result of a - b (unsigned)
    wire [1:0] ref_result = {1'b0, a} - {1'b0, b};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Difference is XOR of inputs
    always @(posedge clk)
        ap_diff_xor: assert (diff == (a ^ b));

    // Borrow is ~a & b
    always @(posedge clk)
        ap_borrow: assert (borrow == (~a & b));

    // Combined: {borrow, diff} == a - b (as 2-bit unsigned)
    always @(posedge clk)
        ap_combined: assert ({borrow, diff} == ref_result);

    // Borrow only occurs when a < b (i.e., a==0, b==1)
    always @(posedge clk)
        ap_borrow_condition: assert (borrow == (a < b));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no borrow (a >= b)
    always @(posedge clk)
        cp_no_borrow: cover (borrow == 1'b0 && diff == 1'b1);

    // Cover: borrow (a < b)
    always @(posedge clk)
        cp_borrow: cover (borrow == 1'b1);

    // Cover: both zero
    always @(posedge clk)
        cp_both_zero: cover (a == 0 && b == 0);

    // Cover: a=1, b=0
    always @(posedge clk)
        cp_a_gt_b: cover (a == 1 && b == 0);

endmodule
