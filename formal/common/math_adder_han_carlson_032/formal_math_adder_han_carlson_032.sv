// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_han_carlson_032 (32-bit Han-Carlson adder)
// Proves: {cout, sum} == a + b + cin

module formal_math_adder_han_carlson_032 #(
    parameter int N = 32
) (
    input logic clk
);

    (* anyconst *) logic [N-1:0] a;
    (* anyconst *) logic [N-1:0] b;
    (* anyconst *) logic         cin;

    logic [N-1:0] sum;
    logic         cout;

    math_adder_han_carlson_032 #(.N(N)) dut (
        .i_a    (a),
        .i_b    (b),
        .i_cin  (cin),
        .ow_sum (sum),
        .ow_cout(cout)
    );

    // Reference: (N+1)-bit result of a + b + cin
    wire [N:0] ref_result = {1'b0, a} + {1'b0, b} + {{N{1'b0}}, cin};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: {cout, sum} == a + b + cin
    always @(posedge clk)
        ap_adder_correct: assert ({cout, sum} == ref_result);

    // Carry matches overflow bit
    always @(posedge clk)
        ap_carry_overflow: assert (cout == ref_result[N]);

    // Sum matches lower N bits
    always @(posedge clk)
        ap_sum_lower: assert (sum == ref_result[N-1:0]);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no carry with non-zero inputs
    always @(posedge clk)
        cp_no_carry: cover (cout == 1'b0 && a != '0 && b != '0);

    // Cover: carry generated
    always @(posedge clk)
        cp_carry_gen: cover (cout == 1'b1);

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zeros: cover (a == '0 && b == '0 && cin == 1'b0);

    // Cover: all ones
    always @(posedge clk)
        cp_all_ones: cover (a == {N{1'b1}} && b == {N{1'b1}} && cin == 1'b1);

    // Cover: carry-in propagation through all bits
    always @(posedge clk)
        cp_cin_propagate: cover (a == {N{1'b1}} && b == '0 && cin == 1'b1 && cout == 1'b1);

endmodule
