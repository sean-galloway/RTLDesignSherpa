// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_full_nbit (N-bit ripple-carry full adder)
// Proves: {cout, sum} == a + b + cin

module formal_math_adder_full_nbit #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] a;
    (* anyconst *) logic [WIDTH-1:0] b;
    (* anyconst *) logic             cin;

    logic [WIDTH-1:0] sum;
    logic             cout;

    math_adder_full_nbit #(.N(WIDTH)) dut (
        .i_a     (a),
        .i_b     (b),
        .i_c     (cin),
        .ow_sum  (sum),
        .ow_carry(cout)
    );

    // Reference: (WIDTH+1)-bit result of a + b + cin
    wire [WIDTH:0] ref_result = {1'b0, a} + {1'b0, b} + {{WIDTH{1'b0}}, cin};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: {cout, sum} == a + b + cin
    always @(posedge clk)
        ap_adder_correct: assert ({cout, sum} == ref_result);

    // Carry out matches MSB of reference
    always @(posedge clk)
        ap_carry: assert (cout == ref_result[WIDTH]);

    // Sum matches lower WIDTH bits
    always @(posedge clk)
        ap_sum: assert (sum == ref_result[WIDTH-1:0]);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no carry out
    always @(posedge clk)
        cp_no_carry: cover (cout == 1'b0 && a != '0 && b != '0);

    // Cover: carry out
    always @(posedge clk)
        cp_carry: cover (cout == 1'b1);

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zeros: cover (a == '0 && b == '0 && cin == 1'b0);

    // Cover: all ones
    always @(posedge clk)
        cp_all_ones: cover (a == {WIDTH{1'b1}} && b == {WIDTH{1'b1}} && cin == 1'b1);

    // Cover: carry-in propagates through all ones
    always @(posedge clk)
        cp_cin_propagate: cover (a == {WIDTH{1'b1}} && b == '0 && cin == 1'b1 && cout == 1'b1);

endmodule
