// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_ripple_carry (N-bit ripple carry adder)
// Proves: {carry, sum} == a + b + cin for WIDTH=8

module formal_math_adder_ripple_carry #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] a;
    (* anyconst *) logic [WIDTH-1:0] b;
    (* anyconst *) logic             cin;

    logic [WIDTH-1:0] sum;
    logic             carry;

    math_adder_ripple_carry #(.N(WIDTH)) dut (
        .i_a     (a),
        .i_b     (b),
        .i_c     (cin),
        .ow_sum  (sum),
        .ow_carry(carry)
    );

    // Reference: (WIDTH+1)-bit result of a + b + cin
    wire [WIDTH:0] ref_result = {1'b0, a} + {1'b0, b} + {{WIDTH{1'b0}}, cin};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: {carry, sum} == a + b + cin
    always @(posedge clk)
        ap_adder_correct: assert ({carry, sum} == ref_result);

    // Carry must be set when a + b + cin overflows WIDTH bits
    always @(posedge clk)
        ap_carry_overflow: assert (carry == ref_result[WIDTH]);

    // Sum matches lower WIDTH bits
    always @(posedge clk)
        ap_sum_lower: assert (sum == ref_result[WIDTH-1:0]);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no carry
    always @(posedge clk)
        cp_no_carry: cover (carry == 1'b0 && a != '0 && b != '0);

    // Cover: carry generated
    always @(posedge clk)
        cp_carry_gen: cover (carry == 1'b1);

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zeros: cover (a == '0 && b == '0 && cin == 1'b0);

    // Cover: all ones
    always @(posedge clk)
        cp_all_ones: cover (a == {WIDTH{1'b1}} && b == {WIDTH{1'b1}} && cin == 1'b1);

    // Cover: carry-in propagates through
    always @(posedge clk)
        cp_cin_propagate: cover (a == {WIDTH{1'b1}} && b == '0 && cin == 1'b1 && carry == 1'b1);

endmodule
