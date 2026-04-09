// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_multiplier_carry_save (N-bit carry-save multiplier)
// Proves: ow_product == i_multiplier * i_multiplicand
// Uses WIDTH=4 for tractable formal verification

module formal_math_multiplier_carry_save #(
    parameter int WIDTH = 4
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] multiplier;
    (* anyconst *) logic [WIDTH-1:0] multiplicand;

    logic [2*WIDTH-1:0] product;

    math_multiplier_carry_save #(.N(WIDTH)) dut (
        .i_multiplier  (multiplier),
        .i_multiplicand(multiplicand),
        .ow_product    (product)
    );

    // Reference: simple multiplication
    wire [2*WIDTH-1:0] ref_product = multiplier * multiplicand;

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: product == multiplier * multiplicand
    always @(posedge clk)
        ap_mul_correct: assert (product == ref_product);

    // Product of zero inputs is zero
    always @(posedge clk)
        ap_zero_mul: assert (!(multiplier == '0 || multiplicand == '0) || product == '0);

    // Multiplication by 1
    always @(posedge clk)
        ap_mul_by_one: assert (multiplier != {{(WIDTH-1){1'b0}}, 1'b1} ||
                               product == {{WIDTH{1'b0}}, multiplicand});

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: both zero
    always @(posedge clk)
        cp_both_zero: cover (multiplier == '0 && multiplicand == '0);

    // Cover: max * max
    always @(posedge clk)
        cp_max_mul: cover (multiplier == {WIDTH{1'b1}} && multiplicand == {WIDTH{1'b1}});

    // Cover: non-trivial product
    always @(posedge clk)
        cp_nontrivial: cover (multiplier > 1 && multiplicand > 1 && product > 0);

    // Cover: product uses all bits (MSB set)
    always @(posedge clk)
        cp_msb_set: cover (product[2*WIDTH-1] == 1'b1);

endmodule
