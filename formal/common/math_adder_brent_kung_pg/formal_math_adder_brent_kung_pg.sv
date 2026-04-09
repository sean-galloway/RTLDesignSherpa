// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_brent_kung_pg (bitwise PG cell)
// Proves: p == a^b, g == a&b (propagate/generate definitions)

module formal_math_adder_brent_kung_pg (
    input logic clk
);

    (* anyconst *) logic a;
    (* anyconst *) logic b;

    logic g;
    logic p;

    math_adder_brent_kung_pg dut (
        .i_a (a),
        .i_b (b),
        .ow_g(g),
        .ow_p(p)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Generate is AND (carry generated when both inputs are 1)
    always @(posedge clk)
        ap_generate: assert (g == (a & b));

    // Propagate is XOR (carry propagated when exactly one input is 1)
    always @(posedge clk)
        ap_propagate: assert (p == (a ^ b));

    // Generate implies NOT propagate (mutual exclusion for single bits)
    always @(posedge clk)
        ap_gen_not_prop: assert (!(g && p));

    // At least one of {g, p, neither} must hold (no both-zero only when a==0,b==0)
    always @(posedge clk)
        ap_coverage: assert ((g || p) == (a || b));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: both zero (no generate, no propagate)
    always @(posedge clk)
        cp_both_zero: cover (g == 1'b0 && p == 1'b0);

    // Cover: propagate only
    always @(posedge clk)
        cp_prop_only: cover (g == 1'b0 && p == 1'b1);

    // Cover: generate only
    always @(posedge clk)
        cp_gen_only: cover (g == 1'b1 && p == 1'b0);

    // Cover: both inputs high
    always @(posedge clk)
        cp_both_high: cover (a == 1'b1 && b == 1'b1);

endmodule
