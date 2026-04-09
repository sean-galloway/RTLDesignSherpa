// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_prefix_cell_gray (Kogge-Stone / Han-Carlson gray cell)
// Proves: g_out = g_hi | (p_hi & g_lo) (generate-only merge, no propagate output)
// Gray cells are used at the final stage where only the carry (generate) is needed.

module formal_math_prefix_cell_gray (
    input logic clk
);

    (* anyconst *) logic g_hi;
    (* anyconst *) logic p_hi;
    (* anyconst *) logic g_lo;

    logic g_out;

    math_prefix_cell_gray dut (
        .i_g_hi(g_hi),
        .i_p_hi(p_hi),
        .i_g_lo(g_lo),
        .ow_g  (g_out)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Kogge-Stone gray cell generate merge: g_out = g_hi | (p_hi & g_lo)
    always @(posedge clk)
        ap_generate: assert (g_out == (g_hi | (p_hi & g_lo)));

    // If high generates, output must generate
    always @(posedge clk)
        ap_hi_gen_dominates: assert (!g_hi || g_out);

    // If high propagates and low generates, output generates
    always @(posedge clk)
        ap_prop_gen: assert (!(p_hi && g_lo) || g_out);

    // Structural equivalence: same generate equation as black cell and BK gray cell
    always @(posedge clk)
        ap_matches_black_gen: assert (g_out == (g_hi | (p_hi & g_lo)));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: generate from high position
    always @(posedge clk)
        cp_gen_from_hi: cover (g_hi == 1'b1 && g_out == 1'b1);

    // Cover: generate from propagation
    always @(posedge clk)
        cp_gen_from_prop: cover (g_hi == 1'b0 && p_hi == 1'b1 && g_lo == 1'b1 && g_out == 1'b1);

    // Cover: no generate (kill)
    always @(posedge clk)
        cp_no_gen: cover (g_out == 1'b0);

    // Cover: all inputs high
    always @(posedge clk)
        cp_all_high: cover (g_hi == 1'b1 && p_hi == 1'b1 && g_lo == 1'b1);

endmodule
