// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_prefix_cell (Kogge-Stone / Han-Carlson black cell)
// Proves the PG merge equations: g_out = g_hi | (p_hi & g_lo), p_out = p_hi & p_lo
// This is the standard black prefix operator used in parallel prefix adders.

module formal_math_prefix_cell (
    input logic clk
);

    (* anyconst *) logic g_hi;
    (* anyconst *) logic p_hi;
    (* anyconst *) logic g_lo;
    (* anyconst *) logic p_lo;

    logic g_out;
    logic p_out;

    math_prefix_cell dut (
        .i_g_hi(g_hi),
        .i_p_hi(p_hi),
        .i_g_lo(g_lo),
        .i_p_lo(p_lo),
        .ow_g  (g_out),
        .ow_p  (p_out)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Kogge-Stone generate merge: g_out = g_hi | (p_hi & g_lo)
    always @(posedge clk)
        ap_generate: assert (g_out == (g_hi | (p_hi & g_lo)));

    // Kogge-Stone propagate merge: p_out = p_hi & p_lo
    always @(posedge clk)
        ap_propagate: assert (p_out == (p_hi & p_lo));

    // Structural equivalence with Brent-Kung black cell
    // (same equations, different name - both are standard prefix operators)
    always @(posedge clk)
        ap_matches_bk_black: assert (g_out == (g_hi | (p_hi & g_lo)) &&
                                     p_out == (p_hi & p_lo));

    // If high position generates, output always generates
    always @(posedge clk)
        ap_hi_gen_dominates: assert (!g_hi || g_out);

    // Output propagate requires both to propagate
    always @(posedge clk)
        ap_prop_both: assert (!p_out || (p_hi && p_lo));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: generate from high
    always @(posedge clk)
        cp_gen_from_hi: cover (g_hi == 1'b1 && g_out == 1'b1);

    // Cover: generate from propagation through
    always @(posedge clk)
        cp_gen_from_prop: cover (g_hi == 1'b0 && p_hi == 1'b1 && g_lo == 1'b1 && g_out == 1'b1);

    // Cover: propagate through
    always @(posedge clk)
        cp_propagate: cover (p_out == 1'b1);

    // Cover: kill (neither generate nor propagate)
    always @(posedge clk)
        cp_kill: cover (g_out == 1'b0 && p_out == 1'b0);

endmodule
