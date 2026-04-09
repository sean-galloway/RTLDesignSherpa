// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_brent_kung_black (black prefix cell)
// Proves: g_out == g_hi | (p_hi & g_lo), p_out == p_hi & p_lo

module formal_math_adder_brent_kung_black (
    input logic clk
);

    (* anyconst *) logic g_hi;
    (* anyconst *) logic p_hi;
    (* anyconst *) logic g_lo;
    (* anyconst *) logic p_lo;

    logic g_out;
    logic p_out;

    math_adder_brent_kung_black dut (
        .i_g    (g_hi),
        .i_p    (p_hi),
        .i_g_km1(g_lo),
        .i_p_km1(p_lo),
        .ow_g   (g_out),
        .ow_p   (p_out)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Black cell generate: g_out = g_hi | (p_hi & g_lo)
    always @(posedge clk)
        ap_generate: assert (g_out == (g_hi | (p_hi & g_lo)));

    // Black cell propagate: p_out = p_hi & p_lo
    always @(posedge clk)
        ap_propagate: assert (p_out == (p_hi & p_lo));

    // If high generates, output must generate regardless of low
    always @(posedge clk)
        ap_hi_gen_dominates: assert (!g_hi || g_out);

    // If high propagates and low generates, output generates
    always @(posedge clk)
        ap_prop_gen: assert (!(p_hi && g_lo) || g_out);

    // Output propagate requires BOTH inputs to propagate
    always @(posedge clk)
        ap_prop_both: assert (p_out == (p_hi && p_lo));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: output generates from high
    always @(posedge clk)
        cp_gen_from_hi: cover (g_hi == 1'b1 && g_out == 1'b1);

    // Cover: output generates from propagation
    always @(posedge clk)
        cp_gen_from_prop: cover (g_hi == 1'b0 && p_hi == 1'b1 && g_lo == 1'b1 && g_out == 1'b1);

    // Cover: output propagates
    always @(posedge clk)
        cp_propagate: cover (p_out == 1'b1);

    // Cover: neither generate nor propagate
    always @(posedge clk)
        cp_kill: cover (g_out == 1'b0 && p_out == 1'b0);

endmodule
