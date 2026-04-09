// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_brent_kung_gray (gray prefix cell)
// Proves: g_out == g_hi | (p_hi & g_lo)

module formal_math_adder_brent_kung_gray (
    input logic clk
);

    (* anyconst *) logic g_hi;
    (* anyconst *) logic p_hi;
    (* anyconst *) logic g_lo;

    logic g_out;

    math_adder_brent_kung_gray dut (
        .i_g    (g_hi),
        .i_p    (p_hi),
        .i_g_km1(g_lo),
        .ow_g   (g_out)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Gray cell generate: g_out = g_hi | (p_hi & g_lo)
    always @(posedge clk)
        ap_generate: assert (g_out == (g_hi | (p_hi & g_lo)));

    // If high generates, output must generate
    always @(posedge clk)
        ap_hi_gen_dominates: assert (!g_hi || g_out);

    // If high propagates and low generates, output generates
    always @(posedge clk)
        ap_prop_gen: assert (!(p_hi && g_lo) || g_out);

    // Gray cell matches black cell generate equation (same formula)
    always @(posedge clk)
        ap_match_black_gen: assert (g_out == (g_hi | (p_hi & g_lo)));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: output generates from high
    always @(posedge clk)
        cp_gen_from_hi: cover (g_hi == 1'b1 && g_out == 1'b1);

    // Cover: output generates from propagation
    always @(posedge clk)
        cp_gen_from_prop: cover (g_hi == 1'b0 && p_hi == 1'b1 && g_lo == 1'b1 && g_out == 1'b1);

    // Cover: no generate (kill case)
    always @(posedge clk)
        cp_no_gen: cover (g_out == 1'b0);

    // Cover: all inputs high
    always @(posedge clk)
        cp_all_high: cover (g_hi == 1'b1 && p_hi == 1'b1 && g_lo == 1'b1);

endmodule
