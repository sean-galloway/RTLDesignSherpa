// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_grouppg_008
// Purpose: Math Adder Brent Kung Grouppg 008 module
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_grouppg_008 #(
    parameter int N = 8
) (
    input  logic [N:0] i_p,
    input  logic [N:0] i_g,
    output logic [N:0] ow_gg,
    output logic [N:0] ow_pp
);

    // Per-bit scalars for the prefix chain, NOT bit-selects of ow_gg.
    //
    // This is a Brent-Kung prefix tree: bit 1 feeds 3 feeds 7 feeds 15,
    // strictly forwards, never back. But when every bit is a select of the
    // SAME output vector, Verilator schedules that vector as one node and
    // "bit 3 reads bit 1" becomes ow_gg depending on itself -- reported as
    // UNOPTFLAT: Circular combinational logic, which fails any build that
    // treats warnings as errors. It failed all six Dadda/Wallace multiplier
    // tests, which use this adder as their final CPA.
    //
    // `verilator split_var` is the usual answer and does NOT work here:
    // cocotb builds with --public-flat-rw, and Verilator refuses to split a
    // public variable (SPLITVAR). Scalars solve it structurally instead --
    // each is its own net, and ow_gg is now only ever WRITTEN in this module,
    // so no cycle can be inferred. Same logic, same connectivity.
    logic w_gg_1, w_gg_2, w_gg_3, w_gg_4, w_gg_5, w_gg_6, w_gg_7, w_gg_8;

    // `split_var` so Verilator schedules ow_gg PER BIT, not as one node.
    // This is a Brent-Kung prefix tree: bit 1 feeds bit 3 feeds bit 7 feeds
    // bit 15, strictly forwards. But every bit is driven by a different
    // sub-instance of the SAME vector, so scheduling ow_gg as a single node
    // makes "bit 3 reads bit 1" look like ow_gg depending on itself --
    // reported as UNOPTFLAT: Circular combinational logic, which fails any
    // build that treats warnings as errors. There is no loop; splitting the
    // variable lets the scheduler see the real, acyclic dependency.
    // The metacomment is a comment to every other tool.
    logic G_3_2;
    logic P_3_2;
    logic G_5_4;
    logic P_5_4;
    logic G_7_6;
    logic P_7_6;
    logic G_7_4;
    logic P_7_4;
    math_adder_brent_kung_gray gray_block_1_0 (
        .i_g(i_g[1]),
        .i_p(i_p[1]),
        .i_g_km1(i_g[0]),
        .ow_g(w_gg_1)
    );
    math_adder_brent_kung_black black_block_3_2 (
        .i_g(i_g[3]),
        .i_p(i_p[3]),
        .i_g_km1(i_g[2]),
        .i_p_km1(i_p[2]),
        .ow_g(G_3_2),
        .ow_p(P_3_2)
    );
    math_adder_brent_kung_black black_block_5_4 (
        .i_g(i_g[5]),
        .i_p(i_p[5]),
        .i_g_km1(i_g[4]),
        .i_p_km1(i_p[4]),
        .ow_g(G_5_4),
        .ow_p(P_5_4)
    );
    math_adder_brent_kung_black black_block_7_6 (
        .i_g(i_g[7]),
        .i_p(i_p[7]),
        .i_g_km1(i_g[6]),
        .i_p_km1(i_p[6]),
        .ow_g(G_7_6),
        .ow_p(P_7_6)
    );
    math_adder_brent_kung_gray gray_block_3_0 (
        .i_g(G_3_2),
        .i_p(P_3_2),
        .i_g_km1(w_gg_1),
        .ow_g(w_gg_3)
    );
    math_adder_brent_kung_black black_block_7_4 (
        .i_g(G_7_6),
        .i_p(P_7_6),
        .i_g_km1(G_5_4),
        .i_p_km1(P_5_4),
        .ow_g(G_7_4),
        .ow_p(P_7_4)
    );
    math_adder_brent_kung_gray gray_block_7_0 (
        .i_g(G_7_4),
        .i_p(P_7_4),
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_7)
    );
    math_adder_brent_kung_gray gray_block_5_3 (
        .i_g(G_5_4),
        .i_p(P_5_4),
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_5)
    );
    math_adder_brent_kung_gray gray_block_2_1 (
        .i_g(i_g[2]),
        .i_p(i_p[2]),
        .i_g_km1(w_gg_1),
        .ow_g(w_gg_2)
    );
    math_adder_brent_kung_gray gray_block_4_3 (
        .i_g(i_g[4]),
        .i_p(i_p[4]),
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_4)
    );
    math_adder_brent_kung_gray gray_block_6_5 (
        .i_g(i_g[6]),
        .i_p(i_p[6]),
        .i_g_km1(w_gg_5),
        .ow_g(w_gg_6)
    );
    math_adder_brent_kung_gray gray_block_8_7 (
        .i_g(i_g[8]),
        .i_p(i_p[8]),
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_8)
    );
    assign ow_gg[0] = i_g[0];
    assign ow_pp[0] = i_p[0];
    assign ow_gg[1] = w_gg_1;
    assign ow_gg[2] = w_gg_2;
    assign ow_gg[3] = w_gg_3;
    assign ow_gg[4] = w_gg_4;
    assign ow_gg[5] = w_gg_5;
    assign ow_gg[6] = w_gg_6;
    assign ow_gg[7] = w_gg_7;
    assign ow_gg[8] = w_gg_8;

endmodule
