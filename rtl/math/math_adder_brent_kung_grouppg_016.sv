// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_brent_kung_grouppg_016
// Purpose: Math Adder Brent Kung Grouppg 016 module
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module math_adder_brent_kung_grouppg_016 #(
    parameter int N = 16
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
    logic w_gg_1, w_gg_2, w_gg_3, w_gg_4, w_gg_5, w_gg_6, w_gg_7, w_gg_8, w_gg_9, w_gg_10, w_gg_11, w_gg_12, w_gg_13, w_gg_14, w_gg_15, w_gg_16;

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
    logic G_9_8;
    logic P_9_8;
    logic G_11_10;
    logic P_11_10;
    logic G_13_12;
    logic P_13_12;
    logic G_15_14;
    logic P_15_14;
    logic G_7_4;
    logic P_7_4;
    logic G_11_8;
    logic P_11_8;
    logic G_15_12;
    logic P_15_12;
    logic G_15_8;
    logic P_15_8;
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
    math_adder_brent_kung_black black_block_9_8 (
        .i_g(i_g[9]),
        .i_p(i_p[9]),
        .i_g_km1(i_g[8]),
        .i_p_km1(i_p[8]),
        .ow_g(G_9_8),
        .ow_p(P_9_8)
    );
    math_adder_brent_kung_black black_block_11_10 (
        .i_g(i_g[11]),
        .i_p(i_p[11]),
        .i_g_km1(i_g[10]),
        .i_p_km1(i_p[10]),
        .ow_g(G_11_10),
        .ow_p(P_11_10)
    );
    math_adder_brent_kung_black black_block_13_12 (
        .i_g(i_g[13]),
        .i_p(i_p[13]),
        .i_g_km1(i_g[12]),
        .i_p_km1(i_p[12]),
        .ow_g(G_13_12),
        .ow_p(P_13_12)
    );
    math_adder_brent_kung_black black_block_15_14 (
        .i_g(i_g[15]),
        .i_p(i_p[15]),
        .i_g_km1(i_g[14]),
        .i_p_km1(i_p[14]),
        .ow_g(G_15_14),
        .ow_p(P_15_14)
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
    math_adder_brent_kung_black black_block_11_8 (
        .i_g(G_11_10),
        .i_p(P_11_10),
        .i_g_km1(G_9_8),
        .i_p_km1(P_9_8),
        .ow_g(G_11_8),
        .ow_p(P_11_8)
    );
    math_adder_brent_kung_black black_block_15_12 (
        .i_g(G_15_14),
        .i_p(P_15_14),
        .i_g_km1(G_13_12),
        .i_p_km1(P_13_12),
        .ow_g(G_15_12),
        .ow_p(P_15_12)
    );
    math_adder_brent_kung_gray gray_block_7_0 (
        .i_g(G_7_4),
        .i_p(P_7_4),
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_7)
    );
    math_adder_brent_kung_black black_block_15_8 (
        .i_g(G_15_12),
        .i_p(P_15_12),
        .i_g_km1(G_11_8),
        .i_p_km1(P_11_8),
        .ow_g(G_15_8),
        .ow_p(P_15_8)
    );
    math_adder_brent_kung_gray gray_block_15_0 (
        .i_g(G_15_8),
        .i_p(P_15_8),
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_15)
    );
    math_adder_brent_kung_gray gray_block_11_7 (
        .i_g(G_11_8),
        .i_p(P_11_8),
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_11)
    );
    math_adder_brent_kung_gray gray_block_5_3 (
        .i_g(G_5_4),
        .i_p(P_5_4),
        .i_g_km1(w_gg_3),
        .ow_g(w_gg_5)
    );
    math_adder_brent_kung_gray gray_block_9_7 (
        .i_g(G_9_8),
        .i_p(P_9_8),
        .i_g_km1(w_gg_7),
        .ow_g(w_gg_9)
    );
    math_adder_brent_kung_gray gray_block_13_11 (
        .i_g(G_13_12),
        .i_p(P_13_12),
        .i_g_km1(w_gg_11),
        .ow_g(w_gg_13)
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
    math_adder_brent_kung_gray gray_block_10_9 (
        .i_g(i_g[10]),
        .i_p(i_p[10]),
        .i_g_km1(w_gg_9),
        .ow_g(w_gg_10)
    );
    math_adder_brent_kung_gray gray_block_12_11 (
        .i_g(i_g[12]),
        .i_p(i_p[12]),
        .i_g_km1(w_gg_11),
        .ow_g(w_gg_12)
    );
    math_adder_brent_kung_gray gray_block_14_13 (
        .i_g(i_g[14]),
        .i_p(i_p[14]),
        .i_g_km1(w_gg_13),
        .ow_g(w_gg_14)
    );
    math_adder_brent_kung_gray gray_block_16_15 (
        .i_g(i_g[16]),
        .i_p(i_p[16]),
        .i_g_km1(w_gg_15),
        .ow_g(w_gg_16)
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
    assign ow_gg[9] = w_gg_9;
    assign ow_gg[10] = w_gg_10;
    assign ow_gg[11] = w_gg_11;
    assign ow_gg[12] = w_gg_12;
    assign ow_gg[13] = w_gg_13;
    assign ow_gg[14] = w_gg_14;
    assign ow_gg[15] = w_gg_15;
    assign ow_gg[16] = w_gg_16;

endmodule
