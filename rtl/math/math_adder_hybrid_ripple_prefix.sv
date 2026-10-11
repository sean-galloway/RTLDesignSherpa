// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_adder_hybrid_ripple_prefix
// Purpose: Hybrid adder combining a low-order ripple-carry chain with a
//          single Kogge-Stone parallel-prefix tree for the upper bits. The
//          prefix network computes both carry-in hypotheses (c_in = 0 and
//          c_in = 1) implicitly through the group-propagate/generate terms;
//          the actual carry-in from the ripple section is injected at the
//          boundary with one 2:1 mux per upper sum bit (no duplicated tree).
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-11

`timescale 1ns / 1ps

module math_adder_hybrid_ripple_prefix #(
    parameter int N = 32,
    parameter int RIPPLE_BITS = 8
) (
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
);

    // Elaboration-time parameter guard
    generate
    if ((RIPPLE_BITS < 1) || (RIPPLE_BITS >= N) || (N < 2)) begin : gen_param_error
        initial $error("Invalid parameters: must have 1 <= RIPPLE_BITS < N and N >= 2");
    end else begin : gen_valid_params

    localparam int M = N - RIPPLE_BITS;                    // Upper prefix width
    localparam int LEVELS = (M <= 1) ? 0 : $clog2(M);      // Prefix levels for Kogge-Stone

    // Single combinational process. The prefix recurrence uses exactly the
    // math_prefix_cell equations (G = g_hi | (p_hi & g_lo), P = p_hi & p_lo)
    // evaluated level-by-level into automatic arrays, and the low-order
    // ripple is the full-adder carry chain; one process keeps the whole
    // carry DAG in one verilator evaluation ordering (no UNOPTFLAT).
    always_comb begin
        automatic logic [M-1:0] p [0:LEVELS];
        automatic logic [M-1:0] g [0:LEVELS];
        automatic logic c;

        for (int i = 0; i < M; i++) begin
            p[0][i] = i_a[i + RIPPLE_BITS] ^ i_b[i + RIPPLE_BITS];
            g[0][i] = i_a[i + RIPPLE_BITS] & i_b[i + RIPPLE_BITS];
        end
        for (int lvl = 1; lvl <= LEVELS; lvl++) begin
            for (int j = 0; j < M; j++) begin
                if (j < (1 << (lvl - 1))) begin
                    p[lvl][j] = p[lvl-1][j];
                    g[lvl][j] = g[lvl-1][j];
                end else begin
                    // math_prefix_cell equations
                    p[lvl][j] = p[lvl-1][j] & p[lvl-1][j - (1 << (lvl - 1))];
                    g[lvl][j] = g[lvl-1][j] | (p[lvl-1][j] & g[lvl-1][j - (1 << (lvl - 1))]);
                end
            end
        end

        // Low-order ripple-carry chain
        c = i_c;
        for (int b = 0; b < RIPPLE_BITS; b++) begin
            ow_sum[b] = i_a[b] ^ i_b[b] ^ c;
            c         = (i_a[b] & i_b[b]) | (i_a[b] & c) | (i_b[b] & c);
        end

        // Boundary: carry INTO upper bit b is the prefix over bits [0..b-1]
        // (exclusive of bit b itself); c_lo carries into upper bit 0.
        // carry_i(c_in) = G_(i-1) | (P_(i-1) & c_in) covers both hypotheses
        // with the single tree.
        for (int b = 0; b < M; b++) begin
            if (b == 0) begin
                ow_sum[RIPPLE_BITS] = i_a[RIPPLE_BITS] ^ i_b[RIPPLE_BITS] ^ c;
            end else begin
                ow_sum[b + RIPPLE_BITS] = i_a[b + RIPPLE_BITS] ^ i_b[b + RIPPLE_BITS]
                                          ^ (g[LEVELS][b-1] | (p[LEVELS][b-1] & c));
            end
        end
        ow_carry = g[LEVELS][M-1] | (p[LEVELS][M-1] & c);
    end

    end
    endgenerate

endmodule : math_adder_hybrid_ripple_prefix
