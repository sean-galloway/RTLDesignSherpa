// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gf_lfsr_encoder
// Purpose:
//   Systematic Reed-Solomon parity generator: a 2t-stage LFSR over GF(2^m)
//   whose taps are the generator polynomial's coefficients.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: gf_lfsr_encoder
//==============================================================================
// Description:
//   Polynomial division of the data block by g(x). One symbol step is
//
//     fb   = data ^ r[2t-1]
//     r[j] = r[j-1] ^ fb * g[j]      (j = 1 .. 2t-1)
//     r[0] = fb * g[0]
//
//   and an i_step applies it i_count times in one cycle (1 .. S symbols, the
//   low lanes of i_data first): the S single steps are unrolled and the
//   state after the i_count-th is taken, so a partial final beat costs nothing
//   but a mux. The tap multiplies are constant, so the unrolled chain is one
//   XOR network whatever S is.
//
//   where g(x) = prod_{i=0}^{2t-1} (x - alpha^(b+i)) is computed at elaboration
//   from gf_pkg, so no coefficient is typed in and any (m, t, b) elaborates.
//   After the k data symbols the register holds the 2t parity symbols with
//   the highest-degree coefficient in r[2t-1]. i_shift then drains S symbols
//   at a time: ow_parity lane u holds r[2t-1-u] (transmission order, lane 0
//   first) and each shift moves the register up by S with zero feedback, so
//   after ceil(2t/S) shifts it is all-zero, ready for the next block with no
//   separate clear.
//
//   i_step and i_shift are mutually exclusive by construction in the core;
//   if both are high, i_step wins.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t, correctable symbols; the LFSR has 2t stages. Default 8.
//   FIRST_ROOT:   b, the exponent of the first root of g(x). Default 0.
//   SYMBOLS_PER_BEAT: S, symbols per i_step / i_shift. Default 1.
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   i_step:     take i_count data symbols from i_data (feedback enabled)
//   i_data:     S symbols, symbol 0 in the low lane
//   i_count:    how many of them are present, 1 .. S (low lanes)
//   i_shift:    shift S parity symbols out (feedback disabled)
//   ow_parity:  the next S parity symbols in transmission order, lane 0 first
//
//==============================================================================

module gf_lfsr_encoder
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int FIRST_ROOT   = 0,
    parameter int SYMBOLS_PER_BEAT = 1
) (
    input  logic                                     aclk,
    input  logic                                     aresetn,
    input  logic                                     i_step,
    input  logic [SYMBOLS_PER_BEAT*SYMBOL_WIDTH-1:0] i_data,
    input  logic [$clog2(SYMBOLS_PER_BEAT+1)-1:0]    i_count,
    input  logic                                     i_shift,
    output logic [SYMBOLS_PER_BEAT*SYMBOL_WIDTH-1:0] ow_parity
);

    localparam int M  = SYMBOL_WIDTH;
    localparam int T2 = 2 * T_SYMBOLS;
    localparam int S  = SYMBOLS_PER_BEAT;

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 2 || M > GF_MAX_M)
            $error("gf_lfsr_encoder: SYMBOL_WIDTH must be 2..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("gf_lfsr_encoder: PRIM_POLY 0x%0h is not primitive of degree %0d", PRIM_POLY, M);
        if (T_SYMBOLS < 1 || T2 > (1 << M) - 2)
            $error("gf_lfsr_encoder: T_SYMBOLS %0d out of range for GF(2^%0d)", T_SYMBOLS, M);
        if (FIRST_ROOT < 0 || FIRST_ROOT > (1 << M) - 2)
            $error("gf_lfsr_encoder: FIRST_ROOT %0d out of range", FIRST_ROOT);
        if (S < 1)
            $error("gf_lfsr_encoder: SYMBOLS_PER_BEAT must be >= 1 (got %0d)", S);
    end

    // -------------------------------------------------------------------------
    // Generator polynomial g(x) = prod (x - alpha^(b+i)), i = 0 .. 2t-1.
    // GEN packs g_0 .. g_{2t-1}; the leading coefficient g_{2t} = 1 is implicit.
    // Built by repeated multiplication of the running polynomial by
    // (x + alpha^(b+i)) -- in characteristic 2, minus is plus.
    // -------------------------------------------------------------------------
    localparam int GEN_W = T2 * M;

    function automatic logic [GEN_W-1:0] build_gen();
        gf_wide_t g [T2+1];      // g[0..T2], g[T2] is the leading 1
        gf_wide_t root;
        logic [GEN_W-1:0] r;
        for (int j = 0; j <= T2; j++) g[j] = '0;
        g[0] = gf_wide_t'(1);
        for (int i = 0; i < T2; i++) begin
            root = gf_alpha_pow(FIRST_ROOT + i, M, PRIM_POLY);
            // multiply g (degree i) by (x + root): new g[j] = g[j-1] + root*g[j]
            for (int j = i + 1; j >= 1; j--)
                g[j] = g[j-1] ^ gf_mul_fn(root, g[j], M, PRIM_POLY);
            g[0] = gf_mul_fn(root, g[0], M, PRIM_POLY);
        end
        for (int j = 0; j < T2; j++) r[j*M +: M] = g[j][M-1:0];
        return r;
    endfunction

    localparam logic [GEN_W-1:0] GEN = build_gen();

    // -------------------------------------------------------------------------
    // Datapath. One symbol step as a function on the whole register (the tap
    // multiplies are by constants, so gf_mul_fn with the constant as its first
    // operand folds to an XOR network); S of them unrolled, the i_count-th
    // state taken.
    // -------------------------------------------------------------------------
    typedef logic [M-1:0] state_t [T2];

    function automatic state_t step_one(input state_t r, input logic [M-1:0] d);
        state_t       n;
        logic [M-1:0] fb;
        /* verilator lint_off UNUSEDSIGNAL */   // a gf_wide_t whose low M bits are the value
        gf_wide_t     w;
        /* verilator lint_on UNUSEDSIGNAL */
        fb   = d ^ r[T2-1];
        w    = gf_mul_fn(gf_wide_t'(GEN[0 +: M]), gf_wide_t'(fb), M, PRIM_POLY);
        n[0] = w[M-1:0];
        for (int j = 1; j < T2; j++) begin
            w    = gf_mul_fn(gf_wide_t'(GEN[j*M +: M]), gf_wide_t'(fb), M, PRIM_POLY);
            n[j] = r[j-1] ^ w[M-1:0];
        end
        return n;
    endfunction

    state_t r_reg;
    state_t w_chain [S+1];   // w_chain[u] = state after u symbols
    state_t w_next;

    always_comb begin
        w_chain[0] = r_reg;
        for (int u = 0; u < S; u++)
            w_chain[u+1] = step_one(w_chain[u], i_data[u*M +: M]);
        w_next = w_chain[S];
        for (int u = 1; u <= S; u++)
            if (i_count == ($clog2(S+1))'(u)) w_next = w_chain[u];
    end

    // parity lanes: lane u is r[2t-1-u]; beyond the register (S > 2t) zero
    always_comb begin
        for (int u = 0; u < S; u++)
            ow_parity[u*M +: M] = (u < T2) ? r_reg[T2-1-u] : '0;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int j = 0; j < T2; j++) r_reg[j] <= '0;
        end else if (i_step) begin
            r_reg <= w_next;
        end else if (i_shift) begin
            for (int j = 0; j < T2; j++) r_reg[j] <= (j >= S) ? r_reg[j-S] : '0;
        end
    )

endmodule : gf_lfsr_encoder
