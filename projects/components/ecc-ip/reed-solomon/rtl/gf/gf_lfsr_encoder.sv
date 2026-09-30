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
//   Polynomial division of the data block by g(x), one symbol per i_step:
//
//     fb   = data ^ r[2t-1]
//     r[j] = r[j-1] ^ fb * g[j]      (j = 1 .. 2t-1)
//     r[0] = fb * g[0]
//
//   where g(x) = prod_{i=0}^{2t-1} (x - alpha^(b+i)) is computed at elaboration
//   from gf_pkg, so no coefficient is typed in and any (m, t, b) elaborates.
//   After the k data symbols the register holds the 2t parity symbols with
//   the highest-degree coefficient in r[2t-1]. i_shift then drains them: each
//   shift moves r[j-1] into r[j] with zero feedback, so ow_parity presents the
//   parity symbols in transmission order and the register is all-zero after
//   2t shifts, ready for the next block with no separate clear.
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
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   i_step:     shift one data symbol in (feedback enabled)
//   i_data:     the data symbol
//   i_shift:    shift one parity symbol out (feedback disabled)
//   ow_parity:  r[2t-1], the next parity symbol in transmission order
//
//==============================================================================

module gf_lfsr_encoder
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int FIRST_ROOT   = 0
) (
    input  logic                    aclk,
    input  logic                    aresetn,
    input  logic                    i_step,
    input  logic [SYMBOL_WIDTH-1:0] i_data,
    input  logic                    i_shift,
    output logic [SYMBOL_WIDTH-1:0] ow_parity
);

    localparam int M  = SYMBOL_WIDTH;
    localparam int T2 = 2 * T_SYMBOLS;

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
    // Datapath
    // -------------------------------------------------------------------------
    logic [M-1:0] r_reg [T2];
    logic [M-1:0] w_fb;
    logic [M-1:0] w_tap [T2];

    assign w_fb      = i_data ^ r_reg[T2-1];
    assign ow_parity = r_reg[T2-1];

    for (genvar j = 0; j < T2; j++) begin : g_tap
        gf_mul_const #(
            .SYMBOL_WIDTH(M),
            .PRIM_POLY   (PRIM_POLY),
            .CONST       (int'(GEN[j*M +: M]))
        ) u_tap (
            .i_a (w_fb),
            .ow_p(w_tap[j])
        );
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int j = 0; j < T2; j++) r_reg[j] <= '0;
        end else if (i_step) begin
            r_reg[0] <= w_tap[0];
            for (int j = 1; j < T2; j++) r_reg[j] <= r_reg[j-1] ^ w_tap[j];
        end else if (i_shift) begin
            r_reg[0] <= '0;
            for (int j = 1; j < T2; j++) r_reg[j] <= r_reg[j-1];
        end
    )

endmodule : gf_lfsr_encoder
