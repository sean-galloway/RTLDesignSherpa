// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gf_mul
// Purpose:
//   Variable-by-variable multiplier in GF(2^m). Combinational, no clock.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

//==============================================================================
// Module: gf_mul
//==============================================================================
// Description:
//   Polynomial-basis (Mastrovito) multiplier. Stage 1 forms the carry-less
//   product of the two m-bit operands as a (2m-1)-bit polynomial: an m x m AND
//   array whose anti-diagonals are XOR-reduced. Stage 2 reduces the high m-1
//   bits back under the primitive polynomial: x^k mod p(x) is a constant m-bit
//   vector for each k in [m, 2m-2], computed at elaboration by gf_pkg, so the
//   reduction is a constant XOR network gated by the high product bits.
//
//   Depth is about log2(m) XOR levels for the product and log2(m) for the
//   reduction. There are no carries anywhere; DSP inference is irrelevant.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m, the field is GF(2^m). Range 2..16. Default 8.
//   PRIM_POLY:    primitive polynomial with bit m set. Default 0x11D
//                 (x^8+x^4+x^3+x^2+1, the DVB / reference-profile field).
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   i_a, i_b: operands
//   ow_p:     product a * b
//
//==============================================================================

module gf_mul
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D
) (
    input  logic [SYMBOL_WIDTH-1:0] i_a,
    input  logic [SYMBOL_WIDTH-1:0] i_b,
    output logic [SYMBOL_WIDTH-1:0] ow_p
);

    localparam int M = SYMBOL_WIDTH;

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 2 || M > GF_MAX_M)
            $error("gf_mul: SYMBOL_WIDTH must be 2..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("gf_mul: PRIM_POLY 0x%0h is not a primitive polynomial of degree %0d",
                   PRIM_POLY, M);
    end

    // -------------------------------------------------------------------------
    // Reduction constants: RED[k-M] = x^k mod p(x) for k = M .. 2M-2, packed
    // M bits each into one vector so it is a plain localparam.
    // -------------------------------------------------------------------------
    localparam int RED_W = M * (M - 1);

    // (a function result is assigned to a variable before its bits are
    // selected: Vivado rejects a select on a function call, Synth 8-12513)
    function automatic logic [RED_W-1:0] build_red();
        logic [RED_W-1:0] r;
        /* verilator lint_off UNUSEDSIGNAL */   // a gf_wide_t whose low M bits are the value
        gf_wide_t         v;
        /* verilator lint_on UNUSEDSIGNAL */
        r = '0;
        for (int k = M; k <= 2 * M - 2; k++) begin
            v = gf_alpha_pow(k, M, PRIM_POLY);
            r[(k-M)*M +: M] = v[M-1:0];
        end
        return r;
    endfunction

    localparam logic [RED_W-1:0] RED = build_red();

    // -------------------------------------------------------------------------
    // Stage 1: carry-less product, 2M-1 bits
    // -------------------------------------------------------------------------
    logic [2*M-2:0] w_prod;

    always_comb begin
        w_prod = '0;
        for (int i = 0; i < M; i++)
            for (int j = 0; j < M; j++)
                w_prod[i+j] = w_prod[i+j] ^ (i_a[i] & i_b[j]);
    end

    // -------------------------------------------------------------------------
    // Stage 2: fold the high bits back with the reduction constants
    // -------------------------------------------------------------------------
    always_comb begin
        ow_p = w_prod[M-1:0];
        for (int k = M; k <= 2 * M - 2; k++)
            if (w_prod[k]) ow_p = ow_p ^ RED[(k-M)*M +: M];
    end

endmodule : gf_mul
