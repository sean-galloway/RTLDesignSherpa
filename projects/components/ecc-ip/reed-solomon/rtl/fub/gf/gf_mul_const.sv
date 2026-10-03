// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gf_mul_const
// Purpose:
//   Multiply by a build-time constant in GF(2^m). Combinational, no clock.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

//==============================================================================
// Module: gf_mul_const
//==============================================================================
// Description:
//   Multiplication by a constant c is a linear map over GF(2), so it is an
//   m x m bit matrix: column i is (x^i * c) mod p(x). gf_pkg computes the
//   matrix at elaboration and the product is the XOR of the columns selected
//   by the set bits of the operand -- at most m XOR trees of up to m inputs,
//   with no AND gates at all.
//
//   This is the block the encoder LFSR taps, the syndrome cells and the Chien
//   cells are made of, so it is instantiated more than anything else in the
//   codec.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m, the field is GF(2^m). Range 2..16. Default 8.
//   PRIM_POLY:    primitive polynomial with bit m set. Default 0x11D.
//   CONST:        the multiplier, a field element in 0 .. 2^m-1. Default 2
//                 (alpha, the multiply-by-x step).
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   i_a:  operand
//   ow_p: product a * CONST
//
//==============================================================================

module gf_mul_const
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int CONST        = 2
) (
    input  logic [SYMBOL_WIDTH-1:0] i_a,
    output logic [SYMBOL_WIDTH-1:0] ow_p
);

    localparam int M = SYMBOL_WIDTH;

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 2 || M > GF_MAX_M)
            $error("gf_mul_const: SYMBOL_WIDTH must be 2..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("gf_mul_const: PRIM_POLY 0x%0h is not a primitive polynomial of degree %0d",
                   PRIM_POLY, M);
        if (CONST < 0 || CONST >= (1 << M))
            $error("gf_mul_const: CONST %0d is not a field element of GF(2^%0d)", CONST, M);
    end

    // -------------------------------------------------------------------------
    // Column i of the multiply-by-CONST matrix: (x^i * CONST) mod p(x)
    // -------------------------------------------------------------------------
    localparam int MAT_W = M * M;

    function automatic logic [MAT_W-1:0] build_matrix();
        logic [MAT_W-1:0] r;
        gf_wide_t         col;
        r   = '0;
        col = gf_wide_t'(CONST);
        for (int i = 0; i < M; i++) begin
            r[i*M +: M] = col[M-1:0];
            col = gf_mul_x(col, M, PRIM_POLY);
        end
        return r;
    endfunction

    localparam logic [MAT_W-1:0] MAT = build_matrix();

    // -------------------------------------------------------------------------
    // Product: XOR of the selected columns
    // -------------------------------------------------------------------------
    always_comb begin
        ow_p = '0;
        for (int i = 0; i < M; i++)
            if (i_a[i]) ow_p = ow_p ^ MAT[i*M +: M];
    end

endmodule : gf_mul_const
