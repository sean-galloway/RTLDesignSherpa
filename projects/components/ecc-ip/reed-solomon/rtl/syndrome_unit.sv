// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: syndrome_unit
// Purpose:
//   The 2t syndromes of a received block, S_i = r(alpha^(b+i)), i = 0..2t-1,
//   accumulated one symbol per i_step; a zero flag over all of them.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

//==============================================================================
// Module: syndrome_unit
//==============================================================================
// Description:
//   2t gf_syndrome_cells in parallel, each on its own root alpha^(b+i). The
//   caller steps them with every received symbol, marking the block's first
//   symbol with i_first; after the last symbol ow_synd holds the 2t syndromes
//   packed S_0 in the low m bits, and ow_all_zero says the block is a
//   codeword (no correction needed). The caller latches both on its block
//   boundary; the cells start over on the next block's first symbol.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t; 2t syndromes. Default 8.
//   FIRST_ROOT:   b. Default 0.
//
//==============================================================================

module syndrome_unit
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int FIRST_ROOT   = 0
) (
    input  logic                                  aclk,
    input  logic                                  aresetn,
    input  logic                                  i_step,
    input  logic                                  i_first,
    input  logic [SYMBOL_WIDTH-1:0]               i_data,
    output logic [2*T_SYMBOLS*SYMBOL_WIDTH-1:0]   ow_synd,
    output logic                                  ow_all_zero
);

    localparam int M  = SYMBOL_WIDTH;
    localparam int T2 = 2 * T_SYMBOLS;

    initial begin : param_check
        if (T_SYMBOLS < 1 || T2 > (1 << M) - 2)
            $error("syndrome_unit: T_SYMBOLS %0d out of range for GF(2^%0d)", T_SYMBOLS, M);
    end

    for (genvar i = 0; i < T2; i++) begin : g_cell
        gf_syndrome_cell #(
            .SYMBOL_WIDTH(M),
            .PRIM_POLY   (PRIM_POLY),
            .ROOT_EXP    (FIRST_ROOT + i)
        ) u_cell (
            .aclk   (aclk),
            .aresetn(aresetn),
            .i_step (i_step),
            .i_first(i_first),
            .i_data (i_data),
            .ow_synd(ow_synd[i*M +: M])
        );
    end

    assign ow_all_zero = (ow_synd == '0);

endmodule : syndrome_unit
