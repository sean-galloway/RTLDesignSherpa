// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gf_syndrome_cell
// Purpose:
//   One syndrome accumulator: S = r(alpha^ROOT_EXP) by Horner's rule as the
//   received symbols arrive in transmission order.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: gf_syndrome_cell
//==============================================================================
// Description:
//   One Horner step is s <= s * alpha^ROOT_EXP ^ symbol; an i_step applies
//   i_count of them (1 .. S, the low lanes of i_data first), with the state
//   zeroed first when i_first marks the block's first beat. The first beat of
//   a block carries i_first, so no separate clear is needed and the cell is
//   ready for the next block the cycle after the last beat of the previous
//   one. After the n-th symbol ow_synd holds sum_j r_j * alpha^(ROOT_EXP *
//   (n-1-j)), the syndrome at that root. The S steps are unrolled; the root
//   multiply is constant, so the chain is one XOR network.
//
//   ow_next is the combinational next value, so a caller that sees the block's
//   last symbol can take the finished syndrome in the same cycle instead of
//   waiting a clock for the register.
//
//   One gf_mul_const (the root) and an m-bit register.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   ROOT_EXP:     the root's exponent, b + i for syndrome i. Default 0.
//   SYMBOLS_PER_BEAT: S. Default 1.
//
//==============================================================================

module gf_syndrome_cell
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int ROOT_EXP     = 0,
    parameter int SYMBOLS_PER_BEAT = 1
) (
    input  logic                                     aclk,
    input  logic                                     aresetn,
    input  logic                                     i_step,
    input  logic                                     i_first,
    input  logic [SYMBOLS_PER_BEAT*SYMBOL_WIDTH-1:0] i_data,
    input  logic [$clog2(SYMBOLS_PER_BEAT+1)-1:0]    i_count,
    output logic [SYMBOL_WIDTH-1:0]                  ow_synd,
    output logic [SYMBOL_WIDTH-1:0]                  ow_next    // the value ow_synd takes if i_step is high now
);

    localparam int M    = SYMBOL_WIDTH;
    localparam int S    = SYMBOLS_PER_BEAT;
    localparam int ROOT = int'(gf_alpha_pow(ROOT_EXP, M, PRIM_POLY));

    logic [M-1:0] r_s;
    logic [M-1:0] w_chain [S+1];
    logic [M-1:0] w_next;

    always_comb begin
        w_chain[0] = i_first ? '0 : r_s;
        for (int u = 0; u < S; u++)
            w_chain[u+1] = gf_mul_fn(gf_wide_t'(ROOT), gf_wide_t'(w_chain[u]), M, PRIM_POLY)[M-1:0]
                           ^ i_data[u*M +: M];
        w_next = w_chain[S];
        for (int u = 1; u <= S; u++)
            if (i_count == ($clog2(S+1))'(u)) w_next = w_chain[u];
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_s <= '0;
        end else if (i_step) begin
            r_s <= w_next;
        end
    )

    assign ow_synd = r_s;
    assign ow_next = w_next;

endmodule : gf_syndrome_cell
