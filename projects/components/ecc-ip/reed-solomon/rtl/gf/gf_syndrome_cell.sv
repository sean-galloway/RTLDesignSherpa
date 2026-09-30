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
//   s <= (i_first ? 0 : s * alpha^ROOT_EXP) ^ i_data on every i_step. The
//   first symbol of a block carries i_first, so no separate clear is needed
//   and the cell is ready for the next block the cycle after the last symbol
//   of the previous one. After the n-th symbol ow_synd holds
//   sum_j r_j * alpha^(ROOT_EXP * (n-1-j)), the syndrome at that root.
//
//   One gf_mul_const (the root) and an m-bit register.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   ROOT_EXP:     the root's exponent, b + i for syndrome i. Default 0.
//
//==============================================================================

module gf_syndrome_cell
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int ROOT_EXP     = 0
) (
    input  logic                    aclk,
    input  logic                    aresetn,
    input  logic                    i_step,
    input  logic                    i_first,
    input  logic [SYMBOL_WIDTH-1:0] i_data,
    output logic [SYMBOL_WIDTH-1:0] ow_synd
);

    localparam int M    = SYMBOL_WIDTH;
    localparam int ROOT = int'(gf_alpha_pow(ROOT_EXP, M, PRIM_POLY));

    logic [M-1:0] r_s;
    logic [M-1:0] w_s_root;

    gf_mul_const #(
        .SYMBOL_WIDTH(M),
        .PRIM_POLY   (PRIM_POLY),
        .CONST       (ROOT)
    ) u_root (
        .i_a (r_s),
        .ow_p(w_s_root)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_s <= '0;
        end else if (i_step) begin
            r_s <= (i_first ? '0 : w_s_root) ^ i_data;
        end
    )

    assign ow_synd = r_s;

endmodule : gf_syndrome_cell
