// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: forney_evaluator
// Purpose:
//   The error value at the position the Chien search is looking at:
//   e_j = X_j^(1-b-2t) * Omega(X_j^-1) / Lambda'(X_j^-1).
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: forney_evaluator
//==============================================================================
// Description:
//   With the riBM solver Omega is the high half of S(x)Lambda(x), so the
//   exponent is 1 - b - 2t; with the Euclid solver it is the textbook
//   S*Lambda mod x^2t and the exponent is 1 - b (OMEGA_HIGH_HALF selects;
//   dv/tbclasses/rs_model.py proves both against reedsolo). The Chien search
//   supplies X_j^-1 * Lambda'(X_j^-1) as its odd-index sum, which turns the
//   formula into
//
//     e_j = [ X_j^-(b+off) * Omega(X_j^-1) ] / odd_sum,  off = 2t or 0
//
//   and the bracket is a Chien-style walk of its own: cell i holds
//   Omega_i * X_j^-(i+b+2t), loaded at position 0 as
//   Omega_i * alpha^(-(i+b+2t)(n-1)) and stepped by alpha^(i+b+2t). The sum of
//   the t cells is the numerator; one gf_inv and one gf_mul finish it.
//
//   o_den_zero flags odd_sum == 0, which cannot happen at a genuine root and
//   marks the block uncorrectable when it does.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t; Omega_0 .. Omega_{t-1}. Default 8.
//   N_SYMBOLS:    n. Default 2^m - 1.
//   FIRST_ROOT:   b. Default 0.
//
//==============================================================================

module forney_evaluator
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int N_SYMBOLS    = (1 << SYMBOL_WIDTH) - 1,
    parameter int FIRST_ROOT   = 0,
    // 1: Omega is riBM's high half of S*Lambda (exponent offset b + 2t);
    // 0: Omega is the textbook S*Lambda mod x^2t, as the Euclid solver gives (offset b)
    parameter bit OMEGA_HIGH_HALF = 1'b1
) (
    input  logic                               aclk,
    input  logic                               aresetn,
    input  logic                               i_load,
    input  logic [T_SYMBOLS*SYMBOL_WIDTH-1:0]  i_omega,
    input  logic                               i_step,
    input  logic [SYMBOL_WIDTH-1:0]            i_odd_sum,
    output logic [SYMBOL_WIDTH-1:0]            o_err_val,
    output logic                               o_den_zero
);

    localparam int M   = SYMBOL_WIDTH;
    localparam int T   = T_SYMBOLS;
    localparam int N   = N_SYMBOLS;
    localparam int OFF = FIRST_ROOT + (OMEGA_HIGH_HALF ? 2 * T : 0);   // the exponent offset

    logic [M-1:0] r_w     [T];
    logic [M-1:0] w_w_init[T];
    logic [M-1:0] w_w_step[T];

    for (genvar i = 0; i < T; i++) begin : g_cell
        gf_mul_const #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(-(i + OFF) * (N - 1), M, PRIM_POLY)))
        ) u_init (.i_a(i_omega[i*M +: M]), .ow_p(w_w_init[i]));

        gf_mul_const #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(i + OFF, M, PRIM_POLY)))
        ) u_step (.i_a(r_w[i]), .ow_p(w_w_step[i]));

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_w[i] <= '0;
            end else if (i_load) begin
                r_w[i] <= w_w_init[i];
            end else if (i_step) begin
                r_w[i] <= w_w_step[i];
            end
        )
    end

    logic [M-1:0] w_num;
    logic [M-1:0] w_den_inv;

    always_comb begin
        w_num = '0;
        for (int i = 0; i < T; i++) w_num = w_num ^ r_w[i];
    end

    gf_inv #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_inv (
        .i_a(i_odd_sum), .ow_inv(w_den_inv), .ow_zero(o_den_zero));

    gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_mul (
        .i_a(w_num), .i_b(w_den_inv), .ow_p(o_err_val));

endmodule : forney_evaluator
