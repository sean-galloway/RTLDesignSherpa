// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chien_search
// Purpose:
//   Evaluate the error locator at every symbol position of the block, one
//   position per cycle in transmission order, flagging the roots.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: chien_search
//==============================================================================
// Description:
//   Symbol j (j = 0 first transmitted) has location X_j = alpha^(n-1-j); it is
//   in error when Lambda(X_j^-1) = 0. Cell i holds c_i = Lambda_i * X_j^-i:
//   on i_load it takes Lambda_i * alpha^(-i(n-1)) (position 0, a constant
//   multiply that also absorbs the shortening offset), and each i_step
//   multiplies it by alpha^i to move to position j+1. Then
//
//     o_root    = (sum_i c_i == 0)                Lambda(X_j^-1) == 0
//     o_odd_sum = sum over odd i of c_i           = X_j^-1 * Lambda'(X_j^-1)
//
//   The odd-index sum is the formal derivative in characteristic 2, handed to
//   the Forney evaluator so the derivative costs nothing extra. Both outputs
//   describe the position the cells currently hold; the caller counts j.
//
//   t+1 cells, each a gf_mul_const for the load and one for the step.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t; Lambda_0 .. Lambda_t. Default 8.
//   N_SYMBOLS:    n, the block length (sets the first position). Default 2^m - 1.
//
//==============================================================================

module chien_search
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int N_SYMBOLS    = (1 << SYMBOL_WIDTH) - 1
) (
    input  logic                                   aclk,
    input  logic                                   aresetn,
    input  logic                                   i_load,
    input  logic [(T_SYMBOLS+1)*SYMBOL_WIDTH-1:0]  i_lambda,
    input  logic                                   i_step,
    output logic                                   o_root,
    output logic [SYMBOL_WIDTH-1:0]                o_odd_sum
);

    localparam int M = SYMBOL_WIDTH;
    localparam int T = T_SYMBOLS;
    localparam int N = N_SYMBOLS;

    initial begin : param_check
        if (N < 2 * T + 1 || N > (1 << M) - 1)
            $error("chien_search: N_SYMBOLS %0d out of range for t = %0d, m = %0d", N, T, M);
    end

    logic [M-1:0] r_c     [T+1];
    logic [M-1:0] w_c_init[T+1];
    logic [M-1:0] w_c_step[T+1];

    for (genvar i = 0; i <= T; i++) begin : g_cell
        // Lambda_i * alpha^(-i(n-1)): the value at position 0
        gf_mul_const #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(-i * (N - 1), M, PRIM_POLY)))
        ) u_init (.i_a(i_lambda[i*M +: M]), .ow_p(w_c_init[i]));

        // times alpha^i: the step to position j+1
        gf_mul_const #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(i, M, PRIM_POLY)))
        ) u_step (.i_a(r_c[i]), .ow_p(w_c_step[i]));

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_c[i] <= '0;
            end else if (i_load) begin
                r_c[i] <= w_c_init[i];
            end else if (i_step) begin
                r_c[i] <= w_c_step[i];
            end
        )
    end

    logic [M-1:0] w_sum;
    logic [M-1:0] w_odd;

    always_comb begin
        w_sum = '0;
        w_odd = '0;
        for (int i = 0; i <= T; i++) begin
            w_sum = w_sum ^ r_c[i];
            if (i % 2 == 1) w_odd = w_odd ^ r_c[i];
        end
    end

    assign o_root    = (w_sum == '0);
    assign o_odd_sum = w_odd;

endmodule : chien_search
