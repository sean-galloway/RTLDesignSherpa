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
//   in error when Lambda(X_j^-1) = 0. The cells hold one beat of S positions:
//   cell i holds c_i = Lambda_i * X_j^-i for the beat's first position j, and
//   lane u (position j+u) evaluates sum_i c_i * alpha^(iu) -- a constant
//   multiply per cell and lane. On i_load the cells take Lambda_i *
//   alpha^(-i(n-1)) (position 0, absorbing the shortening offset) and each
//   i_step multiplies cell i by alpha^(iS) to move to the next beat. Then, per
//   lane u,
//
//     o_root[u]    = (sum_i c_i alpha^(iu) == 0)              Lambda(X^-1) == 0
//     o_odd_sum[u] = sum over odd i of c_i alpha^(iu)         = X^-1 * Lambda'(X^-1)
//
//   The odd-index sum is the formal derivative in characteristic 2, handed to
//   the Forney evaluator so the derivative costs nothing extra. Both outputs
//   describe the beat the cells currently hold; the caller counts beats.
//
//   t+1 cells; the load, step and lane multiplies are all by constants (XOR
//   networks), (t+1)(S+2) of them.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t; Lambda_0 .. Lambda_t. Default 8.
//   N_SYMBOLS:    n, the block length (sets the first position). Default 2^m - 1.
//   SYMBOLS_PER_BEAT: S, positions evaluated per beat. Default 1.
//
//==============================================================================

module chien_search
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8,
    parameter int N_SYMBOLS    = (1 << SYMBOL_WIDTH) - 1,
    parameter int SYMBOLS_PER_BEAT = 1
) (
    input  logic                                   aclk,
    input  logic                                   aresetn,
    input  logic                                   i_load,
    input  logic [(T_SYMBOLS+1)*SYMBOL_WIDTH-1:0]  i_lambda,
    input  logic                                   i_step,
    output logic [SYMBOLS_PER_BEAT-1:0]            o_root,
    output logic [SYMBOLS_PER_BEAT*SYMBOL_WIDTH-1:0] o_odd_sum
);

    localparam int M = SYMBOL_WIDTH;
    localparam int T = T_SYMBOLS;
    localparam int N = N_SYMBOLS;
    localparam int S = SYMBOLS_PER_BEAT;

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

        // times alpha^(iS): the step to the next beat
        gf_mul_const #(
            .SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(i * S, M, PRIM_POLY)))
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

    // lane u: cell i contributes c_i * alpha^(iu), a constant multiply
    localparam int LANE_W = (T + 1) * S;

    function automatic logic [LANE_W*M-1:0] build_lane_consts();
        logic [LANE_W*M-1:0] r;
        for (int u = 0; u < S; u++)
            for (int i = 0; i <= T; i++)
                r[(u*(T+1)+i)*M +: M] = gf_alpha_pow(i * u, M, PRIM_POLY)[M-1:0];
        return r;
    endfunction

    localparam logic [LANE_W*M-1:0] LANE_K = build_lane_consts();

    always_comb begin
        for (int u = 0; u < S; u++) begin
            logic [M-1:0] sum, odd, term;
            sum = '0;
            odd = '0;
            for (int i = 0; i <= T; i++) begin
                term = gf_mul_fn(gf_wide_t'(LANE_K[(u*(T+1)+i)*M +: M]), gf_wide_t'(r_c[i]),
                                 M, PRIM_POLY)[M-1:0];
                sum = sum ^ term;
                if (i % 2 == 1) odd = odd ^ term;
            end
            o_root[u]              = (sum == '0);
            o_odd_sum[u*M +: M]    = odd;
        end
    end

endmodule : chien_search
