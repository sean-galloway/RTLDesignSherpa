// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: key_equation_solver_ribm
// Purpose:
//   Error-locator and error-evaluator polynomials from the 2t syndromes in
//   exactly 2t cycles, by the reformulated inversionless Berlekamp-Massey
//   algorithm (Sarwate and Shanbhag, 2001).
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: key_equation_solver_ribm
//==============================================================================
// Description:
//   3t+1 ribm_pe cells hold Delta~ and Theta~. On i_start they load
//   Delta~_i = Theta~_i = S_i for i < 2t, 0 for 2t <= i < 3t, and 1 at 3t;
//   gamma = 1, k = 0. Each of the following 2t cycles is one iteration:
//
//     delta = Delta~_0
//     swap  = (delta != 0) && (k >= 0)
//     cells update (see ribm_pe); gamma <= swap ? delta : gamma;
//     k <= swap ? -k - 1 : k + 1
//
//   After 2t iterations o_done pulses and, until the next i_start:
//     o_lambda = Delta~_{t .. 3t}   (Lambda_0 .. Lambda_2t, 2t+1 coefficients)
//     o_omega  = Delta~_{0 .. t-1}  (the evaluator, see below)
//     o_deg    = degree of Lambda over all 2t+1 coefficients
//     o_deg_err = any of Lambda_{t+1..2t} is nonzero, i.e. more than t errors
//
//   Both polynomials carry the same unknown scale factor, so Chien search
//   finds the same roots and Forney's ratio is unaffected. Note that this
//   evaluator is the HIGH half of S(x)Lambda(x) -- coefficients 2t .. 3t-1 --
//   not the textbook Omega = S*Lambda mod x^2t; the Forney exponent in the
//   evaluator block accounts for it (X^(1 - b - 2t) instead of X^(1 - b)).
//   dv/tbclasses/rs_model.py is the bit-exact reference for all of this.
//
//   Cost: 2(3t+1) gf_mul plus 2(3t+1) m-bit registers; the critical path is
//   one multiply and one XOR and does not grow with t.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t. Default 8.
//
//==============================================================================

module key_equation_solver_ribm
    import gf_pkg::*;
#(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D,
    parameter int T_SYMBOLS    = 8
) (
    input  logic                                     aclk,
    input  logic                                     aresetn,
    input  logic                                     i_start,
    input  logic [2*T_SYMBOLS*SYMBOL_WIDTH-1:0]      i_synd,
    output logic                                     o_busy,
    output logic                                     o_done,
    output logic [(2*T_SYMBOLS+1)*SYMBOL_WIDTH-1:0]  o_lambda,
    output logic [T_SYMBOLS*SYMBOL_WIDTH-1:0]        o_omega,
    output logic [$clog2(2*T_SYMBOLS+1)-1:0]         o_deg,
    output logic                                     o_deg_err
);

    localparam int M     = SYMBOL_WIDTH;
    localparam int T     = T_SYMBOLS;
    localparam int T2    = 2 * T;
    localparam int NPE   = 3 * T + 1;
    localparam int IT_W  = $clog2(T2 + 1);
    localparam int K_W   = IT_W + 2;               // k ranges within +-(2t+1)
    localparam int DEG_W = $clog2(T2 + 1);

    initial begin : param_check
        if (T < 1 || T2 > (1 << M) - 2)
            $error("key_equation_solver_ribm: T_SYMBOLS %0d out of range for GF(2^%0d)", T, M);
    end

    // -------------------------------------------------------------------------
    // Control
    // -------------------------------------------------------------------------
    logic                    r_busy;
    logic [IT_W-1:0]         r_iter;
    logic [M-1:0]            r_gamma;
    logic signed [K_W-1:0]   r_k;
    logic                    w_step;
    logic                    w_swap;
    logic [M-1:0]            w_delta;

    logic [M-1:0] w_d   [NPE+1];   // Delta~_0 .. Delta~_3t, plus a constant 0 above
    logic [M-1:0] w_th  [NPE];
    logic [M-1:0] w_init[NPE];

    assign w_delta   = w_d[0];
    assign w_step    = r_busy;
    assign w_swap    = (w_delta != '0) && (r_k >= 0);
    assign w_d[NPE]  = '0;

    for (genvar i = 0; i < NPE; i++) begin : g_init
        if (i < T2) begin : g_synd
            assign w_init[i] = i_synd[i*M +: M];
        end else if (i == 3 * T) begin : g_one
            assign w_init[i] = M'(1);
        end else begin : g_zero
            assign w_init[i] = '0;
        end
    end

    for (genvar i = 0; i < NPE; i++) begin : g_pe
        ribm_pe #(
            .SYMBOL_WIDTH(M),
            .PRIM_POLY   (PRIM_POLY)
        ) u_pe (
            .aclk        (aclk),
            .aresetn     (aresetn),
            .i_load      (i_start),
            .i_init      (w_init[i]),
            .i_step      (w_step),
            .i_swap      (w_swap),
            .i_gamma     (r_gamma),
            .i_delta     (w_delta),
            .i_delta_next(w_d[i+1]),
            .o_delta     (w_d[i]),
            .o_theta     (w_th[i])
        );
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_busy  <= 1'b0;
            r_iter  <= '0;
            r_gamma <= '0;
            r_k     <= '0;
            o_done  <= 1'b0;
        end else begin
            o_done <= 1'b0;
            if (i_start) begin
                r_busy  <= 1'b1;
                r_iter  <= '0;
                r_gamma <= M'(1);
                r_k     <= '0;
            end else if (r_busy) begin
                r_gamma <= w_swap ? w_delta : r_gamma;
                r_k     <= w_swap ? (-r_k - K_W'(1)) : (r_k + K_W'(1));
                r_iter  <= r_iter + IT_W'(1);
                if (r_iter == IT_W'(T2 - 1)) begin
                    r_busy <= 1'b0;
                    o_done <= 1'b1;
                end
            end
        end
    )

    assign o_busy = r_busy;

    // -------------------------------------------------------------------------
    // Outputs: the array after 2t iterations
    // -------------------------------------------------------------------------
    for (genvar i = 0; i < T; i++) begin : g_omega
        assign o_omega[i*M +: M] = w_d[i];
    end
    for (genvar i = 0; i <= T2; i++) begin : g_lambda
        assign o_lambda[i*M +: M] = w_d[T + i];
    end

    always_comb begin
        o_deg     = '0;
        o_deg_err = 1'b0;
        for (int i = 0; i <= T2; i++) begin
            if (w_d[T + i] != '0) begin
                o_deg = DEG_W'(i);
                if (i > T) o_deg_err = 1'b1;
            end
        end
    end

    // Theta is internal state only; keep lint quiet about the unread copies.
    logic unused_th;
    always_comb begin
        unused_th = 1'b0;
        for (int i = 0; i < NPE; i++) unused_th = unused_th ^ (^w_th[i]);
    end

endmodule : key_equation_solver_ribm
