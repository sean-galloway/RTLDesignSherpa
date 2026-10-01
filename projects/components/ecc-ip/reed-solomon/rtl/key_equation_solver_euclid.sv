// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: key_equation_solver_euclid
// Purpose:
//   Error-locator and error-evaluator polynomials from the 2t syndromes by
//   the inversionless extended Euclidean algorithm, in at most 2t cycles.
//   Same ports as key_equation_solver_ribm; selected by KES_ALGO = "EUCLID".
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: key_equation_solver_euclid
//==============================================================================
// Description:
//   Extended Euclid on (x^2t, S(x)) until the remainder's degree drops below
//   t; the multiplier of S is Lambda and the remainder is Omega. Division is
//   replaced by cross-multiplication (Shao et al. 1985) and the variable
//   alignment shift by keeping every polynomial TOP-ALIGNED:
//
//     R, Q      2t+1 symbols, leading coefficient at index 2t, nominal
//               degrees degR, degQ
//     lam~, mu~ Lambda * x^(2t-degR) and Mu * x^(2t-degQ) in 2t+3 symbols,
//               so the pair (R, lam~) shifts together and the cross-multiply
//               of the two pairs needs no shifter
//
//   Each cycle does one of:
//     normalise R:  R[2t] == 0            R *= x, lam~ *= x, degR--
//     normalise Q:  Q[2t] == 0            Q *= x, mu~ *= x,  degQ--
//     cross:        Rn = (Q[2t]*R ^ R[2t]*Q) * x,  Ln = (Q[2t]*lam~ ^ R[2t]*mu~) * x
//                   if degR < degQ the old (R, lam~, degR) becomes the divisor
//                   degR = max(degR, degQ) - 1
//   and stops when degR < t. Then Lambda_j = lam~[j + 2t - degR] for
//   j = 0 .. 2t (the top t coefficients are the more-than-t-errors check, as
//   in the riBM solver) and Omega_j = R[j + 2t - degR] for j = 0 .. t-1.
//
//   Omega here is the TEXTBOOK evaluator, S*Lambda mod x^2t, not riBM's high
//   half: the Forney block takes OMEGA_HIGH_HALF = 0 for this solver and the
//   decoder core sets it from KES_ALGO. dv/tbclasses/rs_model.py::euclid is
//   the bit-exact reference; it and the riBM solver decode identically.
//
//   Cost: 2(2t+1) + 2(2t+3) gf_mul (about 8t) plus the four register arrays;
//   the critical path is a multiply, an XOR, and the degree compare that
//   drives the swap -- longer than riBM's, which is why riBM is the default.
//   Latency is data-dependent: t+1 .. 2t cycles plus one for the final check
//   (measured over 3000 blocks per profile in rs_model.py; at t <= 2 a zero
//   leading syndrome costs a normalise step and 2t+1 occurs). The safety stop
//   is at 4t+8.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//   T_SYMBOLS:    t. Default 8.
//
//==============================================================================

module key_equation_solver_euclid
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
    localparam int LW    = T2 + 3;                 // lam~ / mu~ entries
    localparam int DG_W  = $clog2(T2 + 1) + 2;     // signed nominal degrees
    localparam int DEG_W = $clog2(T2 + 1);
    localparam int CYC_W = $clog2(4 * T + 8);

    initial begin : param_check
        if (T < 1 || T2 > (1 << M) - 2)
            $error("key_equation_solver_euclid: T_SYMBOLS %0d out of range for GF(2^%0d)", T, M);
    end

    // -------------------------------------------------------------------------
    // State
    // -------------------------------------------------------------------------
    logic [M-1:0]           r_r  [T2+1];
    logic [M-1:0]           r_q  [T2+1];
    logic [M-1:0]           r_l  [LW];
    logic [M-1:0]           r_mu [LW];
    logic signed [DG_W-1:0] r_deg_r;
    logic signed [DG_W-1:0] r_deg_q;
    logic                   r_busy;
    logic [CYC_W-1:0]       r_cycles;

    logic [M-1:0] w_a;        // R[2t]
    logic [M-1:0] w_b;        // Q[2t]
    logic         w_finished;
    logic         w_norm_r;
    logic         w_norm_q;
    logic         w_cross;
    logic         w_swap;

    logic signed [DG_W-1:0] w_deg_r_nxt, w_deg_q_nxt;
    logic                   w_finished_nxt;

    logic [M-1:0] w_rn [T2+1];   // Q[2t]*R ^ R[2t]*Q, before the shift
    logic [M-1:0] w_ln [LW];     // Q[2t]*lam~ ^ R[2t]*mu~

    assign w_a        = r_r[T2];
    assign w_b        = r_q[T2];
    assign w_finished = (r_deg_r < DG_W'(T)) || (r_deg_q < 0) || (r_cycles == '1);
    assign w_norm_r   = !w_finished && (w_a == '0);
    assign w_norm_q   = !w_finished && (w_a != '0) && (w_b == '0);
    assign w_cross    = !w_finished && (w_a != '0) && (w_b != '0);
    assign w_swap     = (r_deg_r < r_deg_q);

    // The degrees this iteration is about to write. w_finished reads the
    // degrees ALREADY written, so acting on it alone spends a whole cycle
    // merely noticing the solve is over -- on a short codeword that single
    // cycle is the difference between line rate and a gap at every block
    // boundary. Sampling the NEXT degrees lets the last update and o_done
    // land on the same edge; the outputs are combinational off r_l/r_r/
    // r_deg_r, so they are valid in the cycle o_done is visible either way.
    always_comb begin
        w_deg_r_nxt = r_deg_r;
        w_deg_q_nxt = r_deg_q;
        if (w_norm_r) begin
            w_deg_r_nxt = r_deg_r - DG_W'(1);
        end else if (w_norm_q) begin
            w_deg_q_nxt = r_deg_q - DG_W'(1);
        end else if (w_cross) begin
            if (w_swap) begin
                w_deg_q_nxt = r_deg_r;
                w_deg_r_nxt = r_deg_q - DG_W'(1);
            end else begin
                w_deg_r_nxt = r_deg_r - DG_W'(1);
            end
        end
    end

    assign w_finished_nxt = (w_deg_r_nxt < DG_W'(T)) || (w_deg_q_nxt < 0)
                            || ((r_cycles + CYC_W'(1)) == '1);

    for (genvar i = 0; i <= T2; i++) begin : g_r
        logic [M-1:0] w_br, w_aq;
        gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_br (.i_a(w_b), .i_b(r_r[i]), .ow_p(w_br));
        gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_aq (.i_a(w_a), .i_b(r_q[i]), .ow_p(w_aq));
        assign w_rn[i] = w_br ^ w_aq;
    end
    for (genvar i = 0; i < LW; i++) begin : g_l
        logic [M-1:0] w_bl, w_am;
        gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_bl (.i_a(w_b), .i_b(r_l[i]),  .ow_p(w_bl));
        gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_am (.i_a(w_a), .i_b(r_mu[i]), .ow_p(w_am));
        assign w_ln[i] = w_bl ^ w_am;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i <= T2; i++) begin r_r[i] <= '0; r_q[i] <= '0; end
            for (int i = 0; i < LW; i++) begin r_l[i] <= '0; r_mu[i] <= '0; end
            r_deg_r  <= '0;
            r_deg_q  <= '0;
            r_busy   <= 1'b0;
            r_cycles <= '0;
            o_done   <= 1'b0;
        end else begin
            o_done <= 1'b0;
            if (i_start) begin
                // R = x^2t; Q = S(x) top-aligned (S_{2t-1} at index 2t); lam~ = 0; mu~ = x
                for (int i = 0; i <= T2; i++) begin
                    r_r[i] <= (i == T2) ? M'(1) : '0;
                    r_q[i] <= (i == 0) ? '0 : i_synd[(i-1)*M +: M];
                end
                for (int i = 0; i < LW; i++) begin
                    r_l[i]  <= '0;
                    r_mu[i] <= (i == 1) ? M'(1) : '0;
                end
                r_deg_r  <= DG_W'(T2);
                r_deg_q  <= DG_W'(T2 - 1);
                r_busy   <= 1'b1;
                r_cycles <= '0;
            end else if (r_busy) begin
                r_cycles <= r_cycles + CYC_W'(1);
                if (w_finished) begin
                    r_busy <= 1'b0;
                    o_done <= 1'b1;
                end else if (w_norm_r) begin
                    r_r[0] <= '0;
                    r_l[0] <= '0;
                    for (int i = 1; i <= T2; i++) r_r[i] <= r_r[i-1];
                    for (int i = 1; i < LW; i++)  r_l[i] <= r_l[i-1];
                    r_deg_r <= r_deg_r - DG_W'(1);
                end else if (w_norm_q) begin
                    r_q[0]  <= '0;
                    r_mu[0] <= '0;
                    for (int i = 1; i <= T2; i++) r_q[i]  <= r_q[i-1];
                    for (int i = 1; i < LW; i++)  r_mu[i] <= r_mu[i-1];
                    r_deg_q <= r_deg_q - DG_W'(1);
                end else if (w_cross) begin
                    r_r[0] <= '0;
                    r_l[0] <= '0;
                    for (int i = 1; i <= T2; i++) r_r[i] <= w_rn[i-1];
                    for (int i = 1; i < LW; i++)  r_l[i] <= w_ln[i-1];
                    if (w_swap) begin
                        for (int i = 0; i <= T2; i++) r_q[i]  <= r_r[i];
                        for (int i = 0; i < LW; i++)  r_mu[i] <= r_l[i];
                        r_deg_q <= r_deg_r;
                        r_deg_r <= r_deg_q - DG_W'(1);
                    end else begin
                        r_deg_r <= r_deg_r - DG_W'(1);
                    end
                end
                // Retire on the SAME edge as the final update. This is a later
                // non-blocking write to r_busy/o_done than the chain above, so
                // it wins while every array update still lands.
                if (!w_finished && w_finished_nxt) begin
                    r_busy <= 1'b0;
                    o_done <= 1'b1;
                end
            end
        end
    )

    assign o_busy = r_busy;

    // -------------------------------------------------------------------------
    // Outputs: un-shift by 2t - degR (degR is 0 .. t-1 at the end, so the shift
    // is t+1 .. 2t; anything else means the safety stop hit and deg_err says so)
    // -------------------------------------------------------------------------
    logic [DG_W-1:0] w_sh;
    assign w_sh = DG_W'(T2) - r_deg_r;

    always_comb begin
        o_deg     = '0;
        o_deg_err = 1'b0;
        for (int j = 0; j <= T2; j++) begin
            logic [M-1:0] c;
            c = '0;
            for (int i = 0; i < LW; i++)
                if (DG_W'(i) == DG_W'(j) + w_sh) c = r_l[i];
            o_lambda[j*M +: M] = c;
            if (c != '0) begin
                o_deg = DEG_W'(j);
                if (j > T) o_deg_err = 1'b1;
            end
        end
        for (int j = 0; j < T; j++) begin
            logic [M-1:0] c;
            c = '0;
            for (int i = 0; i <= T2; i++)
                if (DG_W'(i) == DG_W'(j) + w_sh) c = r_r[i];
            o_omega[j*M +: M] = c;
        end
        if (r_deg_r < 0 || r_deg_r >= DG_W'(T)) o_deg_err = 1'b1;
    end

endmodule : key_equation_solver_euclid
