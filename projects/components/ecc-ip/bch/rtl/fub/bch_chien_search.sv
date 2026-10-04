// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_chien_search
// Purpose:
//   Evaluate the error locator polynomial Lambda(x) at every bit position of
//   the received BCH codeword and flag the roots. Because the code is binary,
//   every root is a bit-flip location and no Forney stage is needed.
//
//   This block emits beat-wide root flags in transmission order and a running
//   root count. The decoder core qualifies the raw root flags with the final
//   correctability verdict at correction time; this fub has no correctability
//   input (the MAS internals describe a decoder-core function, not this block).
//
// Documentation: projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/04_chien_search.md
// Subsystem: bch
//
// Author: sean galloway
// Created: 2026-10-03

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: bch_chien_search
//==============================================================================
// Description:
//   Position p (p = 0 first transmitted) has location X_p = alpha^(N-1-p); it
//   is in error when Lambda(X_p^-1) = 0. T_BITS+1 Horner cells hold the
//   coefficient contributions for the beat's first position; lane u evaluates
//   the inner sum for position p+u:
//
//     Lambda(X_{p+u}^-1) = sum_i Lambda_i * alpha^(-i*(N-1-p-u))
//                        = sum_i (Lambda_i * alpha^(-i*(N-1-p))) * alpha^(i*u)
//
//   On i_load the cells take Lambda_i * alpha^(-i*(N-1)) (position 0). Each
//   i_step multiplies cell i by alpha^(i*BITS_PER_BEAT) to move to the next
//   beat. Lane u therefore evaluates position p+u.
//
//   The position counter ranges 0 .. N_BITS-1 and drives out_last. Roots in
//   positions beyond N_BITS-1 in the final partial beat are suppressed.
//
//   Throughput: ceil(N_BITS / BITS_PER_BEAT) cycles per block, single
//   outstanding block (the decoder core pipelines whole blocks, not walks).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   FIELD_DIM:     m, the field is GF(2^m). Default bch_pkg::FIELD_DIM.
//   PRIM_POLY:     primitive polynomial with bit m set. Default bch_pkg::PRIM_POLY.
//   T_BITS:        t, correctable bit errors. Default bch_pkg::T_BITS.
//   N_BITS:        n, received codeword length in bits. Default bch_pkg::N_BITS.
//   BITS_PER_BEAT: B, bits per valid/ready beat. Default bch_pkg::BITS_PER_BEAT.
//
//==============================================================================

module bch_chien_search
    import bch_pkg::*;
    import gf_pkg::*;
#(
    parameter int FIELD_DIM     = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY     = bch_pkg::PRIM_POLY,
    parameter int T_BITS        = bch_pkg::T_BITS,
    parameter int N_BITS        = bch_pkg::N_BITS,
    parameter int BITS_PER_BEAT = bch_pkg::BITS_PER_BEAT
) (
    input  logic                                       aclk,
    input  logic                                       aresetn,

    input  logic                                       in_valid,
    output logic                                       in_ready,
    input  logic [(T_BITS + 1) * FIELD_DIM - 1 : 0]   in_lambda,
    /* verilator lint_off UNUSEDSIGNAL */
    input  logic [$clog2(T_BITS + 1) - 1 : 0]          in_lambda_degree,
    /* verilator lint_on UNUSEDSIGNAL */

    output logic                                       out_valid,
    input  logic                                       out_ready,
    output logic [BITS_PER_BEAT - 1 : 0]               out_flip_en,
    output logic [$clog2(T_BITS + 1) - 1 : 0]          out_root_count,
    output logic                                       out_last
);

    localparam int M      = FIELD_DIM;
    localparam int T      = T_BITS;
    localparam int N      = N_BITS;
    localparam int B      = BITS_PER_BEAT;
    localparam int CNT_W  = $clog2(N + B);
    localparam int RC_W   = $clog2(T + 1);

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 3 || M > GF_MAX_M)
            $error("bch_chien_search: FIELD_DIM must be 3..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("bch_chien_search: PRIM_POLY 0x%0h is not primitive of degree %0d", PRIM_POLY, M);
        if (T < 1 || 2 * T > (1 << M) - 2)
            $error("bch_chien_search: T_BITS %0d out of range for GF(2^%0d)", T, M);
        if (N < 2 * T + 1 || N > (1 << M) - 1)
            $error("bch_chien_search: N_BITS %0d out of range for GF(2^%0d), T=%0d", N, M, T);
        if (B < 1 || B > N)
            $error("bch_chien_search: BITS_PER_BEAT %0d out of range 1..N (%0d)", B, N);
    end

    // -------------------------------------------------------------------------
    // Control
    // -------------------------------------------------------------------------
    logic             w_in_fire;
    logic             w_out_fire;
    logic             w_last;
    logic [CNT_W-1:0] r_position;
    logic             r_out_valid;
    logic [RC_W-1:0]  r_root_count;
    logic             w_load;
    logic             w_step;

    assign w_in_fire  = in_valid && in_ready;
    assign w_out_fire = out_valid && out_ready;
    assign w_last     = (r_position + CNT_W'(B)) >= CNT_W'(N);
    assign w_load     = w_in_fire;
    assign w_step     = w_out_fire && !w_last;

    assign in_ready   = !r_out_valid;
    assign out_valid  = r_out_valid;
    assign out_last   = w_last;

    // -------------------------------------------------------------------------
    // Horner cells: one per locator coefficient
    // -------------------------------------------------------------------------
    logic [M-1:0] r_c     [T+1];
    logic [M-1:0] w_c_init[T+1];
    logic [M-1:0] w_c_step[T+1];

    for (genvar i = 0; i <= T; i++) begin : g_cell
        gf_mul_const #(
            .SYMBOL_WIDTH(M),
            .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(-i * (N - 1), M, PRIM_POLY)))
        ) u_init (
            .i_a(in_lambda[i*M +: M]),
            .ow_p(w_c_init[i])
        );

        gf_mul_const #(
            .SYMBOL_WIDTH(M),
            .PRIM_POLY(PRIM_POLY),
            .CONST(int'(gf_alpha_pow(i * B, M, PRIM_POLY)))
        ) u_step (
            .i_a(r_c[i]),
            .ow_p(w_c_step[i])
        );

        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn)) begin
                r_c[i] <= '0;
            end else if (w_load) begin
                r_c[i] <= w_c_init[i];
            end else if (w_step) begin
                r_c[i] <= w_c_step[i];
            end
        )
    end

    // -------------------------------------------------------------------------
    // Lane evaluation: B positions per beat
    // -------------------------------------------------------------------------
    localparam int LANE_W = (T + 1) * B;

    function automatic logic [LANE_W*M-1:0] build_lane_consts();
        logic [LANE_W*M-1:0] r;
        /* verilator lint_off UNUSEDSIGNAL */
        gf_wide_t            v;
        /* verilator lint_on UNUSEDSIGNAL */
        r = '0;
        for (int u = 0; u < B; u++)
            for (int i = 0; i <= T; i++) begin
                v = gf_alpha_pow(i * u, M, PRIM_POLY);
                r[(u*(T+1)+i)*M +: M] = v[M-1:0];
            end
        return r;
    endfunction

    localparam logic [LANE_W*M-1:0] LANE_K = build_lane_consts();

    logic [B-1:0] w_root;
    logic [B-1:0] w_pos_valid;

    always_comb begin
        for (int u = 0; u < B; u++) begin
            logic [M-1:0] sum, term;
            /* verilator lint_off UNUSEDSIGNAL */
            gf_wide_t     w;
            /* verilator lint_on UNUSEDSIGNAL */
            sum = '0;
            for (int i = 0; i <= T; i++) begin
                w    = gf_mul_fn(gf_wide_t'(LANE_K[(u*(T+1)+i)*M +: M]),
                                 gf_wide_t'(r_c[i]), M, PRIM_POLY);
                term = w[M-1:0];
                sum  = sum ^ term;
            end
            w_root[u] = (sum == '0);
        end
    end

    always_comb begin
        for (int u = 0; u < B; u++) begin
            w_pos_valid[u] = (CNT_W'(r_position) + CNT_W'(u)) < CNT_W'(N);
        end
    end

    // -------------------------------------------------------------------------
    // Beat outputs
    // -------------------------------------------------------------------------
    logic [RC_W-1:0] w_beat_root_count;

    always_comb begin
        w_beat_root_count = '0;
        for (int u = 0; u < B; u++) begin
            if (w_pos_valid[u] && w_root[u]) begin
                w_beat_root_count = w_beat_root_count + RC_W'(1);
            end
        end
    end

    assign out_flip_en    = w_root & w_pos_valid;
    assign out_root_count = r_root_count + w_beat_root_count;

    // -------------------------------------------------------------------------
    // Position and running-count state
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_position   <= '0;
            r_out_valid  <= 1'b0;
            r_root_count <= '0;
        end else begin
            if (w_load) begin
                r_position   <= '0;
                r_out_valid  <= 1'b1;
                r_root_count <= '0;
            end else if (w_out_fire) begin
                if (w_last) begin
                    r_out_valid <= 1'b0;
                    r_position  <= '0;
                end else begin
                    r_position   <= r_position + CNT_W'(B);
                    r_root_count <= out_root_count;
                end
            end
        end
    )

endmodule : bch_chien_search
