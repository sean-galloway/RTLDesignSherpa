// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_key_equation_solver
// Purpose:
//   Inverts the binary BCH key equation from the t odd syndromes to the
//   error-locator polynomial Lambda(x). The even syndromes are rebuilt by
//   squaring the odd ones, then an imported Reed-Solomon riBM array produces
//   Lambda in exactly 2t cycles.
//
// Documentation: projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/03_key_equation_solver.md
// Subsystem: bch
//
// Author: sean galloway
// Created: 2026-10-03

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: bch_key_equation_solver
//==============================================================================
// Description:
//   Combinational syndrome expander + imported key_equation_solver_ribm.
//
//   The input carries the t independent odd syndromes S_first_odd,
//   S_first_odd+2, ... in lane 0..t-1.  The full sequence S_1 .. S_2t is
//   reconstructed: odd positions come from the input lane, even positions are
//   the GF square of the half-index syndrome (S_2j = S_j^2 over GF(2^m)).
//   This matches bch_model._full_syndrome_sequence bit-for-bit.
//
//   Control is a single iteration counter plus completion qualifier: one block
//   outstanding at a time.  in_ready is low while the riBM is busy or while a
//   completed result is waiting for out_ready.
//
//   out_lambda carries Lambda_0 .. Lambda_T (the low t+1 riBM lanes).  When
//   any higher coefficient is nonzero the block flags out_more_than_t and
//   clamps out_lambda_degree to T; otherwise the degree is the true locator
//   degree.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   FIELD_DIM:  m, the field is GF(2^m). Default from bch_pkg.
//   PRIM_POLY:  primitive polynomial with bit m set. Default from bch_pkg.
//   T_BITS:     t, correctable bit errors. Default from bch_pkg.
//   FIRST_ROOT: b, first consecutive root of g(x). Default from bch_pkg.
//               Guarded to <= 1 because the golden model only supports the
//               narrow-sense / CCSDS cases where the first odd root is 1.
//   KES_ALGO:   solver algorithm.  Only "RIBM" is implemented today.
//
//==============================================================================

module bch_key_equation_solver
    import bch_pkg::*;
    import gf_pkg::*;
#(
    parameter int FIELD_DIM = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY = bch_pkg::PRIM_POLY,
    parameter int T_BITS    = bch_pkg::T_BITS,
    parameter int N_BITS    = bch_pkg::N_BITS,
    parameter int FIRST_ROOT = bch_pkg::FIRST_ROOT,
    parameter string KES_ALGO = "RIBM"
) (
    input  logic                                 aclk,
    input  logic                                 aresetn,

    input  logic                                 in_valid,
    output logic                                 in_ready,
    input  logic [T_BITS*FIELD_DIM-1:0]          in_syndromes,

    output logic                                 out_valid,
    input  logic                                 out_ready,
    output logic [(T_BITS+1)*FIELD_DIM-1:0]      out_lambda,
    output logic [$clog2(T_BITS+1)-1:0]          out_lambda_degree,
    output logic                                 out_more_than_t
);

    localparam int M     = FIELD_DIM;
    localparam int T     = T_BITS;
    localparam int TWOT = 2 * T;
    localparam int DEGW = $clog2(T + 1);

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 3 || M > GF_MAX_M)
            $error("bch_key_equation_solver: FIELD_DIM must be 3..%0d (got %0d)", GF_MAX_M, M);
        if (T < 1 || TWOT > (1 << M) - 2)
            $error("bch_key_equation_solver: T_BITS %0d out of range for GF(2^%0d)", T, M);
        if (N_BITS < TWOT + 1 || N_BITS > (1 << M) - 1)
            $error("bch_key_equation_solver: N_BITS %0d out of range for GF(2^%0d)", N_BITS, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("bch_key_equation_solver: PRIM_POLY 0x%0h is not primitive of degree %0d",
                   PRIM_POLY, M);
        if (FIRST_ROOT > 1)
            $error("bch_key_equation_solver: FIRST_ROOT %0d > 1 is not supported",
                   FIRST_ROOT);
        if (KES_ALGO != "RIBM")
            $error("bch_key_equation_solver: KES_ALGO '%s' not implemented (only 'RIBM' supported)",
                   KES_ALGO);
    end

    // -------------------------------------------------------------------------
    // Syndrome expander: S_1 .. S_2t from the t odd input lanes
    // -------------------------------------------------------------------------
    logic [M-1:0] w_full [TWOT];

    always_comb begin : syndrome_expander
        gf_wide_t w_sq;
        w_sq = '0;
        for (int i = 1; i <= TWOT; i++) begin
            if (i % 2 == 1) begin
                // lane j holds S_{first_odd + 2j}; for FIRST_ROOT <= 1 first_odd == 1
                w_full[i - 1] = in_syndromes[((i - 1) / 2) * M +: M];
            end else begin
                w_sq = gf_mul_fn(gf_wide_t'(w_full[i/2 - 1]),
                                 gf_wide_t'(w_full[i/2 - 1]),
                                 M, PRIM_POLY) & gf_mask(M);
                w_full[i - 1] = w_sq[M - 1:0];
            end
        end
    end

    logic [TWOT*M-1:0] w_i_synd;
    always_comb begin : pack_syndromes
        for (int i = 0; i < TWOT; i++) begin
            w_i_synd[i * M +: M] = w_full[i];
        end
    end

    // -------------------------------------------------------------------------
    // Imported riBM array
    // -------------------------------------------------------------------------
    logic              w_start;
    logic              w_ribm_done;
    logic              w_ribm_busy;
    logic [(TWOT+1)*M-1:0] w_ribm_lambda;
    logic [T*M-1:0]    w_ribm_omega;
    logic [$clog2(TWOT+1)-1:0] w_ribm_deg;
    logic              w_ribm_deg_err;

    logic [$clog2(TWOT+1)-1:0] w_erasure_count;
    assign w_erasure_count = '0;

    key_equation_solver_ribm #(
        .SYMBOL_WIDTH    (M),
        .PRIM_POLY       (PRIM_POLY),
        .T_SYMBOLS       (T),
        .ERASURE_SUPPORT (0)
    ) u_ribm (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .i_start        (w_start),
        .i_synd         (w_i_synd),
        .i_erasure_count(w_erasure_count),
        .o_busy         (w_ribm_busy),
        .o_done         (w_ribm_done),
        .o_lambda       (w_ribm_lambda),
        .o_omega        (w_ribm_omega),
        .o_deg          (w_ribm_deg),
        .o_deg_err      (w_ribm_deg_err)
    );

    // Sink the unread evaluator; keep lint quiet about it.
    logic unused_omega;
    always_comb begin
        unused_omega = 1'b0;
        for (int i = 0; i < T; i++)
            unused_omega = unused_omega ^ (^w_ribm_omega[i * M +: M]);
    end

    // -------------------------------------------------------------------------
    // Output readout: Lambda_0 .. Lambda_t, degree, and more-than-t flag
    // -------------------------------------------------------------------------
    for (genvar i = 0; i <= T; i++) begin : g_lambda
        assign out_lambda[i * M +: M] = w_ribm_lambda[i * M +: M];
    end

    assign out_more_than_t = w_ribm_deg_err;
    assign out_lambda_degree = w_ribm_deg_err ? DEGW'(T) : DEGW'(w_ribm_deg);

    // -------------------------------------------------------------------------
    // Control: single outstanding block, no FSM
    // -------------------------------------------------------------------------
    logic r_out_valid;

    assign in_ready = !w_ribm_busy && !r_out_valid;
    assign w_start  = in_valid && in_ready;
    assign out_valid = r_out_valid;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_out_valid <= 1'b0;
        end else begin
            if (w_ribm_done) begin
                r_out_valid <= 1'b1;
            end else if (r_out_valid && out_ready) begin
                r_out_valid <= 1'b0;
            end
        end
    )

endmodule : bch_key_equation_solver
