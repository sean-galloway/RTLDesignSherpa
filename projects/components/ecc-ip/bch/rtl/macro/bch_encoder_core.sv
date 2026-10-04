// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_encoder_core
// Purpose:
//   Systematic binary BCH encoder core: K_BITS data bits in, N_BITS coded
//   bits out, valid/ready at both ends, block boundary on `last`.
//
// Documentation: projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/01_encoder.md
// Subsystem: bch
//
// Author: sean galloway
// Created: 2026-10-03

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: bch_encoder_core
//==============================================================================
// Description:
//   Two phases per block:
//
//   DATA:  each accepted beat steps the GF(2^m) bit-LFSR and passes straight
//          to the output (systematic code) with out_last = 0. `in_last`
//          marks the final data beat; the accepted data-bit count is checked
//          against K_BITS and a mismatch pulses frame_err, but the block is
//          still encoded as given.
//   DRAIN: in_ready is held low while the N_BITS - K_BITS parity bits shift
//          out of the LFSR; the final parity beat carries out_last = 1. The
//          LFSR is all-zero again when the drain ends, so the next block
//          needs no explicit clear.
//
//   BITS_PER_BEAT = B bits travel per beat, bit 0 in the low bit. in_keep
//   says how many are present and must be low-aligned and contiguous; only a
//   block's last data beat may be partial. Data beats pass through with their
//   keep; parity follows in ceil((N-K)/B) beats, the final one partial when B
//   does not divide N-K.
//
//   Throughput: one input beat per cycle while the consumer keeps up; the
//   parity gap is ceil((N_BITS - K_BITS) / BITS_PER_BEAT) cycles. A block
//   therefore costs ceil(K_BITS/B) + ceil((N_BITS-K_BITS)/B) beats.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   FIELD_DIM:     m, the field is GF(2^m). Default 6.
//   PRIM_POLY:     primitive polynomial with bit m set. Default 0x43.
//   T_BITS:        t, correctable bit errors. Default 1.
//   N_BITS:        n, codeword length in bits. Default 63.
//   BITS_PER_BEAT: B, bits per valid/ready beat. Default 8.
//   FIRST_ROOT:    b, first consecutive root of g(x). Default 1.
//   K_BITS:        derived k = n - deg(g); exposed for convenience.
//   SKID_DEPTH:    output skid depth, 2..8. Default 2.
//
//==============================================================================

module bch_encoder_core
    import bch_pkg::*;
    import gf_pkg::*;
#(
    parameter int FIELD_DIM     = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY     = bch_pkg::PRIM_POLY,
    parameter int T_BITS        = bch_pkg::T_BITS,
    parameter int N_BITS        = bch_pkg::N_BITS,
    parameter int BITS_PER_BEAT = bch_pkg::BITS_PER_BEAT,
    parameter int FIRST_ROOT    = bch_pkg::FIRST_ROOT,
    parameter int K_BITS        = N_BITS - bch_degree_g(FIELD_DIM, PRIM_POLY, T_BITS, FIRST_ROOT),
    parameter int SKID_DEPTH    = 2
) (
    input  logic                  aclk,
    input  logic                  aresetn,

    input  logic                  in_valid,
    output logic                  in_ready,
    input  logic [BITS_PER_BEAT-1:0] in_data,
    input  logic [BITS_PER_BEAT-1:0] in_keep,
    input  logic                  in_last,

    output logic                  out_valid,
    input  logic                  out_ready,
    output logic [BITS_PER_BEAT-1:0] out_data,
    output logic [BITS_PER_BEAT-1:0] out_keep,
    output logic                  out_last,

    output logic                  frame_err
);

    localparam int M     = FIELD_DIM;
    localparam int DEG_G = bch_degree_g(M, PRIM_POLY, T_BITS, FIRST_ROOT);
    localparam int N     = N_BITS;
    localparam int K     = K_BITS;
    localparam int B     = BITS_PER_BEAT;
    localparam int CW    = $clog2(B + 1);
    localparam int CNT_W = $clog2(N + B + 1);
    localparam int SK_W  = 1 + B + B;  // {last, keep, data}

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 3 || M > GF_MAX_M)
            $error("bch_encoder_core: FIELD_DIM must be 3..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("bch_encoder_core: PRIM_POLY 0x%0h is not primitive of degree %0d", PRIM_POLY, M);
        if (T_BITS < 1 || 2 * T_BITS > (1 << M) - 2)
            $error("bch_encoder_core: T_BITS %0d out of range for GF(2^%0d)", T_BITS, M);
        if (N < 2 * T_BITS + 1 || N > (1 << M) - 1)
            $error("bch_encoder_core: N_BITS %0d out of range for GF(2^%0d)", N, M);
        if (K < 1)
            $error("bch_encoder_core: K_BITS %0d; N_BITS must exceed deg(g)=%0d", K, DEG_G);
        if (B < 1 || B > K)
            $error("bch_encoder_core: BITS_PER_BEAT %0d out of range 1..K (%0d)", B, K);
        if (SKID_DEPTH < 2 || SKID_DEPTH > 8)
            $error("bch_encoder_core: SKID_DEPTH must be 2..8 (got %0d)", SKID_DEPTH);
    end

    // -------------------------------------------------------------------------
    // Generator polynomial and LFSR state
    // -------------------------------------------------------------------------
    // Generator coefficients are stored in fixed GF_MAX_M-bit lanes, so index
    // by j*GF_MAX_M even though only the low M bits are used.
    localparam logic [DEG_G * GF_MAX_M - 1:0] GEN_PACKED =
        bch_gen_poly_packed(M, PRIM_POLY, T_BITS, FIRST_ROOT)[DEG_G * GF_MAX_M - 1:0];
    localparam logic [DEG_G - 1:0]            GEN_BITS    =
        bch_gen_poly_bits(M, PRIM_POLY, T_BITS, FIRST_ROOT)[DEG_G - 1:0];

    // Packed LFSR state: lane j occupies bits [j*M +: M]; lane 0 is the
    // low-order remainder coefficient, lane DEG_G-1 is the coefficient that
    // shifts out first during the parity drain.
    localparam int ST_W = DEG_G * M;

    function automatic logic [ST_W-1:0] lfsr_step(input logic [ST_W-1:0] r,
                                                   input logic [M-1:0]    d);
        logic [ST_W-1:0] n;
        logic [M-1:0]    fb;
        gf_wide_t        w;
        fb = d ^ r[DEG_G*M-1 -: M];
        for (int j = 0; j < DEG_G; j++) begin
            logic [M-1:0] prev;
            prev = (j == 0) ? '0 : r[(j-1)*M +: M];
            if (GEN_BITS[j]) begin
                w = gf_mul_fn(gf_wide_t'(GEN_PACKED[j * GF_MAX_M +: M]), gf_wide_t'(fb), M, PRIM_POLY);
                n[j*M +: M] = prev ^ w[M-1:0];
            end else begin
                n[j*M +: M] = prev;
            end
        end
        return n;
    endfunction

    // The chain is an unpacked array of packed states, the proven
    // gf_lfsr_encoder idiom: as a packed vector with part-select writes this
    // loop trips Verilator ALWCOMBORDER in the sim build (the lint flow runs
    // -Wno-fatal and misses it); whole-element writes of an unpacked array
    // do not. r_lfsr stays packed -- it is shifted and bit-indexed below.
    // w_in_count is declared here, ahead of its use in the chain mux.
    typedef logic [ST_W-1:0] state_t [B+1];

    logic [ST_W-1:0] r_lfsr;
    state_t          w_chain;
    logic [ST_W-1:0] w_lfsr_next;
    logic [CW-1:0]   w_in_count;

    always_comb begin
        w_chain[0] = r_lfsr;
        for (int u = 0; u < B; u++) begin
            logic [M-1:0] d;
            d = {{(M-1){1'b0}}, in_data[u]};
            w_chain[u+1] = lfsr_step(w_chain[u], d);
        end
        w_lfsr_next = w_chain[B];
        for (int u = 1; u <= B; u++) begin
            if (w_in_count == CW'(u)) w_lfsr_next = w_chain[u];
        end
    end

    // -------------------------------------------------------------------------
    // Control and counters
    // -------------------------------------------------------------------------
    logic             r_drain;
    logic [CNT_W-1:0] r_bit_count;
    logic [CNT_W-1:0] r_parity_count;
    logic [CNT_W-1:0] r_data_count;

    logic             w_skid_wr_valid;
    logic             w_skid_wr_ready;
    logic [SK_W-1:0]  w_skid_wr_data;
    logic [SK_W-1:0]  w_skid_rd_data;

    logic [CNT_W-1:0] w_count_next;
    logic [CW-1:0]    w_par_beat_len;
    logic [B-1:0]     w_par_keep;
    logic [B-1:0]     w_parity_bits;

    assign in_ready        = !r_drain && w_skid_wr_ready;
    assign w_in_count      = CW'(bch_keep_count(64'(in_keep), B));
    assign w_count_next    = r_data_count + CNT_W'(w_in_count);

    // Parity beat length: full except the final partial beat
    logic [CNT_W-1:0] w_par_rem;
    assign w_par_rem     = CNT_W'(N - K) - r_parity_count;
    assign w_par_beat_len = CW'((r_parity_count + CNT_W'(B) >= CNT_W'(N - K))
                                  ? w_par_rem
                                  : CNT_W'(B));

    always_comb begin
        for (int u = 0; u < B; u++)
            w_par_keep[u] = (u < w_par_beat_len);
    end

    // K-map expressions from the MAS, implemented beat-aware:
    //   w_beat_is_parity uses full B because it is a lookahead, not the actual
    //   beat length; w_parity_phase is still false until r_bit_count >= K.
    wire w_beat_is_parity = (r_bit_count + CNT_W'(B) - CNT_W'(1)) >= CNT_W'(K);
    wire w_parity_phase   = r_drain || ((r_bit_count >= CNT_W'(K)) && w_beat_is_parity);
    wire w_enc_out_last   = w_parity_phase && ((r_parity_count + CNT_W'(w_par_beat_len) - CNT_W'(1)) == CNT_W'(N - K - 1));
    wire w_frame_err      = in_last && ((r_data_count + CNT_W'(w_in_count)) != CNT_W'(K));

    // Pack parity bits from the high-order LFSR registers (lane 0 first)
    always_comb begin
        for (int u = 0; u < B; u++) begin
            if (u < w_par_beat_len)
                w_parity_bits[u] = r_lfsr[(DEG_G - 1 - u) * M];
            else
                w_parity_bits[u] = 1'b0;
        end
    end

    // Output select
    always_comb begin
        if (r_drain) begin
            w_skid_wr_valid = 1'b1;
            w_skid_wr_data  = {w_enc_out_last, w_par_keep, w_parity_bits};
        end else begin
            w_skid_wr_valid = in_valid;
            w_skid_wr_data  = {1'b0, in_keep, in_data};
        end
    end

    // -------------------------------------------------------------------------
    // Registers
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_drain        <= 1'b0;
            r_bit_count    <= '0;
            r_parity_count <= '0;
            r_data_count   <= '0;
            frame_err      <= 1'b0;
            r_lfsr         <= '0;
        end else begin
            frame_err <= 1'b0;
            if (in_valid && in_ready) begin
                r_lfsr       <= w_lfsr_next;
                r_data_count <= w_count_next;
                if (in_last) begin
                    r_drain        <= 1'b1;
                    r_bit_count    <= w_count_next;
                    r_parity_count <= '0;
                    frame_err      <= w_frame_err;
                end
            end else if (r_drain && w_skid_wr_ready) begin
                // Shift parity registers by the emitted beat length
                automatic int shift = int'(w_par_beat_len);
                r_lfsr         <= r_lfsr << (shift * M);
                r_parity_count <= r_parity_count + CNT_W'(w_par_beat_len);
                r_bit_count    <= r_bit_count + CNT_W'(w_par_beat_len);
                if (w_enc_out_last) begin
                    r_drain      <= 1'b0;
                    r_data_count <= '0;
                end
            end
        end
    )

    // -------------------------------------------------------------------------
    // Output skid buffer
    // -------------------------------------------------------------------------
    /* verilator lint_off PINCONNECTEMPTY */
    gaxi_skid_buffer #(
        .DATA_WIDTH(SK_W),
        .DEPTH     (SKID_DEPTH)
    ) u_out_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_skid_wr_valid),
        .wr_ready   (w_skid_wr_ready),
        .wr_data    (w_skid_wr_data),
        .count      (),
        .rd_valid   (out_valid),
        .rd_ready   (out_ready),
        .rd_count   (),
        .rd_data    (w_skid_rd_data)
    );
    /* verilator lint_on PINCONNECTEMPTY */

    assign {out_last, out_keep, out_data} = w_skid_rd_data;

endmodule : bch_encoder_core
