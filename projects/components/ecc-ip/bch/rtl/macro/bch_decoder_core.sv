// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_decoder_core
// Purpose:
//   Binary BCH decoder core: N_BITS received bits in, K_BITS corrected data
//   bits out with a per-block verdict, valid/ready at both ends, block boundary
//   on `last`. Integrates the syndrome unit, key-equation solver, and Chien
//   search fubs with one minimal control FSM.
//
// Documentation: projects/components/ecc-ip/bch/docs/bch_mas/ch02_blocks/05_decoder_core.md
// Subsystem: bch
//
// Author: sean galloway
// Created: 2026-10-03

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: bch_decoder_core
//==============================================================================
// Description:
//   Six-state block sequencer (IDLE / SYND / SOLVE / CHIEN / RECHECK / RELEASE)
//   around the three gate-green BCH fubs. The core is single outstanding: a block is
//   fully received before the next one can start. Block-level pipelining is
//   PRD D6 / TASK-005 follow-on work.
//
//   SYND:   received beats are written into a register buffer while the first
//           syndrome unit accumulates. A correctly framed block (exactly N
//           bits) either bypasses SOLVE/CHIEN/RECHECK when the syndromes are all
//           zero or proceeds to SOLVE. A mis-framed block enters the RELEASE
//           passthrough path after the syndrome unit is flushed to N bits.
//   SOLVE:  the key-equation solver runs 2t cycles on the odd syndromes.
//   CHIEN:  the Chien search walks the N bit positions; each beat's raw flip
//           mask is stored, and the corrected beat is fed to an optional second
//           syndrome unit for the re-check.
//   RECHECK: one-cycle wait for the optional second syndrome unit to finish so
//            the verdict can include its zero-syndrome result. Skipped when
//            ENABLE_RECHECK is 0.
//   RELEASE: the buffered block is emitted. Corrections are applied here and
//            only when the final verdict says the block is correctable; an
//            uncorrectable or frame-err block leaves bit-for-bit unchanged.
//            The verdict uses {degree <= t, root_count == degree, recheck zero}.
//
//   The corrected-stream re-check is gated by ENABLE_RECHECK. With it on, the
//            block is declared uncorrectable if the re-computed odd syndromes
//            are non-zero -- this is the R2 "never silently pass a failed
//            block" property. With it off, the verdict omits the re-check
//            (documented weaker posture).
//
//   Output framing: status sideband is valid on every emitted beat and may be
//   sampled with out_last. Correctable/no-error/uncorrectable blocks emit the
//   first K_BITS in ceil(K_BITS/BITS_PER_BEAT) beats; frame-err blocks emit
//   every received bit that was buffered.
//
//   Over-long blocks (issue #90): a block whose bit count reaches N without
//   in_last, or overshoots N, is a framing violation. The core keeps
//   accepting it (buffered up to BEATS_N beats; the surplus is dropped),
//   declares frame_err when in_last arrives, emits the buffered prefix, and
//   clears the syndrome unit so the next block starts clean -- a runaway
//   stream can stall the pipeline but can never deadlock it. Inter-block
//   pipelining stays open under PRD D6.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   FIELD_DIM, PRIM_POLY, T_BITS, N_BITS, BITS_PER_BEAT, FIRST_ROOT: as in the
//        encoder and the fubs.
//   K_BITS: derived k = n - deg(g); exposed for convenience.
//   ENABLE_RECHECK: 1 = run a second syndrome unit over the corrected stream
//        and include its zero-syndrome result in the verdict (default).
//
//==============================================================================

module bch_decoder_core
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
    parameter bit  ENABLE_RECHECK = 1
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

    output logic                  out_status_ok,
    output logic [$clog2(T_BITS+1)-1:0] out_status_corrected,
    output logic                  out_status_uncorrectable,
    output logic                  out_status_frame_err
);

    localparam int M        = FIELD_DIM;
    localparam int T        = T_BITS;
    localparam int N        = N_BITS;
    localparam int B        = BITS_PER_BEAT;
    localparam int K        = K_BITS;
    localparam int CW       = $clog2(B + 1);
    localparam int CNT_W    = $clog2(N + B + 1);
    localparam int BEATS_N  = (N + B - 1) / B;
    localparam int BEATS_K  = (K + B - 1) / B;
    localparam int STATUS_W = $clog2(T + 1);
    localparam int BEAT_W   = $clog2(BEATS_N + 1);

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 3 || M > GF_MAX_M)
            $error("bch_decoder_core: FIELD_DIM must be 3..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("bch_decoder_core: PRIM_POLY 0x%0h is not primitive of degree %0d", PRIM_POLY, M);
        if (T < 1 || 2 * T > (1 << M) - 2)
            $error("bch_decoder_core: T_BITS %0d out of range for GF(2^%0d)", T, M);
        if (N < 2 * T + 1 || N > (1 << M) - 1)
            $error("bch_decoder_core: N_BITS %0d out of range for GF(2^%0d)", N, M);
        if (K < 1)
            $error("bch_decoder_core: K_BITS %0d; N_BITS must exceed deg(g)", K);
        if (B < 1 || B > K)
            $error("bch_decoder_core: BITS_PER_BEAT %0d out of range 1..K (%0d)", B, K);
    end

    // -------------------------------------------------------------------------
    // FSM and datapath registers
    // -------------------------------------------------------------------------
    typedef enum logic [2:0] {IDLE, SYND, SOLVE, CHIEN, RECHECK, RELEASE} state_t;
    state_t r_state;

    // Block buffer: received beats and per-beat flip masks
    logic [B-1:0] r_buf      [BEATS_N];
    logic [B-1:0] r_buf_keep [BEATS_N];
    logic [B-1:0] r_flip     [BEATS_N];

    // SYND counters / framing
    logic [CNT_W-1:0] r_rx_bit_count;
    logic [BEAT_W-1:0] r_rx_beat_count;
    logic              r_frame_err;
    logic              r_over_n;
    logic [BEAT_W-1:0] r_rx_beats_total;
    logic              r_block_ending;
    logic              r_synd_flush;
    logic [CNT_W-1:0]  r_flush_rem;

    // Solver result
    logic [STATUS_W-1:0] r_lambda_degree;
    logic              r_more_than_t;
    logic              r_solver_started;

    // CHIEN / RELEASE
    logic [BEAT_W-1:0] r_chien_beat_count;
    logic [STATUS_W-1:0] r_chien_root_count;
    logic [BEAT_W-1:0] r_release_idx;
    logic [BEAT_W-1:0] r_release_beats;
    logic              r_release_apply;

    // Status register (valid throughout RELEASE)
    logic              r_st_ok;
    logic [STATUS_W-1:0] r_st_corrected;
    logic              r_st_uncorrectable;
    logic              r_st_frame_err;

    // -------------------------------------------------------------------------
    // First syndrome unit (received-block syndromes)
    // -------------------------------------------------------------------------
    logic              w_synd_in_ready;
    logic              w_synd_out_valid;
    logic              w_synd_out_ready;
    logic [T*M-1:0]    w_synd_out_syndromes;
    logic              w_synd_out_no_error;
    logic              w_synd_clear;

    // During a SYND flush we feed zero padding into the syndrome unit so it
    // reaches N_BITS and can be handshaked clean for the next block.
    logic [B-1:0]      w_flush_keep;
    logic [CW-1:0]     w_flush_count;
    logic [B-1:0]      w_synd_in_data;
    logic [B-1:0]      w_synd_in_keep;
    logic              w_synd_in_valid;

    bch_syndrome_unit #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .BITS_PER_BEAT(BITS_PER_BEAT), .FIRST_ROOT(FIRST_ROOT)
    ) u_synd (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .in_valid    (w_synd_in_valid),
        .in_ready    (w_synd_in_ready),
        .in_data     (w_synd_in_data),
        .in_keep     (w_synd_in_keep),
        .in_last     (in_last),
        .i_clear     (w_synd_clear),
        .out_valid   (w_synd_out_valid),
        .out_ready   (w_synd_out_ready),
        .out_syndromes(w_synd_out_syndromes),
        .out_no_error(w_synd_out_no_error)
    );

    // -------------------------------------------------------------------------
    // Key-equation solver
    // -------------------------------------------------------------------------
    logic              w_kes_in_ready;
    logic              w_kes_out_valid;
    logic              w_kes_out_ready;
    logic [(T+1)*M-1:0] w_kes_out_lambda;
    logic [STATUS_W-1:0] w_kes_out_lambda_degree;
    logic              w_kes_out_more_than_t;

    bch_key_equation_solver #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .FIRST_ROOT(FIRST_ROOT)
    ) u_kes (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .in_valid       ((r_state == SOLVE) && !r_solver_started),
        .in_ready       (w_kes_in_ready),
        .in_syndromes   (w_synd_out_syndromes),
        .out_valid      (w_kes_out_valid),
        .out_ready      (w_kes_out_ready),
        .out_lambda     (w_kes_out_lambda),
        .out_lambda_degree(w_kes_out_lambda_degree),
        .out_more_than_t(w_kes_out_more_than_t)
    );

    // -------------------------------------------------------------------------
    // Chien search
    // -------------------------------------------------------------------------
    logic              w_chien_in_ready;
    logic              w_chien_out_valid;
    logic              w_chien_out_ready;
    logic [B-1:0]      w_chien_out_flip_en;
    logic [STATUS_W-1:0] w_chien_out_root_count;
    logic              w_chien_out_last;

    bch_chien_search #(
        .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
        .N_BITS(N_BITS), .BITS_PER_BEAT(BITS_PER_BEAT)
    ) u_chien (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .in_valid       ((r_state == SOLVE) && w_kes_out_valid),
        .in_ready       (w_chien_in_ready),
        .in_lambda      (w_kes_out_lambda),
        .in_lambda_degree(r_lambda_degree),
        .out_valid      (w_chien_out_valid),
        .out_ready      (w_chien_out_ready),
        .out_flip_en    (w_chien_out_flip_en),
        .out_root_count (w_chien_out_root_count),
        .out_last       (w_chien_out_last)
    );

    // -------------------------------------------------------------------------
    // Re-check syndrome unit (optional)
    // -------------------------------------------------------------------------
    logic              w_rechk_in_ready;
    logic              w_rechk_out_valid;
    logic              w_rechk_out_ready;
    logic              w_rechk_out_no_error;
    logic [B-1:0]      w_rechk_keep;
    logic [B-1:0]      w_rechk_data;

    if (ENABLE_RECHECK) begin : g_rechk
        /* verilator lint_off PINCONNECTEMPTY */
        bch_syndrome_unit #(
            .FIELD_DIM(FIELD_DIM), .PRIM_POLY(PRIM_POLY), .T_BITS(T_BITS),
            .N_BITS(N_BITS), .BITS_PER_BEAT(BITS_PER_BEAT), .FIRST_ROOT(FIRST_ROOT)
        ) u_rechk (
            .aclk        (aclk),
            .aresetn     (aresetn),
            .in_valid    (w_chien_out_valid && (r_state == CHIEN)),
            .in_ready    (w_rechk_in_ready),
            .in_data     (w_rechk_data),
            .in_keep     (w_rechk_keep),
            .in_last     (w_chien_out_last),
            .i_clear     (1'b0),
            .out_valid   (w_rechk_out_valid),
            .out_ready   (w_rechk_out_ready),
            .out_syndromes(),
            .out_no_error(w_rechk_out_no_error)
        );
        /* verilator lint_on PINCONNECTEMPTY */
    end else begin : g_no_rechk
        assign w_rechk_in_ready   = 1'b0;
        assign w_rechk_out_valid  = 1'b0;
        assign w_rechk_out_no_error = 1'b1;
    end

    // -------------------------------------------------------------------------
    // Combinational helpers
    // -------------------------------------------------------------------------
    logic [CW-1:0]     w_in_count;
    logic              w_in_fire;
    logic [CNT_W-1:0]  w_rx_base;
    logic [CNT_W-1:0]  w_rx_bit_next;
    logic              w_frame_err_event;
    logic              w_over_n_event;
    logic              w_over_n_now;
    logic [BEAT_W-1:0] w_rx_beat_next;
    logic [BEAT_W-1:0] w_rx_beats_now;
    logic              w_block_ending_now;
    logic              w_synd_result_valid;
    logic              w_verdict_correctable;

    // The bit count the presenting beat would extend: the live block's count
    // in SYND, zero in IDLE -- r_rx_bit_count is not re-initialised until the
    // first beat fires, so outside SYND it still holds the PREVIOUS block's
    // total and must not seed the next block's framing arithmetic.
    assign w_rx_base          = (r_state == IDLE) ? CNT_W'(0) : r_rx_bit_count;
    assign w_in_count         = CW'(bch_keep_count(64'(in_keep), B));
    assign w_in_fire          = in_valid && in_ready;
    assign w_rx_bit_next      = w_rx_base + CNT_W'(w_in_count);
    // Framing violation: the last beat lands anywhere but on N, or the count
    // reaches/passes N on a non-final beat (issue #90 -- an over-long block).
    // in_valid-based, not in_fire-based: feeding it back through in_ready
    // would close a combinational loop, and a beat presenting past N is a
    // violation whether or not this cycle accepts it.
    assign w_over_n_event     = in_valid && !in_last && (w_rx_bit_next >= CNT_W'(N));
    assign w_frame_err_event  = w_in_fire && ((in_last && (w_rx_bit_next != CNT_W'(N)))
                                              || (!in_last && (w_rx_bit_next >= CNT_W'(N))));
    assign w_rx_beat_next     = r_rx_beat_count + BEAT_W'(1);
    assign w_rx_beats_now     = (r_state == IDLE) ? BEAT_W'(1) : w_rx_beat_next;
    assign w_block_ending_now = w_in_fire && in_last;
    // Per-block over-N view: in IDLE the registered flag is stale (it belongs
    // to the previous block), so only the current beat's event counts there.
    assign w_over_n_now       = (r_state == IDLE) ? w_over_n_event
                                                  : (r_over_n || w_over_n_event);

    // Only act on a syndrome-unit result once the block boundary has arrived.
    // For a too-long block the result may become valid before in_last; we wait.
    assign w_synd_result_valid = w_synd_out_ready && (r_block_ending || w_block_ending_now) && !r_synd_flush;

    // Syndrome unit input mux for flush padding
    assign w_flush_count     = (CNT_W'(B) < r_flush_rem) ? CW'(B) : CW'(r_flush_rem);
    always_comb begin
        w_flush_keep = '0;
        for (int u = 0; u < B; u++)
            if (u < w_flush_count) w_flush_keep[u] = 1'b1;
    end

    // Only let the syndrome unit step when this core actually accepts the beat,
    // and never past N bits of the current block: beyond N the block is a
    // framing violation whose surplus must not re-arm or corrupt the unit's
    // accumulation (issue #90).
    assign w_synd_in_valid   = r_synd_flush ? 1'b1 : (in_valid && in_ready && !w_over_n_now);
    assign w_synd_in_data    = r_synd_flush ? '0    : in_data;
    assign w_synd_in_keep    = r_synd_flush ? w_flush_keep : in_keep;
    assign w_synd_out_ready  = (r_state == SYND) && w_synd_out_valid;
    // Once a block is over-N the unit's in_ready is moot (it is either holding
    // a completed result or frozen mid-count): keep accepting so the sender
    // can reach in_last and the violation can be released.
    assign in_ready          = ((r_state == IDLE)
                                || ((r_state == SYND) && !r_synd_flush && !r_block_ending))
                               && (w_over_n_now || w_synd_in_ready);
    // The unit's accumulated state is meaningless for an over-N block; clear
    // it as the block releases so the next block starts from zero.
    assign w_synd_clear      = (r_state == SYND) && r_over_n && r_block_ending;

    // Solver / Chien handshakes
    assign w_kes_out_ready   = (r_state == SOLVE) && w_kes_out_valid;
    assign w_chien_out_ready = (r_state == CHIEN);
    assign w_rechk_out_ready = ENABLE_RECHECK &&
                               (((r_state == CHIEN) && w_chien_out_last && w_chien_out_valid) ||
                                (r_state == RECHECK));

    // Re-check beat data and keep (only valid positions are fed)
    always_comb begin
        for (int u = 0; u < B; u++)
            w_rechk_keep[u] = (r_chien_beat_count * B + u) < N;
    end
    /* verilator lint_off WIDTHTRUNC */
    assign w_rechk_data = (r_buf[r_chien_beat_count] ^ w_chien_out_flip_en) & w_rechk_keep;
    /* verilator lint_on WIDTHTRUNC */

    // Final verdict: degree in range, root count matches degree, re-check passes.
    // In CHIEN the live root count is valid on the last beat; in RECHECK we use
    // the value captured at the last beat because the Chien fub resets it.
    assign w_verdict_correctable = !r_more_than_t
                                   && (((r_state == CHIEN) ? w_chien_out_root_count : r_chien_root_count)
                                       == r_lambda_degree)
                                   && (!ENABLE_RECHECK || w_rechk_out_no_error);

    // -------------------------------------------------------------------------
    // Output formatting
    // -------------------------------------------------------------------------
    logic [B-1:0] w_release_keep;
    always_comb begin
        for (int u = 0; u < B; u++)
            w_release_keep[u] = (r_release_idx * B + u) < K;
    end

    /* verilator lint_off WIDTHTRUNC */
    assign out_valid            = (r_state == RELEASE) && (r_release_idx < r_release_beats);
    assign out_keep             = r_st_frame_err ? r_buf_keep[r_release_idx] : w_release_keep;
    assign out_data             = r_buf[r_release_idx] ^ (r_flip[r_release_idx] & {B{r_release_apply}});
    assign out_last             = (r_release_idx == r_release_beats - 1);
    /* verilator lint_on WIDTHTRUNC */

    assign out_status_ok          = r_st_ok;
    assign out_status_corrected   = r_st_corrected;
    assign out_status_uncorrectable = r_st_uncorrectable;
    assign out_status_frame_err   = r_st_frame_err;

    // -------------------------------------------------------------------------
    // Control FSM
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_state          <= IDLE;
            r_rx_bit_count   <= '0;
            r_rx_beat_count  <= '0;
            r_frame_err      <= 1'b0;
            r_over_n         <= 1'b0;
            r_rx_beats_total <= '0;
            r_block_ending   <= 1'b0;
            r_synd_flush     <= 1'b0;
            r_flush_rem      <= '0;
            r_lambda_degree  <= '0;
            r_more_than_t    <= 1'b0;
            r_solver_started <= 1'b0;
            r_chien_beat_count <= '0;
            r_chien_root_count <= '0;
            r_release_idx    <= '0;
            r_release_beats  <= '0;
            r_release_apply  <= 1'b0;
            r_st_ok          <= 1'b0;
            r_st_corrected   <= '0;
            r_st_uncorrectable <= 1'b0;
            r_st_frame_err   <= 1'b0;
            for (int i = 0; i < BEATS_N; i++) begin
                r_buf[i]      <= '0;
                r_buf_keep[i] <= '0;
                r_flip[i]     <= '0;
            end
        end else begin
            case (r_state)
                IDLE: begin
                    if (w_in_fire) begin
                        r_state         <= SYND;
                        r_rx_bit_count  <= CNT_W'(w_in_count);
                        r_rx_beat_count <= BEAT_W'(1);
                        r_buf[0]        <= in_data;
                        r_buf_keep[0]   <= in_keep;
                        r_frame_err     <= w_frame_err_event;
                        r_over_n        <= w_over_n_event;
                        r_block_ending  <= w_block_ending_now;
                        if (in_last) begin
                            r_rx_beats_total <= BEAT_W'(1);
                            if (w_frame_err_event) begin
                                // short frame_err: need to flush syndrome unit
                                r_synd_flush <= 1'b1;
                                r_flush_rem  <= CNT_W'(N) - CNT_W'(w_in_count);
                            end
                        end
                    end
                end

                SYND: begin
                    if (w_in_fire) begin
                        // An over-N block can outgrow the buffer; store the
                        // first BEATS_N beats and drop the surplus (issue #90).
                        if (r_rx_beat_count < BEAT_W'(BEATS_N)) begin
                            /* verilator lint_off WIDTHTRUNC */
                            r_buf[r_rx_beat_count]      <= in_data;
                            r_buf_keep[r_rx_beat_count] <= in_keep;
                            /* verilator lint_on WIDTHTRUNC */
                        end
                        r_rx_bit_count              <= w_rx_bit_next;
                        r_rx_beat_count             <= (r_rx_beat_count == BEAT_W'(BEATS_N))
                                                       ? BEAT_W'(BEATS_N) : w_rx_beat_next;
                        r_frame_err                 <= w_frame_err_event;
                        r_over_n                    <= w_over_n_now;
                        r_block_ending              <= w_block_ending_now;
                        if (in_last) begin
                            r_rx_beats_total <= (w_rx_beats_now > BEAT_W'(BEATS_N))
                                                ? BEAT_W'(BEATS_N) : w_rx_beats_now;
                            if (w_frame_err_event && (w_rx_bit_next < CNT_W'(N))) begin
                                r_synd_flush <= 1'b1;
                                r_flush_rem  <= CNT_W'(N) - w_rx_bit_next;
                            end
                        end
                    end else if (r_synd_flush && w_synd_in_ready) begin
                        // feed padding zeros until the syndrome unit reaches N
                        if (CNT_W'(B) < r_flush_rem)
                            r_flush_rem <= r_flush_rem - CNT_W'(B);
                        else
                            r_flush_rem <= '0;
                    end

                    if (r_over_n && r_block_ending) begin
                        // issue #90: over-long block -- the syndrome result is
                        // moot; release the buffered prefix as frame_err and
                        // clear the syndrome unit (w_synd_clear) for the next
                        r_state          <= RELEASE;
                        r_block_ending   <= 1'b0;
                        r_release_idx    <= '0;
                        r_release_beats  <= r_rx_beats_total;
                        r_release_apply  <= 1'b0;
                        r_st_ok          <= 1'b0;
                        r_st_corrected   <= '0;
                        r_st_uncorrectable <= 1'b0;
                        r_st_frame_err   <= 1'b1;
                    end else if (w_synd_result_valid) begin
                        // syndrome result is ready and the block has ended
                        if (r_frame_err) begin
                            r_state          <= RELEASE;
                            r_block_ending   <= 1'b0;
                            r_release_idx    <= '0;
                            r_release_beats  <= r_rx_beats_total;
                            r_release_apply  <= 1'b0;
                            r_st_ok          <= 1'b0;
                            r_st_corrected   <= '0;
                            r_st_uncorrectable <= 1'b0;
                            r_st_frame_err   <= 1'b1;
                        end else if (w_synd_out_no_error) begin
                            r_state          <= RELEASE;
                            r_block_ending   <= 1'b0;
                            r_release_idx    <= '0;
                            r_release_beats  <= BEAT_W'(BEATS_K);
                            r_release_apply  <= 1'b0;
                            r_st_ok          <= 1'b1;
                            r_st_corrected   <= '0;
                            r_st_uncorrectable <= 1'b0;
                            r_st_frame_err   <= 1'b0;
                        end else begin
                            r_state          <= SOLVE;
                            r_block_ending   <= 1'b0;
                            r_solver_started <= 1'b0;
                        end
                    end else if (r_synd_flush && w_synd_out_ready) begin
                        // padding flushed the syndrome unit clean
                        r_state          <= RELEASE;
                        r_synd_flush     <= 1'b0;
                        r_block_ending   <= 1'b0;
                        r_release_idx    <= '0;
                        r_release_beats  <= r_rx_beats_total;
                        r_release_apply  <= 1'b0;
                        r_st_ok          <= 1'b0;
                        r_st_corrected   <= '0;
                        r_st_uncorrectable <= 1'b0;
                        r_st_frame_err   <= 1'b1;
                    end
                end

                SOLVE: begin
                    if (!r_solver_started && w_kes_in_ready) begin
                        r_solver_started <= 1'b1;
                    end
                    if (w_kes_out_ready) begin
                        r_state          <= CHIEN;
                        r_lambda_degree  <= w_kes_out_lambda_degree;
                        r_more_than_t    <= w_kes_out_more_than_t;
                        r_chien_beat_count <= '0;
                        r_solver_started <= 1'b0;
                    end
                end

                CHIEN: begin
                    if (w_chien_out_ready && w_chien_out_valid) begin
                        /* verilator lint_off WIDTHTRUNC */
                        r_flip[r_chien_beat_count] <= w_chien_out_flip_en;
                        /* verilator lint_on WIDTHTRUNC */
                        r_chien_beat_count         <= r_chien_beat_count + BEAT_W'(1);

                        if (w_chien_out_last) begin
                            r_chien_root_count <= w_chien_out_root_count;
                            if (ENABLE_RECHECK) begin
                                r_state <= RECHECK;
                            end else begin
                                r_state          <= RELEASE;
                                r_release_idx    <= '0;
                                r_release_beats  <= BEAT_W'(BEATS_K);
                                if (w_verdict_correctable) begin
                                    r_release_apply  <= 1'b1;
                                    r_st_ok          <= 1'b0;
                                    r_st_corrected   <= w_chien_out_root_count;
                                    r_st_uncorrectable <= 1'b0;
                                    r_st_frame_err   <= 1'b0;
                                end else begin
                                    r_release_apply  <= 1'b0;
                                    r_st_ok          <= 1'b0;
                                    r_st_corrected   <= '0;
                                    r_st_uncorrectable <= 1'b1;
                                    r_st_frame_err   <= 1'b0;
                                end
                            end
                        end
                    end
                end

                RECHECK: begin
                    if (w_rechk_out_valid && w_rechk_out_ready) begin
                        r_state          <= RELEASE;
                        r_release_idx    <= '0;
                        r_release_beats  <= BEAT_W'(BEATS_K);
                        if (w_verdict_correctable) begin
                            r_release_apply  <= 1'b1;
                            r_st_ok          <= 1'b0;
                            r_st_corrected   <= r_chien_root_count;
                            r_st_uncorrectable <= 1'b0;
                            r_st_frame_err   <= 1'b0;
                        end else begin
                            r_release_apply  <= 1'b0;
                            r_st_ok          <= 1'b0;
                            r_st_corrected   <= '0;
                            r_st_uncorrectable <= 1'b1;
                            r_st_frame_err   <= 1'b0;
                        end
                    end
                end

                RELEASE: begin
                    if (out_valid && out_ready) begin
                        if (out_last) begin
                            r_state <= IDLE;
                            // status remains stable through the last beat
                        end else begin
                            r_release_idx <= r_release_idx + BEAT_W'(1);
                        end
                    end
                end

                default: r_state <= IDLE;
            endcase
        end
    )

    // -------------------------------------------------------------------------
    // Lint quieting
    // -------------------------------------------------------------------------
    // The KES and Chien fubs expose signals that are unused at this integration
    // level or are dead when ENABLE_RECHECK is off. Tie them off explicitly.
    logic unused_signals;
    always_comb begin
        unused_signals = 1'b0;
        unused_signals ^= w_kes_in_ready ^ w_chien_in_ready;
        if (!ENABLE_RECHECK) begin
            unused_signals ^= w_rechk_in_ready ^ w_rechk_out_valid
                           ^ (^w_rechk_data) ^ (^w_rechk_keep);
        end
    end

endmodule : bch_decoder_core
