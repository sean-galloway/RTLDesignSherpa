// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_rd_crc_check
// Purpose: Master-side read driver + integrity checker for memory-controller
//          characterization. Walks the SAME algorithmic address mix
//          (via dma_address_gen) and the SAME LFSR seed schedule as
//          axi4_master_wr_pattern_gen, so the returned R beats can be
//          compared bit-for-bit against the locally-regenerated pattern.
//          Accumulates a CRC-32 over the returned data so the harness can
//          also compare actual_crc against the writer's expected_crc.
//
// Documentation: projects/NexysA7/ddr2-characterization/README.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-06-25

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: axi4_master_rd_crc_check
//==============================================================================
// Description:
//   Drives a CSR-programmed sequence of AXI4 read bursts at the FUB side of
//   `axi4_master_rd`, with addresses from `dma_address_gen`. As each R beat
//   returns it is compared against the same LFSR stream the writer used,
//   and the running CRC is accumulated over the LFSR words.
//
//   Workflow:
//     1. Software programs cfg_* (same shape as axi4_master_wr_pattern_gen)
//     2. Software pulses cfg_start.
//     3. The block walks index_0 = 0..cfg_txn_count-1 through
//        dma_address_gen, issuing one AR per index. For each AR it
//        consumes cfg_burst_len R beats and compares each to the locally-
//        regenerated LFSR pattern. A mismatch latches o_data_error.
//     4. dataint_crc accumulates over the LFSR stream (NOT the returned
//        rdata — same as the writer side, so o_actual_crc matches the
//        writer's o_expected_crc when the wire is clean).
//     5. When all cfg_txn_count bursts have completed (rlast received on
//        the last burst), cfg_done asserts.
//
//   Serial-burst v1: at most one AR outstanding (rlast must complete before
//   the next AR is issued). Multi-outstanding is a v2 extension that needs
//   per-id LFSR/CRC contexts.
//
//   The LFSR + CRC config (seed, polynomial, width) MUST match the writer
//   side or the comparison and CRC roll-up are meaningless. The default
//   parameters here mirror axi4_master_wr_pattern_gen exactly.
//
//   ===== OUT-OF-ORDER COMPLETION — KNOWN LIMITATION (v2 TODO) =====
//
//   The v1 LFSR mirror advances on every accepted R beat, so the expected
//   value at beat K depends on K — the *arrival* index — not on the AR's
//   (address, beat_index_within_burst). With AXI4 this is fine while:
//
//     1. Only one outstanding AR (serial v1: rlast gates the next AR), OR
//     2. All ARs share the same ID — AXI4 mandates in-order R per id, so
//        beat arrival order matches issue order under same-id traffic.
//
//   With multiple outstanding ARs at distinct IDs, the controller is free
//   to return their R bursts interleaved or fully OOO. The current LFSR
//   stream is a single phase counter; an OOO return reorders R beats vs
//   the writer's W phase and per-beat compare + CRC roll-up both break.
//
//   For v2:
//     - Switch the "expected" function to a deterministic per-address
//       hash, e.g. expected_word(addr_word_idx) = LFSR_skip(seed,
//       hash(addr_word_idx)). Compare per-beat against the looked-up
//       value rather than a phase counter.
//     - Make the CRC accumulator commutative (XOR-sum over per-beat
//       values, not the LFSR stream) OR accumulate per-burst CRCs in a
//       slot indexed by AR id and only roll up at cfg_done.
//     - The writer's o_expected_crc has to use the same commutative
//       roll-up so the two values can still be compared end-to-end.
//
//   Until that lands, the harness CSR must keep the read block in
//   single-outstanding mode (cfg_force_inorder or all-same-id) when
//   the controller has OOO enabled.
//==============================================================================
module axi4_master_rd_crc_check #(
    // ---- AXI ----
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_USER_WIDTH = 1,

    // ---- LFSR (MUST match axi4_master_wr_pattern_gen) ----
    parameter int                    LFSR_WIDTH = 32,
    parameter logic [31:0]           LFSR_SEED  = 32'hDEADBEEF,
    parameter logic [47:0]           LFSR_TAPS  = {12'd32, 12'd22, 12'd2, 12'd1},

    // ---- CRC (MUST match axi4_master_wr_pattern_gen) ----
    parameter int                    CRC_WIDTH      = 32,
    parameter int                    CRC_DATA_WIDTH = 32,
    parameter logic [CRC_WIDTH-1:0]  CRC_POLY       = 32'h04C11DB7,
    parameter logic [CRC_WIDTH-1:0]  CRC_POLY_INIT  = '1,
    parameter logic [CRC_WIDTH-1:0]  CRC_XOROUT     = '1,

    // ---- Workload ----
    parameter int TXN_COUNT_WIDTH = 16,
    parameter int INDEX_WIDTH     = 16,
    parameter int STRIDE_WIDTH    = 24,

    // ---- Aliases ----
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // ==========================================================================
    // Configuration — same shape as axi4_master_wr_pattern_gen so the
    // harness CSR can drive both blocks from one descriptor word.
    // ==========================================================================
    input  logic [AW-1:0]                       cfg_start_addr,
    input  logic signed [STRIDE_WIDTH-1:0]      cfg_addr_stride_0,
    input  logic signed [STRIDE_WIDTH-1:0]      cfg_addr_stride_1,
    input  logic [AW-1:0]                       cfg_addr_wrap_mask_0,
    input  logic [AW-1:0]                       cfg_addr_wrap_mask_1,

    input  logic [7:0]                          cfg_burst_len,    // beats (1..256). arlen = len-1
    input  logic [TXN_COUNT_WIDTH-1:0]          cfg_txn_count,
    input  logic [IW-1:0]                       cfg_axi_id,
    input  logic [2:0]                          cfg_axi_size,
    input  logic [1:0]                          cfg_axi_burst,

    input  logic [LFSR_WIDTH-1:0]               cfg_lfsr_seed,    // 0 → use param

    // Data source select: 0 = phase-counter LFSR; 1 = address-derived
    // hash. In hash mode each beat's expected data is a pure function
    // of its byte address, so multi-id / OOO completion still validates
    // (the per-beat compare looks up f(addr) not the LFSR phase). MUST
    // match the writer's cfg_data_mode + seeds for cross-block validity.
    input  logic                                cfg_data_mode,
    input  logic [31:0]                         cfg_hash_seed0,
    input  logic [31:0]                         cfg_hash_seed1,
    input  logic [31:0]                         cfg_hash_seed2,

    // Inter-burst idle gap (0..15 cycles between rlast on burst N and
    // the AR for burst N+1). Independent from the writer's gap so a
    // sweep can vary R-side pressure separately.
    input  logic [3:0]                          cfg_rd_gap,

    input  logic                                cfg_start,
    output logic                                cfg_done,

    // ==========================================================================
    // Telemetry
    // ==========================================================================
    output logic [CRC_WIDTH-1:0]                o_actual_crc,
    output logic                                o_actual_crc_valid,  // high with cfg_done
    output logic                                o_data_error,        // sticky on R beat mismatch
    output logic                                o_rresp_error,       // sticky on non-OKAY R beat
    output logic [TXN_COUNT_WIDTH-1:0]          o_beats_mismatched,  // count of mismatching R beats

    // ==========================================================================
    // M-side AXI4 (out to fabric)
    // ==========================================================================
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready
);

    //==========================================================================
    // FSM
    //==========================================================================
    typedef enum logic [2:0] {
        S_IDLE       = 3'd0,
        S_AR_REQ     = 3'd1,
        S_R_BEATS    = 3'd2,
        S_GAP        = 3'd3,   // cfg_rd_gap idle cycles between bursts
        S_DONE       = 3'd4
    } state_e;

    state_e                       r_state;

    // Latched workload program
    logic [AW-1:0]                r_base_addr;
    logic signed [STRIDE_WIDTH-1:0] r_stride_0, r_stride_1;
    logic [AW-1:0]                r_wrap_0, r_wrap_1;
    logic [7:0]                   r_burst_len;
    logic [3:0]                   r_rd_gap;
    logic [TXN_COUNT_WIDTH-1:0]   r_txn_count;
    logic [IW-1:0]                r_axi_id;
    logic [2:0]                   r_axi_size;
    logic [1:0]                   r_axi_burst;
    logic [LFSR_WIDTH-1:0]        r_lfsr_seed_eff;
    logic                         r_data_mode;       // 0=LFSR, 1=ADDR_HASH
    logic [31:0]                  r_hash_seed0;
    logic [31:0]                  r_hash_seed1;
    logic [31:0]                  r_hash_seed2;
    // Burst's accepted AR address, latched at AR handshake so the per-beat
    // byte-address calc has a stable anchor for hash-mode regeneration.
    logic [AW-1:0]                r_burst_base_addr;

    // Progress counters
    logic [TXN_COUNT_WIDTH-1:0]   r_ar_issued;
    logic [TXN_COUNT_WIDTH-1:0]   r_bursts_done;
    logic [7:0]                   r_beats_in_burst;
    logic [3:0]                   r_gap_left;
    // One-shot request marker — same fix as axi4_master_wr_pattern_gen.
    // Prevents the address-gen from capturing r_ar_issued multiple times
    // while we wait for its pipelined result.
    logic                         r_addr_req_done;

    //==========================================================================
    // dma_address_gen — same shape as the writer-side use
    //==========================================================================
    logic                         w_addr_req_valid;
    logic                         w_addr_req_ready;
    logic                         w_addr_result_valid;
    logic                         w_addr_result_ready;
    logic [AW-1:0]                w_addr_result;

    dma_address_gen #(
        .ADDR_WIDTH  (AW),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (8)
    ) u_addr_gen (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_base_addr),
        .i_cfg_stride_0    (r_stride_0),
        .i_cfg_stride_1    (r_stride_1),
        .i_cfg_wrap_mask_0 (r_wrap_0),
        .i_cfg_wrap_mask_1 (r_wrap_1),

        .i_req_valid       (w_addr_req_valid),
        .o_req_ready       (w_addr_req_ready),
        .i_req_index_0     (INDEX_WIDTH'(r_ar_issued)),
        .i_req_index_1     (INDEX_WIDTH'(0)),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_addr_result_valid),
        .i_result_ready    (w_addr_result_ready),
        .o_result_addr     (w_addr_result),
        .o_result_tag      ()
    );

    //==========================================================================
    // LFSR — advances on every accepted R beat. Same logic as writer side
    // so the two LFSR streams stay phase-aligned: same total beat count
    // ⇒ same word ⇒ bit-for-bit match.
    //==========================================================================
    logic                         w_r_beat;       // accepted R beat at FUB side
    logic                         w_lfsr_load;
    logic [LFSR_WIDTH-1:0]        w_lfsr_out;

    // Same combinational seed mux as axi4_master_wr_pattern_gen.
    logic [LFSR_WIDTH-1:0] w_lfsr_seed_data;
    assign w_lfsr_seed_data = w_lfsr_load
                            ? ((cfg_lfsr_seed == '0) ? LFSR_SEED
                                                     : cfg_lfsr_seed)
                            : r_lfsr_seed_eff;

    shifter_lfsr_fibonacci #(
        .WIDTH          (LFSR_WIDTH),
        .TAP_INDEX_WIDTH(12),
        .TAP_COUNT      (4)
    ) u_lfsr (
        .clk      (aclk),
        .rst_n    (aresetn),
        .enable   (w_r_beat || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(w_lfsr_seed_data),
        .taps     (LFSR_TAPS),
        .lfsr_out (w_lfsr_out),
        .lfsr_done()
    );

    //==========================================================================
    // CRC — over the LFSR stream (NOT rdata). Matches writer-side accounting.
    //==========================================================================
    localparam int W_CRC_CHUNKS = CRC_DATA_WIDTH / 8;

    dataint_crc #(
        .DATA_WIDTH(CRC_DATA_WIDTH),
        .CRC_WIDTH (CRC_WIDTH),
        .REFIN     (0),
        .REFOUT    (0)
    ) u_crc (
        .POLY              (CRC_POLY),
        .POLY_INIT         (CRC_POLY_INIT),
        .XOROUT            (CRC_XOROUT),
        .clk               (aclk),
        .rst_n             (aresetn),
        .load_crc_start    (w_lfsr_load),
        .load_from_cascade (1'b0),
        .cascade_sel       ({W_CRC_CHUNKS{1'b1}}),
        .data              (w_lfsr_out),
        .crc               (o_actual_crc)
    );

    //==========================================================================
    // FUB-side AXI handshakes — driven from FSM
    //==========================================================================
    logic                         fub_arvalid;
    logic                         fub_arready;
    logic                         fub_rvalid;
    logic                         fub_rready;
    logic                         fub_rlast;
    logic [DW-1:0]                fub_rdata;
    logic [1:0]                   fub_rresp;

    assign w_r_beat = fub_rvalid && fub_rready;

    assign fub_arvalid           = (r_state == S_AR_REQ) && w_addr_result_valid;
    assign w_addr_result_ready   = fub_arvalid && fub_arready;
    assign w_addr_req_valid      = (r_state == S_AR_REQ) && !r_addr_req_done;

    // Always ready to accept R while we're in R_BEATS (or briefly during
    // the AR_REQ -> R_BEATS handoff cycle).
    assign fub_rready = (r_state == S_R_BEATS);

    //==========================================================================
    // Expected pattern data — two sources, muxed by r_data_mode:
    //   mode 0: 32-bit Fibonacci LFSR replicated across DW (phase-counter)
    //   mode 1: 32-bit Murmur3-fmix-style address hash, per-32-bit slice
    //==========================================================================
    localparam int REPLICATION_FACTOR = (DW + 31) / 32;
    logic [REPLICATION_FACTOR*32-1:0] w_expected_replicated;
    assign w_expected_replicated = {REPLICATION_FACTOR{w_lfsr_out}};

    // Per-beat byte address for hash mode.
    logic [AW-1:0]                w_byte_addr_for_beat;
    assign w_byte_addr_for_beat = r_burst_base_addr
        + (AW'({{(AW-8){1'b0}}, r_beats_in_burst}) << r_axi_size);

    // MUST match axi4_master_wr_pattern_gen::addr_hash32 bit-for-bit.
    function automatic logic [31:0] addr_hash32(
        input logic [31:0] addr,
        input logic [31:0] s0,
        input logic [31:0] s1,
        input logic [31:0] s2
    );
        logic [31:0] x;
        x = addr ^ s0;
        x = x ^ (x >> 16);
        x = x * (s1 | 32'h1);
        x = x ^ (x >> 13);
        x = x * (s2 | 32'h1);
        x = x ^ (x >> 16);
        return x;
    endfunction

    logic [REPLICATION_FACTOR*32-1:0] w_hash_replicated;
    always_comb begin
        for (int s = 0; s < REPLICATION_FACTOR; s++) begin
            w_hash_replicated[s*32 +: 32] = addr_hash32(
                w_byte_addr_for_beat[31:0] + 32'(s * 4),
                r_hash_seed0,
                r_hash_seed1,
                r_hash_seed2);
        end
    end

    logic [DW-1:0]                    w_expected_data;
    assign w_expected_data = r_data_mode
                           ? w_hash_replicated[DW-1:0]
                           : w_expected_replicated[DW-1:0];

    // Per-beat data mismatch (combinational). Latched on w_r_beat below.
    logic                             w_beat_mismatch;
    assign w_beat_mismatch = w_r_beat && (fub_rdata != w_expected_data);

    //==========================================================================
    // Sequential FSM + counters + sticky errors
    //==========================================================================
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_state            <= S_IDLE;
            r_base_addr        <= '0;
            r_stride_0         <= '0;
            r_stride_1         <= '0;
            r_wrap_0           <= '0;
            r_wrap_1           <= '0;
            r_burst_len        <= 8'd0;
            r_rd_gap           <= 4'd0;
            r_txn_count        <= '0;
            r_axi_id           <= '0;
            r_axi_size         <= 3'd0;
            r_axi_burst        <= 2'd1;
            r_lfsr_seed_eff    <= LFSR_SEED;
            r_data_mode        <= 1'b0;
            r_hash_seed0       <= 32'd0;
            r_hash_seed1       <= 32'd0;
            r_hash_seed2       <= 32'd0;
            r_burst_base_addr  <= '0;
            r_ar_issued        <= '0;
            r_bursts_done      <= '0;
            r_beats_in_burst   <= 8'd0;
            r_gap_left         <= 4'd0;
            r_addr_req_done    <= 1'b0;
            o_actual_crc_valid <= 1'b0;
            o_data_error       <= 1'b0;
            o_rresp_error      <= 1'b0;
            o_beats_mismatched <= '0;
        end else begin
            unique case (r_state)
                S_IDLE: begin
                    if (cfg_start) begin
                        r_base_addr     <= cfg_start_addr;
                        r_stride_0      <= cfg_addr_stride_0;
                        r_stride_1      <= cfg_addr_stride_1;
                        r_wrap_0        <= cfg_addr_wrap_mask_0;
                        r_wrap_1        <= cfg_addr_wrap_mask_1;
                        r_burst_len     <= (cfg_burst_len == 8'd0) ? 8'd1 : cfg_burst_len;
                        r_txn_count     <= cfg_txn_count;
                        r_axi_id        <= cfg_axi_id;
                        r_axi_size      <= cfg_axi_size;
                        r_axi_burst     <= cfg_axi_burst;
                        r_lfsr_seed_eff <= (cfg_lfsr_seed == '0) ? LFSR_SEED : cfg_lfsr_seed;
                        r_data_mode     <= cfg_data_mode;
                        r_hash_seed0    <= cfg_hash_seed0;
                        r_hash_seed1    <= cfg_hash_seed1;
                        r_hash_seed2    <= cfg_hash_seed2;
                        r_rd_gap        <= cfg_rd_gap;
                        r_ar_issued     <= '0;
                        r_bursts_done   <= '0;
                        r_beats_in_burst<= 8'd0;
                        r_gap_left      <= 4'd0;
                        r_addr_req_done <= 1'b0;
                        o_actual_crc_valid <= 1'b0;
                        o_data_error       <= 1'b0;
                        o_rresp_error      <= 1'b0;
                        o_beats_mismatched <= '0;
                        r_state         <= (cfg_txn_count == '0) ? S_DONE : S_AR_REQ;
                    end
                end

                S_AR_REQ: begin
                    if (w_addr_req_valid && w_addr_req_ready) begin
                        r_addr_req_done <= 1'b1;
                    end
                    if (fub_arvalid && fub_arready) begin
                        r_ar_issued       <= r_ar_issued + 1'b1;
                        r_state           <= S_R_BEATS;
                        r_beats_in_burst  <= 8'd0;
                        r_burst_base_addr <= w_addr_result;
                    end
                end

                S_R_BEATS: begin
                    if (w_r_beat) begin
                        if (fub_rlast) begin
                            r_bursts_done   <= r_bursts_done + 1'b1;
                            r_addr_req_done <= 1'b0;  // re-arm for next burst
                            if (r_bursts_done + 1'b1 == r_txn_count) begin
                                r_state            <= S_DONE;
                                // CRC roll-up is only meaningful in LFSR
                                // mode (phase-counter contract); hash mode
                                // proves integrity via per-beat compare.
                                o_actual_crc_valid <= !r_data_mode;
                            end else if (r_rd_gap != 4'd0) begin
                                r_state    <= S_GAP;
                                r_gap_left <= r_rd_gap;
                            end else begin
                                r_state <= S_AR_REQ;
                            end
                        end else begin
                            r_beats_in_burst <= r_beats_in_burst + 8'd1;
                        end
                    end
                end

                S_GAP: begin
                    if (r_gap_left == 4'd1) begin
                        r_state    <= S_AR_REQ;
                        r_gap_left <= 4'd0;
                    end else begin
                        r_gap_left <= r_gap_left - 4'd1;
                    end
                end

                S_DONE: begin
                    if (cfg_start) begin
                        // Direct re-arm — same path as the writer block.
                        r_base_addr     <= cfg_start_addr;
                        r_stride_0      <= cfg_addr_stride_0;
                        r_stride_1      <= cfg_addr_stride_1;
                        r_wrap_0        <= cfg_addr_wrap_mask_0;
                        r_wrap_1        <= cfg_addr_wrap_mask_1;
                        r_burst_len     <= (cfg_burst_len == 8'd0) ? 8'd1 : cfg_burst_len;
                        r_txn_count     <= cfg_txn_count;
                        r_axi_id        <= cfg_axi_id;
                        r_axi_size      <= cfg_axi_size;
                        r_axi_burst     <= cfg_axi_burst;
                        r_lfsr_seed_eff <= (cfg_lfsr_seed == '0) ? LFSR_SEED : cfg_lfsr_seed;
                        r_data_mode     <= cfg_data_mode;
                        r_hash_seed0    <= cfg_hash_seed0;
                        r_hash_seed1    <= cfg_hash_seed1;
                        r_hash_seed2    <= cfg_hash_seed2;
                        r_rd_gap        <= cfg_rd_gap;
                        r_ar_issued     <= '0;
                        r_bursts_done   <= '0;
                        r_beats_in_burst<= 8'd0;
                        r_gap_left      <= 4'd0;
                        r_addr_req_done <= 1'b0;
                        o_actual_crc_valid <= 1'b0;
                        o_data_error       <= 1'b0;
                        o_rresp_error      <= 1'b0;
                        o_beats_mismatched <= '0;
                        r_state            <= (cfg_txn_count == '0) ? S_DONE : S_AR_REQ;
                    end
                end

                default: r_state <= S_IDLE;
            endcase

            // Per-beat data + rresp checks (sticky)
            if (w_r_beat) begin
                if (w_beat_mismatch) begin
                    o_data_error       <= 1'b1;
                    o_beats_mismatched <= o_beats_mismatched + 1'b1;
                end
                if (fub_rresp != 2'b00) begin
                    o_rresp_error <= 1'b1;
                end
            end
        end
    end)

    assign w_lfsr_load = cfg_start && ((r_state == S_IDLE) || (r_state == S_DONE));

    assign cfg_done = (r_state == S_DONE)
                   && (r_bursts_done == r_txn_count);

    //==========================================================================
    // axi4_master_rd — bundles the AR/R skid buffers + protocol.
    //==========================================================================
    axi4_master_rd #(
        .SKID_DEPTH_AR (SKID_DEPTH_AR),
        .SKID_DEPTH_R  (SKID_DEPTH_R),
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_master_rd (
        .aclk            (aclk),
        .aresetn         (aresetn),

        // FUB AR
        .fub_axi_arid    (r_axi_id),
        .fub_axi_araddr  (w_addr_result),
        .fub_axi_arlen   (r_burst_len - 8'd1),
        .fub_axi_arsize  (r_axi_size),
        .fub_axi_arburst (r_axi_burst),
        .fub_axi_arlock  (1'b0),
        .fub_axi_arcache (4'b0011),
        .fub_axi_arprot  (3'b000),
        .fub_axi_arqos   (4'b0000),
        .fub_axi_arregion(4'b0000),
        .fub_axi_aruser  ('0),
        .fub_axi_arvalid (fub_arvalid),
        .fub_axi_arready (fub_arready),

        // FUB R
        .fub_axi_rid     (),
        .fub_axi_rdata   (fub_rdata),
        .fub_axi_rresp   (fub_rresp),
        .fub_axi_rlast   (fub_rlast),
        .fub_axi_ruser   (),
        .fub_axi_rvalid  (fub_rvalid),
        .fub_axi_rready  (fub_rready),

        // M-side AXI passthrough
        .m_axi_arid      (m_axi_arid),
        .m_axi_araddr    (m_axi_araddr),
        .m_axi_arlen     (m_axi_arlen),
        .m_axi_arsize    (m_axi_arsize),
        .m_axi_arburst   (m_axi_arburst),
        .m_axi_arlock    (m_axi_arlock),
        .m_axi_arcache   (m_axi_arcache),
        .m_axi_arprot    (m_axi_arprot),
        .m_axi_arqos     (m_axi_arqos),
        .m_axi_arregion  (m_axi_arregion),
        .m_axi_aruser    (m_axi_aruser),
        .m_axi_arvalid   (m_axi_arvalid),
        .m_axi_arready   (m_axi_arready),
        .m_axi_rid       (m_axi_rid),
        .m_axi_rdata     (m_axi_rdata),
        .m_axi_rresp     (m_axi_rresp),
        .m_axi_rlast     (m_axi_rlast),
        .m_axi_ruser     (m_axi_ruser),
        .m_axi_rvalid    (m_axi_rvalid),
        .m_axi_rready    (m_axi_rready),
        .busy            ()
    );

endmodule : axi4_master_rd_crc_check
