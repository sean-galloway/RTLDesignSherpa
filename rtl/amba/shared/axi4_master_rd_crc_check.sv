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
//   Fully decoupled AR and R: two independent dma_address_gen instances
//   walk the same descriptor in parallel. AR runs as fast as arready +
//   addr-gen pipeline allow; R consumes at the slave's rvalid rate.
//   arvalid stays asserted from its first cycle to the last AR handshake
//   when cfg_rd_gap = 0. cfg_rd_gap > 0 pauses both AR and R together.
//   Multi-id deeper OOO is a v2 extension that needs per-id contexts.
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
    parameter logic [47:0]           LFSR_TAPS  = {12'd23, 12'd3, 12'd2, 12'd1},

    // ---- CRC (MUST match axi4_master_wr_pattern_gen) ----
    parameter int                    CRC_WIDTH      = 32,
    parameter int                    CRC_DATA_WIDTH = 32,
    parameter logic [CRC_WIDTH-1:0]  CRC_POLY       = 32'h04C11DB7,
    // Reflection MUST match the slave-side blocks (CRC_REFIN/REFOUT default 1
    // there) or writer-vs-slave CRC compares can never match. The old
    // hardcoded REFIN(0)/REFOUT(0) here broke the documented interchange --
    // unnoticed while the accumulate strobe was also tied off (both sides
    // emitted constant zero).
    parameter int                    CRC_REFIN      = 1,
    parameter int                    CRC_REFOUT     = 1,
    parameter logic [CRC_WIDTH-1:0]  CRC_POLY_INIT  = '1,
    parameter logic [CRC_WIDTH-1:0]  CRC_XOROUT     = '1,

    // ---- Workload ----
    parameter int TXN_COUNT_WIDTH = 16,
    parameter int INDEX_WIDTH     = 16,
    parameter int STRIDE_WIDTH    = 24,

    // Legal-AxLEN quantum: AXI beats per DRAM burst; cfg_burst_len MUST be a
    // nonzero integer multiple of this (one AXI burst -> integer DRAM bursts).
    // Project-specific (DRAM BL x gear x device width) -> a PARAMETER. 1 =
    // unconstrained (default). A non-conforming arlen SLVERR/partial-writes at
    // the intake and the CRC read-back then mismatches. Mirror of the write gen.
    parameter int BURST_LEN_MULTIPLE = 1,

    // ---- Debug observability ----
    // When > 0, instantiate a `DBG_FIFO_DEPTH`-deep gaxi_fifo_sync that
    // captures (actual_rdata, expected_data, mismatch_bit) on every R
    // beat handshake. The bench drains it via the dbg_* valid/ready
    // handshake and logs ground-truth disagreement per beat. When 0 the
    // generate block elides the FIFO and the dbg_* outputs are tied off.
    parameter int DBG_FIFO_DEPTH  = 0,

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
    input  logic [IW-1:0]                       cfg_axi_id,       // FIXED-mode id / start seed for COUNTER+LFSR modes
    // AR ID generation mode:
    //   0 = FIXED:   every AR uses cfg_axi_id verbatim
    //   1 = COUNTER: 8-bit counter starting at cfg_axi_id[7:0], +1 per AR
    //   2 = LFSR:    8-bit Fibonacci LFSR seeded from cfg_axi_id[7:0]|1
    input  logic [1:0]                          cfg_id_mode,
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
    // 1:1 accounting: TOO MANY beats is as much an error as too few. A stray /
    // late / duplicate R beat arriving while the engine is not consuming
    // (IDLE / DONE / GAP, or RUN with no burst outstanding) is DRAINED here
    // (so it cannot sit on the bus and poison the NEXT run's compare as its
    // first beat) and latched as a sticky error + count.
    output logic                                o_stray_beat_error,  // sticky
    output logic [TXN_COUNT_WIDTH-1:0]          o_stray_beats,       // count

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
    output logic                       m_axi_rready,

    // ==========================================================================
    // Debug observability — drained by the bench when DBG_FIFO_DEPTH > 0.
    // Each pop yields one (actual, expected, mismatch) record captured
    // at the corresponding R beat handshake. Tied off when depth == 0.
    // ==========================================================================
    output logic                       dbg_valid,
    input  logic                       dbg_ready,
    output logic [DW-1:0]              dbg_actual,
    output logic [DW-1:0]              dbg_expected,
    output logic                       dbg_mismatch
);

    //==========================================================================
    // Config guard — the AxLEN==integer-multiple-of-DRAM-burst requirement (read
    // side). On each cfg_start, verify cfg_burst_len is a nonzero multiple of
    // BURST_LEN_MULTIPLE (AXI beats per DRAM burst). A non-conforming value SLVERRs
    // / partial-reads at the intake and the CRC read-back mismatches. Sim-only
    // ($error); the host must validate before programming BLEN_TXN on silicon.
    // Skipped when BURST_LEN_MULTIPLE==1 (unconstrained). Mirror of the write gen.
    //==========================================================================
`ifndef SYNTHESIS
    always_ff @(posedge aclk) begin
        if (aresetn && cfg_start && (BURST_LEN_MULTIPLE > 1)) begin
            assert (cfg_burst_len != 8'd0)
                else $error("axi4_master_rd_crc_check: cfg_burst_len=0 illegal");
            assert ((32'(cfg_burst_len) % BURST_LEN_MULTIPLE) == 0)
                else $error("axi4_master_rd_crc_check: cfg_burst_len=%0d not a multiple of BURST_LEN_MULTIPLE=%0d (AXI beats per DRAM burst) -> ragged burst -> SLVERR/partial read",
                            cfg_burst_len, BURST_LEN_MULTIPLE);
        end
    end
`endif

    //==========================================================================
    // FSM — fully decoupled AR and R (two independent addr-gens). arvalid
    // never drops from first assertion to last AR handshake at gap=0.
    //==========================================================================
    typedef enum logic [1:0] {
        S_IDLE = 2'd0,
        S_RUN  = 2'd1,   // AR + R paths active
        S_GAP  = 2'd2,
        S_DONE = 2'd3
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
    logic                         r_data_mode;
    logic [31:0]                  r_hash_seed0;
    logic [31:0]                  r_hash_seed1;
    logic [31:0]                  r_hash_seed2;
    logic [1:0]                   r_id_mode;
    logic [7:0]                   r_id_counter;

    // Progress counters — AR and R paths advance independently.
    logic [TXN_COUNT_WIDTH-1:0]   r_ar_req_count;     // AR addr-gen req handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_ar_issued;        // AR handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_r_req_count;      // R addr-gen req handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_bursts_done;      // rlast handshakes
    logic [7:0]                   r_beats_in_burst;   // beat in current R burst
    logic [3:0]                   r_gap_left;

    //==========================================================================
    // dma_address_gen — two independent instances walking the same
    // descriptor. AR path uses u_addr_gen_ar; R path (for hash-mode
    // expected data regen) uses u_addr_gen_r.
    //==========================================================================
    logic                         w_ar_addr_req_valid;
    logic                         w_ar_addr_req_ready;
    logic                         w_ar_addr_result_valid;
    logic                         w_ar_addr_result_ready;
    logic [AW-1:0]                w_ar_addr_result;

    logic                         w_r_addr_req_valid;
    logic                         w_r_addr_req_ready;
    logic                         w_r_addr_result_valid;
    logic                         w_r_addr_result_ready;
    logic [AW-1:0]                w_r_addr_result;

    dma_address_gen #(
        .ADDR_WIDTH  (AW),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (8)
    ) u_addr_gen_ar (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_base_addr),
        .i_cfg_stride_0    (r_stride_0),
        .i_cfg_stride_1    (r_stride_1),
        .i_cfg_wrap_mask_0 (r_wrap_0),
        .i_cfg_wrap_mask_1 (r_wrap_1),

        .i_req_valid       (w_ar_addr_req_valid),
        .o_req_ready       (w_ar_addr_req_ready),
        .i_req_index_0     (INDEX_WIDTH'(r_ar_req_count)),
        .i_req_index_1     (INDEX_WIDTH'(0)),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_ar_addr_result_valid),
        .i_result_ready    (w_ar_addr_result_ready),
        .o_result_addr     (w_ar_addr_result),
        .o_result_tag      ()
    );

    dma_address_gen #(
        .ADDR_WIDTH  (AW),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (8)
    ) u_addr_gen_r (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_base_addr),
        .i_cfg_stride_0    (r_stride_0),
        .i_cfg_stride_1    (r_stride_1),
        .i_cfg_wrap_mask_0 (r_wrap_0),
        .i_cfg_wrap_mask_1 (r_wrap_1),

        .i_req_valid       (w_r_addr_req_valid),
        .o_req_ready       (w_r_addr_req_ready),
        .i_req_index_0     (INDEX_WIDTH'(r_r_req_count)),
        .i_req_index_1     (INDEX_WIDTH'(0)),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_r_addr_result_valid),
        .i_result_ready    (w_r_addr_result_ready),
        .o_result_addr     (w_r_addr_result),
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
        .REFIN     (CRC_REFIN),
        .REFOUT    (CRC_REFOUT)
    ) u_crc (
        .POLY              (CRC_POLY),
        .POLY_INIT         (CRC_POLY_INIT),
        .XOROUT            (CRC_XOROUT),
        .clk               (aclk),
        .rst_n             (aresetn),
        .load_crc_start    (w_lfsr_load),
        .load_from_cascade (w_r_beat),  // accumulate pre-advance LFSR word on every accepted R beat
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

    //==========================================================================
    // AR ID generator — mirrors the writer's AW ID logic.
    //==========================================================================
    logic [7:0]  w_id_lfsr_out;
    logic        w_id_lfsr_advance;

    assign w_id_lfsr_advance = fub_arvalid && fub_arready;

    shifter_lfsr_fibonacci #(
        .WIDTH          (8),
        .TAP_INDEX_WIDTH(4),
        .TAP_COUNT      (4)
    ) u_id_lfsr (
        .clk      (aclk),
        .rst_n    (aresetn),
        .enable   (w_id_lfsr_advance || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(cfg_axi_id[7:0] | 8'h01),
        .taps     ({4'd7, 4'd6, 4'd5, 4'd1}),
        .lfsr_out (w_id_lfsr_out),
        .lfsr_done()
    );

    logic [IW-1:0] w_ar_id_out;
    always_comb begin
        unique case (r_id_mode)
            2'd0:    w_ar_id_out = r_axi_id;
            2'd1:    w_ar_id_out = IW'(r_id_counter);
            2'd2:    w_ar_id_out = IW'(w_id_lfsr_out);
            default: w_ar_id_out = r_axi_id;
        endcase
    end

    assign w_r_beat = fub_rvalid && fub_rready;

    // ---- AR path ----
    assign w_ar_addr_req_valid = (r_state == S_RUN)
                              && (r_ar_req_count < r_txn_count);
    assign fub_arvalid         = (r_state == S_RUN)
                              && (r_ar_issued < r_txn_count)
                              && w_ar_addr_result_valid;
    assign w_ar_addr_result_ready = fub_arvalid && fub_arready;

    // ---- R path ----
    // Keep the R addr-gen producing per-burst base addresses for the
    // hash-mode expected data regen. Pop on rlast so the next burst's
    // base is in place for the following beat.
    assign w_r_addr_req_valid = (r_state == S_RUN)
                             && (r_r_req_count < r_txn_count);
    assign w_r_addr_result_ready = w_r_beat && fub_rlast;

    // Ready to absorb R beats only after the AR for this burst is on
    // the wire AND the R addr-gen has produced the base address.
    logic w_r_consuming, w_stray_beat;
    assign w_r_consuming = (r_state == S_RUN)
                        && (r_bursts_done < r_ar_issued)
                        && w_r_addr_result_valid;
    // A STRAY is an R beat with NO outstanding burst to own it (over-delivery
    // or a late return from a previous run): DRAIN it (rready high) and flag
    // it, instead of leaving it parked on the bus to desync the next run's
    // compare. A beat for an OUTSTANDING burst that we are merely not ready
    // to consume yet (S_GAP, addr-gen not ready) is NOT a stray — it waits on
    // the bus exactly as before.
    // Detect on the FUB side of the internal read skid, not the m_axi pins:
    // the skid has no same-cycle fall-through, so a pin-side detect accepted
    // the stray INTO the skid and then dropped rready -- the beat parked at
    // the skid head and poisoned the next run's first compare (the exact
    // failure this drain exists to prevent). fub_rvalid sees the parked beat
    // until it is genuinely popped.
    assign w_stray_beat  = fub_rvalid && !w_r_consuming
                        && (r_bursts_done == r_ar_issued);
    assign fub_rready    = w_r_consuming || w_stray_beat;

    //==========================================================================
    // Expected pattern data — two sources, muxed by r_data_mode:
    //   mode 0: 32-bit Fibonacci LFSR replicated across DW (phase-counter)
    //   mode 1: 32-bit Murmur3-fmix-style address hash, per-32-bit slice
    //==========================================================================
    localparam int REPLICATION_FACTOR = (DW + 31) / 32;
    logic [REPLICATION_FACTOR*32-1:0] w_expected_replicated;
    assign w_expected_replicated = {REPLICATION_FACTOR{w_lfsr_out}};

    // Per-beat byte address for hash mode. Anchored on w_r_addr_result
    // (current burst's base from the R addr-gen).
    logic [AW-1:0]                w_byte_addr_for_beat;
    assign w_byte_addr_for_beat = w_r_addr_result
        + (AW'({{(AW-8){1'b0}}, r_beats_in_burst}) << r_axi_size);

    // ---- Compare pipeline (matches the pipelined hash latency) -------------
    // The mode-1 expected-data hash chains two 32-bit multiplies — the same
    // ~25 ns / 4-DSP cone as the writer, which combinationally fed the per-beat
    // compare and missed 100 MHz. Here each multiply is isolated in its own
    // register stage; the RETURNED rdata rides through the same stages so the
    // compare happens at the pipeline output, aligned with the delayed expected
    // value. The R handshake and beat/burst accounting are unchanged (still
    // keyed on w_r_beat); only the data compare is delayed, and cfg_done waits
    // for the pipeline to drain so no trailing mismatch is missed.
    localparam int REP     = REPLICATION_FACTOR;
    localparam int HSTAGES = 4;                 // 2 mults, each isolated

    logic [31:0] w_s1_odd, w_s2_odd;
    assign w_s1_odd = r_hash_seed1 | 32'h1;
    assign w_s2_odd = r_hash_seed2 | 32'h1;

    // Combinational stage-0: (addr + s*4) ^ s0, then ^ >>16 (cheap).
    logic [REP-1:0][31:0] w_cp_t_in;
    always_comb begin
        for (int s = 0; s < REP; s++) begin
            logic [31:0] x;
            x = (w_byte_addr_for_beat[31:0] + 32'(s * 4)) ^ r_hash_seed0;
            w_cp_t_in[s] = x ^ (x >> 16);
        end
    end

    logic [HSTAGES-1:0]         r_cp_valid;
    logic [HSTAGES-1:0]         r_cp_mode;
    logic [HSTAGES-1:0][DW-1:0] r_cp_rdata;   // returned data, delayed to match
    logic [HSTAGES-1:0][DW-1:0] r_cp_lfsr;    // expected LFSR-replicated data
    logic [REP-1:0][31:0]       r_cp_t;    // s1: (addr^s0)^>>16
    logic [REP-1:0][31:0]       r_cp_p1;   // s2: t * s1_odd   (multiply #1)
    logic [REP-1:0][31:0]       r_cp_u;    // s3: p1 ^ (p1>>13)
    logic [REP-1:0][31:0]       r_cp_p2;   // s4: u * s2_odd   (multiply #2)

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_cp_valid <= '0;
            r_cp_mode  <= '0;
            r_cp_rdata <= '0;
            r_cp_lfsr  <= '0;
            r_cp_t     <= '0;
            r_cp_p1    <= '0;
            r_cp_u     <= '0;
            r_cp_p2    <= '0;
        end else begin
            // Stage 1: capture an arriving R beat.
            r_cp_valid[0] <= w_r_beat;
            r_cp_mode [0] <= r_data_mode;
            r_cp_rdata[0] <= fub_rdata;
            r_cp_lfsr [0] <= w_expected_replicated[DW-1:0];
            r_cp_t        <= w_cp_t_in;
            // Stage 2: first multiply.
            r_cp_valid[1] <= r_cp_valid[0];
            r_cp_mode [1] <= r_cp_mode [0];
            r_cp_rdata[1] <= r_cp_rdata[0];
            r_cp_lfsr [1] <= r_cp_lfsr [0];
            for (int s = 0; s < REP; s++) r_cp_p1[s] <= r_cp_t[s] * w_s1_odd;
            // Stage 3: xorshift.
            r_cp_valid[2] <= r_cp_valid[1];
            r_cp_mode [2] <= r_cp_mode [1];
            r_cp_rdata[2] <= r_cp_rdata[1];
            r_cp_lfsr [2] <= r_cp_lfsr [1];
            for (int s = 0; s < REP; s++) r_cp_u[s] <= r_cp_p1[s] ^ (r_cp_p1[s] >> 13);
            // Stage 4: second multiply.
            r_cp_valid[3] <= r_cp_valid[2];
            r_cp_mode [3] <= r_cp_mode [2];
            r_cp_rdata[3] <= r_cp_rdata[2];
            r_cp_lfsr [3] <= r_cp_lfsr [2];
            for (int s = 0; s < REP; s++) r_cp_p2[s] <= r_cp_u[s] * w_s2_odd;
        end
    end)

    // Pipeline output: expected = mode ? hash : lfsr; compare vs delayed rdata.
    logic [DW-1:0] w_cp_expected;
    always_comb begin
        logic [REP*32-1:0] hash_word;
        for (int s = 0; s < REP; s++)
            hash_word[s*32 +: 32] = r_cp_p2[s] ^ (r_cp_p2[s] >> 16);
        w_cp_expected = r_cp_mode[HSTAGES-1] ? hash_word[DW-1:0]
                                             : r_cp_lfsr[HSTAGES-1];
    end

    // Per-beat data mismatch at the pipeline output.
    logic w_cp_mismatch;
    assign w_cp_mismatch = r_cp_valid[HSTAGES-1]
                        && (r_cp_rdata[HSTAGES-1] != w_cp_expected);

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
            r_id_mode          <= 2'd0;
            r_id_counter       <= 8'd0;
            r_ar_req_count     <= '0;
            r_ar_issued        <= '0;
            r_r_req_count      <= '0;
            r_bursts_done      <= '0;
            r_beats_in_burst   <= 8'd0;
            r_gap_left         <= 4'd0;
            o_actual_crc_valid <= 1'b0;
            o_data_error       <= 1'b0;
            o_rresp_error      <= 1'b0;
            o_beats_mismatched <= '0;
            o_stray_beat_error <= 1'b0;
            o_stray_beats      <= '0;
        end else begin
            // stray-beat drain accounting (any state; cfg_start clears)
            if (w_stray_beat && fub_rvalid && fub_rready) begin
                o_stray_beat_error <= 1'b1;
                o_stray_beats      <= o_stray_beats + 1'b1;
            end
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
                        r_id_mode       <= cfg_id_mode;
                        r_id_counter    <= cfg_axi_id[7:0];
                        r_rd_gap        <= cfg_rd_gap;
                        r_ar_req_count   <= '0;
                        r_ar_issued      <= '0;
                        r_r_req_count    <= '0;
                        r_bursts_done    <= '0;
                        r_beats_in_burst <= 8'd0;
                        r_gap_left       <= 4'd0;
                        o_actual_crc_valid <= 1'b0;
                        o_data_error       <= 1'b0;
                        o_rresp_error      <= 1'b0;
                        o_beats_mismatched <= '0;
                        o_stray_beat_error <= 1'b0;
                        o_stray_beats      <= '0;
                        r_state         <= (cfg_txn_count == '0) ? S_DONE : S_RUN;
                    end
                end

                S_RUN: begin
                    // AR addr-gen req
                    if (w_ar_addr_req_valid && w_ar_addr_req_ready) begin
                        r_ar_req_count <= r_ar_req_count + 1'b1;
                    end
                    // AR handshake
                    if (fub_arvalid && fub_arready) begin
                        r_ar_issued  <= r_ar_issued + 1'b1;
                        r_id_counter <= r_id_counter + 8'd1;
                    end
                    // R addr-gen req
                    if (w_r_addr_req_valid && w_r_addr_req_ready) begin
                        r_r_req_count <= r_r_req_count + 1'b1;
                    end
                    // R beat handshake
                    if (w_r_beat) begin
                        if (fub_rlast) begin
                            r_beats_in_burst <= 8'd0;
                            r_bursts_done    <= r_bursts_done + 1'b1;
                            if (r_bursts_done + 1'b1 == r_txn_count) begin
                                r_state            <= S_DONE;
                                o_actual_crc_valid <= !r_data_mode;
                            end else if (r_rd_gap != 4'd0) begin
                                r_state    <= S_GAP;
                                r_gap_left <= r_rd_gap;
                            end
                        end else begin
                            r_beats_in_burst <= r_beats_in_burst + 8'd1;
                        end
                    end
                end

                S_GAP: begin
                    if (r_gap_left == 4'd1) begin
                        r_state    <= S_RUN;
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
                        r_id_mode       <= cfg_id_mode;
                        r_id_counter    <= cfg_axi_id[7:0];
                        r_rd_gap        <= cfg_rd_gap;
                        r_ar_req_count   <= '0;
                        r_ar_issued      <= '0;
                        r_r_req_count    <= '0;
                        r_bursts_done    <= '0;
                        r_beats_in_burst <= 8'd0;
                        r_gap_left       <= 4'd0;
                        o_actual_crc_valid <= 1'b0;
                        o_data_error       <= 1'b0;
                        o_rresp_error      <= 1'b0;
                        o_beats_mismatched <= '0;
                        r_state            <= (cfg_txn_count == '0) ? S_DONE : S_RUN;
                    end
                end

                default: r_state <= S_IDLE;
            endcase

            // Per-beat data mismatch — accumulated at the compare-pipeline
            // output (delayed HSTAGES cycles from the R beat). rresp is checked
            // immediately at the R beat (no hash dependency).
            if (w_cp_mismatch) begin
                o_data_error       <= 1'b1;
                o_beats_mismatched <= o_beats_mismatched + 1'b1;
            end
            if (w_r_beat && fub_rresp != 2'b00) begin
                o_rresp_error <= 1'b1;
            end
        end
    end)

    assign w_lfsr_load = cfg_start && ((r_state == S_IDLE) || (r_state == S_DONE));

    // Wait for the compare pipeline to drain so trailing beats' mismatches
    // are accumulated before cfg_done is observed.
    assign cfg_done = (r_state == S_DONE)
                   && (r_bursts_done == r_txn_count)
                   && !(|r_cp_valid);

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
        .fub_axi_arid    (w_ar_id_out),
        .fub_axi_araddr  (w_ar_addr_result),
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

    //==========================================================================
    // Debug FIFO — only synthesized when DBG_FIFO_DEPTH > 0. Captures
    // (actual, expected, mismatch) per R beat handshake so the bench can
    // walk the disagreements rather than guessing from `o_data_error`
    // alone. When DBG_FIFO_DEPTH == 0 the generate `else` arm ties the
    // outputs to 0 and the FIFO is not built.
    //==========================================================================
    generate
        if (DBG_FIFO_DEPTH > 0) begin : g_dbg_fifo
            localparam int DBG_REC_W = 2 * DW + 1;
            logic [DBG_REC_W-1:0] w_dbg_din;
            logic [DBG_REC_W-1:0] w_dbg_dout;
            logic                 w_dbg_wr_ready_unused;

            // Captured at the compare-pipeline output (delayed to match the
            // hash latency) so the trace record's expected/mismatch line up
            // with the returned data.
            assign w_dbg_din = {r_cp_rdata[HSTAGES-1], w_cp_expected, w_cp_mismatch};

            gaxi_fifo_sync #(
                .DATA_WIDTH (DBG_REC_W),
                .DEPTH      (DBG_FIFO_DEPTH)
            ) u_dbg_fifo (
                .axi_aclk    (aclk),
                .axi_aresetn (aresetn),
                .wr_valid    (r_cp_valid[HSTAGES-1]),
                .wr_ready    (w_dbg_wr_ready_unused),
                .wr_data     (w_dbg_din),
                .rd_ready    (dbg_ready),
                .rd_valid    (dbg_valid),
                .rd_data     (w_dbg_dout),
                .count       ()
            );

            assign dbg_actual   = w_dbg_dout[DBG_REC_W-1   -: DW];
            assign dbg_expected = w_dbg_dout[DBG_REC_W-1-DW -: DW];
            assign dbg_mismatch = w_dbg_dout[0];
        end else begin : g_no_dbg
            assign dbg_valid    = 1'b0;
            assign dbg_actual   = '0;
            assign dbg_expected = '0;
            assign dbg_mismatch = 1'b0;
        end
    endgenerate

endmodule : axi4_master_rd_crc_check
