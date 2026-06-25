// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr_pattern_gen
// Purpose: Master-side write driver for memory-controller characterization.
//          Walks an algorithmic address mix (via dma_address_gen) and emits
//          LFSR-pattern data (via shifter_lfsr_fibonacci) through axi4_master_wr.
//          Accumulates a CRC-32 over the data written so the read-side
//          (axi4_master_rd_crc_check) has an expected value to compare against.
//
// Documentation: projects/NexysA7/ddr2-characterization/README.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-06-25

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: axi4_master_wr_pattern_gen
//==============================================================================
// Description:
//   Drives a CSR-programmed sequence of AXI4 write bursts at the FUB side of
//   `axi4_master_wr`, with addresses from `dma_address_gen` and data from a
//   Fibonacci LFSR seeded by the CSR. Pairs with `axi4_master_rd_crc_check`
//   for end-to-end data integrity validation.
//
//   Workflow:
//     1. Software programs the cfg_* ports (start addr, addr-gen knobs,
//        burst len, txn count, AXI id/size/burst attributes).
//     2. Software pulses `cfg_start`.
//     3. The block walks index_0 = 0..cfg_txn_count-1 through dma_address_gen,
//        issuing one AW per index. For each AW it streams `cfg_burst_len`
//        beats of LFSR data on W. The LFSR advances on every W beat
//        (regardless of burst boundary), so the data stream is a
//        deterministic function of (cfg_lfsr_seed, total_beats_so_far).
//     4. dataint_crc accumulates over the same LFSR stream; o_expected_crc
//        carries the running value, latched valid on cfg_done.
//     5. When all cfg_txn_count B responses have been received,
//        `cfg_done` asserts and stays high until the next cfg_start pulse.
//
//   Fully decoupled AW and W: two independent dma_address_gen instances
//   walk the same descriptor in parallel. AW runs as fast as awready +
//   addr-gen pipeline allow; W runs at slave's wready rate. awvalid
//   stays asserted from its first cycle to the last AW handshake when
//   cfg_wr_gap = 0 — the addr-gen produces 1 result/cycle once warmed
//   up. cfg_wr_gap > 0 pauses both AW and W together. AXI4 outstanding
//   is bounded by the slave's awready throttling, not by this block.
//
//   Address dimensions: walks dma_address_gen's index_0 only; index_1 is
//   held at 0. To exercise the 2D path, instantiate a second pattern_gen
//   with a different cfg_addr_stride_1 + descriptor program.
//
// Parameters:
//   AXI_*          - standard AXI4 widths
//   LFSR_WIDTH     - LFSR width; defaults to 32. Matches the slave-side
//                    block so master/slave CRC values are interchangeable.
//   LFSR_TAPS      - maximal-length Fibonacci taps; default {32,22,2,1}.
//   CRC_WIDTH      - CRC width; 32 by default
//   CRC_DATA_WIDTH - bytes per CRC update; we update 32 bits per LFSR step
//                    so this is fixed at 32 to match the slave side.
//   TXN_COUNT_WIDTH- width of cfg_txn_count; default 16 (up to 64K bursts)
//   INDEX_WIDTH    - dma_address_gen index width; default 16
//   STRIDE_WIDTH   - dma_address_gen signed stride width; default 24
//==============================================================================
module axi4_master_wr_pattern_gen #(
    // ---- AXI ----
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 4,
    parameter int SKID_DEPTH_B  = 2,
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int AXI_USER_WIDTH  = 1,
    parameter int AXI_WSTRB_WIDTH = AXI_DATA_WIDTH / 8,

    // ---- LFSR ----
    parameter int                    LFSR_WIDTH = 32,
    parameter logic [31:0]           LFSR_SEED  = 32'hDEADBEEF,
    parameter logic [47:0]           LFSR_TAPS  = {12'd32, 12'd22, 12'd2, 12'd1},

    // ---- CRC (mirror slave-side defaults so the two are interchangeable) ----
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
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_WSTRB_WIDTH
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    // ==========================================================================
    // Configuration — programmed by the harness CSR. Static during a run;
    // a new cfg_start pulse re-samples them.
    // ==========================================================================
    // Address generator descriptor (passed through to dma_address_gen)
    input  logic [AW-1:0]                       cfg_start_addr,
    input  logic signed [STRIDE_WIDTH-1:0]      cfg_addr_stride_0,
    input  logic signed [STRIDE_WIDTH-1:0]      cfg_addr_stride_1,
    input  logic [AW-1:0]                       cfg_addr_wrap_mask_0,
    input  logic [AW-1:0]                       cfg_addr_wrap_mask_1,

    // Burst shape
    input  logic [7:0]                          cfg_burst_len,    // beats (1..256). awlen = cfg_burst_len - 1
    input  logic [TXN_COUNT_WIDTH-1:0]          cfg_txn_count,    // total bursts to issue
    input  logic [IW-1:0]                       cfg_axi_id,       // ID for all AW
    input  logic [2:0]                          cfg_axi_size,     // awsize
    input  logic [1:0]                          cfg_axi_burst,    // awburst (INCR=1)

    // LFSR seed override — if 0, defaults to the LFSR_SEED parameter.
    // Lets the CSR re-seed without recompile.
    input  logic [LFSR_WIDTH-1:0]               cfg_lfsr_seed,

    // Data source select: 0 = phase-counter LFSR (default, OOO-unsafe);
    // 1 = address-derived hash (OOO-safe, data is f(beat_byte_addr)).
    // Hash mode lets multi-id / OOO-completion traffic still validate
    // because each beat's expected data is a pure function of its
    // address — no phase counter to get out of sync. The 3 seeds drive
    // a Murmur3-fmix-style mixer (xor-shift + odd mul) so all-zero or
    // all-one input addresses don't collapse to stuck output patterns.
    input  logic                                cfg_data_mode,
    input  logic [31:0]                         cfg_hash_seed0,
    input  logic [31:0]                         cfg_hash_seed1,
    input  logic [31:0]                         cfg_hash_seed2,

    // Inter-burst idle gap. Adds 0..15 idle cycles between the end of one
    // burst (wlast accepted) and the next AW request. Used to vary the
    // throughput stress on the downstream controller during sweeps.
    input  logic [3:0]                          cfg_wr_gap,

    // Start / done handshake
    input  logic                                cfg_start,        // pulse → begin workload
    output logic                                cfg_done,         // high once all B's received

    // ==========================================================================
    // Telemetry
    // ==========================================================================
    output logic [CRC_WIDTH-1:0]                o_expected_crc,
    output logic                                o_expected_crc_valid,  // high with cfg_done
    output logic                                o_bresp_error,         // sticky on any non-OKAY BRESP

    // ==========================================================================
    // M-side AXI4 (out to the fabric → controller → DRAM)
    // ==========================================================================
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready
);

    //==========================================================================
    // FSM — fully decoupled AW and W (two independent addr-gens). awvalid
    // never drops from first assertion to last AW handshake at gap=0.
    //==========================================================================
    typedef enum logic [1:0] {
        S_IDLE = 2'd0,   // wait for cfg_start
        S_RUN  = 2'd1,   // AW + W paths active
        S_GAP  = 2'd2,   // cfg_wr_gap idle cycles between bursts
        S_DONE = 2'd3    // all wlast issued; await final B's
    } state_e;

    state_e                       r_state;

    // Latched workload program (sampled at cfg_start so software can change
    // cfg_* in the next cycle without disturbing the run).
    logic [AW-1:0]                r_base_addr;
    logic signed [STRIDE_WIDTH-1:0] r_stride_0, r_stride_1;
    logic [AW-1:0]                r_wrap_0, r_wrap_1;
    logic [7:0]                   r_burst_len;
    logic [3:0]                   r_wr_gap;
    logic [TXN_COUNT_WIDTH-1:0]   r_txn_count;
    logic [IW-1:0]                r_axi_id;
    logic [2:0]                   r_axi_size;
    logic [1:0]                   r_axi_burst;
    logic [LFSR_WIDTH-1:0]        r_lfsr_seed_eff;
    logic                         r_data_mode;       // 0=LFSR, 1=ADDR_HASH
    logic [31:0]                  r_hash_seed0;
    logic [31:0]                  r_hash_seed1;
    logic [31:0]                  r_hash_seed2;

    // Progress counters — AW and W paths advance independently. AW path
    // tracks request + handshake counts for the AW addr-gen. W path
    // tracks request + handshake counts for the W addr-gen.
    logic [TXN_COUNT_WIDTH-1:0]   r_aw_req_count;     // AW addr-gen req handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_aw_issued;        // AW handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_w_req_count;      // W addr-gen req handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_w_bursts_done;    // wlast handshakes
    logic [TXN_COUNT_WIDTH-1:0]   r_b_received;       // B handshakes
    logic [7:0]                   r_w_beat_idx;       // beat in current W burst
    logic [3:0]                   r_gap_left;         // S_GAP countdown

    //==========================================================================
    // dma_address_gen — two independent instances walking the same
    // descriptor. AW path uses u_addr_gen_aw; W path uses u_addr_gen_w.
    // Same cfg + same indices => same address sequence in both.
    //==========================================================================
    logic                         w_aw_addr_req_valid;
    logic                         w_aw_addr_req_ready;
    logic                         w_aw_addr_result_valid;
    logic                         w_aw_addr_result_ready;
    logic [AW-1:0]                w_aw_addr_result;

    logic                         w_w_addr_req_valid;
    logic                         w_w_addr_req_ready;
    logic                         w_w_addr_result_valid;
    logic                         w_w_addr_result_ready;
    logic [AW-1:0]                w_w_addr_result;

    dma_address_gen #(
        .ADDR_WIDTH  (AW),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (8)
    ) u_addr_gen_aw (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_base_addr),
        .i_cfg_stride_0    (r_stride_0),
        .i_cfg_stride_1    (r_stride_1),
        .i_cfg_wrap_mask_0 (r_wrap_0),
        .i_cfg_wrap_mask_1 (r_wrap_1),

        .i_req_valid       (w_aw_addr_req_valid),
        .o_req_ready       (w_aw_addr_req_ready),
        .i_req_index_0     (INDEX_WIDTH'(r_aw_req_count)),
        .i_req_index_1     (INDEX_WIDTH'(0)),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_aw_addr_result_valid),
        .i_result_ready    (w_aw_addr_result_ready),
        .o_result_addr     (w_aw_addr_result),
        .o_result_tag      ()
    );

    dma_address_gen #(
        .ADDR_WIDTH  (AW),
        .INDEX_WIDTH (INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH),
        .TAG_WIDTH   (8)
    ) u_addr_gen_w (
        .i_clk             (aclk),
        .i_rst_n           (aresetn),

        .i_cfg_base_addr   (r_base_addr),
        .i_cfg_stride_0    (r_stride_0),
        .i_cfg_stride_1    (r_stride_1),
        .i_cfg_wrap_mask_0 (r_wrap_0),
        .i_cfg_wrap_mask_1 (r_wrap_1),

        .i_req_valid       (w_w_addr_req_valid),
        .o_req_ready       (w_w_addr_req_ready),
        .i_req_index_0     (INDEX_WIDTH'(r_w_req_count)),
        .i_req_index_1     (INDEX_WIDTH'(0)),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_w_addr_result_valid),
        .i_result_ready    (w_w_addr_result_ready),
        .o_result_addr     (w_w_addr_result),
        .o_result_tag      ()
    );

    //==========================================================================
    // LFSR — advances on every accepted W beat (or seed-load at cfg_start).
    //==========================================================================
    logic                         w_w_beat;       // accepted W beat at FUB side
    logic                         w_lfsr_load;    // pulse cfg_start to load seed
    logic [LFSR_WIDTH-1:0]        w_lfsr_out;

    // Seed value to drive on cfg_start. r_lfsr_seed_eff updates one
    // cycle later (NBA from the FSM block), so to load the *correct*
    // seed at cfg_start we must mux it combinationally here.
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
        .enable   (w_w_beat || w_lfsr_load),
        .seed_load(w_lfsr_load),
        .seed_data(w_lfsr_seed_data),
        .taps     (LFSR_TAPS),
        .lfsr_out (w_lfsr_out),
        .lfsr_done()
    );

    //==========================================================================
    // CRC — accumulates over the SAME LFSR stream we send out on W.
    //==========================================================================
    logic [CRC_WIDTH-1:0]         w_expected_crc;
    logic                         w_crc_load_start;

    assign w_crc_load_start = w_lfsr_load;

    // dataint_crc's CHUNKS = DATA_WIDTH / 8 → 4 for 32-bit. cascade_sel
    // selects which byte index drives the cascade; tie all 4 hot so every
    // byte of every LFSR output participates in the CRC.
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
        .load_crc_start    (w_crc_load_start),
        .load_from_cascade (1'b0),
        .cascade_sel       ({W_CRC_CHUNKS{1'b1}}),
        .data              (w_lfsr_out),
        .crc               (w_expected_crc)
    );

    //==========================================================================
    // FUB-side AXI handshakes — driven from FSM + LFSR
    //==========================================================================
    logic                         fub_awvalid;
    logic                         fub_awready;
    logic                         fub_wvalid;
    logic                         fub_wready;
    logic                         fub_wlast;
    logic                         fub_bvalid;
    logic                         fub_bready;
    logic [1:0]                   fub_bresp;

    assign w_w_beat = fub_wvalid && fub_wready;

    // ---- AW path ----
    // Keep the AW addr-gen requested for every AW we'll issue. addr-gen
    // self-throttles via req_ready.
    assign w_aw_addr_req_valid = (r_state == S_RUN)
                              && (r_aw_req_count < r_txn_count);

    // awvalid stays asserted as long as we have AWs left and the addr-gen
    // has produced the next address. No outstanding cap — slave's awready
    // throttles. Gap pauses by switching state away from S_RUN.
    assign fub_awvalid       = (r_state == S_RUN)
                            && (r_aw_issued < r_txn_count)
                            && w_aw_addr_result_valid;
    assign w_aw_addr_result_ready = fub_awvalid && fub_awready;

    // ---- W path ----
    // Same shape on the W addr-gen: keep requesting per-burst base
    // addresses. Pop on wlast so the next burst's base lines up.
    assign w_w_addr_req_valid = (r_state == S_RUN)
                             && (r_w_req_count < r_txn_count);

    // W beats: only stream if (a) the slave has at least seen this
    // burst's AW (r_w_bursts_done < r_aw_issued) and (b) the W addr-gen
    // has produced the base address.
    assign fub_wvalid        = (r_state == S_RUN)
                            && (r_w_bursts_done < r_aw_issued)
                            && w_w_addr_result_valid;
    assign fub_wlast         = fub_wvalid
                            && (r_w_beat_idx == r_burst_len - 8'd1);
    assign w_w_addr_result_ready = w_w_beat && fub_wlast;

    // B is always ready once we're past IDLE so the slave can drain B's
    // even during S_GAP or S_DONE.
    assign fub_bready        = (r_state != S_IDLE);

    //==========================================================================
    // Data path — two sources, muxed by r_data_mode:
    //   mode 0: 32-bit Fibonacci LFSR replicated across DW (phase-counter,
    //           breaks under multi-id / OOO completion)
    //   mode 1: 32-bit Murmur3-fmix-style address hash, per-32-bit slice
    //           (OOO-safe: each beat's data is f(byte_addr, seeds), so
    //           reorder doesn't perturb the per-beat compare)
    //
    // In mode 1 the CRC pipeline (which was built for the phase-counter
    // contract) is not load-bearing; o_expected_crc_valid is gated low and
    // the harness must use per-beat compare (o_data_error) for integrity.
    //==========================================================================
    localparam int REPLICATION_FACTOR = (DW + 31) / 32;
    logic [REPLICATION_FACTOR*32-1:0] w_data_replicated;
    assign w_data_replicated = {REPLICATION_FACTOR{w_lfsr_out}};

    // Per-beat byte address for the CURRENT W burst. Anchored on
    // w_w_addr_result (the W addr-gen's current output) and stepped by
    // 2**axsize bytes per beat. Full-beat writes only — strobes are
    // all-ones.
    logic [AW-1:0]                w_byte_addr_for_beat;
    assign w_byte_addr_for_beat = w_w_addr_result
        + (AW'({{(AW-8){1'b0}}, r_w_beat_idx}) << r_axi_size);

    // Murmur3 fmix32-style mixer with all three constants replaced by
    // cfg seeds. Odd-forced multiplies + xor-shifts kill low-entropy inputs
    // (addr = 0, addr = ~0, etc.) — the avalanche property says one input
    // bit flips ≥ half the output bits.
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

    // One hash per 32-bit slice in the beat. Slice s uses byte_addr + s*4
    // so different slices within the same beat differ as well.
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

    // Final W data: mode select between LFSR-replicated and hash.
    logic [DW-1:0]                    w_wdata_out;
    assign w_wdata_out = r_data_mode
                       ? w_hash_replicated[DW-1:0]
                       : w_data_replicated[DW-1:0];

    //==========================================================================
    // Sequential FSM + counters
    //==========================================================================
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_state           <= S_IDLE;
            r_base_addr       <= '0;
            r_stride_0        <= '0;
            r_stride_1        <= '0;
            r_wrap_0          <= '0;
            r_wrap_1          <= '0;
            r_burst_len       <= 8'd0;
            r_wr_gap          <= 4'd0;
            r_txn_count       <= '0;
            r_axi_id          <= '0;
            r_axi_size        <= 3'd0;
            r_axi_burst       <= 2'd1;   // INCR
            r_lfsr_seed_eff   <= LFSR_SEED;
            r_data_mode       <= 1'b0;
            r_hash_seed0      <= 32'd0;
            r_hash_seed1      <= 32'd0;
            r_hash_seed2      <= 32'd0;
            r_aw_req_count    <= '0;
            r_aw_issued       <= '0;
            r_w_req_count     <= '0;
            r_w_bursts_done   <= '0;
            r_b_received      <= '0;
            r_w_beat_idx      <= 8'd0;
            r_gap_left        <= 4'd0;
            o_expected_crc       <= '0;
            o_expected_crc_valid <= 1'b0;
            o_bresp_error        <= 1'b0;
        end else begin
            unique case (r_state)
                S_IDLE: begin
                    if (cfg_start) begin
                        // Latch the program
                        r_base_addr     <= cfg_start_addr;
                        r_stride_0      <= cfg_addr_stride_0;
                        r_stride_1      <= cfg_addr_stride_1;
                        r_wrap_0        <= cfg_addr_wrap_mask_0;
                        r_wrap_1        <= cfg_addr_wrap_mask_1;
                        r_burst_len     <= (cfg_burst_len == 8'd0) ? 8'd1 : cfg_burst_len;
                        r_wr_gap        <= cfg_wr_gap;
                        r_txn_count     <= cfg_txn_count;
                        r_axi_id        <= cfg_axi_id;
                        r_axi_size      <= cfg_axi_size;
                        r_axi_burst     <= cfg_axi_burst;
                        r_lfsr_seed_eff <= (cfg_lfsr_seed == '0) ? LFSR_SEED : cfg_lfsr_seed;
                        r_data_mode     <= cfg_data_mode;
                        r_hash_seed0    <= cfg_hash_seed0;
                        r_hash_seed1    <= cfg_hash_seed1;
                        r_hash_seed2    <= cfg_hash_seed2;
                        r_aw_req_count   <= '0;
                        r_aw_issued      <= '0;
                        r_w_req_count    <= '0;
                        r_w_bursts_done  <= '0;
                        r_b_received     <= '0;
                        r_w_beat_idx     <= 8'd0;
                        r_gap_left       <= 4'd0;
                        o_expected_crc_valid <= 1'b0;
                        o_bresp_error        <= 1'b0;
                        r_state         <= (cfg_txn_count == '0) ? S_DONE : S_RUN;
                    end
                end

                S_RUN: begin
                    // ---- AW addr-gen req counter ----
                    if (w_aw_addr_req_valid && w_aw_addr_req_ready) begin
                        r_aw_req_count <= r_aw_req_count + 1'b1;
                    end
                    // ---- AW handshake ----
                    if (fub_awvalid && fub_awready) begin
                        r_aw_issued <= r_aw_issued + 1'b1;
                    end
                    // ---- W addr-gen req counter ----
                    if (w_w_addr_req_valid && w_w_addr_req_ready) begin
                        r_w_req_count <= r_w_req_count + 1'b1;
                    end

                    // ---- W beat handshake ----
                    if (w_w_beat) begin
                        if (fub_wlast) begin
                            r_w_beat_idx    <= 8'd0;
                            r_w_bursts_done <= r_w_bursts_done + 1'b1;
                            if (r_w_bursts_done + 1'b1 == r_txn_count) begin
                                r_state <= S_DONE;
                            end else if (r_wr_gap != 4'd0) begin
                                r_state    <= S_GAP;
                                r_gap_left <= r_wr_gap;
                            end
                        end else begin
                            r_w_beat_idx <= r_w_beat_idx + 8'd1;
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
                        // Re-arm directly — same latch set as S_IDLE.
                        r_base_addr     <= cfg_start_addr;
                        r_stride_0      <= cfg_addr_stride_0;
                        r_stride_1      <= cfg_addr_stride_1;
                        r_wrap_0        <= cfg_addr_wrap_mask_0;
                        r_wrap_1        <= cfg_addr_wrap_mask_1;
                        r_burst_len     <= (cfg_burst_len == 8'd0) ? 8'd1 : cfg_burst_len;
                        r_wr_gap        <= cfg_wr_gap;
                        r_txn_count     <= cfg_txn_count;
                        r_axi_id        <= cfg_axi_id;
                        r_axi_size      <= cfg_axi_size;
                        r_axi_burst     <= cfg_axi_burst;
                        r_lfsr_seed_eff <= (cfg_lfsr_seed == '0) ? LFSR_SEED : cfg_lfsr_seed;
                        r_data_mode     <= cfg_data_mode;
                        r_hash_seed0    <= cfg_hash_seed0;
                        r_hash_seed1    <= cfg_hash_seed1;
                        r_hash_seed2    <= cfg_hash_seed2;
                        r_aw_req_count   <= '0;
                        r_aw_issued      <= '0;
                        r_w_req_count    <= '0;
                        r_w_bursts_done  <= '0;
                        r_b_received     <= '0;
                        r_w_beat_idx     <= 8'd0;
                        r_gap_left       <= 4'd0;
                        o_expected_crc_valid <= 1'b0;
                        o_bresp_error        <= 1'b0;
                        r_state              <= (cfg_txn_count == '0) ? S_DONE : S_RUN;
                    end
                end

                default: r_state <= S_IDLE;
            endcase

            // B-response accounting (independent of FSM phase, except we
            // never accept B while in IDLE pre-start).
            if (fub_bvalid && fub_bready) begin
                r_b_received <= r_b_received + 1'b1;
                if (fub_bresp != 2'b00) begin
                    o_bresp_error <= 1'b1;
                end
            end

            // Latch the expected CRC at the last W beat of the last burst.
            // Only meaningful in LFSR mode; hash mode uses per-beat compare
            // (o_data_error on the read side) as the integrity contract.
            if (r_state == S_RUN && w_w_beat && fub_wlast
                && r_w_bursts_done + 1'b1 == r_txn_count
                && !r_data_mode) begin
                o_expected_crc       <= w_expected_crc;
                o_expected_crc_valid <= 1'b1;
            end
        end
    end)

    // Pulse on any cfg_start that initiates a run — IDLE→RUN OR the
    // S_DONE direct re-arm.
    assign w_lfsr_load = cfg_start && ((r_state == S_IDLE) || (r_state == S_DONE));

    // cfg_done: all txn_count B's received AND we're past the active run.
    assign cfg_done = (r_state == S_DONE)
                   && (r_b_received == r_txn_count);

    //==========================================================================
    // axi4_master_wr — bundles the AW/W/B skid buffers + protocol.
    // The FUB side is the pattern-gen handshake; the M side goes out to the
    // controller / fabric.
    //==========================================================================
    axi4_master_wr #(
        .SKID_DEPTH_AW (SKID_DEPTH_AW),
        .SKID_DEPTH_W  (SKID_DEPTH_W),
        .SKID_DEPTH_B  (SKID_DEPTH_B),
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH(AXI_WSTRB_WIDTH)
    ) u_master_wr (
        .aclk            (aclk),
        .aresetn         (aresetn),

        // FUB AW
        .fub_axi_awid    (r_axi_id),
        .fub_axi_awaddr  (w_aw_addr_result),
        .fub_axi_awlen   (r_burst_len - 8'd1),
        .fub_axi_awsize  (r_axi_size),
        .fub_axi_awburst (r_axi_burst),
        .fub_axi_awlock  (1'b0),
        .fub_axi_awcache (4'b0011),
        .fub_axi_awprot  (3'b000),
        .fub_axi_awqos   (4'b0000),
        .fub_axi_awregion(4'b0000),
        .fub_axi_awuser  ('0),
        .fub_axi_awvalid (fub_awvalid),
        .fub_axi_awready (fub_awready),

        // FUB W
        .fub_axi_wdata   (w_wdata_out),
        .fub_axi_wstrb   ({SW{1'b1}}),   // full beat — no partial strobes
        .fub_axi_wlast   (fub_wlast),
        .fub_axi_wuser   ('0),
        .fub_axi_wvalid  (fub_wvalid),
        .fub_axi_wready  (fub_wready),

        // FUB B
        .fub_axi_bid     (),
        .fub_axi_bresp   (fub_bresp),
        .fub_axi_buser   (),
        .fub_axi_bvalid  (fub_bvalid),
        .fub_axi_bready  (fub_bready),

        // M-side AXI — passthrough to outer ports
        .m_axi_awid      (m_axi_awid),
        .m_axi_awaddr    (m_axi_awaddr),
        .m_axi_awlen     (m_axi_awlen),
        .m_axi_awsize    (m_axi_awsize),
        .m_axi_awburst   (m_axi_awburst),
        .m_axi_awlock    (m_axi_awlock),
        .m_axi_awcache   (m_axi_awcache),
        .m_axi_awprot    (m_axi_awprot),
        .m_axi_awqos     (m_axi_awqos),
        .m_axi_awregion  (m_axi_awregion),
        .m_axi_awuser    (m_axi_awuser),
        .m_axi_awvalid   (m_axi_awvalid),
        .m_axi_awready   (m_axi_awready),
        .m_axi_wdata     (m_axi_wdata),
        .m_axi_wstrb     (m_axi_wstrb),
        .m_axi_wlast     (m_axi_wlast),
        .m_axi_wuser     (m_axi_wuser),
        .m_axi_wvalid    (m_axi_wvalid),
        .m_axi_wready    (m_axi_wready),
        .m_axi_bid       (m_axi_bid),
        .m_axi_bresp     (m_axi_bresp),
        .m_axi_buser     (m_axi_buser),
        .m_axi_bvalid    (m_axi_bvalid),
        .m_axi_bready    (m_axi_bready),
        .busy            ()
    );

endmodule : axi4_master_wr_pattern_gen
