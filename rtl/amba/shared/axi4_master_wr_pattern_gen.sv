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

    // Legal-AxLEN quantum: the number of AXI beats that make one DRAM burst, i.e.
    // cfg_burst_len MUST be a nonzero integer multiple of this (one AXI burst maps
    // to an integer number of DRAM bursts). Project-specific — depends on the DRAM
    // BL, the AXI:DRAM-beat gear, and the device width — so it is a PARAMETER. 1 =
    // unconstrained (default; no check). A non-conforming cfg_burst_len yields a
    // ragged final sub-command in pumice_wr_splitter -> SLVERR / partial write.
    parameter int BURST_LEN_MULTIPLE = 1,

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
    input  logic [IW-1:0]                       cfg_axi_id,       // FIXED-mode id / start seed for COUNTER+LFSR modes
    // AW ID generation mode:
    //   0 = FIXED:   every AW uses cfg_axi_id verbatim
    //   1 = COUNTER: 8-bit counter starting at cfg_axi_id[7:0], +1 per AW
    //   2 = LFSR:    8-bit Fibonacci LFSR seeded from cfg_axi_id[7:0]|1
    // Counter / LFSR widths are 8-bit internally and zero-extended (or
    // truncated) to IW at the awid output.
    input  logic [1:0]                          cfg_id_mode,
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
    // Config guard — the AxLEN==integer-multiple-of-DRAM-burst requirement.
    // On each cfg_start, verify cfg_burst_len is a nonzero multiple of
    // BURST_LEN_MULTIPLE (AXI beats per DRAM burst). A non-conforming value would
    // otherwise SILENTLY produce a ragged final sub-command (pumice_wr_splitter)
    // that SLVERRs / partial-writes at pumice_wr_intake. Sim-only ($error); on
    // silicon the host must validate before programming BLEN_TXN. Skipped when
    // BURST_LEN_MULTIPLE==1 (unconstrained).
    //==========================================================================
`ifndef SYNTHESIS
    always_ff @(posedge aclk) begin
        if (aresetn && cfg_start && (BURST_LEN_MULTIPLE > 1)) begin
            assert (cfg_burst_len != 8'd0)
                else $error("axi4_master_wr_pattern_gen: cfg_burst_len=0 illegal");
            assert ((32'(cfg_burst_len) % BURST_LEN_MULTIPLE) == 0)
                else $error("axi4_master_wr_pattern_gen: cfg_burst_len=%0d not a multiple of BURST_LEN_MULTIPLE=%0d (AXI beats per DRAM burst) -> ragged burst -> SLVERR/partial write",
                            cfg_burst_len, BURST_LEN_MULTIPLE);
        end
    end
`endif

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
    logic [1:0]                   r_id_mode;         // 0=FIXED, 1=COUNTER, 2=LFSR
    logic [7:0]                   r_id_counter;      // 8-bit AW ID counter

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

    // Production-side W-beat signals (into the hash pipeline). Distinct from
    // the master-facing fub_wvalid/fub_wlast, which are driven by the staging
    // FIFO output (see Data path). Pipelining the hash decouples the two.
    logic                         w_gen_valid;
    logic                         w_gen_wlast;

    //==========================================================================
    // AW ID generator — three modes muxed by r_id_mode.
    //   FIXED:   pass r_axi_id through.
    //   COUNTER: 8-bit counter, seeded with cfg_axi_id[7:0] at cfg_start,
    //            +1 per AW handshake (wraps).
    //   LFSR:    8-bit maximal-length Fibonacci LFSR with taps {8,6,5,4},
    //            seeded with cfg_axi_id[7:0] | 8'h01 (avoid all-zero seed).
    //==========================================================================
    logic [7:0]  w_id_lfsr_out;
    logic        w_id_lfsr_advance;

    assign w_id_lfsr_advance = fub_awvalid && fub_awready;

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
        .taps     ({4'd8, 4'd6, 4'd5, 4'd4}),
        .lfsr_out (w_id_lfsr_out),
        .lfsr_done()
    );

    // Mode mux for awid
    logic [IW-1:0] w_aw_id_out;
    always_comb begin
        unique case (r_id_mode)
            2'd0:    w_aw_id_out = r_axi_id;
            2'd1:    w_aw_id_out = IW'(r_id_counter);
            2'd2:    w_aw_id_out = IW'(w_id_lfsr_out);
            default: w_aw_id_out = r_axi_id;
        endcase
    end

    // w_w_beat (pipeline admit) is defined in the Data path section below,
    // where the staging-FIFO occupancy is known.

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

    // W-beat PRODUCTION (into the hash pipeline). Produce when (a) the slave
    // has at least seen this burst's AW (r_w_bursts_done < r_aw_issued) and
    // (b) the W addr-gen has produced the base address. The actual admit
    // (w_w_beat) additionally requires staging-FIFO room — see Data path.
    // The master's fub_wvalid/fub_wlast are driven from the FIFO output.
    assign w_gen_valid       = (r_state == S_RUN)
                            && (r_w_bursts_done < r_aw_issued)
                            && w_w_addr_result_valid;
    assign w_gen_wlast       = w_gen_valid
                            && (r_w_beat_idx == r_burst_len - 8'd1);
    assign w_w_addr_result_ready = w_w_beat && w_gen_wlast;

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
    localparam int REP     = (DW + 31) / 32;   // 32-bit slices per beat
    localparam int HSTAGES = 4;                 // 2 mults, each isolated
    localparam int WFIFO_DEPTH = 16;

    logic [REP*32-1:0] w_data_replicated;
    assign w_data_replicated = {REP{w_lfsr_out}};

    // Per-beat byte address for the CURRENT W burst. Anchored on
    // w_w_addr_result (the W addr-gen's current output) and stepped by
    // 2**axsize bytes per beat. Full-beat writes only — strobes all-ones.
    logic [AW-1:0]                w_byte_addr_for_beat;
    assign w_byte_addr_for_beat = w_w_addr_result
        + (AW'({{(AW-8){1'b0}}, r_w_beat_idx}) << r_axi_size);

    // Odd-forced Murmur3-fmix multiplier constants (from cfg seeds).
    logic [31:0] w_s1_odd, w_s2_odd;
    assign w_s1_odd = r_hash_seed1 | 32'h1;
    assign w_s2_odd = r_hash_seed2 | 32'h1;

    // Combinational stage-0: (addr + s*4) ^ s0, then ^ >>16 (cheap).
    logic [REP-1:0][31:0] w_hp_t_in;
    always_comb begin
        for (int s = 0; s < REP; s++) begin
            logic [31:0] x;
            x = (w_byte_addr_for_beat[31:0] + 32'(s * 4)) ^ r_hash_seed0;
            w_hp_t_in[s] = x ^ (x >> 16);
        end
    end

    // ---- Hash pipeline ------------------------------------------------------
    // The mode-1 Murmur hash chains two 32-bit multiplies — combinationally a
    // ~25 ns / 4-DSP cone that misses 100 MHz. Each multiply is isolated in its
    // own register stage (DSP output register carries it); wlast/mode/LFSR-data
    // ride alongside so the output stays beat-aligned. Latency-insensitive:
    // per-beat data VALUES and order are unchanged, so the golden-CRC /
    // per-beat-compare contract still holds.
    logic [HSTAGES-1:0]         r_hp_valid;
    logic [HSTAGES-1:0]         r_hp_wlast;
    logic [HSTAGES-1:0]         r_hp_mode;
    logic [HSTAGES-1:0][DW-1:0] r_hp_lfsr;
    logic [REP-1:0][31:0]       r_hp_t;    // s1: (addr^s0)^>>16
    logic [REP-1:0][31:0]       r_hp_p1;   // s2: t * s1_odd   (multiply #1)
    logic [REP-1:0][31:0]       r_hp_u;    // s3: p1 ^ (p1>>13)
    logic [REP-1:0][31:0]       r_hp_p2;   // s4: u * s2_odd   (multiply #2)

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_hp_valid <= '0;
            r_hp_wlast <= '0;
            r_hp_mode  <= '0;
            r_hp_lfsr  <= '0;
            r_hp_t     <= '0;
            r_hp_p1    <= '0;
            r_hp_u     <= '0;
            r_hp_p2    <= '0;
        end else begin
            // Stage 1: admit.
            r_hp_valid[0] <= w_w_beat;
            r_hp_wlast[0] <= w_gen_wlast;
            r_hp_mode [0] <= r_data_mode;
            r_hp_lfsr [0] <= w_data_replicated[DW-1:0];
            r_hp_t        <= w_hp_t_in;
            // Stage 2: first multiply.
            r_hp_valid[1] <= r_hp_valid[0];
            r_hp_wlast[1] <= r_hp_wlast[0];
            r_hp_mode [1] <= r_hp_mode [0];
            r_hp_lfsr [1] <= r_hp_lfsr [0];
            for (int s = 0; s < REP; s++) r_hp_p1[s] <= r_hp_t[s] * w_s1_odd;
            // Stage 3: xorshift.
            r_hp_valid[2] <= r_hp_valid[1];
            r_hp_wlast[2] <= r_hp_wlast[1];
            r_hp_mode [2] <= r_hp_mode [1];
            r_hp_lfsr [2] <= r_hp_lfsr [1];
            for (int s = 0; s < REP; s++) r_hp_u[s] <= r_hp_p1[s] ^ (r_hp_p1[s] >> 13);
            // Stage 4: second multiply.
            r_hp_valid[3] <= r_hp_valid[2];
            r_hp_wlast[3] <= r_hp_wlast[2];
            r_hp_mode [3] <= r_hp_mode [2];
            r_hp_lfsr [3] <= r_hp_lfsr [2];
            for (int s = 0; s < REP; s++) r_hp_p2[s] <= r_hp_u[s] * w_s2_odd;
        end
    end)

    // Pipeline output: final xorshift + mode mux.
    logic [DW-1:0] w_hp_wdata;
    always_comb begin
        logic [REP*32-1:0] hash_word;
        for (int s = 0; s < REP; s++)
            hash_word[s*32 +: 32] = r_hp_p2[s] ^ (r_hp_p2[s] >> 16);
        w_hp_wdata = r_hp_mode[HSTAGES-1] ? hash_word[DW-1:0]
                                          : r_hp_lfsr[HSTAGES-1];
    end

    // ---- Staging FIFO {wlast, wdata} ---------------------------------------
    // Decouples the hash pipeline from the AXI W handshake so W streams
    // back-to-back independent of pipeline fill / master backpressure.
    localparam int WFIFO_DW = DW + 1;
    logic                 w_wfifo_wr_ready;
    logic                 w_wfifo_rd_valid, w_wfifo_rd_ready;
    logic [WFIFO_DW-1:0]  w_wfifo_rd_data;
    logic [$clog2(WFIFO_DEPTH):0] w_wfifo_count;

    gaxi_fifo_sync #(
        .REGISTERED (0),   // mux mode: rd_data = head combinationally (show-ahead)
        .DATA_WIDTH (WFIFO_DW),
        .DEPTH      (WFIFO_DEPTH)
    ) u_wdata_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (r_hp_valid[HSTAGES-1]),
        .wr_ready    (w_wfifo_wr_ready),
        .wr_data     ({r_hp_wlast[HSTAGES-1], w_hp_wdata}),
        .rd_ready    (w_wfifo_rd_ready),
        .count       (w_wfifo_count),
        .rd_valid    (w_wfifo_rd_valid),
        .rd_data     (w_wfifo_rd_data)
    );

    // ADMIT a beat when the generator has one AND the FIFO has room for it
    // plus the HSTAGES beats already in flight (they WILL land regardless).
    localparam logic [$clog2(WFIFO_DEPTH):0] WFIFO_ADMIT_HI =
        ($clog2(WFIFO_DEPTH)+1)'(WFIFO_DEPTH - HSTAGES - 1);
    assign w_w_beat = w_gen_valid && w_wfifo_wr_ready
                   && (w_wfifo_count <= WFIFO_ADMIT_HI);

    // Master W driven from the FIFO output (wstrb tied full-beat at instance).
    logic [DW-1:0] w_wdata_out;
    assign w_wdata_out      = w_wfifo_rd_data[DW-1:0];
    assign fub_wlast        = w_wfifo_rd_data[DW];
    assign fub_wvalid       = w_wfifo_rd_valid;
    assign w_wfifo_rd_ready = fub_wvalid && fub_wready;

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
            r_id_mode         <= 2'd0;
            r_id_counter      <= 8'd0;
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
                        r_id_mode       <= cfg_id_mode;
                        r_id_counter    <= cfg_axi_id[7:0];
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
                        r_aw_issued  <= r_aw_issued + 1'b1;
                        // Advance the ID counter regardless of mode — it's
                        // only sourced when r_id_mode==COUNTER, but keeping
                        // it free-running is harmless and avoids a mode
                        // branch in the critical path.
                        r_id_counter <= r_id_counter + 8'd1;
                    end
                    // ---- W addr-gen req counter ----
                    if (w_w_addr_req_valid && w_w_addr_req_ready) begin
                        r_w_req_count <= r_w_req_count + 1'b1;
                    end

                    // ---- W beat handshake (production/admit into pipeline) ----
                    if (w_w_beat) begin
                        if (w_gen_wlast) begin
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
                        r_id_mode       <= cfg_id_mode;
                        r_id_counter    <= cfg_axi_id[7:0];
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
            if (r_state == S_RUN && w_w_beat && w_gen_wlast
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
        .fub_axi_awid    (w_aw_id_out),
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
