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
//   Serial-burst v1: at most one burst outstanding (AW handshake gates the
//   next W). Multi-outstanding is a v2 extension. Predictability is the v1
//   priority — characterization sweeps want one variable changing at a time.
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
    // FSM
    //==========================================================================
    typedef enum logic [1:0] {
        S_IDLE       = 2'd0,   // wait for cfg_start
        S_AW_REQ     = 2'd1,   // request next address; drive AW until handshake
        S_W_BEATS    = 2'd2,   // stream burst_len beats of LFSR data on W
        S_DONE       = 2'd3    // all bursts issued; await final B's then go IDLE on the next cfg_start
    } state_e;

    state_e                       r_state;

    // Latched workload program (sampled at cfg_start so software can change
    // cfg_* in the next cycle without disturbing the run).
    logic [AW-1:0]                r_base_addr;
    logic signed [STRIDE_WIDTH-1:0] r_stride_0, r_stride_1;
    logic [AW-1:0]                r_wrap_0, r_wrap_1;
    logic [7:0]                   r_burst_len;
    logic [TXN_COUNT_WIDTH-1:0]   r_txn_count;
    logic [IW-1:0]                r_axi_id;
    logic [2:0]                   r_axi_size;
    logic [1:0]                   r_axi_burst;
    logic [LFSR_WIDTH-1:0]        r_lfsr_seed_eff;

    // Progress counters
    logic [TXN_COUNT_WIDTH-1:0]   r_aw_issued;
    logic [TXN_COUNT_WIDTH-1:0]   r_b_received;
    logic [7:0]                   r_beats_in_burst;   // 0..r_burst_len-1
    // One-shot request marker: high after this burst's address request has
    // been latched by dma_address_gen, low on entry to S_AW_REQ for the
    // next burst. Prevents duplicate requests while we wait for the
    // pipelined result — without this, the address-gen captures r_aw_issued
    // multiple times (with the stale value) and burst N's AW gets burst
    // (N-1)'s address.
    logic                         r_addr_req_done;

    //==========================================================================
    // dma_address_gen — descriptor inputs come from the latched cfg.
    // Drive index_0 = r_aw_issued, index_1 = 0.
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
        .i_req_index_0     (INDEX_WIDTH'(r_aw_issued)),
        .i_req_index_1     (INDEX_WIDTH'(0)),
        .i_req_tag         (8'd0),

        .o_result_valid    (w_addr_result_valid),
        .i_result_ready    (w_addr_result_ready),
        .o_result_addr     (w_addr_result),
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

    // AW valid: in S_AW_REQ once dma_address_gen has produced an address.
    assign fub_awvalid       = (r_state == S_AW_REQ) && w_addr_result_valid;
    // We pop the address gen result on the AW handshake.
    assign w_addr_result_ready = fub_awvalid && fub_awready;
    // Request the address for THIS burst exactly once. r_addr_req_done
    // gates against firing duplicate requests while we wait for the
    // pipelined result.
    assign w_addr_req_valid  = (r_state == S_AW_REQ) && !r_addr_req_done;

    assign fub_wvalid        = (r_state == S_W_BEATS);
    assign fub_wlast         = (r_state == S_W_BEATS)
                            && (r_beats_in_burst == r_burst_len - 8'd1);
    assign fub_bready        = (r_state == S_W_BEATS) || (r_state == S_AW_REQ)
                            || (r_state == S_DONE);

    //==========================================================================
    // Replicate the 32-bit LFSR across the AXI data width
    //==========================================================================
    localparam int REPLICATION_FACTOR = (DW + 31) / 32;
    logic [REPLICATION_FACTOR*32-1:0] w_data_replicated;
    assign w_data_replicated = {REPLICATION_FACTOR{w_lfsr_out}};

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
            r_txn_count       <= '0;
            r_axi_id          <= '0;
            r_axi_size        <= 3'd0;
            r_axi_burst       <= 2'd1;   // INCR
            r_lfsr_seed_eff   <= LFSR_SEED;
            r_aw_issued       <= '0;
            r_b_received      <= '0;
            r_beats_in_burst  <= 8'd0;
            r_addr_req_done   <= 1'b0;
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
                        r_txn_count     <= cfg_txn_count;
                        r_axi_id        <= cfg_axi_id;
                        r_axi_size      <= cfg_axi_size;
                        r_axi_burst     <= cfg_axi_burst;
                        r_lfsr_seed_eff <= (cfg_lfsr_seed == '0) ? LFSR_SEED : cfg_lfsr_seed;
                        r_aw_issued     <= '0;
                        r_b_received    <= '0;
                        r_beats_in_burst<= 8'd0;
                        r_addr_req_done <= 1'b0;
                        o_expected_crc_valid <= 1'b0;
                        o_bresp_error        <= 1'b0;
                        // Move to S_AW_REQ only if there's actually work to do.
                        r_state         <= (cfg_txn_count == '0) ? S_DONE : S_AW_REQ;
                    end
                end

                S_AW_REQ: begin
                    // Latch that we've placed the address request once
                    // we get o_req_ready back.
                    if (w_addr_req_valid && w_addr_req_ready) begin
                        r_addr_req_done <= 1'b1;
                    end
                    if (fub_awvalid && fub_awready) begin
                        // AW accepted; start W beats next cycle
                        r_state          <= S_W_BEATS;
                        r_beats_in_burst <= 8'd0;
                    end
                end

                S_W_BEATS: begin
                    if (w_w_beat) begin
                        if (r_beats_in_burst == r_burst_len - 8'd1) begin
                            // Burst's last W beat issued. Advance to next AW
                            // (or finish). We do NOT wait for B before next AW
                            // — B is consumed in parallel via fub_bready and
                            // counted into r_b_received.
                            r_aw_issued      <= r_aw_issued + 1'b1;
                            r_beats_in_burst <= 8'd0;
                            r_addr_req_done  <= 1'b0;  // re-arm for next burst
                            if (r_aw_issued + 1'b1 == r_txn_count) begin
                                r_state <= S_DONE;
                            end else begin
                                r_state <= S_AW_REQ;
                            end
                        end else begin
                            r_beats_in_burst <= r_beats_in_burst + 8'd1;
                        end
                    end
                end

                S_DONE: begin
                    if (cfg_start) begin
                        // Re-arm directly: re-latch the program and jump
                        // straight to AW_REQ. Going via IDLE would lose
                        // the cfg_start pulse (it's a 1-cycle strobe).
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
                        r_aw_issued     <= '0;
                        r_b_received    <= '0;
                        r_beats_in_burst<= 8'd0;
                        r_addr_req_done <= 1'b0;
                        o_expected_crc_valid <= 1'b0;
                        o_bresp_error        <= 1'b0;
                        r_state              <= (cfg_txn_count == '0) ? S_DONE : S_AW_REQ;
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

            // Latch the expected CRC at completion (one cycle after the
            // last W beat — w_lfsr_out has settled, u_crc has consumed it).
            if (r_state == S_W_BEATS && w_w_beat
                && r_beats_in_burst == r_burst_len - 8'd1
                && r_aw_issued + 1'b1 == r_txn_count) begin
                o_expected_crc       <= w_expected_crc;
                o_expected_crc_valid <= 1'b1;
            end
        end
    end)

    // Pulse on any cfg_start that initiates a run — that's IDLE→AW_REQ
    // OR the S_DONE direct re-arm.
    assign w_lfsr_load = cfg_start && ((r_state == S_IDLE) || (r_state == S_DONE));

    // cfg_done: all txn_count B's received AND we're past S_IDLE.
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
        .fub_axi_awaddr  (w_addr_result),
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
        .fub_axi_wdata   (w_data_replicated[DW-1:0]),
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
