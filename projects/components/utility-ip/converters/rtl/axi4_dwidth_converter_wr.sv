// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_dwidth_converter_wr
// Purpose: AXI4 Write Data Width Converter (WRITE-ONLY, STANDALONE)
//
// Description:
//   Converts between AXI4 write interfaces of different data widths.
//   Handles ONLY write path (AW, W, B channels) - no read support.
//
//   The W channel data path is delegated to the validated
//   axi_data_upsize / axi_data_dnsize primitives in this same
//   directory (each with its own pytest suite). This wrapper still
//   owns: AW/W/B skid buffers, the AW awlen/awsize rewrite, the
//   wuser carry that the primitives don't handle, and the B channel
//   split-fold CAM (per-AWID outstanding-split counter, BUG-008).
//
//   For read conversion, use axi4_dwidth_converter_rd.sv.
//
// Parameters:
//   S_AXI_DATA_WIDTH: Slave interface data width (32, 64, 128, 256)
//   M_AXI_DATA_WIDTH: Master interface data width (32, 64, 128, 256)
//   AXI_ID_WIDTH: Transaction ID width (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_USER_WIDTH: User signal width (0-1024)
//   SKID_DEPTH_AW: AW channel skid buffer depth (2-8, default 2)
//   SKID_DEPTH_W: W channel skid buffer depth (2-8, default 4)
//   SKID_DEPTH_B: B channel skid buffer depth (2-8, default 2)
//
// Author: RTL Design Sherpa
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_dwidth_converter_wr #(
    // Width Configuration
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 128,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,

    // Skid buffer packed widths
    localparam int AW_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + AXI_USER_WIDTH,
    localparam int W_WIDTH  = S_AXI_DATA_WIDTH + S_STRB_WIDTH + 1 + AXI_USER_WIDTH,
    localparam int B_WIDTH  = AXI_ID_WIDTH + 2 + AXI_USER_WIDTH
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI Write Interface
    //==========================================================================

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write Data Channel
    input  logic [S_AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [S_STRB_WIDTH-1:0]     s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    //==========================================================================
    // Master AXI Write Interface
    //==========================================================================

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // Write Data Channel
    output logic [M_AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [M_STRB_WIDTH-1:0]     m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready
);
    // Boundary reset synchronization. The port aresetn is treated as an
    // asynchronous-assert input of unknown deassert quality: an N=3
    // reset_sync (rtl/cdc, formally proven) produces the internal reset
    // every block below sees.
    logic w_aresetn;
    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1)
    ) u_reset_sync (
        .clk        (aclk),
        .rst_n      (aresetn),
        .sync_rst_n (w_aresetn)
    );


    //==========================================================================
    // Parameter Validation
    //==========================================================================

    initial begin
        if (S_AXI_DATA_WIDTH != 2**$clog2(S_AXI_DATA_WIDTH))
            $error("S_AXI_DATA_WIDTH must be power of 2");
        if (M_AXI_DATA_WIDTH != 2**$clog2(M_AXI_DATA_WIDTH))
            $error("M_AXI_DATA_WIDTH must be power of 2");
        if (WIDTH_RATIO < 2)
            $error("WIDTH_RATIO must be >= 2");
        if (!UPSIZE && !DOWNSIZE)
            $error("Must be either UPSIZE or DOWNSIZE mode");
    end

    //==========================================================================
    // Internal Signals - AW Channel (after skid buffer, before conversion)
    //==========================================================================

    logic [AW_WIDTH-1:0]       int_aw_data;
    logic                      int_aw_valid;
    logic                      int_aw_ready;

    logic [AXI_ID_WIDTH-1:0]   int_awid;
    logic [AXI_ADDR_WIDTH-1:0] int_awaddr;
    logic [7:0]                int_awlen;
    logic [2:0]                int_awsize;
    logic [1:0]                int_awburst;
    logic                      int_awlock;
    logic [3:0]                int_awcache;
    logic [2:0]                int_awprot;
    logic [3:0]                int_awqos;
    logic [3:0]                int_awregion;
    logic [AXI_USER_WIDTH-1:0] int_awuser;

    //==========================================================================
    // Internal Signals - W Channel (after skid buffer, before conversion)
    //==========================================================================

    logic [W_WIDTH-1:0]          int_w_data;
    logic                        int_w_valid;
    logic                        int_w_ready;

    logic [S_AXI_DATA_WIDTH-1:0] int_wdata;
    logic [S_STRB_WIDTH-1:0]     int_wstrb;
    logic                        int_wlast;
    logic [AXI_USER_WIDTH-1:0]   int_wuser;

    //==========================================================================
    // Internal Signals - B Channel (before skid buffer, after pass-through)
    //==========================================================================

    logic [B_WIDTH-1:0]        int_b_data;
    logic                      int_b_valid;

    // Shared DOWNSIZE control signals (driven in gen_aw_downsize, consumed
    // by gen_b_fold for the per-burst B CAM).
    logic       w_aw_issue;
    logic       w_this_last;
    // A free B-CAM slot exists (driven in gen_b_fold, consumed in
    // gen_aw_downsize): a slave burst's FINAL master AW must not issue
    // unless the CAM can take its entry, or the push would be dropped and
    // that burst's B responses would match nothing (BUG-008 follow-up:
    // the CAM drains on B return while the split queue drains on W
    // framing, so split-queue space alone does not bound CAM occupancy).
    logic       w_b_cam_slot_free;

    // Burst-split queue / B CAM depth.  Shared across generate blocks so
    // both the W framing queue and the per-burst B CAM are the same size.
    localparam int SPLITQ_DEPTH = 16;

    // -----------------------------------------------------------------
    // Downsize burst-split queue (driven in gen_aw_downsize, consumed by
    // the W framing counter; tied off for upsize).
    //
    // One slave burst can need more narrow beats than one legal master
    // burst can carry, so the AW splitter issues several master bursts
    // and records each one's beat count here for W framing.  The B
    // channel no longer walks this queue: BUG-008 showed that out-of-order
    // B responses across IDs misalign a single B read pointer, so the B
    // fold is now a per-burst outstanding-split counter keyed by AWID.
    // -----------------------------------------------------------------
    logic       split_w_avail;   // an unconsumed entry exists for W framing
    logic [8:0] split_w_beats;   // its master-burst beat count (1..256)
    logic       split_w_pop;     // W side: consumed this entry

    // UPSIZE only (driven in gen_aw_upsize, consumed in gen_w_upsize):
    // start lane of the burst the next W beats belong to, and the gate
    // that holds W off until its AW has been accepted (the lane comes
    // from AWADDR). Tied inert in DOWNSIZE.
    logic [7:0] w_upsize_start_lane;
    logic       w_upsize_w_gate;
    logic                      int_b_ready;

    logic [AXI_ID_WIDTH-1:0]   int_bid;
    logic [1:0]                int_bresp;
    logic [AXI_USER_WIDTH-1:0] int_buser;

    //==========================================================================
    // AW Channel Skid Buffer (Timing Closure)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AW_WIDTH)
    ) aw_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(w_aresetn),
        .wr_valid   (s_axi_awvalid),
        .wr_ready   (s_axi_awready),
        .wr_data    ({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize,
                      s_axi_awburst, s_axi_awlock, s_axi_awcache, s_axi_awprot,
                      s_axi_awqos, s_axi_awregion, s_axi_awuser}),
        .rd_valid   (int_aw_valid),
        .rd_ready   (int_aw_ready),
        .rd_data    (int_aw_data),
        .count      (),
        .rd_count   ()
    );

    assign {int_awid, int_awaddr, int_awlen, int_awsize, int_awburst,
            int_awlock, int_awcache, int_awprot, int_awqos, int_awregion,
            int_awuser} = int_aw_data;

    //==========================================================================
    // W Channel Skid Buffer (Timing + Data Buffering)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(W_WIDTH)
    ) w_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(w_aresetn),
        .wr_valid   (s_axi_wvalid),
        .wr_ready   (s_axi_wready),
        .wr_data    ({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
        .rd_valid   (int_w_valid),
        .rd_ready   (int_w_ready),
        .rd_data    (int_w_data),
        .count      (),
        .rd_count   ()
    );

    assign {int_wdata, int_wstrb, int_wlast, int_wuser} = int_w_data;

    //==========================================================================
    // B Channel Skid Buffer (Timing Closure - Reverse Direction)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(B_WIDTH)
    ) b_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(w_aresetn),
        .wr_valid   (int_b_valid),
        .wr_ready   (int_b_ready),
        .wr_data    (int_b_data),
        .rd_valid   (s_axi_bvalid),
        .rd_ready   (s_axi_bready),
        .rd_data    ({s_axi_bid, s_axi_bresp, s_axi_buser}),
        .count      (),
        .rd_count   ()
    );

    assign int_b_data = {int_bid, int_bresp, int_buser};

    //==========================================================================
    // Write Address Channel Conversion (awlen/awsize rewrite)
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_aw_downsize
            // W runs free in DOWNSIZE; no lane offset on the narrow side.
            assign w_upsize_start_lane = 8'd0;
            assign w_upsize_w_gate     = 1'b1;

            // Downsize: slave (wide) → master (narrow). One wide beat
            // becomes WIDTH_RATIO narrow beats -- and that product does
            // not fit a burst. AXI4 allows 256 beats, so a full-length
            // slave burst needs up to 256*WIDTH_RATIO narrow beats,
            // which is neither expressible in AWLEN nor legal. The old
            // ((awlen+1)*RATIO)-1 computed straight into the 8-bit field
            // and wrapped: 511 truncated to 255 (half the burst lost),
            // and at 4:1 a 128-beat slave burst asked for 515 and got 3.
            //
            // So one slave burst is SPLIT into as many master bursts of
            // <= 256 beats as it takes, each recorded in the split queue
            // for the W framing and B fold. WRAP never gets here: AXI4
            // caps it at 16 beats, and 16*RATIO <= 256 for every ratio
            // this converter supports.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int MAX_BEATS   = 256;
            localparam int CNTW        = 9 + $clog2(WIDTH_RATIO);
            localparam int SPLITQ_AW    = $clog2(SPLITQ_DEPTH);

            logic [CNTW-1:0]           r_split_remaining;
            logic [AXI_ADDR_WIDTH-1:0] r_split_addr;
            logic                      r_split_active;
            logic [8:0]                w_this_beats;

            assign w_this_beats = (r_split_remaining > CNTW'(MAX_BEATS))
                                  ? 9'(MAX_BEATS) : 9'(r_split_remaining);
            assign w_this_last  = (r_split_remaining <= CNTW'(MAX_BEATS));
            assign w_aw_issue   = m_axi_awvalid && m_axi_awready;

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    r_split_remaining <= '0;
                    r_split_addr      <= '0;
                    r_split_active    <= 1'b0;
                end else if (!r_split_active) begin
                    if (int_aw_valid) begin
                        r_split_remaining <= (CNTW'(int_awlen) + CNTW'(1))
                                             * CNTW'(WIDTH_RATIO);
                        r_split_addr      <= int_awaddr;
                        r_split_active    <= 1'b1;
                    end
                end else if (w_aw_issue) begin
                    if (w_this_last) begin
                        r_split_remaining <= '0;
                        r_split_active    <= 1'b0;
                    end else begin
                        r_split_remaining <= r_split_remaining
                                             - CNTW'(MAX_BEATS);
                        // FIXED holds the address; INCR walks on. WRAP
                        // cannot reach a split (see above).
                        if (int_awburst != 2'b00)
                            r_split_addr <= r_split_addr
                                + AXI_ADDR_WIDTH'(MAX_BEATS * M_STRB_WIDTH);
                    end
                end
            )

            // Split queue: one memory, one read pointer for W framing.
            // Push at each master AW issue; AW is back-pressured on full
            // so it cannot overflow.
            logic [9:0]           splitq_mem [SPLITQ_DEPTH];
            logic [SPLITQ_AW:0]   splitq_wptr, splitq_rptr_w;
            logic                 w_splitq_full;

            // Full is checked against the W pointer: once W has framed a
            // master burst's data the entry can be reused for new AWs.
            assign w_splitq_full =
                (splitq_wptr[SPLITQ_AW-1:0] == splitq_rptr_w[SPLITQ_AW-1:0]) &&
                (splitq_wptr[SPLITQ_AW]     != splitq_rptr_w[SPLITQ_AW]);
            assign split_w_avail = (splitq_wptr != splitq_rptr_w);
            assign split_w_beats = splitq_mem[splitq_rptr_w[SPLITQ_AW-1:0]][8:0];

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    splitq_wptr   <= '0;
                    splitq_rptr_w <= '0;
                end else begin
                    if (w_aw_issue) begin
                        splitq_mem[splitq_wptr[SPLITQ_AW-1:0]]
                            <= {w_this_last, w_this_beats};
                        splitq_wptr <= splitq_wptr + 1'b1;
                    end
                    if (split_w_pop) splitq_rptr_w <= splitq_rptr_w + 1'b1;
                end
            )

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = r_split_addr;
            assign m_axi_awlen    = 8'(w_this_beats - 9'd1);
            assign m_axi_awsize   = MASTER_SIZE[2:0];
            assign m_axi_awburst  = int_awburst;
            assign m_axi_awlock   = int_awlock;
            assign m_axi_awcache  = int_awcache;
            assign m_axi_awprot   = int_awprot;
            assign m_axi_awqos    = int_awqos;
            assign m_axi_awregion = int_awregion;
            assign m_axi_awuser   = int_awuser;
            // The final master AW of a slave burst also pushes the B CAM,
            // so it must wait for a free CAM slot; mid-split AWs need none.
            assign m_axi_awvalid  = r_split_active && !w_splitq_full &&
                                    (!w_this_last || w_b_cam_slot_free);
            // the slave's AW is consumed only when its FINAL master
            // burst is issued
            assign int_aw_ready   = w_aw_issue && w_this_last;

        end else begin : gen_aw_upsize
            // Upsize: slave (narrow) → master (wide). Divide burst length
            // by ratio (round up), counting the start lane: an INCR burst
            // may begin mid-wide-word, in which case its first wide beat
            // is partial and the lane offset eats into the first group.
            // Division can never overflow AWLEN, so no splitting is
            // needed and the split queue is tied off.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int LANE_W      = $clog2(WIDTH_RATIO);

            assign split_w_avail = 1'b0;
            assign split_w_beats = 9'd0;

            // Narrow-lane offset of the burst start inside the wide word.
            logic [LANE_W-1:0] w_aw_lane;
            assign w_aw_lane = LANE_W'(int_awaddr[$clog2(M_STRB_WIDTH)-1:0]
                                       >> $clog2(S_STRB_WIDTH));

            // AW-lane queue: the W packer needs the start lane of the
            // burst its FIRST W beat belongs to, and W may run ahead of
            // or behind AW. One entry per accepted AW, popped when the
            // wide burst's WLAST completes. W is held off while empty
            // (deadlock-free: AW never depends on W). Same inline-queue
            // pattern as the read converter's burst-length FIFO.
            localparam int WLANE_DEPTH = 16;
            localparam int WLANE_AW    = $clog2(WLANE_DEPTH);
            logic [LANE_W-1:0]  wlane_mem [WLANE_DEPTH];
            logic [WLANE_AW:0]  wlane_wptr, wlane_rptr;
            logic               w_wlane_full, w_wlane_avail;
            assign w_wlane_full  = (wlane_wptr[WLANE_AW] != wlane_rptr[WLANE_AW]) &&
                                   (wlane_wptr[WLANE_AW-1:0] == wlane_rptr[WLANE_AW-1:0]);
            assign w_wlane_avail = (wlane_wptr != wlane_rptr);

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    wlane_wptr <= '0;
                    wlane_rptr <= '0;
                end else begin
                    if (int_aw_valid && int_aw_ready) begin
                        wlane_mem[wlane_wptr[WLANE_AW-1:0]] <= w_aw_lane;
                        wlane_wptr <= wlane_wptr + 1'b1;
                    end
                    // Pop on the NARROW side's last beat: the head must
                    // track the burst the CURRENT narrow beat belongs to.
                    // Popping on the wide WLAST raced back-to-back bursts:
                    // burst B's first narrow beat can be accepted in the
                    // same cycle as burst A's last wide handshake and
                    // would sample A's stale lane.
                    if (int_w_valid && int_w_ready && int_wlast) begin
                        wlane_rptr <= wlane_rptr + 1'b1;
                    end
                end
            )

            assign w_upsize_start_lane = 8'(wlane_mem[wlane_rptr[WLANE_AW-1:0]]);
            assign w_upsize_w_gate     = w_wlane_avail;

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = int_awaddr;
            // Wide beats = ceil((lane + narrow_beats) / RATIO); 10-bit
            // intermediate so lane + 255 + RATIO cannot wrap.
            assign m_axi_awlen    = 8'(((10'(w_aw_lane) + 10'(int_awlen) + 10'(WIDTH_RATIO))
                                        / 10'(WIDTH_RATIO)) - 10'd1);
            assign m_axi_awsize   = MASTER_SIZE[2:0];
            assign m_axi_awburst  = int_awburst;
            assign m_axi_awlock   = int_awlock;
            assign m_axi_awcache  = int_awcache;
            assign m_axi_awprot   = int_awprot;
            assign m_axi_awqos    = int_awqos;
            assign m_axi_awregion = int_awregion;
            assign m_axi_awuser   = int_awuser;
            assign m_axi_awvalid  = int_aw_valid && !w_wlane_full;
            assign int_aw_ready   = m_axi_awready && !w_wlane_full;

`ifdef SIMULATION
            // Mid-word starts are supported for INCR (lane-placed data,
            // leading strobes disabled). FIXED/WRAP keep the wide-aligned
            // requirement -- their lane semantics through the packer are
            // not defined here.
            always_ff @(posedge aclk) begin
                if (w_aresetn && int_aw_valid && int_aw_ready &&
                    (int_awburst != 2'b01) &&
                    (int_awaddr[$clog2(M_STRB_WIDTH)-1:0] != '0)) begin
                    $error("axi4_dwidth_converter_wr: upsize %s AW addr 0x%h is not aligned to the %0d-byte wide bus",
                           (int_awburst == 2'b00) ? "FIXED" : "WRAP",
                           int_awaddr, M_STRB_WIDTH);
                end
            end
`endif
        end
    endgenerate

    //==========================================================================
    // W Channel WUSER Carry
    //
    //   The validated axi_data_{upsize,dnsize} primitives carry only one
    //   sideband (WSTRB on the W channel). WUSER stays constant within a
    //   burst in normal AXI4 traffic, so we register the latest value
    //   from the slave-side W handshake and present it on every
    //   master-side W beat.
    //==========================================================================

    logic [AXI_USER_WIDTH-1:0] r_wuser_held;

    `ALWAYS_FF_RST(aclk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            r_wuser_held <= '0;
        end else if (int_w_valid && int_w_ready) begin
            r_wuser_held <= int_wuser;
        end
    )

    assign m_axi_wuser = r_wuser_held;

    //==========================================================================
    // W Channel Data Conversion (delegates to validated primitives)
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_w_downsize
            // Slave wide, master narrow. W direction: slave → master, so
            // wide → narrow. axi_data_dnsize with TRACK_BURSTS=0 — the
            // slave's wlast drives narrow_last on the final narrow beat
            // from the last wide beat (matches the master's awlen rewrite).
            // WSTRB slices per narrow beat: SB_BROADCAST=0.
            logic w_dnsize_valid;
            logic w_dnsize_ready;

            axi_data_dnsize #(
                .WIDE_WIDTH      (S_AXI_DATA_WIDTH),
                .NARROW_WIDTH    (M_AXI_DATA_WIDTH),
                .WIDE_SB_WIDTH   (S_STRB_WIDTH),
                .NARROW_SB_WIDTH (M_STRB_WIDTH),
                .SB_BROADCAST    (0),
                .TRACK_BURSTS    (0),
                .BURST_LEN_WIDTH (8)
            ) u_w_dnsize (
                .aclk            (aclk),
                .aresetn         (w_aresetn),
                .burst_len       (8'd0),
                .burst_start     (1'b0),
                .start_lane      ('0),  // untracked mode: port unused
                .wide_valid      (int_w_valid),
                .wide_ready      (int_w_ready),
                .wide_data       (int_wdata),
                .wide_sideband   (int_wstrb),
                .wide_last       (int_wlast),
                .narrow_valid    (w_dnsize_valid),
                .narrow_ready    (w_dnsize_ready),
                .narrow_data     (m_axi_wdata),
                .narrow_sideband (m_axi_wstrb),
                .narrow_last     ()                 // frames the SLAVE burst; see below
            );

            // The dnsize frames the whole SLAVE burst, but the AW side
            // may have split it into several master bursts, each needing
            // its own WLAST at its own boundary. A counter holds the
            // beat count of the master burst currently draining, loaded
            // from the split queue -- a queue, not a snapshot of the AW
            // side, because AW deliberately runs ahead of W and a single
            // shared register would be overwritten mid-burst (that
            // exact failure delivered 505 of 512 beats in an earlier
            // version of this fix).
            //
            // W data is held until its burst's entry has been loaded, so
            // no beat can slip through unframed. The next entry loads on the
            // current burst's last W handshake when it is already queued (AW
            // runs ahead of W), so back-to-back bursts stream without a dead
            // cycle; it loads from empty otherwise.
            logic [8:0] r_w_beats_left;
            logic       w_last_hs;

            assign w_last_hs   = m_axi_wvalid && m_axi_wready && (r_w_beats_left == 9'd1);
            assign split_w_pop = split_w_avail && ((r_w_beats_left == 9'd0) || w_last_hs);

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    r_w_beats_left <= 9'd0;
                end else if (split_w_pop) begin
                    r_w_beats_left <= split_w_beats;
                end else if (m_axi_wvalid && m_axi_wready) begin
                    r_w_beats_left <= r_w_beats_left - 9'd1;
                end
            )

            assign m_axi_wvalid  = w_dnsize_valid && (r_w_beats_left != 9'd0);
            assign w_dnsize_ready = m_axi_wready && (r_w_beats_left != 9'd0);
            assign m_axi_wlast   = (r_w_beats_left == 9'd1);

            // (split_w_pop driven above)

        end else begin : gen_w_upsize
            assign split_w_pop = 1'b0;
            // Slave narrow, master wide. W direction: slave → master, so
            // narrow → wide. axi_data_upsize concatenates WSTRBs:
            // SB_OR_MODE=0. wlast on the narrow side terminates the
            // accumulation early (matches existing UPSIZE semantics).
            // W is held off until its AW is queued: the packer's start
            // lane comes from AWADDR (see the AW-lane queue above).
            logic w_upz_nready;
            assign int_w_ready = w_upz_nready && w_upsize_w_gate;

            axi_data_upsize #(
                .NARROW_WIDTH    (S_AXI_DATA_WIDTH),
                .WIDE_WIDTH      (M_AXI_DATA_WIDTH),
                .NARROW_SB_WIDTH (S_STRB_WIDTH),
                .WIDE_SB_WIDTH   (M_STRB_WIDTH),
                .SB_OR_MODE      (0)
            ) u_w_upsize (
                .aclk            (aclk),
                .aresetn         (w_aresetn),
                .narrow_valid    (int_w_valid && w_upsize_w_gate),
                .narrow_ready    (w_upz_nready),
                .narrow_data     (int_wdata),
                .narrow_sideband (int_wstrb),
                .narrow_last     (int_wlast),
                .start_lane      (w_upsize_start_lane[$clog2(WIDTH_RATIO)-1:0]),
                .wide_valid      (m_axi_wvalid),
                .wide_ready      (m_axi_wready),
                .wide_data       (m_axi_wdata),
                .wide_sideband   (m_axi_wstrb),
                .wide_last       (m_axi_wlast)
            );
        end
    endgenerate

    //==========================================================================
    // Write Response Channel
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_b_fold
            // B is registered on entry (a 2-deep skid, GitHub #119): the CAM
            // match and fold start from a flop and m_axi_bready is the skid's
            // registered ready, not a function of the CAM match. In a bridge
            // the unregistered form put a slave's CAM lookup, the crossbar's
            // B arbiter, this CAM match and the slave CAM's free in one
            // cycle -- the worst path of every fixture with a write
            // converter (4-7.5 ns over at 100 MHz on the Artix-7).
            localparam int BQ_W = AXI_ID_WIDTH + 2 + AXI_USER_WIDTH;
            logic                      q_bvalid;
            logic                      q_bready;
            logic [AXI_ID_WIDTH-1:0]   q_bid;
            logic [1:0]                q_bresp;
            logic [AXI_USER_WIDTH-1:0] q_buser;
            logic [BQ_W-1:0]           q_bpkt;

            gaxi_skid_buffer #(
                .DEPTH      (2),
                .DATA_WIDTH (BQ_W)
            ) b_in_skid (
                .axi_aclk   (aclk),
                .axi_aresetn(w_aresetn),
                .wr_valid   (m_axi_bvalid),
                .wr_ready   (m_axi_bready),
                .wr_data    ({m_axi_bid, m_axi_bresp, m_axi_buser}),
                .rd_valid   (q_bvalid),
                .rd_ready   (q_bready),
                .rd_data    (q_bpkt),
                .count      (),
                .rd_count   ()
            );
            assign {q_bid, q_bresp, q_buser} = q_bpkt;

            // A split slave burst gets several master B responses; the
            // slave expects ONE.  The old implementation walked a single
            // split-queue read pointer and assumed B responses arrived in
            // issue order.  BUG-008: when responses return cross-ID out of
            // order, that pointer misaligns and the wrong B is forwarded.
            //
            // Fix: keep a small CAM of outstanding slave bursts.  An entry
            // is allocated when a slave burst's final master AW is issued,
            // carrying the burst's AWID and the number of master bursts it
            // was split into.  Every B response searches the CAM for the
            // oldest matching AWID, decrements that burst's counter, folds
            // the response (worst-case wins), and forwards only when the
            // counter reaches zero.  Same-ID bursts stay in order; cross-ID
            // bursts can complete in any order.
            localparam int B_CAM_DEPTH = SPLITQ_DEPTH;
            localparam int B_CAM_AW    = $clog2(B_CAM_DEPTH);

            typedef struct packed {
                logic [AXI_ID_WIDTH-1:0] id;
                logic [7:0]              count;
                logic [1:0]              worst;
            } b_cam_entry_t;

            b_cam_entry_t b_cam [B_CAM_DEPTH];
            logic [B_CAM_DEPTH-1:0]  b_cam_valid;
            // b_cam_older[i]: the entries of i's ID that were live when i
            // was pushed -- all older than i.  i is its ID's oldest live
            // entry once none of them is still valid.
            logic [B_CAM_DEPTH-1:0]  b_cam_older [B_CAM_DEPTH];
            // b_cam_last[i]: entry i's count is 1 -- its next B is the slave
            // B. Registered so the decision is an AND with the hit vector.
            logic [B_CAM_DEPTH-1:0]  b_cam_last;

            // The burst currently being split.  The AW splitter finishes one
            // slave burst before accepting the next, so a single open-burst
            // register is enough.
            logic                    r_b_open_valid;
            logic [AXI_ID_WIDTH-1:0] r_b_open_id;
            logic [7:0]              r_b_open_count;

            // Push the open burst to the CAM on its final master AW issue.
            // Combinational: for a single-beat (unsplit) burst r_b_open_valid
            // is still low on the issue cycle, so the count is exactly 1.
            logic [7:0]              w_b_cam_push_count;
            assign w_b_cam_push_count = r_b_open_valid ? (r_b_open_count + 8'd1)
                                                       : 8'd1;

            // Find a free CAM slot for the next push.
            logic [B_CAM_AW-1:0] w_b_cam_free_idx;
            logic                w_b_cam_free_found;
            always_comb begin
                w_b_cam_free_found = 1'b0;
                w_b_cam_free_idx   = '0;
                for (int i = 0; i < B_CAM_DEPTH; i++) begin
                    if (!b_cam_valid[i] && !w_b_cam_free_found) begin
                        w_b_cam_free_found = 1'b1;
                        w_b_cam_free_idx   = B_CAM_AW'(i);
                    end
                end
            end
            assign w_b_cam_slot_free = w_b_cam_free_found;

            // Find the oldest outstanding burst matching the current B ID.
            // Same-ID B responses return in order, so the B belongs to that
            // ID's oldest live entry: the one whose older-set has fully
            // retired.  Exactly one entry qualifies, so the index is an OR
            // reduction (GitHub #119).  This replaced a 16-way serial
            // age-compare loop that synthesized to a ~32-LUT chain (WNS
            // -30 ns at 100 MHz on the Artix-7) and whose 5-bit age wrapped
            // at 32 (bridge BUG-016).  Correct whether or not same-ID bursts
            // are serialized: with at most one live entry per ID (the owner
            // invariant recorded at BUG-016) every older-set is empty.
            logic [B_CAM_DEPTH-1:0] w_b_cam_hit;
            logic                   w_b_cam_match;
            logic                   w_b_cam_last;     // the hit entry ends its slave burst
            logic [1:0]             w_b_cam_worst;    // the hit entry's folded response
            logic [B_CAM_DEPTH-1:0] w_b_cam_same_id;   // live entries of the pushed AWID
            // Consumers read the one-hot hit vector directly (AND-OR), never
            // an encoded index: encode-then-decode fanned out to every
            // entry's enable and was the converter's worst path in a bridge.
            always_comb begin
                w_b_cam_worst = '0;
                for (int i = 0; i < B_CAM_DEPTH; i++) begin
                    w_b_cam_hit[i] = b_cam_valid[i] && (b_cam[i].id == q_bid) &&
                                     ((b_cam_older[i] & b_cam_valid) == '0);
                    w_b_cam_same_id[i] = b_cam_valid[i] && (b_cam[i].id == int_awid);
                    if (w_b_cam_hit[i])
                        w_b_cam_worst = w_b_cam_worst | b_cam[i].worst;
                end
            end
            assign w_b_cam_match = |w_b_cam_hit;
            assign w_b_cam_last  = |(w_b_cam_hit & b_cam_last);

            // Drive B channel outputs.
            assign int_bid      = q_bid;
            assign int_buser    = q_buser;
            assign int_b_valid  = q_bvalid && w_b_cam_last;
            assign int_bresp    = (q_bresp > w_b_cam_worst) ? q_bresp : w_b_cam_worst;
            assign q_bready = (q_bvalid && w_b_cam_last)
                                  ? int_b_ready : 1'b1;

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    r_b_open_valid   <= 1'b0;
                    r_b_open_id      <= '0;
                    r_b_open_count   <= '0;
                    for (int i = 0; i < B_CAM_DEPTH; i++) begin
                        b_cam_valid[i] <= 1'b0;
                        b_cam[i]       <= '0;
                        b_cam_older[i] <= '0;
                        b_cam_last[i]  <= 1'b0;
                    end
                end else begin
                    // Track the burst currently being split.
                    if (w_aw_issue) begin
                        if (!r_b_open_valid) begin
                            // First master AW of a new slave burst.
                            r_b_open_valid <= 1'b1;
                            r_b_open_id    <= int_awid;
                            r_b_open_count <= 8'd1;
                        end else begin
                            r_b_open_count <= r_b_open_count + 8'd1;
                        end
                    end

                    // Close the open burst on its final master AW issue.
                    if (int_aw_valid && int_aw_ready) begin
                        r_b_open_valid <= 1'b0;
                    end

                    // Push finalized burst into the CAM when its last
                    // master AW is issued.  Use the current AWID directly so
                    // single-beat bursts do not suffer a register-update race.
                    if (w_aw_issue && w_this_last) begin
                        if (w_b_cam_free_found) begin
                            b_cam_valid[w_b_cam_free_idx] <= 1'b1;
                            b_cam[w_b_cam_free_idx].id    <= int_awid;
                            b_cam[w_b_cam_free_idx].count <= w_b_cam_push_count;
                            b_cam_last[w_b_cam_free_idx]  <= (w_b_cam_push_count == 8'd1);
                            b_cam[w_b_cam_free_idx].worst <= 2'b00;
                            // The slot's previous occupant is gone: drop it
                            // from every older-set, then record which live
                            // entries of this ID the new one waits behind.
                            for (int i = 0; i < B_CAM_DEPTH; i++)
                                b_cam_older[i][w_b_cam_free_idx] <= 1'b0;
                            b_cam_older[w_b_cam_free_idx] <= w_b_cam_same_id;
                        end
                    end

                    // Process an incoming master B response.
                    for (int i = 0; i < B_CAM_DEPTH; i++) begin
                        if (q_bvalid && q_bready && w_b_cam_hit[i]) begin
                            if (b_cam_last[i]) begin
                                b_cam_valid[i] <= 1'b0;
                            end else begin
                                b_cam[i].count <= b_cam[i].count - 8'd1;
                                b_cam_last[i]  <= (b_cam[i].count == 8'd2);
                                if (q_bresp > b_cam[i].worst)
                                    b_cam[i].worst <= q_bresp;
                            end
                        end
                    end
                end
            )

`ifdef SIMULATION
            // Defense in depth: gen_aw_downsize already gates a burst's final
            // master AW on w_b_cam_slot_free, so this should be unreachable.
            always_ff @(posedge aclk) begin
                if (w_aresetn && w_aw_issue && w_this_last && !w_b_cam_free_found)
                    $error("axi4_dwidth_converter_wr: B CAM overflow");
            end
`endif

        end else begin : gen_b_pass
            // Upsize: every master burst maps 1:1 to a slave burst, so no
            // CAM exists and AW issue is never CAM-gated.
            assign w_b_cam_slot_free = 1'b1;
            assign int_bid      = m_axi_bid;
            assign int_bresp    = m_axi_bresp;
            assign int_buser    = m_axi_buser;
            assign int_b_valid  = m_axi_bvalid;
            assign m_axi_bready = int_b_ready;
        end
    endgenerate

endmodule : axi4_dwidth_converter_wr
