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
//   Every legal AXI4 write burst is carried (bridge BUG-018/019): FIXED,
//   INCR and WRAP, any AWSIZE, unaligned starts, in three modes (CM_PACK,
//   CM_PASS, CM_EXPAND; see the localparams). UPSIZE full-width INCR
//   packs W through the validated axi_data_upsize primitive; every other
//   W path is converted in this wrapper (the DOWNSIZE chunk slicer, the
//   UPSIZE pass-through). The wrapper also owns the AW/W/B skid buffers,
//   the AW rewrite and split sequencer, the wuser carry, and the B
//   channel split-fold CAM (per-AWID outstanding-split counter, BUG-008).
//   CM_EXPAND (DOWNSIZE FIXED / WRAP wider than the narrow bus) issues
//   one master burst per slave beat: correct, but not fast.
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
    localparam int LANE_W       = $clog2(WIDTH_RATIO),

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
    // The master AW on offer is its slave burst's FIRST, and the number of
    // master bursts that slave burst splits into (1..WIDTH_RATIO).
    logic       w_this_first;
    logic [8:0] w_this_parts;
    // A free B-CAM slot exists (driven in gen_b_fold, consumed in
    // gen_aw_downsize): a slave burst's FIRST master AW must not issue
    // unless the CAM can take its entry, or the push would be dropped and
    // that burst's B responses would match nothing (BUG-008 follow-up:
    // the CAM drains on B return while the split queue drains on W
    // framing, so split-queue space alone does not bound CAM occupancy).
    // The entry is pushed at the first master AW, not the last: a slave may
    // answer part 1 while a later part's AW still waits, and a B with no
    // entry is taken and dropped (converters BUG-012).
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
    logic [1:0]        split_w_mode;    // its conversion mode
    logic [LANE_W-1:0] split_w_lane;    // the wide-word chunk its first beat comes from
    logic [LANE_W-1:0] split_w_rmask;   // chunks per slave beat - 1

    // Conversion mode of each master burst (bridge BUG-018/019), as in the
    // read converter:
    //   CM_PACK   UPSIZE: full-width INCR, packed into wide beats (start lane
    //             counted). DOWNSIZE: INCR wider than the narrow bus, as
    //             narrow INCR pieces of <= 256 beats.
    //   CM_PASS   a burst no wider than the narrower bus: issued unchanged
    //             (same address, length, size and type), one beat for one.
    //   CM_EXPAND DOWNSIZE FIXED / WRAP wider than the narrow bus: one narrow
    //             INCR piece per slave beat, at that beat's address.
    localparam logic [1:0] CM_PACK = 2'd0, CM_PASS = 2'd1, CM_EXPAND = 2'd2;

    // UPSIZE only (driven in gen_aw_upsize, consumed in gen_w_upsize):
    // start lane of the burst the next W beats belong to, and the gate
    // that holds W off until its AW has been accepted (the lane comes
    // from AWADDR). Tied inert in DOWNSIZE.
    logic [7:0] w_upsize_start_lane;
    logic       w_upsize_w_gate;
    // UPSIZE CM_PASS: the head burst's mode and address walk
    logic [1:0]                       w_upsize_mode;
    logic [$clog2(M_STRB_WIDTH)-1:0]  w_upsize_pa;      // first beat address, low bits
    logic [2:0]                       w_upsize_size;
    logic [1:0]                       w_upsize_burst;
    logic [7:0]                       w_upsize_len;
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
            assign w_upsize_mode       = CM_PACK;
            assign w_upsize_pa         = '0;
            assign w_upsize_size       = '0;
            assign w_upsize_burst      = '0;
            assign w_upsize_len        = '0;

            // Downsize: slave (wide) -> master (narrow). Every slave burst
            // becomes one or more master bursts, each legal AXI on the
            // narrow bus (bridge BUG-018/019), the same three modes as the
            // read converter:
            //
            //   CM_PASS   AWSIZE fits the narrow bus: the burst is issued
            //             unchanged; each wide W beat gives one narrow beat.
            //   CM_PACK   INCR wider than the narrow bus: narrow INCR pieces
            //             of <= 256 beats covering the burst's bytes from its
            //             (possibly unaligned) start. A wide beat of 2^size
            //             bytes is 2^(size - narrow size) narrow beats, the
            //             first fewer by its start lane. The first piece is
            //             shortened by that lane too, so every later piece
            //             starts on a slave-beat boundary, at
            //             aligned(start) + n * 256 narrow beats (BUG-019:
            //             the old step walked on from the unaligned start).
            //             AXI4 allows 256 beats, so a full-length slave burst
            //             needs up to 256*WIDTH_RATIO narrow beats -- neither
            //             expressible in AWLEN nor legal (the old
            //             ((awlen+1)*RATIO)-1 wrapped 511 to 255).
            //   CM_EXPAND FIXED / WRAP wider than the narrow bus: one narrow
            //             INCR piece per slave beat, at that beat's address.
            //
            // Each piece is recorded in the split queue for the W framing
            // and counted into the B fold.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int MAX_BEATS   = 256;
            localparam int CNTW        = 9 + $clog2(WIDTH_RATIO);
            localparam int CNTP        = CNTW + 1;
            localparam int SPLITQ_AW   = $clog2(SPLITQ_DEPTH);
            localparam int AW          = AXI_ADDR_WIDTH;

            logic [CNTW-1:0]           r_split_remaining;  // CM_PACK: narrow beats left
            logic [AW-1:0]             r_split_addr;       // the next master burst's address
            logic [8:0]                r_beats_left;       // CM_EXPAND: slave beats left
            logic                      r_split_active;
            logic                      r_split_issued;     // a part of this burst has issued
            logic [1:0]                w_mode;
            logic [2:0]                w_rlog;             // log2(narrow beats per slave beat)
            logic [AW-1:0]             w_bmask;            // slave beat bytes - 1
            logic [AW-1:0]             w_wmask;            // WRAP container bytes - 1
            logic [AW-1:0]             w_next_beat;        // CM_EXPAND: the next slave beat's address
            logic [8:0]                w_lane_in_beat;     // narrow lane of r_split_addr in its beat
            logic [8:0]                w_cap;
            logic [8:0]                w_this_beats;
            logic [LANE_W-1:0]         w_this_lane;        // the piece's first chunk in the wide word
            logic [LANE_W-1:0]         w_this_rmask;       // chunks per slave beat - 1

            assign w_mode = (int_awsize <= 3'(MASTER_SIZE)) ? CM_PASS
                          : (int_awburst == 2'b01)          ? CM_PACK : CM_EXPAND;
            assign w_rlog         = int_awsize - 3'(MASTER_SIZE);   // unused in CM_PASS
            assign w_bmask        = (AW'(1) << int_awsize) - AW'(1);
            assign w_wmask        = ((AW'(int_awlen) + AW'(1)) << int_awsize) - AW'(1);
            assign w_lane_in_beat = 9'((r_split_addr & w_bmask) >> MASTER_SIZE);
            // 0 after the first piece: later pieces start beat-aligned
            assign w_cap          = 9'(MAX_BEATS) - w_lane_in_beat;
            assign w_next_beat    = (int_awburst == 2'b10)
                ? ((r_split_addr & ~w_wmask) |
                   (((r_split_addr & ~w_bmask) + w_bmask + AW'(1)) & w_wmask))
                : r_split_addr;                                     // FIXED holds
            assign w_this_lane    = LANE_W'(r_split_addr[$clog2(S_STRB_WIDTH)-1:0] >> MASTER_SIZE);
            assign w_this_rmask   = (w_mode == CM_PASS) ? '0 : LANE_W'((9'd1 << w_rlog) - 9'd1);

            always_comb begin
                case (w_mode)
                    CM_PASS: begin
                        w_this_beats = 9'(int_awlen) + 9'd1;
                        w_this_last  = 1'b1;
                        w_this_parts = 9'd1;
                    end
                    CM_EXPAND: begin
                        w_this_beats = (9'd1 << w_rlog) - w_lane_in_beat;
                        w_this_last  = (r_beats_left == 9'd1);
                        w_this_parts = 9'(int_awlen) + 9'd1;
                    end
                    default: begin
                        w_this_beats = (r_split_remaining > CNTW'(w_cap))
                                       ? w_cap : 9'(r_split_remaining);
                        w_this_last  = (r_split_remaining <= CNTW'(w_cap));
                        // the first piece is 256 - lane long, so the parts
                        // tile (len+1) << rlog narrow beats in 256s
                        w_this_parts = 9'((((CNTP'(int_awlen) + CNTP'(1)) << w_rlog)
                                           + CNTP'(MAX_BEATS - 1)) >> 8);
                    end
                endcase
            end
            assign w_this_first = !r_split_issued;
            assign w_aw_issue   = m_axi_awvalid && m_axi_awready;

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    r_split_remaining <= '0;
                    r_split_addr      <= '0;
                    r_beats_left      <= '0;
                    r_split_active    <= 1'b0;
                    r_split_issued    <= 1'b0;
                end else if (!r_split_active) begin
                    r_split_issued <= 1'b0;
                    if (int_aw_valid) begin
                        // narrow beats from the start lane to the end of the
                        // last slave beat
                        r_split_remaining <= ((CNTW'(int_awlen) + CNTW'(1)) << w_rlog)
                                             - CNTW'((int_awaddr & w_bmask) >> MASTER_SIZE);
                        r_split_addr      <= int_awaddr;
                        r_beats_left      <= 9'(int_awlen) + 9'd1;
                        r_split_active    <= 1'b1;
                    end
                end else if (w_aw_issue) begin
                    r_split_issued <= !w_this_last;
                    if (w_this_last) begin
                        r_split_remaining <= '0;
                        r_split_active    <= 1'b0;
                    end else begin
                        r_split_remaining <= r_split_remaining - CNTW'(w_this_beats);
                        r_beats_left      <= r_beats_left - 9'd1;
                        r_split_addr      <= (w_mode == CM_EXPAND) ? w_next_beat
                            : ((r_split_addr & ~w_bmask) + AW'(MAX_BEATS * M_STRB_WIDTH));
                    end
                end
            )

            // Split queue: one memory, one read pointer for W framing.
            // Push at each master AW issue; AW is back-pressured on full
            // so it cannot overflow. Entry: {mode, first chunk, chunks per
            // slave beat - 1, beats}.
            localparam int SQ_W = 2 + 2 * LANE_W + 9;
            logic [SQ_W-1:0]      splitq_mem [SPLITQ_DEPTH];
            logic [SPLITQ_AW:0]   splitq_wptr, splitq_rptr_w;
            logic                 w_splitq_full;

            // Full is checked against the W pointer: once W has framed a
            // master burst's data the entry can be reused for new AWs.
            assign w_splitq_full =
                (splitq_wptr[SPLITQ_AW-1:0] == splitq_rptr_w[SPLITQ_AW-1:0]) &&
                (splitq_wptr[SPLITQ_AW]     != splitq_rptr_w[SPLITQ_AW]);
            assign split_w_avail = (splitq_wptr != splitq_rptr_w);
            assign {split_w_mode, split_w_lane, split_w_rmask, split_w_beats} =
                splitq_mem[splitq_rptr_w[SPLITQ_AW-1:0]];

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    splitq_wptr   <= '0;
                    splitq_rptr_w <= '0;
                end else begin
                    if (w_aw_issue) begin
                        splitq_mem[splitq_wptr[SPLITQ_AW-1:0]]
                            <= {w_mode, w_this_lane, w_this_rmask, w_this_beats};
                        splitq_wptr <= splitq_wptr + 1'b1;
                    end
                    if (split_w_pop) splitq_rptr_w <= splitq_rptr_w + 1'b1;
                end
            )

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = r_split_addr;
            assign m_axi_awlen    = 8'(w_this_beats - 9'd1);
            assign m_axi_awsize   = (w_mode == CM_PASS) ? int_awsize  : MASTER_SIZE[2:0];
            assign m_axi_awburst  = (w_mode == CM_PASS) ? int_awburst : 2'b01;
            assign m_axi_awlock   = int_awlock;
            assign m_axi_awcache  = int_awcache;
            assign m_axi_awprot   = int_awprot;
            assign m_axi_awqos    = int_awqos;
            assign m_axi_awregion = int_awregion;
            assign m_axi_awuser   = int_awuser;
            // The FIRST master AW of a slave burst pushes the B CAM, so it
            // must wait for a free CAM slot; later parts need none.
            assign m_axi_awvalid  = r_split_active && !w_splitq_full &&
                                    (!w_this_first || w_b_cam_slot_free);
            // the slave's AW is consumed only when its FINAL master
            // burst is issued
            assign int_aw_ready   = w_aw_issue && w_this_last;

        end else begin : gen_aw_upsize
            // Upsize: slave (narrow) -> master (wide) (bridge BUG-018/019).
            //   CM_PACK  full-width INCR: divide the burst length by the ratio
            //            (round up), counting the start lane: a burst may
            //            begin mid-wide-word, in which case its first wide
            //            beat is partial. Division can never overflow AWLEN,
            //            so nothing splits.
            //   CM_PASS  everything else -- FIXED, WRAP, and INCR narrower
            //            than the slave bus: already legal on the wider bus,
            //            so the AW is issued unchanged and each narrow W beat
            //            becomes one wide beat, its strobes in the lanes the
            //            beat's address selects.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int PAW         = $clog2(M_STRB_WIDTH);

            assign split_w_avail = 1'b0;
            assign split_w_beats = 9'd0;
            assign split_w_mode  = CM_PACK;
            assign split_w_lane  = '0;
            assign split_w_rmask = '0;
            assign w_this_last   = 1'b1;
            assign w_this_first  = 1'b1;
            assign w_this_parts  = 9'd1;
            assign w_aw_issue    = m_axi_awvalid && m_axi_awready;

            logic [1:0] w_mode;
            assign w_mode = ((int_awburst == 2'b01) &&
                             (int_awsize == 3'($clog2(S_STRB_WIDTH)))) ? CM_PACK : CM_PASS;

            // Narrow-lane offset of the burst start inside the wide word.
            logic [LANE_W-1:0] w_aw_lane;
            assign w_aw_lane = LANE_W'(int_awaddr[$clog2(M_STRB_WIDTH)-1:0]
                                       >> $clog2(S_STRB_WIDTH));

            // AW queue: the W side needs, for the burst its FIRST W beat
            // belongs to, the start lane (CM_PACK) or the burst's address
            // walk (CM_PASS), and W may run ahead of or behind AW. One entry
            // per accepted AW, popped on the narrow WLAST. W is held off
            // while empty (deadlock-free: AW never depends on W).
            localparam int WLANE_DEPTH = 16;
            localparam int WLANE_AW    = $clog2(WLANE_DEPTH);
            localparam int WQ_W        = 2 + LANE_W + PAW + 3 + 2 + 8;
            logic [WQ_W-1:0]    wlane_mem [WLANE_DEPTH];
            logic [WLANE_AW:0]  wlane_wptr, wlane_rptr;
            logic               w_wlane_full, w_wlane_avail;
            logic [LANE_W-1:0]  w_head_lane;
            assign w_wlane_full  = (wlane_wptr[WLANE_AW] != wlane_rptr[WLANE_AW]) &&
                                   (wlane_wptr[WLANE_AW-1:0] == wlane_rptr[WLANE_AW-1:0]);
            assign w_wlane_avail = (wlane_wptr != wlane_rptr);

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    wlane_wptr <= '0;
                    wlane_rptr <= '0;
                end else begin
                    if (int_aw_valid && int_aw_ready) begin
                        wlane_mem[wlane_wptr[WLANE_AW-1:0]] <=
                            {w_mode, w_aw_lane, PAW'(int_awaddr), int_awsize, int_awburst, int_awlen};
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

            assign {w_upsize_mode, w_head_lane, w_upsize_pa, w_upsize_size,
                    w_upsize_burst, w_upsize_len} = wlane_mem[wlane_rptr[WLANE_AW-1:0]];
            assign w_upsize_start_lane = 8'(w_head_lane);
            assign w_upsize_w_gate     = w_wlane_avail;

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = int_awaddr;
            // Wide beats = ceil((lane + narrow_beats) / RATIO); 10-bit
            // intermediate so lane + 255 + RATIO cannot wrap.
            assign m_axi_awlen    = (w_mode == CM_PASS) ? int_awlen
                                  : 8'(((10'(w_aw_lane) + 10'(int_awlen) + 10'(WIDTH_RATIO))
                                        / 10'(WIDTH_RATIO)) - 10'd1);
            assign m_axi_awsize   = (w_mode == CM_PASS) ? int_awsize : MASTER_SIZE[2:0];
            assign m_axi_awburst  = int_awburst;
            assign m_axi_awlock   = int_awlock;
            assign m_axi_awcache  = int_awcache;
            assign m_axi_awprot   = int_awprot;
            assign m_axi_awqos    = int_awqos;
            assign m_axi_awregion = int_awregion;
            assign m_axi_awuser   = int_awuser;
            assign m_axi_awvalid  = int_aw_valid && !w_wlane_full;
            assign int_aw_ready   = m_axi_awready && !w_wlane_full;
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
            // Slave wide, master narrow. W direction: slave -> master, so
            // wide -> narrow, one narrow beat per chunk of the wide beat that
            // the master burst covers (bridge BUG-018/019). Each master burst
            // is framed by its split-queue entry -- a queue, not a snapshot
            // of the AW side, because AW deliberately runs ahead of W and a
            // single shared register would be overwritten mid-burst (that
            // exact failure delivered 505 of 512 beats in an earlier
            // version). The entry gives:
            //   beats   the master burst's narrow beat count, for its WLAST
            //   lane    the chunk its first narrow beat comes from (an
            //           unaligned or mid-burst start is not chunk 0)
            //   rmask   chunks per slave beat - 1: the wide beat is taken
            //           when its last covered chunk goes (a narrow AWSIZE
            //           covers fewer than WIDTH_RATIO chunks)
            //   mode    CM_PASS: one narrow beat per wide beat, from the
            //           chunk that holds its strobes (a beat no wider than
            //           the narrow bus lies inside one chunk)
            //
            // W data is held until its burst's entry has been loaded, so no
            // beat can slip through unframed. The next entry loads on the
            // current burst's last W handshake when it is already queued (AW
            // runs ahead of W), so back-to-back bursts stream without a dead
            // cycle; it loads from empty otherwise.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            logic [8:0]        r_w_beats_left;
            logic [LANE_W-1:0] r_w_chunk;
            logic [LANE_W-1:0] r_w_rmask;
            logic [1:0]        r_w_mode;
            logic [LANE_W-1:0] w_pass_chunk;
            logic [LANE_W-1:0] w_chunk;
            logic              w_last_hs, w_hs, w_take_wide;

            always_comb begin
                w_pass_chunk = '0;
                for (int k = WIDTH_RATIO - 1; k >= 0; k--)
                    if (|int_wstrb[k*M_STRB_WIDTH +: M_STRB_WIDTH])
                        w_pass_chunk = LANE_W'(k);
            end
            assign w_chunk       = (r_w_mode == CM_PASS) ? w_pass_chunk : r_w_chunk;
            assign m_axi_wvalid  = int_w_valid && (r_w_beats_left != 9'd0);
            assign m_axi_wdata   = int_wdata[w_chunk*M_AXI_DATA_WIDTH +: M_AXI_DATA_WIDTH];
            assign m_axi_wstrb   = int_wstrb[w_chunk*M_STRB_WIDTH +: M_STRB_WIDTH];
            assign m_axi_wlast   = (r_w_beats_left == 9'd1);
            assign w_hs          = m_axi_wvalid && m_axi_wready;
            assign w_last_hs     = w_hs && (r_w_beats_left == 9'd1);
            // the wide beat is done with its last covered chunk
            assign w_take_wide   = (r_w_mode == CM_PASS) || ((r_w_chunk & r_w_rmask) == r_w_rmask);
            assign int_w_ready   = m_axi_wready && (r_w_beats_left != 9'd0) && w_take_wide;
            assign split_w_pop   = split_w_avail && ((r_w_beats_left == 9'd0) || w_last_hs);

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    r_w_beats_left <= 9'd0;
                    r_w_chunk      <= '0;
                    r_w_rmask      <= '0;
                    r_w_mode       <= CM_PACK;
                end else if (split_w_pop) begin
                    r_w_beats_left <= split_w_beats;
                    r_w_chunk      <= split_w_lane;
                    r_w_rmask      <= split_w_rmask;
                    r_w_mode       <= split_w_mode;
                end else if (w_hs) begin
                    r_w_beats_left <= r_w_beats_left - 9'd1;
                    r_w_chunk      <= r_w_chunk + LANE_W'(1);
                end
            )

        end else begin : gen_w_upsize
            assign split_w_pop = 1'b0;
            // Slave narrow, master wide. W direction: slave -> master, so
            // narrow -> wide.
            //   CM_PACK: axi_data_upsize concatenates WSTRBs (SB_OR_MODE=0);
            //     wlast on the narrow side terminates the accumulation early.
            //     The packer's start lane comes from AWADDR (the AW queue).
            //   CM_PASS: one wide beat per narrow beat, the data copied into
            //     every chunk and the strobes into the chunk the beat's
            //     address selects. pa walks that address by the burst rules
            //     (AXI A3.4.1); only its low bits matter here. A PASS beat
            //     waits until the packer has sent its last wide beat, so the
            //     two never drive m_axi W at once.
            // W is held off until its AW is queued.
            localparam int PAW = $clog2(M_STRB_WIDTH);
            logic              w_upz_nready, w_upz_wvalid, w_upz_wlast;
            logic [M_AXI_DATA_WIDTH-1:0] w_upz_wdata;
            logic [M_STRB_WIDTH-1:0]     w_upz_wstrb;
            logic              w_pass, w_pass_go, w_sel_prim;
            logic [2:0]        r_prim_bursts;     // bursts the packer has taken in but not sent
            logic              w_prim_busy;
            logic              r_pa_live;         // pa is mid-burst (not the head's start)
            logic [PAW-1:0]    r_pa;
            logic [PAW-1:0]    w_pa, w_pa_bm, w_pa_wm, w_pa_step, w_pa_next;
            logic [15:0]       w_pa_span;
            logic [LANE_W-1:0] w_pa_chunk;

            // The head of the AW queue moves on at the narrow WLAST, while the
            // packer may still hold that burst's last wide beat: m_axi W stays
            // with the packer until it has sent every burst it took in.
            assign w_pass      = (w_upsize_mode == CM_PASS);
            assign w_prim_busy = (r_prim_bursts != 3'd0);
            assign w_sel_prim  = w_prim_busy || !w_pass;
            assign w_pass_go   = w_upsize_w_gate && w_pass && !w_prim_busy;
            assign w_pa      = r_pa_live ? r_pa : w_upsize_pa;
            assign w_pa_bm   = PAW'((16'd1 << w_upsize_size) - 16'd1);
            assign w_pa_span = (16'(w_upsize_len) + 16'd1) << w_upsize_size;
            assign w_pa_wm   = PAW'(w_pa_span - 16'd1);
            assign w_pa_step = (w_pa & ~w_pa_bm) + w_pa_bm + PAW'(1);
            assign w_pa_next = (w_upsize_burst == 2'b00) ? w_pa
                             : (w_upsize_burst == 2'b10) ? ((w_pa & ~w_pa_wm) | (w_pa_step & w_pa_wm))
                             :                              w_pa_step;
            assign w_pa_chunk = LANE_W'(w_pa >> $clog2(S_STRB_WIDTH));

            assign int_w_ready = w_pass ? (w_pass_go && m_axi_wready)
                                        : (w_upz_nready && w_upsize_w_gate);

            always_comb begin
                m_axi_wstrb = '0;
                for (int k = 0; k < WIDTH_RATIO; k++)
                    if (LANE_W'(k) == w_pa_chunk)
                        m_axi_wstrb[k*S_STRB_WIDTH +: S_STRB_WIDTH] = int_wstrb;
                if (w_sel_prim)
                    m_axi_wstrb = w_upz_wstrb;
            end
            assign m_axi_wvalid = w_sel_prim ? w_upz_wvalid : (int_w_valid && w_pass_go);
            assign m_axi_wdata  = w_sel_prim ? w_upz_wdata  : {WIDTH_RATIO{int_wdata}};
            assign m_axi_wlast  = w_sel_prim ? w_upz_wlast  : int_wlast;

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    r_prim_bursts <= 3'd0;
                    r_pa_live     <= 1'b0;
                    r_pa          <= '0;
                end else begin
                    r_prim_bursts <= r_prim_bursts
                        + 3'(!w_pass && int_w_valid && int_w_ready && int_wlast)
                        - 3'(w_sel_prim && w_upz_wvalid && m_axi_wready && w_upz_wlast);
                    if (w_pass && int_w_valid && int_w_ready) begin
                        r_pa      <= w_pa_next;
                        r_pa_live <= !int_wlast;
                    end
                end
            )

            axi_data_upsize #(
                .NARROW_WIDTH    (S_AXI_DATA_WIDTH),
                .WIDE_WIDTH      (M_AXI_DATA_WIDTH),
                .NARROW_SB_WIDTH (S_STRB_WIDTH),
                .WIDE_SB_WIDTH   (M_STRB_WIDTH),
                .SB_OR_MODE      (0)
            ) u_w_upsize (
                .aclk            (aclk),
                .aresetn         (w_aresetn),
                .narrow_valid    (int_w_valid && w_upsize_w_gate && !w_pass),
                .narrow_ready    (w_upz_nready),
                .narrow_data     (int_wdata),
                .narrow_sideband (int_wstrb),
                .narrow_last     (int_wlast),
                .start_lane      (w_upsize_start_lane[$clog2(WIDTH_RATIO)-1:0]),
                .wide_valid      (w_upz_wvalid),
                .wide_ready      (m_axi_wready && w_sel_prim),
                .wide_data       (w_upz_wdata),
                .wide_sideband   (w_upz_wstrb),
                .wide_last       (w_upz_wlast)
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
                logic [8:0]              count;   // up to 256 parts (CM_EXPAND)
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

            // The entry is pushed at the slave burst's FIRST master AW issue,
            // carrying how many master bursts it splits into: every B it
            // will get -- the first part's included, which a slave may return
            // before a later part's AW issues -- finds it (converters
            // BUG-012; the entry used to be pushed at the final AW).
            logic [8:0]              w_b_cam_push_count;
            assign w_b_cam_push_count = w_this_parts;

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
                    for (int i = 0; i < B_CAM_DEPTH; i++) begin
                        b_cam_valid[i] <= 1'b0;
                        b_cam[i]       <= '0;
                        b_cam_older[i] <= '0;
                        b_cam_last[i]  <= 1'b0;
                    end
                end else begin
                    // Push the burst into the CAM when its first master AW
                    // issues (int_awid is that burst's ID throughout).
                    if (w_aw_issue && w_this_first) begin
                        if (w_b_cam_free_found) begin
                            b_cam_valid[w_b_cam_free_idx] <= 1'b1;
                            b_cam[w_b_cam_free_idx].id    <= int_awid;
                            b_cam[w_b_cam_free_idx].count <= w_b_cam_push_count;
                            b_cam_last[w_b_cam_free_idx]  <= (w_b_cam_push_count == 9'd1);
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
                                b_cam[i].count <= b_cam[i].count - 9'd1;
                                b_cam_last[i]  <= (b_cam[i].count == 9'd2);
                                if (q_bresp > b_cam[i].worst)
                                    b_cam[i].worst <= q_bresp;
                            end
                        end
                    end
                end
            )

`ifdef SIMULATION
            // Defense in depth: gen_aw_downsize already gates a burst's first
            // master AW on w_b_cam_slot_free, so this should be unreachable.
            always_ff @(posedge aclk) begin
                if (w_aresetn && w_aw_issue && w_this_first && !w_b_cam_free_found)
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
