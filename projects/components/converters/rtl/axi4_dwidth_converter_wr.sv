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
//   pass-through.
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

    // -----------------------------------------------------------------
    // Downsize burst-split queue (driven in gen_aw_downsize, consumed by
    // the W framing counter and the B fold; tied off for upsize).
    //
    // One slave burst can need more narrow beats than one legal master
    // burst can carry, so the AW splitter issues several master bursts
    // and records each one here: its beat count (for W framing) and
    // whether it is the slave burst's final one (for the B fold). Two
    // read pointers walk one memory -- W pops per completed master
    // burst, B pops per master response -- and since a burst's B always
    // follows its W data, the B pointer is the laggard and full is
    // checked against it alone.
    // -----------------------------------------------------------------
    logic       split_w_avail;   // an unconsumed entry exists for W framing
    logic [8:0] split_w_beats;   // its master-burst beat count (1..256)
    logic       split_w_pop;     // W side: consumed this entry
    logic       split_b_final;   // head-of-B entry: last burst of its slave burst
    logic       split_b_pop;     // B side: consumed one response
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
        .axi_aresetn(aresetn),
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
        .axi_aresetn(aresetn),
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
        .axi_aresetn(aresetn),
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
            localparam int SPLITQ_DEPTH = 16;
            localparam int SPLITQ_AW    = $clog2(SPLITQ_DEPTH);

            logic [CNTW-1:0]           r_split_remaining;
            logic [AXI_ADDR_WIDTH-1:0] r_split_addr;
            logic                      r_split_active;
            logic [8:0]                w_this_beats;
            logic                      w_this_last;
            logic                      w_aw_issue;

            assign w_this_beats = (r_split_remaining > CNTW'(MAX_BEATS))
                                  ? 9'(MAX_BEATS) : 9'(r_split_remaining);
            assign w_this_last  = (r_split_remaining <= CNTW'(MAX_BEATS));
            assign w_aw_issue   = m_axi_awvalid && m_axi_awready;

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
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

            // Split queue: one memory, two read pointers (see the
            // declaration block above). Push at each master AW issue;
            // AW is back-pressured on full so it cannot overflow.
            logic [9:0]           splitq_mem [SPLITQ_DEPTH];
            logic [SPLITQ_AW:0]   splitq_wptr, splitq_rptr_w, splitq_rptr_b;
            logic                 w_splitq_full;

            // B trails W, so B's pointer is the laggard: full-check it.
            assign w_splitq_full =
                (splitq_wptr[SPLITQ_AW-1:0] == splitq_rptr_b[SPLITQ_AW-1:0]) &&
                (splitq_wptr[SPLITQ_AW]     != splitq_rptr_b[SPLITQ_AW]);
            assign split_w_avail = (splitq_wptr != splitq_rptr_w);
            assign split_w_beats = splitq_mem[splitq_rptr_w[SPLITQ_AW-1:0]][8:0];
            assign split_b_final = splitq_mem[splitq_rptr_b[SPLITQ_AW-1:0]][9];

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    splitq_wptr   <= '0;
                    splitq_rptr_w <= '0;
                    splitq_rptr_b <= '0;
                end else begin
                    if (w_aw_issue) begin
                        splitq_mem[splitq_wptr[SPLITQ_AW-1:0]]
                            <= {w_this_last, w_this_beats};
                        splitq_wptr <= splitq_wptr + 1'b1;
                    end
                    if (split_w_pop) splitq_rptr_w <= splitq_rptr_w + 1'b1;
                    if (split_b_pop) splitq_rptr_b <= splitq_rptr_b + 1'b1;
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
            assign m_axi_awvalid  = r_split_active && !w_splitq_full;
            // the slave's AW is consumed only when its FINAL master
            // burst is issued
            assign int_aw_ready   = w_aw_issue && w_this_last;

        end else begin : gen_aw_upsize
            // Upsize: slave (narrow) → master (wide). Divide burst length
            // by ratio (round up). Division can never overflow AWLEN, so
            // no splitting is needed and the split queue is tied off.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);

            assign split_w_avail = 1'b0;
            assign split_w_beats = 9'd0;
            assign split_b_final = 1'b1;

            assign m_axi_awid     = int_awid;
            assign m_axi_awaddr   = int_awaddr;
            assign m_axi_awlen    = ((int_awlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
            assign m_axi_awsize   = MASTER_SIZE[2:0];
            assign m_axi_awburst  = int_awburst;
            assign m_axi_awlock   = int_awlock;
            assign m_axi_awcache  = int_awcache;
            assign m_axi_awprot   = int_awprot;
            assign m_axi_awqos    = int_awqos;
            assign m_axi_awregion = int_awregion;
            assign m_axi_awuser   = int_awuser;
            assign m_axi_awvalid  = int_aw_valid;
            assign int_aw_ready   = m_axi_awready;
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

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
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
                .aresetn         (aresetn),
                .burst_len       (8'd0),
                .burst_start     (1'b0),
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
            // no beat can slip through unframed. For an unsplit burst
            // the queue holds exactly one entry and this degenerates to
            // the old passthrough with one idle cycle at burst start.
            logic [8:0] r_w_beats_left;

            assign split_w_pop = (r_w_beats_left == 9'd0) && split_w_avail;

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_w_beats_left <= 9'd0;
                end else if (r_w_beats_left == 9'd0) begin
                    if (split_w_avail)
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
            axi_data_upsize #(
                .NARROW_WIDTH    (S_AXI_DATA_WIDTH),
                .WIDE_WIDTH      (M_AXI_DATA_WIDTH),
                .NARROW_SB_WIDTH (S_STRB_WIDTH),
                .WIDE_SB_WIDTH   (M_STRB_WIDTH),
                .SB_OR_MODE      (0)
            ) u_w_upsize (
                .aclk            (aclk),
                .aresetn         (aresetn),
                .narrow_valid    (int_w_valid),
                .narrow_ready    (int_w_ready),
                .narrow_data     (int_wdata),
                .narrow_sideband (int_wstrb),
                .narrow_last     (int_wlast),
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
            // A split slave burst gets several master B responses; the
            // slave expects ONE. The split queue's head flag says whether
            // the response now arriving belongs to the final master burst
            // of its slave burst. Non-final responses are consumed
            // immediately and folded (worst case wins -- the same fold
            // axi4_to_axil4_wr uses); the final one carries the folded
            // result to the slave. All master bursts of a slave burst
            // share its ID, so forwarding the final B's ID is correct.
            logic [1:0] r_b_worst;

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_b_worst <= 2'b00;
                end else if (m_axi_bvalid && m_axi_bready) begin
                    if (split_b_final)
                        r_b_worst <= 2'b00;              // slave burst done
                    else if (m_axi_bresp > r_b_worst)
                        r_b_worst <= m_axi_bresp;
                end
            )

            assign split_b_pop  = m_axi_bvalid && m_axi_bready;
            assign int_bid      = m_axi_bid;
            assign int_bresp    = (m_axi_bresp > r_b_worst) ? m_axi_bresp
                                                            : r_b_worst;
            assign int_buser    = m_axi_buser;
            assign int_b_valid  = m_axi_bvalid && split_b_final;
            assign m_axi_bready = split_b_final ? int_b_ready : 1'b1;

        end else begin : gen_b_pass
            assign split_b_pop  = 1'b0;
            assign int_bid      = m_axi_bid;
            assign int_bresp    = m_axi_bresp;
            assign int_buser    = m_axi_buser;
            assign int_b_valid  = m_axi_bvalid;
            assign m_axi_bready = int_b_ready;
        end
    endgenerate

endmodule : axi4_dwidth_converter_wr
