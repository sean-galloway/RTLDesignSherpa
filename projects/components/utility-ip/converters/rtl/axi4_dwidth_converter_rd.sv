// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_dwidth_converter_rd
// Purpose: AXI4 Read Data Width Converter (READ-ONLY, STANDALONE)
//
// Description:
//   Converts between AXI4 read interfaces of different data widths.
//   Handles ONLY read path (AR, R channels) - no write support.
//
//   The R channel data path is delegated to the validated
//   axi_data_upsize / axi_data_dnsize primitives in this same
//   directory (each with its own pytest suite). This wrapper still
//   owns: AR/R skid buffers, the AR arlen/arsize rewrite, the
//   per-ID R reassembly layer (BUG-009), and the rid/ruser carry
//   that the primitives don't handle.
//
//   BUG-009 design note (2026-10-04):
//   AXI4 permits a slave to interleave R beats across ARIDs.  The
//   data primitives can only process one contiguous burst at a time,
//   so a reassembly layer between m_axi R and the primitives buffers
//   beats per ID until an entire master burst is assembled, then feeds
//   that burst contiguously.  To keep the buffer bounded and deadlock-
//   free, each ID can have at most one unassembled master burst in the
//   layer: master AR issue for an ID is throttled until its previous
//   burst has been completely fed to the primitive.  This serializes
//   same-ID read chains through reassembly; cross-ID traffic is still
//   concurrent and can interleave arbitrarily on m_axi R.  A shared
//   beat pool (one linked-list FIFO) is used instead of per-ID FIFOs
//   to avoid the 2^ID_WIDTH area explosion when AXI_ID_WIDTH is large.
//
//   For write conversion, use axi4_dwidth_converter_wr.sv.
//
// Parameters:
//   S_AXI_DATA_WIDTH: Slave interface data width (32, 64, 128, 256)
//   M_AXI_DATA_WIDTH: Master interface data width (32, 64, 128, 256)
//   AXI_ID_WIDTH: Transaction ID width (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_USER_WIDTH: User signal width (0-1024)
//   SKID_DEPTH_AR: AR channel skid buffer depth (2-8, default 2)
//   SKID_DEPTH_R: R channel skid buffer depth (2-8, default 4)
//   RASM_DEPTH: Per-ID beat capacity, >= max master burst (default 272)
//   RASM_MAX_OUTSTANDING: Shared pool capacity in bursts (default 16)
//
// Author: RTL Design Sherpa
// Created: 2025-10-24

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_dwidth_converter_rd #(
    // Width Configuration
    parameter int S_AXI_DATA_WIDTH  = 32,
    parameter int M_AXI_DATA_WIDTH  = 128,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AR     = 4,
    parameter int SKID_DEPTH_R      = 4,

    // BUG-009 reassembly layer sizing.  RASM_DEPTH must cover the
    // largest legal master burst (256 beats) plus a small margin so a
    // per-ID queue never needs to back-pressure legal traffic.
    // RASM_MAX_OUTSTANDING matches the previous AR split / burst-length
    // FIFO depths and bounds the shared beat pool.
    parameter int RASM_DEPTH             = 272,
    parameter int RASM_MAX_OUTSTANDING   = 16,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,

    localparam int NUM_IDS      = 1 << AXI_ID_WIDTH,
    localparam int RASM_POOL_DEPTH = RASM_MAX_OUTSTANDING * RASM_DEPTH,
    localparam int RASM_PTRW    = $clog2(RASM_POOL_DEPTH),
    localparam int RASM_CNTW    = $clog2(RASM_DEPTH + 1),

    // Skid buffer packed widths
    localparam int AR_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + AXI_USER_WIDTH,
    localparam int R_WIDTH  = S_AXI_DATA_WIDTH + 2 + AXI_USER_WIDTH + 1 + AXI_ID_WIDTH
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI Read Interface
    //==========================================================================

    // Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    // Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [S_AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    //==========================================================================
    // Master AXI Read Interface
    //==========================================================================

    // Read Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arlock,
    output logic [3:0]                  m_axi_arcache,
    output logic [2:0]                  m_axi_arprot,
    output logic [3:0]                  m_axi_arqos,
    output logic [3:0]                  m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_aruser,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // Read Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_rid,
    input  logic [M_AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready
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
`ifndef FORMAL
        // The 256-beat AXI4 bound is a configuration invariant for real
        // instances.  Formal wrappers bound the reassembly pool far smaller
        // (RASM_DEPTH/RASM_MAX_OUTSTANDING overrides) to keep the proof
        // state space practical; the logic proven is identical.
        if (RASM_DEPTH < 256)
            $error("RASM_DEPTH must cover the 256-beat AXI4 maximum");
`endif
    end

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // AR channel skid buffer signals
    logic [AR_WIDTH-1:0]         int_ar_data;
    logic                        int_ar_valid;
    logic                        int_ar_ready;

    logic [AXI_ID_WIDTH-1:0]     int_arid;
    logic [AXI_ADDR_WIDTH-1:0]   int_araddr;
    logic [7:0]                  int_arlen;
    logic [2:0]                  int_arsize;
    logic [1:0]                  int_arburst;
    logic                        int_arlock;
    logic [3:0]                  int_arcache;
    logic [2:0]                  int_arprot;
    logic [3:0]                  int_arqos;
    logic [3:0]                  int_arregion;
    logic [AXI_USER_WIDTH-1:0]   int_aruser;

    // R channel skid buffer signals
    logic [R_WIDTH-1:0]          int_r_data;
    logic                        int_r_valid;
    logic                        int_r_ready;

    logic [AXI_ID_WIDTH-1:0]     int_rid;
    logic [S_AXI_DATA_WIDTH-1:0] int_rdata;
    logic [1:0]                  int_rresp;
    logic                        int_rlast;
    logic [AXI_USER_WIDTH-1:0]   int_ruser;

    // Per-ID reassembly records (driven in AR generate blocks, consumed in
    // the reassembly scheduler).  One slot per ID is enough because master
    // AR issue for an ID is blocked while its previous burst is outstanding.
    logic                        rasm_rec_valid [NUM_IDS];
    // rasm_rec_valid is written ONLY by the reassembly block below (single
    // driver — yosys/smt2 rejects the two-process write that simulation
    // tolerates); the AR blocks drive w_rasm_push and own the other fields.
    logic                        w_rasm_push;
    logic [AXI_ID_WIDTH-1:0]     w_rasm_push_id;
    // DOWNSIZE fields
    logic                        rasm_rec_final [NUM_IDS];
    logic [8:0]                  rasm_rec_beats [NUM_IDS];
    // UPSIZE fields
    logic [7:0]                  rasm_rec_nlen  [NUM_IDS];
    logic [$clog2(WIDTH_RATIO)-1:0] rasm_rec_lane [NUM_IDS];

    // Burst-length FIFO handshake (used only in UPSIZE mode).  Replaced by
    // the per-ID record above; the shared wires remain for gen_r_upsize.
    logic                        w_blen_wr_ready;
    logic                        w_blen_rd_valid;
    logic [7:0]                  w_blen_rd_data;
    logic [7:0]                  w_blen_rd_lane;
    logic                        w_blen_pop;

    // Split-flag pop (used only in DOWNSIZE mode).  Replaced by the per-ID
    // record above; the shared wire remains for gen_r_downsize.
    logic                        arsplit_final;
    logic                        arsplit_pop;

    // Primitive-side R interface (output of reassembly scheduler).
    logic [AXI_ID_WIDTH-1:0]     prim_rid;
    logic [M_AXI_DATA_WIDTH-1:0] prim_rdata;
    logic [1:0]                  prim_rresp;
    logic                        prim_rlast;
    logic [AXI_USER_WIDTH-1:0]   prim_ruser;
    logic                        prim_rvalid;
    logic                        prim_rready;

    //==========================================================================
    // AR Channel Skid Buffer (Timing Closure)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(AR_WIDTH)
    ) ar_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (s_axi_arvalid),
        .wr_ready   (s_axi_arready),
        .wr_data    ({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize,
                      s_axi_arburst, s_axi_arlock, s_axi_arcache, s_axi_arprot,
                      s_axi_arqos, s_axi_arregion, s_axi_aruser}),
        .rd_valid   (int_ar_valid),
        .rd_ready   (int_ar_ready),
        .rd_data    (int_ar_data),
        .count      (),
        .rd_count   ()
    );

    // Unpack AR skid buffer output
    assign {int_arid, int_araddr, int_arlen, int_arsize, int_arburst,
            int_arlock, int_arcache, int_arprot, int_arqos, int_arregion,
            int_aruser} = int_ar_data;

    //==========================================================================
    // R Channel Skid Buffer (Timing Closure - Reverse Direction)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(R_WIDTH)
    ) r_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (int_r_valid),
        .wr_ready   (int_r_ready),
        .wr_data    (int_r_data),
        .rd_valid   (s_axi_rvalid),
        .rd_ready   (s_axi_rready),
        .rd_data    ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser}),
        .count      (),
        .rd_count   ()
    );

    // Pack R channel for skid buffer input
    assign int_r_data = {int_rid, int_rdata, int_rresp, int_rlast, int_ruser};

    //==========================================================================
    // Read Address Channel Conversion (arlen/arsize rewrite)
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_ar_downsize
            // Downsize: slave (wide) → master (narrow). One wide beat
            // becomes WIDTH_RATIO narrow beats, and the product does not
            // fit a burst: a full-length slave burst needs up to
            // 256*WIDTH_RATIO narrow beats, which is neither expressible
            // in the 8-bit ARLEN nor a legal AXI4 burst. The old
            // ((arlen+1)*RATIO)-1 wrapped -- 511 truncated to 255 and
            // half the read went missing (same defect the write
            // converter had; see its gen_aw_downsize).
            //
            // So one slave burst is SPLIT into as many master bursts of
            // <= 256 beats as it takes. WRAP never gets here: AXI4 caps
            // it at 16 beats, and 16*RATIO <= 256 for every supported
            // ratio.
            //
            // BUG-009: each issued master AR pushes its {final, beats}
            // record into a per-ID slot.  Master AR issue for an ID is
            // blocked while that slot is occupied, so split master bursts
            // of the same slave burst serialize in reassembly.  This
            // matches the per-ID reservation design and is deadlock-free
            // by construction.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int MAX_BEATS   = 256;
            localparam int CNTW        = 9 + $clog2(WIDTH_RATIO);

            logic [CNTW-1:0]           r_split_remaining;
            logic [AXI_ADDR_WIDTH-1:0] r_split_addr;
            logic                      r_split_active;
            logic [8:0]                w_this_beats;
            logic                      w_this_last;
            logic                      w_ar_issue;
            logic                      w_id_free;

            assign w_this_beats = (r_split_remaining > CNTW'(MAX_BEATS))
                                  ? 9'(MAX_BEATS) : 9'(r_split_remaining);
            assign w_this_last  = (r_split_remaining <= CNTW'(MAX_BEATS));
            assign w_ar_issue   = m_axi_arvalid && m_axi_arready;
            assign w_id_free    = !rasm_rec_valid[int_arid];

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_split_remaining <= '0;
                    r_split_addr      <= '0;
                    r_split_active    <= 1'b0;
                end else if (!r_split_active) begin
                    if (int_ar_valid) begin
                        r_split_remaining <= (CNTW'(int_arlen) + CNTW'(1))
                                             * CNTW'(WIDTH_RATIO);
                        r_split_addr      <= int_araddr;
                        r_split_active    <= 1'b1;
                    end
                end else if (w_ar_issue) begin
                    if (w_this_last) begin
                        r_split_remaining <= '0;
                        r_split_active    <= 1'b0;
                    end else begin
                        r_split_remaining <= r_split_remaining
                                             - CNTW'(MAX_BEATS);
                        // FIXED holds the address; INCR walks on. WRAP
                        // cannot reach a split (see above).
                        if (int_arburst != 2'b00)
                            r_split_addr <= r_split_addr
                                + AXI_ADDR_WIDTH'(MAX_BEATS * M_STRB_WIDTH);
                    end
                end
            )

            assign m_axi_arid     = int_arid;
            assign m_axi_araddr   = r_split_addr;
            assign m_axi_arlen    = 8'(w_this_beats - 9'd1);
            assign m_axi_arsize   = MASTER_SIZE[2:0];
            assign m_axi_arburst  = int_arburst;
            assign m_axi_arlock   = int_arlock;
            assign m_axi_arcache  = int_arcache;
            assign m_axi_arprot   = int_arprot;
            assign m_axi_arqos    = int_arqos;
            assign m_axi_arregion = int_arregion;
            assign m_axi_aruser   = int_aruser;
            // Issue the next split only when the per-ID reassembly slot is free.
            assign m_axi_arvalid  = r_split_active && w_id_free;
            // the slave's AR is consumed only when its FINAL master
            // burst is issued
            assign int_ar_ready   = w_ar_issue && w_this_last;

            // Push the per-ID record on every accepted master AR.  The
            // reassembly block owns rasm_rec_valid (single driver); this
            // block owns the payload fields.
            assign w_rasm_push    = w_ar_issue;
            assign w_rasm_push_id = int_arid;
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    for (int i = 0; i < NUM_IDS; i++) begin
                        rasm_rec_final[i] <= 1'b0;
                        rasm_rec_beats[i] <= '0;
                    end
                end else if (w_ar_issue) begin
                    rasm_rec_final[int_arid] <= w_this_last;
                    rasm_rec_beats[int_arid] <= w_this_beats;
                end
            )

        end else begin : gen_ar_upsize
            // Upsize: slave (narrow) → master (wide). Divide burst length
            // by ratio (round up) and align address down to wide boundary.
            // Division can never overflow ARLEN; the split queue is inert.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int ALIGN_BITS  = $clog2(M_STRB_WIDTH);
            localparam int R_LANE_W    = $clog2(WIDTH_RATIO);

            assign arsplit_final = 1'b1;

            logic [7:0] master_arlen;
            logic [AXI_ADDR_WIDTH-1:0] aligned_araddr;

            // Narrow-lane offset of the burst start inside the wide word.
            // The issued address stays aligned DOWN (the slave returns
            // whole wide words); the R slicer starts at this lane for the
            // burst's first wide word, so the master gets the bytes it
            // actually addressed (mid-word burst starts, projects/components/utility-ip/converters TASK-001 (was CONV-006)).
            logic [R_LANE_W-1:0] w_ar_lane;
            assign w_ar_lane = R_LANE_W'(int_araddr[ALIGN_BITS-1:0] >> $clog2(S_STRB_WIDTH));
            // Wide beats = ceil((lane + narrow_beats) / RATIO); 10-bit
            // intermediate so lane + 255 + RATIO cannot wrap.
            assign master_arlen   = 8'(((10'(w_ar_lane) + 10'(int_arlen) + 10'(WIDTH_RATIO))
                                        / 10'(WIDTH_RATIO)) - 10'd1);
            assign aligned_araddr = {int_araddr[AXI_ADDR_WIDTH-1:ALIGN_BITS], {ALIGN_BITS{1'b0}}};

            assign m_axi_arid     = int_arid;
            assign m_axi_araddr   = aligned_araddr;
            assign m_axi_arlen    = master_arlen;
            assign m_axi_arsize   = MASTER_SIZE[2:0];
            assign m_axi_arburst  = int_arburst;
            assign m_axi_arlock   = int_arlock;
            assign m_axi_arcache  = int_arcache;
            assign m_axi_arprot   = int_arprot;
            assign m_axi_arqos    = int_arqos;
            assign m_axi_arregion = int_arregion;
            assign m_axi_aruser   = int_aruser;
            // Gate AR on the per-ID reassembly slot.
            assign m_axi_arvalid  = int_ar_valid && !rasm_rec_valid[int_arid];
            assign int_ar_ready   = m_axi_arready && !rasm_rec_valid[int_arid];

            // Push the per-ID record on every accepted master AR.
            // rasm_rec_beats holds the number of master wide beats for the
            // reassembly scheduler; rasm_rec_nlen is the narrow length that
            // the dnsize uses to frame its output.  The reassembly block
            // owns rasm_rec_valid (single driver); this block owns these
            // payload fields.
            assign w_rasm_push    = int_ar_valid && int_ar_ready;
            assign w_rasm_push_id = int_arid;
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    for (int i = 0; i < NUM_IDS; i++) begin
                        rasm_rec_beats[i] <= '0;
                        rasm_rec_nlen[i]  <= '0;
                        rasm_rec_lane[i]  <= '0;
                    end
                end else if (int_ar_valid && int_ar_ready) begin
                    rasm_rec_beats[int_arid] <= 9'(master_arlen) + 9'd1;
                    rasm_rec_nlen[int_arid]  <= int_arlen;
                    rasm_rec_lane[int_arid]  <= w_ar_lane;
                end
            )

`ifdef SIMULATION
            // Mid-word starts are supported for INCR (the slicer starts at
            // the addressed lane). FIXED/WRAP keep the wide-aligned
            // requirement -- their lane semantics through the slicer are
            // not defined here.
            always_ff @(posedge aclk) begin
                if (aresetn && int_ar_valid && int_ar_ready &&
                    (int_arburst != 2'b01) &&
                    (int_araddr[ALIGN_BITS-1:0] != '0)) begin
                    $error("axi4_dwidth_converter_rd: upsize %s AR addr 0x%h is not aligned to the %0d-byte wide bus",
                           (int_arburst == 2'b00) ? "FIXED" : "WRAP",
                           int_araddr, M_STRB_WIDTH);
                end
            end
`endif
        end
    endgenerate

    //==========================================================================
    // BUG-009: Per-ID R Reassembly Layer
    //
    //   Master R beats may arrive interleaved across ARIDs.  This layer
    //   demuxes them into per-ID queues backed by a shared beat pool,
    //   detects when a full master burst has arrived, and feeds each
    //   assembled burst contiguously into axi_data_upsize / axi_data_dnsize.
    //   Because the primitive only ever sees one burst at a time, the
    //   existing "most recent rid/ruser" carry remains exact.
    //
    //   Reservation rule: one unassembled master burst per ID.  The AR
    //   generate blocks throttle issue when rasm_rec_valid[id] is set, so
    //   the shared pool need only hold RASM_MAX_OUTSTANDING full bursts.
    //==========================================================================

    // Shared beat pool memories.
    logic [M_AXI_DATA_WIDTH-1:0] rasm_pool_data [RASM_POOL_DEPTH];
    logic [1:0]                  rasm_pool_resp [RASM_POOL_DEPTH];
    logic                        rasm_pool_last [RASM_POOL_DEPTH];
    logic [RASM_PTRW-1:0]        rasm_pool_next [RASM_POOL_DEPTH];

    // Free list.
    logic [RASM_PTRW-1:0]        rasm_free_head;
    logic [RASM_PTRW:0]          rasm_free_count;

    // Per-ID queue state.
    logic [RASM_PTRW-1:0]        rasm_head    [NUM_IDS];
    logic [RASM_PTRW-1:0]        rasm_tail    [NUM_IDS];
    logic [RASM_CNTW-1:0]        rasm_count   [NUM_IDS];
    logic                        rasm_assembled [NUM_IDS];
    logic [AXI_USER_WIDTH-1:0]   rasm_ruser   [NUM_IDS];

    // Scheduler state.
    logic [AXI_ID_WIDTH-1:0]     rasm_sched_ptr;
    logic [AXI_ID_WIDTH-1:0]     rasm_feed_id;
    logic                        rasm_feed_active;

    // Output tracking: holds the ID of the burst whose converted beats are
    // currently emerging from the primitive.  Loaded at the first output beat
    // from the ID being fed, so it remains stable for the entire output burst
    // even if the scheduler moves on to the next burst.
    logic [AXI_ID_WIDTH-1:0]     rasm_out_id;
    logic                        rasm_out_active;

    // Upsize burst-start pulse: asserted from scheduler selection until the
    // first wide beat of the burst is accepted by the dnsize primitive.  This
    // gives a clean pulse for axi_data_dnsize's burst_start input and avoids
    // the boundary race where rasm_feed_active clears on int_rlast in the same
    // cycle r_burst_active goes low.
    logic                        rasm_bstart_pending;

    // Combinational: can we accept a beat for this ID?
    logic w_id_has_room;
    assign w_id_has_room = (rasm_count[m_axi_rid] < RASM_CNTW'(RASM_DEPTH))
                           && (rasm_free_count > '0);

    // m_axi_rready is low only when the arriving ID's queue is full.
    // Cannot happen for legal traffic under the reservation rule.
    assign m_axi_rready = m_axi_rvalid && w_id_has_room;

    // Push logic: allocate from the free list and append to the ID's queue.
    logic [RASM_PTRW-1:0] w_alloc_ptr;
    logic [RASM_PTRW-1:0] w_feed_next;
    logic                 w_push;
    logic                 w_pop;
    logic [RASM_PTRW-1:0] w_old_free_head;
    logic [RASM_PTRW-1:0] w_old_free_next;
    // Scheduler / feed pointers (declared before the reassembly block that
    // consumes them — house declaration-order rule).
    logic [AXI_ID_WIDTH-1:0] w_sched_pick;
    logic                    w_sched_found;
    logic [RASM_PTRW-1:0]    w_feed_ptr;

    assign w_alloc_ptr     = rasm_free_head;
    assign w_feed_next     = rasm_pool_next[w_feed_ptr];
    assign w_push          = m_axi_rvalid && m_axi_rready;
    assign w_pop           = rasm_feed_active && prim_rready;
    assign w_old_free_head = rasm_free_head;
    assign w_old_free_next = rasm_pool_next[rasm_free_head];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            rasm_free_head <= '0;
            rasm_free_count <= (RASM_PTRW+1)'(RASM_POOL_DEPTH);
            for (int i = 0; i < RASM_POOL_DEPTH; i++) begin
                rasm_pool_next[i] <= RASM_PTRW'(i + 1);
            end
            // rasm_rec_valid is owned here (single driver); the AR generate
            // blocks drive w_rasm_push and the payload fields.
            for (int i = 0; i < NUM_IDS; i++) begin
                rasm_rec_valid[i] <= 1'b0;
            end
            for (int i = 0; i < NUM_IDS; i++) begin
                rasm_head[i]      <= '0;
                rasm_tail[i]      <= '0;
                rasm_count[i]     <= '0;
                rasm_assembled[i] <= 1'b0;
                rasm_ruser[i]     <= '0;
            end
            rasm_sched_ptr      <= '0;
            rasm_feed_active    <= 1'b0;
            rasm_feed_id        <= '0;
            rasm_out_active     <= 1'b0;
            rasm_out_id         <= '0;
            rasm_bstart_pending <= 1'b0;
        end else begin
            // AR record push: set the valid bit for the ID whose record the
            // AR generate block just wrote (payload fields live there).
            if (w_rasm_push)
                rasm_rec_valid[w_rasm_push_id] <= 1'b1;

            // Free-list maintenance: must be atomic with respect to simultaneous
            // push and pop.  The old code had two NBAs to rasm_free_head, so a
            // push+pop cycle lost the node after the allocated head and silently
            // corrupted per-ID queues.
            if (w_push || w_pop) begin
                if (w_push && w_pop) begin
                    // Allocate old head, return fed node to the head of the free
                    // list; the node after the old head becomes the fed node's next.
                    rasm_free_head             <= w_feed_ptr;
                    rasm_pool_next[w_feed_ptr] <= w_old_free_next;
                end else if (w_push) begin
                    rasm_free_head <= w_old_free_next;
                end else begin
                    rasm_free_head             <= w_feed_ptr;
                    rasm_pool_next[w_feed_ptr] <= w_old_free_head;
                end
                rasm_free_count <= rasm_free_count + (RASM_PTRW+1)'(w_pop ? 1 : 0)
                                                - (RASM_PTRW+1)'(w_push ? 1 : 0);
            end

            // Push arriving beat into the per-ID queue.
            if (w_push) begin
                // Store the beat.
                rasm_pool_data[w_alloc_ptr] <= m_axi_rdata;
                rasm_pool_resp[w_alloc_ptr] <= m_axi_rresp;
                rasm_pool_last[w_alloc_ptr] <= m_axi_rlast;
                rasm_pool_next[w_alloc_ptr] <= '0;  // becomes new tail

                // Link into the per-ID list.
                if (rasm_count[m_axi_rid] == '0) begin
                    rasm_head[m_axi_rid] <= w_alloc_ptr;
                end else begin
                    rasm_pool_next[rasm_tail[m_axi_rid]] <= w_alloc_ptr;
                end
                rasm_tail[m_axi_rid]  <= w_alloc_ptr;
                rasm_count[m_axi_rid] <= rasm_count[m_axi_rid] + RASM_CNTW'(1);

                // Capture RUSER on the first beat of each burst (pre-push
                // count is zero on beat #1; single-beat bursts must update
                // it too, else they present the previous burst's value).
                if (rasm_count[m_axi_rid] == '0)
                    rasm_ruser[m_axi_rid] <= m_axi_ruser;
            end

            // Assembly detection: a burst is assembled when its beat count
            // matches the per-ID record and the arrived beat carries RLAST.
            // rasm_rec_beats stores master-beat count in both directions
            // (narrow beats for downsize, wide beats for upsize).
            if (w_push) begin
                if (rasm_rec_valid[m_axi_rid]) begin
                    if ((rasm_count[m_axi_rid] + RASM_CNTW'(1) == RASM_CNTW'(rasm_rec_beats[m_axi_rid]))
                        && m_axi_rlast) begin
                        rasm_assembled[m_axi_rid] <= 1'b1;
                    end
                end
            end

            // Advance the feed pointer and free consumed beats.
            if (w_pop) begin
                rasm_count[rasm_feed_id]   <= rasm_count[rasm_feed_id] - RASM_CNTW'(1);
                rasm_head[rasm_feed_id]    <= w_feed_next;

                if (prim_rlast) begin
                    // End of this master burst feeding: release the primitive
                    // input side.  The per-ID reservation clears here for
                    // downsize so the next split of the same slave AR can
                    // issue; for upsize it stays until int_rlast to keep the
                    // output RID exact and to hold burst_start valid.
                    rasm_assembled[rasm_feed_id] <= 1'b0;
                    rasm_bstart_pending          <= 1'b0;
                    if (DOWNSIZE) begin
                        rasm_feed_active             <= 1'b0;
                        rasm_rec_valid[rasm_feed_id] <= 1'b0;
                    end
                end
            end

            // Track which burst is currently emerging from the primitive.
            // Load the output ID when feeding starts while no output is active;
            // this is before the first output beat so int_rid is exact from the
            // first beat.  rasm_out_active follows int_r_valid to mark the
            // output window.
            if (!rasm_out_active && rasm_feed_active) begin
                rasm_out_active <= 1'b1;
                rasm_out_id     <= rasm_feed_id;
            end
            if (int_r_valid && int_r_ready && int_rlast)
                rasm_out_active <= 1'b0;

            // Upsize only: release the feed side and per-ID reassembly record
            // when the converted slave R burst completes.
            if (!DOWNSIZE && int_r_valid && int_r_ready && int_rlast) begin
                rasm_feed_active            <= 1'b0;
                rasm_rec_valid[rasm_feed_id] <= 1'b0;
            end

            // Clear the upsize burst-start pulse once the first wide beat of
            // the burst has been accepted by the primitive.
            if (rasm_feed_active && prim_rready && rasm_bstart_pending)
                rasm_bstart_pending <= 1'b0;

            // Start feeding a newly assembled burst when idle.  For downsize
            // a slave burst spans multiple master splits, so keep feeding the
            // same output ID until int_rlast completes that slave burst;
            // otherwise another ID's split would corrupt the contiguous
            // upsize accumulation.
            if (!rasm_feed_active && w_sched_found) begin
                if (!DOWNSIZE || !rasm_out_active || (w_sched_pick == rasm_out_id)) begin
                    rasm_feed_active    <= 1'b1;
                    rasm_feed_id        <= w_sched_pick;
                    rasm_sched_ptr      <= w_sched_pick + AXI_ID_WIDTH'(1);
                    rasm_bstart_pending <= !DOWNSIZE;
                end
            end
        end
    )

    // Scheduler: round-robin over IDs, select one with an assembled burst.
    always_comb begin
        w_sched_found = 1'b0;
        w_sched_pick  = rasm_sched_ptr;
        for (int i = 0; i < NUM_IDS; i++) begin
            automatic int raw_idx = int'(rasm_sched_ptr) + i;
            automatic int idx     = raw_idx % NUM_IDS;
            if (!w_sched_found && rasm_assembled[idx]) begin
                w_sched_found = 1'b1;
                w_sched_pick  = AXI_ID_WIDTH'(idx);
            end
        end
    end

    // Feed logic: drive the primitive from the head of the selected ID's queue.
    assign w_feed_ptr = rasm_head[rasm_feed_id];

    assign prim_rvalid = rasm_feed_active;
    assign prim_rdata  = rasm_pool_data[w_feed_ptr];
    assign prim_rresp  = rasm_pool_resp[w_feed_ptr];
    assign prim_rlast  = rasm_pool_last[w_feed_ptr];
    assign prim_rid    = rasm_feed_id;
    assign prim_ruser  = rasm_ruser[rasm_feed_id];

`ifdef SIMULATION
    // Protocol checks: flag violations without deadlocking.
    always_ff @(posedge aclk) begin
        if (aresetn && m_axi_rvalid && m_axi_rready) begin
            automatic int idv = int'(m_axi_rid);
            if (!rasm_rec_valid[idv]) begin
                $error("axi4_dwidth_converter_rd: R beat for ID %0d with no outstanding AR record", idv);
            end
            if (rasm_count[idv] >= RASM_CNTW'(RASM_DEPTH)) begin
                $error("axi4_dwidth_converter_rd: ID %0d reassembly queue overflow", idv);
            end
            if (rasm_count[idv] + RASM_CNTW'(1) > RASM_CNTW'(rasm_rec_beats[idv])) begin
                $error("axi4_dwidth_converter_rd: ID %0d received more R beats than AR promised", idv);
            end
            if ((rasm_count[idv] + RASM_CNTW'(1) < RASM_CNTW'(rasm_rec_beats[idv])) && m_axi_rlast) begin
                $error("axi4_dwidth_converter_rd: ID %0d unexpected RLAST (beat %0d of %0d)",
                       idv, rasm_count[idv] + RASM_CNTW'(1), rasm_rec_beats[idv]);
            end
        end
    end
`endif

    //==========================================================================
    // R Channel ID / USER Carry
    //
    //   The validated axi_data_{upsize,dnsize} primitives handle the data
    //   payload, RRESP sideband, and LAST signalling. They do NOT carry
    //   AXI4 transaction id (rid) or the optional ruser sideband, so we
    //   register them on every *primitive* R handshake.  Because the
    //   reassembly layer feeds one contiguous burst at a time, "most recent"
    //   is exact even when master R beats arrived interleaved across IDs.
    //==========================================================================

    // rasm_out_id is loaded when feeding starts while no output is active,
    // so it is stable before the first output beat of each burst and is
    // therefore exact for both upsize and downsize.
    assign int_rid   = rasm_out_id;
    assign int_ruser = rasm_ruser[rasm_out_id];

    //==========================================================================
    // R Channel Data Conversion (delegates to validated primitives)
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_r_downsize
            // Slave wide, master narrow. R direction: master → slave, so
            // narrow → wide. Use axi_data_upsize. RRESP errors must
            // propagate across all sub-beats: SB_OR_MODE=1.
            //
            // The primitive now sees contiguous master bursts from the
            // reassembly scheduler. narrow_last is gated by the per-ID
            // record's final flag so only the last split of a slave burst
            // terminates the upsize accumulation.
            assign arsplit_final = rasm_rec_final[rasm_feed_id];
            assign arsplit_pop   = rasm_feed_active && prim_rready && prim_rlast
                                   && rasm_rec_final[rasm_feed_id];

            axi_data_upsize #(
                .NARROW_WIDTH    (M_AXI_DATA_WIDTH),
                .WIDE_WIDTH      (S_AXI_DATA_WIDTH),
                .NARROW_SB_WIDTH (2),
                .WIDE_SB_WIDTH   (2),
                .SB_OR_MODE      (1)
            ) u_r_upsize (
                .aclk            (aclk),
                .aresetn         (aresetn),
                .narrow_valid    (prim_rvalid),
                .narrow_ready    (prim_rready),
                .narrow_data     (prim_rdata),
                .narrow_sideband (prim_rresp),
                .narrow_last     (prim_rlast && arsplit_final),
                .start_lane      ('0),  // narrow master fetches from the exact addresses
                .wide_valid      (int_r_valid),
                .wide_ready      (int_r_ready),
                .wide_data       (int_rdata),
                .wide_sideband   (int_rresp),
                .wide_last       (int_rlast)
            );

            // No burst-length FIFO needed on the narrow->wide (upsize) data
            // path; keep the shared handshake wires inert.
            assign w_blen_wr_ready = 1'b1;
            assign w_blen_rd_valid = 1'b0;
            assign w_blen_rd_data  = '0;
            assign w_blen_rd_lane  = '0;

        end else begin : gen_r_upsize
            assign arsplit_pop = 1'b0;
            // Slave narrow, master wide. R direction: master → slave, so
            // wide → narrow. axi_data_dnsize (TRACK_BURSTS=1) asserts
            // narrow_last on the last narrow beat of each burst, using that
            // burst's ORIGINAL (pre-rewrite) narrow length.
            //
            // With reassembly, the scheduler feeds one assembled wide burst
            // at a time.  The per-ID record supplies burst_len/start_lane;
            // burst_start is held while the scheduler is feeding.
            localparam int BLEN_FIFO_DEPTH = 16;
            localparam int BLEN_AW         = $clog2(BLEN_FIFO_DEPTH);
            localparam int R_LANE_W        = $clog2(WIDTH_RATIO);

            // Burst-length FIFO is no longer used; the per-ID record carries
            // the framing.  Keep w_blen_wr_ready tied high so the AR block
            // does not stall, and drive the read-side signals from the burst
            // currently being fed.  burst_start is a single-cycle pulse at the
            // first accepted wide beat so axi_data_dnsize opens the burst
            // cleanly without a boundary race between rasm_feed_active and
            // the primitive's internal r_burst_active flag.
            assign w_blen_wr_ready = 1'b1;
            assign w_blen_rd_valid = rasm_bstart_pending;
            assign w_blen_rd_data  = rasm_rec_nlen[rasm_feed_id];
            assign w_blen_rd_lane  = 8'(rasm_rec_lane[rasm_feed_id]);

            // Burst record pop: the per-ID slot is already cleared by the
            // reassembly scheduler when the fed last beat is consumed, but
            // keep a legacy pulse for documentation.
            assign w_blen_pop = rasm_feed_active && prim_rready && prim_rlast;

            axi_data_dnsize #(
                .WIDE_WIDTH       (M_AXI_DATA_WIDTH),
                .NARROW_WIDTH     (S_AXI_DATA_WIDTH),
                .WIDE_SB_WIDTH    (2),
                .NARROW_SB_WIDTH  (2),
                .SB_BROADCAST     (1),
                .TRACK_BURSTS     (1),
                .BURST_LEN_WIDTH  (8)
            ) u_r_dnsize (
                .aclk            (aclk),
                .aresetn         (aresetn),
                .burst_len       (w_blen_rd_data),
                .burst_start     (w_blen_rd_valid),
                .start_lane      (w_blen_rd_lane[$clog2(WIDTH_RATIO)-1:0]),
                .wide_valid      (prim_rvalid),
                .wide_ready      (prim_rready),
                .wide_data       (prim_rdata),
                .wide_sideband   (prim_rresp),
                .wide_last       (prim_rlast),
                .narrow_valid    (int_r_valid),
                .narrow_ready    (int_r_ready),
                .narrow_data     (int_rdata),
                .narrow_sideband (int_rresp),
                .narrow_last     (int_rlast)
            );
        end
    endgenerate

endmodule : axi4_dwidth_converter_rd
