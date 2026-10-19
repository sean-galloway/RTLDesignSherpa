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
//   directory (each with its own pytest suite) when R bursts arrive
//   contiguously (R_INTERLEAVE = 0).  With R_INTERLEAVE = 1 the wrapper
//   converts each beat against its own ID's state instead (gen_rilv).
//   Either way it owns the AR/R skid buffers, the AR arlen/arsize
//   rewrite, the per-ID AR records and the rid/ruser carry.
//
//   R interleave (2026-10-18): AXI4 permits a slave to interleave R beats
//   across ARIDs.  Downsize keeps each ID's partial wide beat in
//   distributed RAM indexed by ID; upsize holds one wide beat and keeps
//   each ID's remaining narrow-beat count.  Nothing buffers a whole burst.
//   Each ID has at most one master burst outstanding: master AR issue for
//   an ID waits until its previous burst has arrived.  Same-ID read chains
//   serialize on that; cross-ID traffic is concurrent and may interleave
//   arbitrarily on m_axi R.  This replaced the BUG-009 shared beat pool
//   (2026-10-04), which stored whole bursts first.
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
//   RASM_DEPTH, RASM_MAX_OUTSTANDING: unused, kept so existing instances
//     still elaborate (they sized the retired beat pool).
//   R_INTERLEAVE: 1 (default) = the m_axi R source may interleave beats of
//     different ARIDs; each beat is converted per ID as it arrives.  0 =
//     the source promises every R burst arrives contiguously (bursts of
//     different IDs may still return in any order); beats go straight to
//     the data primitive, with RID/RUSER carried through its sideband.
//     The bridge builds every read converter with 1: its slaves may
//     interleave R (bridge PRD FR-9).
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

    // Unused: they sized the retired BUG-009 beat pool. Kept so existing
    // instances that set them still elaborate.
    parameter int RASM_DEPTH             = 272,
    parameter int RASM_MAX_OUTSTANDING   = 16,

    // R_INTERLEAVE = 1: R may interleave across IDs, converted per ID as
    // it arrives. 0: contiguous R bursts only (see the header).
    parameter bit R_INTERLEAVE           = 1'b1,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,

    localparam int NUM_IDS      = 1 << AXI_ID_WIDTH,
    // Primitive sideband (R_INTERLEAVE = 0, the only mode that builds the
    // primitives): {RRESP, RID, RUSER}, so every converted beat carries its
    // own burst's ID; 2 bits otherwise, tied off.  RRESP is the MSB field: the upsize
    // primitive folds by numeric max, which then keeps the worst response.
    localparam int PSB_W        = R_INTERLEAVE ? 2 : (2 + AXI_ID_WIDTH + AXI_USER_WIDTH),

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

    // Per-ID AR records (driven in the AR generate blocks, consumed by the
    // R front end, gen_rilv or gen_rbypass).  One slot per ID is enough
    // because master AR issue for an ID is blocked while its previous burst
    // is outstanding.
    logic                        rasm_rec_valid [NUM_IDS];
    // rasm_rec_valid is written ONLY by the R front end below (single
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

    // Primitive-side R interface (R_INTERLEAVE = 0: the registered R input).
    logic [AXI_ID_WIDTH-1:0]     prim_rid;
    logic [M_AXI_DATA_WIDTH-1:0] prim_rdata;
    logic [1:0]                  prim_rresp;
    logic                        prim_rlast;
    logic [AXI_USER_WIDTH-1:0]   prim_ruser;
    logic                        prim_rvalid;
    logic                        prim_rready;

    // Mode interface: what the R primitives need from whichever R-side
    // front end is built (gen_rbypass below; gen_rilv ties them off).
    logic                        w_cur_final;   // DOWNSIZE: this master burst ends its slave burst
    logic                        w_bstart;      // UPSIZE: first wide beat of a burst is presented
    logic [7:0]                  w_blen;        // UPSIZE: that burst's narrow ARLEN
    logic [7:0]                  w_blane;       // UPSIZE: its start lane
    logic [PSB_W-1:0]            prim_sb;
    logic [PSB_W-1:0]            int_sb;

    //==========================================================================
    // AR Channel Skid Buffer (Timing Closure)
    //==========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(AR_WIDTH)
    ) ar_skid (
        .axi_aclk   (aclk),
        .axi_aresetn(w_aresetn),
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
        .axi_aresetn(w_aresetn),
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
            // Each issued master AR pushes its {final, beats} record into
            // a per-ID slot.  Master AR issue for an ID is blocked while
            // that slot is occupied, so the split master bursts of one
            // slave burst go out one after another, each once the previous
            // has arrived.
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

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
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
            // Issue the next split only when the per-ID slot is free.
            assign m_axi_arvalid  = r_split_active && w_id_free;
            // the slave's AR is consumed only when its FINAL master
            // burst is issued
            assign int_ar_ready   = w_ar_issue && w_this_last;

            // Push the per-ID record on every accepted master AR.  The R
            // front end owns rasm_rec_valid (single driver); this block
            // owns the payload fields.
            assign w_rasm_push    = w_ar_issue;
            assign w_rasm_push_id = int_arid;
            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
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
            // Gate AR on the per-ID slot.
            assign m_axi_arvalid  = int_ar_valid && !rasm_rec_valid[int_arid];
            assign int_ar_ready   = m_axi_arready && !rasm_rec_valid[int_arid];

            // Push the per-ID record on every accepted master AR.
            // rasm_rec_beats holds the number of master wide beats;
            // rasm_rec_nlen is the narrow length that frames the output.
            // The R front end owns rasm_rec_valid (single driver); this
            // block owns these payload fields.
            assign w_rasm_push    = int_ar_valid && int_ar_ready;
            assign w_rasm_push_id = int_arid;
            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
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
                if (w_aresetn && int_ar_valid && int_ar_ready &&
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
    // R Interleave (R_INTERLEAVE = 1): per-ID conversion, no reassembly pool
    //
    //   AXI4 lets the m_axi R source interleave beats of different ARIDs
    //   (beats of one ID stay in order). Each beat is converted against its
    //   own ID's state as it arrives, so nothing waits for a whole burst:
    //
    //   DOWNSIZE (narrow m_axi beats folded into wide s_axi beats): each ID
    //     keeps the lanes of its partial wide beat (RATIO-1 narrow lanes, in
    //     distributed RAM indexed by ID), a lane count and the worst RRESP.
    //     The beat that fills the last lane -- or the final split's RLAST --
    //     emits the wide beat with the lanes already held.
    //   UPSIZE (wide m_axi beats sliced into narrow s_axi beats): one wide
    //     beat at a time is held and sliced lane by lane; each ID keeps its
    //     remaining narrow beats and whether its burst has started, so its
    //     next wide beat resumes at lane 0 with the right count.
    //
    //   The per-ID AR records and the one-burst-per-ID reservation are the
    //   same as in the bypass below. This replaced the BUG-009 shared beat
    //   pool (RASM_MAX_OUTSTANDING x RASM_DEPTH beats, ~128k LUTs at 16 x
    //   272 x 128 bits), which stored whole bursts before converting them;
    //   RASM_DEPTH / RASM_MAX_OUTSTANDING are kept for compatibility and
    //   unused (bridge GitHub #119 R interleave, 2026-10-18).
    //==========================================================================

    generate if (R_INTERLEAVE) begin : gen_rilv
        localparam int LW   = (WIDTH_RATIO > 1) ? $clog2(WIDTH_RATIO) : 1;
        localparam int RQ_W = AXI_ID_WIDTH + M_AXI_DATA_WIDTH + 2 + 1 + AXI_USER_WIDTH;

        // R is registered on entry, so every per-ID lookup starts from a flop.
        logic                        q_rvalid, q_rready;
        logic [AXI_ID_WIDTH-1:0]     q_rid;
        logic [M_AXI_DATA_WIDTH-1:0] q_rdata;
        logic [1:0]                  q_rresp;
        logic                        q_rlast;
        logic [AXI_USER_WIDTH-1:0]   q_ruser;
        logic [RQ_W-1:0]             q_rpkt;
        logic                        w_out_hs;

        gaxi_skid_buffer #(
            .DEPTH      (2),
            .DATA_WIDTH (RQ_W)
        ) r_in_skid (
            .axi_aclk   (aclk),
            .axi_aresetn(w_aresetn),
            .wr_valid   (m_axi_rvalid),
            .wr_ready   (m_axi_rready),
            .wr_data    ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
            .rd_valid   (q_rvalid),
            .rd_ready   (q_rready),
            .rd_data    (q_rpkt),
            .count      (),
            .rd_count   ()
        );
        assign {q_rid, q_rdata, q_rresp, q_rlast, q_ruser} = q_rpkt;
        assign w_out_hs = int_r_valid && int_r_ready;

        // The bypass's primitive-side wires are not used in this mode.
        assign prim_rvalid = 1'b0;
        assign prim_rid    = '0;
        assign prim_rdata  = '0;
        assign prim_rresp  = '0;
        assign prim_rlast  = 1'b0;
        assign prim_ruser  = '0;
        assign prim_sb     = '0;
        assign int_sb      = '0;
        assign w_cur_final = 1'b0;
        assign w_bstart    = 1'b0;
        assign w_blen      = '0;
        assign w_blane     = '0;

        if (DOWNSIZE) begin : gen_pack
            // Partial wide beat per ID: lanes 0..RATIO-2 (the last lane is
            // the arriving beat itself), one ID-indexed memory per lane.
            // Written by a reset-free process so each infers distributed
            // RAM; a lane is always written before the wide beat that reads
            // it.
            logic [M_AXI_DATA_WIDTH-1:0] w_acc_rd [WIDTH_RATIO-1];
            logic [LW-1:0]               cnt   [NUM_IDS];
            logic [1:0]                  worst [NUM_IDS];
            logic [LW-1:0]               w_lane;
            logic                        w_final, w_emit, w_take;
            logic [1:0]                  w_resp;

            assign w_lane  = cnt[q_rid];
            assign w_final = q_rlast && rasm_rec_final[q_rid];
            // The arriving beat completes a wide beat: last lane, or the end
            // of the s_axi burst.
            assign w_emit  = (w_lane == LW'(WIDTH_RATIO - 1)) || w_final;
            assign w_take  = q_rvalid && (!w_emit || int_r_ready);
            assign q_rready = !w_emit || int_r_ready;
            assign w_resp  = (q_rresp > worst[q_rid]) ? q_rresp : worst[q_rid];

            always_comb begin
                int_rdata = '0;
                for (int k = 0; k < WIDTH_RATIO; k++) begin
                    if (LW'(k) == w_lane)
                        int_rdata[k*M_AXI_DATA_WIDTH +: M_AXI_DATA_WIDTH] = q_rdata;
                    else if ((k < WIDTH_RATIO - 1) && (LW'(k) < w_lane))
                        int_rdata[k*M_AXI_DATA_WIDTH +: M_AXI_DATA_WIDTH] = w_acc_rd[k];
                end
            end
            assign int_r_valid = q_rvalid && w_emit;
            assign int_rid     = q_rid;
            assign int_rresp   = w_resp;
            assign int_rlast   = w_final;
            assign int_ruser   = q_ruser;

            for (genvar k = 0; k < WIDTH_RATIO - 1; k++) begin : gen_lane
`ifdef XILINX
                (* ram_style = "distributed" *)
`elsif SYNTH_PRAGMA
                /* synthesis ramstyle = "MLAB" */
`endif
                logic [M_AXI_DATA_WIDTH-1:0] acc [NUM_IDS];
                always_ff @(posedge aclk) begin
                    if (w_take && !w_emit && (w_lane == LW'(k)))
                        acc[q_rid] <= q_rdata;
                end
                assign w_acc_rd[k] = acc[q_rid];
            end

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    for (int i = 0; i < NUM_IDS; i++) begin
                        cnt[i]            <= '0;
                        worst[i]          <= 2'b00;
                        rasm_rec_valid[i] <= 1'b0;
                    end
                end else begin
                    if (w_take) begin
                        cnt[q_rid]   <= w_emit ? '0 : w_lane + LW'(1);
                        worst[q_rid] <= w_emit ? 2'b00 : w_resp;
                        // A master burst (one split) has fully arrived: its
                        // reservation frees and the next split may issue.
                        if (q_rlast)
                            rasm_rec_valid[q_rid] <= 1'b0;
                    end
                    if (w_rasm_push)
                        rasm_rec_valid[w_rasm_push_id] <= 1'b1;
                end
            )
        end else begin : gen_slice
            // One wide beat is held and sliced; per-ID count and started flag.
            logic                        cur_valid;
            logic [AXI_ID_WIDTH-1:0]     cur_rid;
            logic [M_AXI_DATA_WIDTH-1:0] cur_data;
            logic [1:0]                  cur_resp;
            logic [AXI_USER_WIDTH-1:0]   cur_user;
            logic [LW-1:0]               cur_lane;
            logic [8:0]                  cur_rem;      // narrow beats left in the burst
            logic [8:0]                  rem   [NUM_IDS];
            logic                        start [NUM_IDS];
            logic                        w_last_narrow, w_wide_done, w_cur_free, w_load;
            logic                        w_byp;        // the next beat continues cur's burst
            logic [LW-1:0]               w_ld_lane;
            logic [8:0]                  w_ld_rem;

            assign w_last_narrow = (cur_rem == 9'd1);
            assign w_wide_done   = w_last_narrow || (cur_lane == LW'(WIDTH_RATIO - 1));
            assign w_cur_free    = !cur_valid || (w_out_hs && w_wide_done);
            assign q_rready      = w_cur_free;
            assign w_load        = q_rvalid && w_cur_free;
            // cur finishes a wide beat of the same ID this cycle without
            // ending its burst: take its count, not the table's stale one.
            assign w_byp         = cur_valid && (cur_rid == q_rid) && !w_last_narrow;
            assign w_ld_lane     = (start[q_rid] || w_byp) ? '0 : LW'(rasm_rec_lane[q_rid]);
            assign w_ld_rem      = w_byp         ? (cur_rem - 9'd1)
                                 : start[q_rid] ? rem[q_rid]
                                 :                9'(rasm_rec_nlen[q_rid]) + 9'd1;

            assign int_r_valid = cur_valid;
            assign int_rdata   = cur_data[cur_lane*S_AXI_DATA_WIDTH +: S_AXI_DATA_WIDTH];
            assign int_rid     = cur_rid;
            assign int_rresp   = cur_resp;
            assign int_rlast   = w_last_narrow;
            assign int_ruser   = cur_user;

            `ALWAYS_FF_RST(aclk, w_aresetn,
                if (`RST_ASSERTED(w_aresetn)) begin
                    cur_valid <= 1'b0;
                    cur_rid   <= '0;
                    cur_data  <= '0;
                    cur_resp  <= '0;
                    cur_user  <= '0;
                    cur_lane  <= '0;
                    cur_rem   <= '0;
                    for (int i = 0; i < NUM_IDS; i++) begin
                        rem[i]            <= '0;
                        start[i]          <= 1'b0;
                        rasm_rec_valid[i] <= 1'b0;
                    end
                end else begin
                    if (w_out_hs) begin
                        cur_lane <= cur_lane + LW'(1);
                        cur_rem  <= cur_rem - 9'd1;
                        if (w_last_narrow) begin
                            // The s_axi burst is complete: its reservation
                            // frees and the ID starts afresh.
                            start[cur_rid]          <= 1'b0;
                            rasm_rec_valid[cur_rid] <= 1'b0;
                        end else if (w_wide_done) begin
                            rem[cur_rid] <= cur_rem - 9'd1;
                        end
                        if (w_wide_done)
                            cur_valid <= 1'b0;
                    end
                    if (w_load) begin
                        cur_valid    <= 1'b1;
                        cur_rid      <= q_rid;
                        cur_data     <= q_rdata;
                        cur_resp     <= q_rresp;
                        cur_user     <= q_ruser;
                        cur_lane     <= w_ld_lane;
                        cur_rem      <= w_ld_rem;
                        start[q_rid] <= 1'b1;
                    end
                    if (w_rasm_push)
                        rasm_rec_valid[w_rasm_push_id] <= 1'b1;
                end
            )
        end

`ifdef SIMULATION
        always_ff @(posedge aclk) begin
            if (w_aresetn && q_rvalid && q_rready && !rasm_rec_valid[q_rid])
                $error("axi4_dwidth_converter_rd: R beat for ID %0d with no outstanding AR record",
                       q_rid);
        end
`endif

    end else begin : gen_rbypass
        //======================================================================
        // R_INTERLEAVE = 0: no reassembly.
        //
        //   The source never interleaves beats of different R bursts, so
        //   each burst reaches the primitive contiguously as it arrives:
        //   no pool, no store-and-forward.  Bursts of different IDs may
        //   still come back in any order, so the per-ID AR records and the
        //   one-burst-per-ID reservation are kept, looked up by the
        //   ARRIVING beat's RID.
        //
        //   DOWNSIZE (narrow master bursts folded into wide beats): every
        //   master burst is a whole number of wide beats from lane 0
        //   (splits are 256 narrow beats, 256 is a multiple of the ratio),
        //   so no wide beat spans two bursts and another ID's burst may
        //   arrive between the splits of a slave burst.  It must be
        //   accepted: refusing it would hold an R arbiter that holds
        //   through RLAST, and the waiting split could never arrive.
        //
        //   UPSIZE (wide master beats sliced to narrow): the dnsize
        //   primitive frames one burst at a time from burst_len, so a new
        //   burst enters once the previous one is leaving it -- on the cycle
        //   its last narrow beat goes, not the cycle after (that cost one
        //   dead cycle per burst).
        //
        //   R is registered on entry (a 2-deep skid): the record lookup by
        //   RID and the primitive's burst framing then start from a flop,
        //   not from the crossbar's R mux (in a bridge that combined path
        //   was the worst one, 19 levels on the Artix-7).
        //======================================================================
        localparam int RQ_W = AXI_ID_WIDTH + M_AXI_DATA_WIDTH + 2 + 1 + AXI_USER_WIDTH;
        logic                        q_rvalid;
        logic                        q_rready;
        logic [AXI_ID_WIDTH-1:0]     q_rid;
        logic [M_AXI_DATA_WIDTH-1:0] q_rdata;
        logic [1:0]                  q_rresp;
        logic                        q_rlast;
        logic [AXI_USER_WIDTH-1:0]   q_ruser;
        logic [RQ_W-1:0]             q_rpkt;

        gaxi_skid_buffer #(
            .DEPTH      (2),
            .DATA_WIDTH (RQ_W)
        ) r_in_skid (
            .axi_aclk   (aclk),
            .axi_aresetn(w_aresetn),
            .wr_valid   (m_axi_rvalid),
            .wr_ready   (m_axi_rready),
            .wr_data    ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
            .rd_valid   (q_rvalid),
            .rd_ready   (q_rready),
            .rd_data    (q_rpkt),
            .count      (),
            .rd_count   ()
        );
        assign {q_rid, q_rdata, q_rresp, q_rlast, q_ruser} = q_rpkt;
        logic r_in_open;    // a burst has entered the primitive, RLAST not yet
        logic r_out_open;   // UPSIZE: a burst is still leaving the primitive
        logic w_gate;
        logic w_prim_hs;
        logic w_out_hs;

        assign w_prim_hs = prim_rvalid && prim_rready;
        assign w_out_hs  = int_r_valid && int_r_ready;
        assign w_gate    = DOWNSIZE ? 1'b1
                         : (r_in_open || !r_out_open || (w_out_hs && int_rlast));

        assign prim_rvalid  = q_rvalid && w_gate;
        assign q_rready     = prim_rready && w_gate;
        assign prim_rid     = q_rid;
        assign prim_rdata   = q_rdata;
        assign prim_rresp   = q_rresp;
        assign prim_rlast   = q_rlast;
        assign prim_ruser   = q_ruser;

        assign w_cur_final = rasm_rec_final[q_rid];
        assign w_bstart    = q_rvalid && w_gate && !r_in_open;
        assign w_blen      = rasm_rec_nlen[q_rid];
        assign w_blane     = 8'(rasm_rec_lane[q_rid]);
        assign prim_sb     = {prim_rresp, prim_rid, prim_ruser};

        assign int_rid   = int_sb[AXI_USER_WIDTH +: AXI_ID_WIDTH];
        assign int_ruser = int_sb[AXI_USER_WIDTH-1:0];
        // RRESP leaves the primitive in the sideband's top field.
        assign int_rresp = int_sb[PSB_W-1 -: 2];

        `ALWAYS_FF_RST(aclk, w_aresetn,
            if (`RST_ASSERTED(w_aresetn)) begin
                for (int i = 0; i < NUM_IDS; i++) begin
                    rasm_rec_valid[i] <= 1'b0;
                end
                r_in_open  <= 1'b0;
                r_out_open <= 1'b0;
            end else begin
                if (w_prim_hs)
                    r_in_open <= !prim_rlast;
                if (!DOWNSIZE) begin
                    if (w_out_hs && int_rlast)
                        r_out_open <= 1'b0;
                    if (w_prim_hs && !r_in_open)
                        r_out_open <= 1'b1;
                end
                // Release the reservation as gen_rilv does: a master
                // burst fully taken (DOWNSIZE), or its converted slave
                // burst fully sent (UPSIZE).  An ID's AR is gated on its
                // slot being free, so set and clear never meet on one ID.
                if (DOWNSIZE && w_prim_hs && prim_rlast)
                    rasm_rec_valid[q_rid] <= 1'b0;
                if (!DOWNSIZE && w_out_hs && int_rlast)
                    rasm_rec_valid[int_rid] <= 1'b0;
                if (w_rasm_push)
                    rasm_rec_valid[w_rasm_push_id] <= 1'b1;
            end
        )

`ifdef SIMULATION
        logic [AXI_ID_WIDTH-1:0] r_in_id;
        always_ff @(posedge aclk)
            if (q_rvalid && q_rready && !r_in_open)
                r_in_id <= q_rid;
        always_ff @(posedge aclk) begin
            if (w_aresetn && q_rvalid && q_rready && !rasm_rec_valid[q_rid])
                $error("axi4_dwidth_converter_rd: R beat for ID %0d with no outstanding AR record (R_INTERLEAVE=0)",
                       q_rid);
            if (w_aresetn && q_rvalid && r_in_open && (q_rid != r_in_id))
                $error("axi4_dwidth_converter_rd: R_INTERLEAVE=0 but ID %0d interleaved into ID %0d's burst",
                       q_rid, r_in_id);
        end
`endif
    end endgenerate


    //==========================================================================
    // R Channel Data Conversion (delegates to validated primitives)
    //==========================================================================

    generate
        if (R_INTERLEAVE) begin : gen_r_none
            // gen_rilv converts R itself.
            assign arsplit_pop = 1'b0;
            if (DOWNSIZE) begin : gen_tie_dn
                assign arsplit_final = 1'b1;
            end
            assign w_blen_wr_ready = 1'b1;
            assign w_blen_rd_valid = 1'b0;
            assign w_blen_rd_data  = '0;
            assign w_blen_rd_lane  = '0;
            assign w_blen_pop      = 1'b0;
        end else if (DOWNSIZE) begin : gen_r_downsize
            // Slave wide, master narrow. R direction: master → slave, so
            // narrow → wide. Use axi_data_upsize. RRESP errors must
            // propagate across all sub-beats: SB_OR_MODE=1.
            //
            // The primitive sees contiguous master bursts (R_INTERLEAVE =
            // 0 promises them). narrow_last is gated by the per-ID
            // record's final flag so only the last split of a slave burst
            // terminates the upsize accumulation.
            assign arsplit_final = w_cur_final;
            assign arsplit_pop   = prim_rvalid && prim_rready && prim_rlast && w_cur_final;

            axi_data_upsize #(
                .NARROW_WIDTH    (M_AXI_DATA_WIDTH),
                .WIDE_WIDTH      (S_AXI_DATA_WIDTH),
                .NARROW_SB_WIDTH (PSB_W),
                .WIDE_SB_WIDTH   (PSB_W),
                .SB_OR_MODE      (1)
            ) u_r_upsize (
                .aclk            (aclk),
                .aresetn         (w_aresetn),
                .narrow_valid    (prim_rvalid),
                .narrow_ready    (prim_rready),
                .narrow_data     (prim_rdata),
                .narrow_sideband (prim_sb),
                .narrow_last     (prim_rlast && arsplit_final),
                .start_lane      ('0),  // narrow master fetches from the exact addresses
                .wide_valid      (int_r_valid),
                .wide_ready      (int_r_ready),
                .wide_data       (int_rdata),
                .wide_sideband   (int_sb),
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
            // One wide burst enters at a time.  The per-ID record supplies
            // burst_len/start_lane.
            localparam int BLEN_FIFO_DEPTH = 16;
            localparam int BLEN_AW         = $clog2(BLEN_FIFO_DEPTH);
            localparam int R_LANE_W        = $clog2(WIDTH_RATIO);

            // Burst-length FIFO is no longer used; the per-ID record carries
            // the framing.  Keep w_blen_wr_ready tied high so the AR block
            // does not stall, and drive the read-side signals from the burst
            // currently being fed.  burst_start is a single-cycle pulse at the
            // first accepted wide beat so axi_data_dnsize opens the burst
            // cleanly, with no boundary race against the primitive's
            // internal r_burst_active flag.
            assign w_blen_wr_ready = 1'b1;
            assign w_blen_rd_valid = w_bstart;
            assign w_blen_rd_data  = w_blen;
            assign w_blen_rd_lane  = w_blane;

            // Burst record pop: the per-ID slot is already cleared by the
            // R front end when the last beat is consumed; this pulse is
            // kept for the primitive's interface only.
            assign w_blen_pop = prim_rvalid && prim_rready && prim_rlast;

            axi_data_dnsize #(
                .WIDE_WIDTH       (M_AXI_DATA_WIDTH),
                .NARROW_WIDTH     (S_AXI_DATA_WIDTH),
                .WIDE_SB_WIDTH    (PSB_W),
                .NARROW_SB_WIDTH  (PSB_W),
                .SB_BROADCAST     (1),
                .TRACK_BURSTS     (1),
                .BURST_LEN_WIDTH  (8)
            ) u_r_dnsize (
                .aclk            (aclk),
                .aresetn         (w_aresetn),
                .burst_len       (w_blen_rd_data),
                .burst_start     (w_blen_rd_valid),
                .start_lane      (w_blen_rd_lane[$clog2(WIDTH_RATIO)-1:0]),
                .wide_valid      (prim_rvalid),
                .wide_ready      (prim_rready),
                .wide_data       (prim_rdata),
                .wide_sideband   (prim_sb),
                .wide_last       (prim_rlast),
                .narrow_valid    (int_r_valid),
                .narrow_ready    (int_r_ready),
                .narrow_data     (int_rdata),
                .narrow_sideband (int_sb),
                .narrow_last     (int_rlast)
            );
        end
    endgenerate

endmodule : axi4_dwidth_converter_rd
