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
//   owns: AR/R skid buffers, the AR arlen/arsize rewrite, and the
//   rid/ruser carry that the primitives don't handle.
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
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // Calculated Parameters
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXI_DATA_WIDTH / 8,
    localparam int WIDTH_RATIO  = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ?
                                  (M_AXI_DATA_WIDTH / S_AXI_DATA_WIDTH) :
                                  (S_AXI_DATA_WIDTH / M_AXI_DATA_WIDTH),
    localparam bit UPSIZE       = (S_AXI_DATA_WIDTH < M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,
    localparam bit DOWNSIZE     = (S_AXI_DATA_WIDTH > M_AXI_DATA_WIDTH) ? 1'b1 : 1'b0,

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

    // Downsize AR-split queue (driven in gen_ar_downsize, consumed by the
    // R path; tied off for upsize). One flag per issued master burst:
    // whether it is the final master burst of its slave burst. Pushed at
    // AR issue, popped at that burst's RLAST, so the head always
    // describes the master burst currently returning data.
    logic       arsplit_final;   // head: current master burst is the last
    logic       arsplit_pop;     // R side: master burst completed
    logic [AXI_USER_WIDTH-1:0]   int_ruser;

    // Burst-length FIFO handshake (used only in the wide->narrow R data path,
    // i.e. UPSIZE mode). Frames each outstanding read burst's original narrow
    // length to when that burst drains through axi_data_dnsize. Driven with
    // safe pass-through defaults in DOWNSIZE mode (see gen_r_downsize).
    logic                        w_blen_wr_ready;   // FIFO has room for a new AR
    logic                        w_blen_rd_valid;   // a pending burst length exists
    logic [7:0]                  w_blen_rd_data;    // head = current burst narrow len

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
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);
            localparam int MAX_BEATS   = 256;
            localparam int CNTW        = 9 + $clog2(WIDTH_RATIO);
            localparam int ARQ_DEPTH   = 16;
            localparam int ARQ_AW      = $clog2(ARQ_DEPTH);

            logic [CNTW-1:0]           r_split_remaining;
            logic [AXI_ADDR_WIDTH-1:0] r_split_addr;
            logic                      r_split_active;
            logic [8:0]                w_this_beats;
            logic                      w_this_last;
            logic                      w_ar_issue;

            assign w_this_beats = (r_split_remaining > CNTW'(MAX_BEATS))
                                  ? 9'(MAX_BEATS) : 9'(r_split_remaining);
            assign w_this_last  = (r_split_remaining <= CNTW'(MAX_BEATS));
            assign w_ar_issue   = m_axi_arvalid && m_axi_arready;

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

            // Final-burst flag queue: pushed per issued master burst,
            // popped by the R path at that burst's RLAST. AR is
            // back-pressured on full, so it cannot overflow.
            logic [ARQ_AW:0] arq_wptr, arq_rptr;
            logic            arq_mem [ARQ_DEPTH];
            logic            w_arq_full;

            assign w_arq_full =
                (arq_wptr[ARQ_AW-1:0] == arq_rptr[ARQ_AW-1:0]) &&
                (arq_wptr[ARQ_AW]     != arq_rptr[ARQ_AW]);
            assign arsplit_final = arq_mem[arq_rptr[ARQ_AW-1:0]];

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    arq_wptr <= '0;
                    arq_rptr <= '0;
                end else begin
                    if (w_ar_issue) begin
                        arq_mem[arq_wptr[ARQ_AW-1:0]] <= w_this_last;
                        arq_wptr <= arq_wptr + 1'b1;
                    end
                    if (arsplit_pop) arq_rptr <= arq_rptr + 1'b1;
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
            assign m_axi_arvalid  = r_split_active && !w_arq_full;
            // the slave's AR is consumed only when its FINAL master
            // burst is issued
            assign int_ar_ready   = w_ar_issue && w_this_last;

        end else begin : gen_ar_upsize
            // Upsize: slave (narrow) → master (wide). Divide burst length
            // by ratio (round up) and align address down to wide boundary.
            // Division can never overflow ARLEN; the split queue is inert.
            localparam int MASTER_SIZE = $clog2(M_STRB_WIDTH);

            assign arsplit_final = 1'b1;
            localparam int ALIGN_BITS  = $clog2(M_STRB_WIDTH);

            logic [7:0] master_arlen;
            logic [AXI_ADDR_WIDTH-1:0] aligned_araddr;

            assign master_arlen   = 8'((int_arlen + 8'(WIDTH_RATIO)) / 8'(WIDTH_RATIO)) - 8'd1;
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
            // Gate AR on burst-length FIFO space so every outstanding read
            // burst is tracked (prevents overflow -> lost RLAST framing).
            assign m_axi_arvalid  = int_ar_valid && w_blen_wr_ready;
            assign int_ar_ready   = m_axi_arready && w_blen_wr_ready;
        end
    endgenerate

    //==========================================================================
    // R Channel ID / USER Carry
    //
    //   The validated axi_data_{upsize,dnsize} primitives handle the data
    //   payload, RRESP sideband, and LAST signalling. They do NOT carry
    //   AXI4 transaction id (rid) or the optional ruser sideband, so we
    //   register them on every master-side R handshake and present the
    //   latest captured value on the slave-side R output.
    //
    //   This works because AXI4 holds rid constant for every beat of a
    //   single transaction, so "most recent rid" is the correct rid for
    //   whatever aggregated/split slave beat is currently being emitted.
    //==========================================================================

    logic [AXI_ID_WIDTH-1:0]   r_rid_held;
    logic [AXI_USER_WIDTH-1:0] r_ruser_held;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rid_held   <= '0;
            r_ruser_held <= '0;
        end else if (m_axi_rvalid && m_axi_rready) begin
            r_rid_held   <= m_axi_rid;
            r_ruser_held <= m_axi_ruser;
        end
    )

    assign int_rid   = r_rid_held;
    assign int_ruser = r_ruser_held;

    //==========================================================================
    // R Channel Data Conversion (delegates to validated primitives)
    //==========================================================================

    generate
        if (DOWNSIZE) begin : gen_r_downsize
            // Slave wide, master narrow. R direction: master → slave, so
            // narrow → wide. Use axi_data_upsize. RRESP errors must
            // propagate across all sub-beats: SB_OR_MODE=1.
            axi_data_upsize #(
                .NARROW_WIDTH    (M_AXI_DATA_WIDTH),
                .WIDE_WIDTH      (S_AXI_DATA_WIDTH),
                .NARROW_SB_WIDTH (2),
                .WIDE_SB_WIDTH   (2),
                .SB_OR_MODE      (1)
            ) u_r_upsize (
                .aclk            (aclk),
                .aresetn         (aresetn),
                .narrow_valid    (m_axi_rvalid),
                .narrow_ready    (m_axi_rready),
                .narrow_data     (m_axi_rdata),
                .narrow_sideband (m_axi_rresp),
                // A split slave burst returns as several master bursts,
                // each with its own RLAST -- but the slave must see ONE.
                // Only the final master burst's RLAST reaches the upsize;
                // the rest are masked and accumulation just continues
                // across the boundary, which is safe because 256 narrow
                // beats is a whole number of wide beats at every ratio.
                .narrow_last     (m_axi_rlast && arsplit_final),
                .wide_valid      (int_r_valid),
                .wide_ready      (int_r_ready),
                .wide_data       (int_rdata),
                .wide_sideband   (int_rresp),
                .wide_last       (int_rlast)
            );

            // step the flag queue as each master burst completes
            assign arsplit_pop = m_axi_rvalid && m_axi_rready && m_axi_rlast;

            // No burst-length FIFO needed on the narrow->wide (upsize) data
            // path; keep the shared handshake wires inert.
            assign w_blen_wr_ready = 1'b1;
            assign w_blen_rd_valid = 1'b0;
            assign w_blen_rd_data  = '0;

        end else begin : gen_r_upsize
            assign arsplit_pop = 1'b0;
            // Slave narrow, master wide. R direction: master → slave, so
            // wide → narrow. axi_data_dnsize (TRACK_BURSTS=1) asserts
            // narrow_last on the last narrow beat of each burst, using that
            // burst's ORIGINAL (pre-rewrite) narrow length.
            //
            // Several read requests can be accepted back-to-back before any R
            // data returns. A single burst_len wire + AR-accept start pulse
            // frames only the FIRST burst: the dnsize ignores start pulses
            // while a burst is active and has no length queue, so bursts 2..N
            // drain with narrow_last never asserted (collapsing N read bursts
            // into one). A small FIFO holds one narrow arlen per outstanding
            // burst; its head feeds the dnsize (burst_start held while the
            // FIFO is non-empty) and is popped when each narrow burst
            // completes, so every burst is framed regardless of overlap.
            // Self-contained circular FIFO (no submodule dependency, so this
            // widely-instantiated converter adds no new filelist deps). Depth
            // covers the max outstanding read bursts; AR is back-pressured when
            // full (see gen_ar_upsize) so it can never overflow.
            localparam int BLEN_FIFO_DEPTH = 16;
            localparam int BLEN_AW         = $clog2(BLEN_FIFO_DEPTH);

            logic [7:0]         blen_mem [BLEN_FIFO_DEPTH];
            logic [BLEN_AW:0]   blen_wptr, blen_rptr;   // extra MSB for full/empty
            logic               w_blen_push, w_blen_pop;

            // AR accepted -> enqueue its narrow length. A slave-side (narrow)
            // burst completes on its last-beat handshake -> dequeue.
            assign w_blen_push = int_ar_valid && int_ar_ready;
            assign w_blen_pop  = int_r_valid && int_r_ready && int_rlast;

            assign w_blen_wr_ready = !((blen_wptr[BLEN_AW-1:0] == blen_rptr[BLEN_AW-1:0]) &&
                                       (blen_wptr[BLEN_AW]     != blen_rptr[BLEN_AW]));   // !full
            assign w_blen_rd_valid = (blen_wptr != blen_rptr);                            // !empty
            assign w_blen_rd_data  = blen_mem[blen_rptr[BLEN_AW-1:0]];

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    blen_wptr <= '0;
                    blen_rptr <= '0;
                end else begin
                    if (w_blen_push) begin
                        blen_mem[blen_wptr[BLEN_AW-1:0]] <= int_arlen;
                        blen_wptr <= blen_wptr + 1'b1;
                    end
                    if (w_blen_pop) blen_rptr <= blen_rptr + 1'b1;
                end
            )

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
                .wide_valid      (m_axi_rvalid),
                .wide_ready      (m_axi_rready),
                .wide_data       (m_axi_rdata),
                .wide_sideband   (m_axi_rresp),
                .wide_last       (m_axi_rlast),
                .narrow_valid    (int_r_valid),
                .narrow_ready    (int_r_ready),
                .narrow_data     (int_rdata),
                .narrow_sideband (int_rresp),
                .narrow_last     (int_rlast)
            );
        end
    endgenerate

endmodule : axi4_dwidth_converter_rd
