// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_slave_watchdog
// Purpose: Sits in front of an AXI4 slave. While the slave answers, it is a
//          zero-latency pass-through. If the slave stops answering for
//          TIMEOUT_CYCLES with work outstanding, it cuts the slave off and
//          completes every outstanding and later transaction itself with
//          DECERR, so a hung slave cannot hang the masters behind it.
//
// Subsystem: amba
// Author: sean galloway
// Created: 2026-10-16 (bridge GitHub #119 L3)
//
// HEALTHY
//   s_axi_* (upstream, e.g. a fabric) passes straight to m_axi_* (the
//   slave). Alongside, a table of up to MAX_OUTSTANDING entries per
//   direction, in issue order, records each AW (ID, its W burst done) and
//   AR (ID, length, beats returned). A response is matched to the oldest
//   live entry of its ID: each entry records at allocation which live
//   entries of its ID are older, and it is the oldest once all of those have
//   completed, so the match is one-hot (no serial search). The table bounds
//   the outstanding count: AWREADY/ARREADY drop while a direction is full.
//
// THE TIMER
//   Counts while work is outstanding (an entry, owed W beats, or a request
//   the slave has not accepted) and the slave is the blocker: no B or R
//   VALID from it and no handshake on any channel. Any handshake with the
//   slave restarts it. A slave that is slow but alive never trips it; a
//   response held off by upstream backpressure does not count against the
//   slave.
//
// THE TRIP (sticky until reset; o_tripped)
//   Taken only in a cycle with no B or R VALID from the slave, so upstream
//   never sees a response withdrawn. From then on:
//   * the slave sees no VALID (it is presumed dead; a request it had not
//     accepted is withdrawn) and BREADY/RREADY high (late responses drain);
//   * every outstanding AW gets one B, DECERR, once its W burst is complete
//     (owed W beats are accepted upstream and dropped);
//   * every outstanding AR gets its remaining R beats, DECERR, RLAST last
//     (a burst the slave had half returned is finished, not restarted);
//   * new requests are answered the same way, like the subtractive slave.
//   Responses are generated oldest-of-their-ID first, so per-ID order holds.
//
// ASSUMPTIONS
//   * W never leads its AW (the bridge's W steering guarantees it).
//   * The slave does not interleave R beats of different IDs (bridge PRD
//     FR-9). A half-returned burst is matched by ID, so interleaving would
//     still be completed correctly, but it is not a supported input.
//
// Parameters:
//   - IW / AW / DW / UW: AXI ID, address, data and user widths
//   - MAX_OUTSTANDING:  entries per direction, 2..64 (bridge: the slave's
//                       max_outstanding)
//   - TIMEOUT_CYCLES:   >= 2; cycles of slave silence before the trip
//   - READ_FILL:        R data on generated beats, replicated

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_slave_watchdog #(
    parameter int          IW              = 4,
    parameter int          AW              = 32,
    parameter int          DW              = 32,
    parameter int          UW              = 1,
    parameter int          MAX_OUTSTANDING = 16,
    parameter int          TIMEOUT_CYCLES  = 1024,
    parameter logic [31:0] READ_FILL       = 32'hDEAD_BEEF,
    localparam int         SW              = DW / 8,
    localparam int         N               = MAX_OUTSTANDING,
    localparam int         NW              = $clog2(N),
    localparam int         TW              = $clog2(TIMEOUT_CYCLES + 1)
) (
    input  logic            aclk,
    input  logic            aresetn,

    // ---- upstream (from the fabric) ---------------------------------------
    input  logic [IW-1:0]   s_axi_awid,
    input  logic [AW-1:0]   s_axi_awaddr,
    input  logic [7:0]      s_axi_awlen,
    input  logic [2:0]      s_axi_awsize,
    input  logic [1:0]      s_axi_awburst,
    input  logic            s_axi_awlock,
    input  logic [3:0]      s_axi_awcache,
    input  logic [2:0]      s_axi_awprot,
    input  logic [3:0]      s_axi_awqos,
    input  logic [3:0]      s_axi_awregion,
    input  logic [UW-1:0]   s_axi_awuser,
    input  logic            s_axi_awvalid,
    output logic            s_axi_awready,
    input  logic [DW-1:0]   s_axi_wdata,
    input  logic [SW-1:0]   s_axi_wstrb,
    input  logic            s_axi_wlast,
    input  logic [UW-1:0]   s_axi_wuser,
    input  logic            s_axi_wvalid,
    output logic            s_axi_wready,
    output logic [IW-1:0]   s_axi_bid,
    output logic [1:0]      s_axi_bresp,
    output logic [UW-1:0]   s_axi_buser,
    output logic            s_axi_bvalid,
    input  logic            s_axi_bready,
    input  logic [IW-1:0]   s_axi_arid,
    input  logic [AW-1:0]   s_axi_araddr,
    input  logic [7:0]      s_axi_arlen,
    input  logic [2:0]      s_axi_arsize,
    input  logic [1:0]      s_axi_arburst,
    input  logic            s_axi_arlock,
    input  logic [3:0]      s_axi_arcache,
    input  logic [2:0]      s_axi_arprot,
    input  logic [3:0]      s_axi_arqos,
    input  logic [3:0]      s_axi_arregion,
    input  logic [UW-1:0]   s_axi_aruser,
    input  logic            s_axi_arvalid,
    output logic            s_axi_arready,
    output logic [IW-1:0]   s_axi_rid,
    output logic [DW-1:0]   s_axi_rdata,
    output logic [1:0]      s_axi_rresp,
    output logic            s_axi_rlast,
    output logic [UW-1:0]   s_axi_ruser,
    output logic            s_axi_rvalid,
    input  logic            s_axi_rready,

    // ---- downstream (to the slave) ----------------------------------------
    output logic [IW-1:0]   m_axi_awid,
    output logic [AW-1:0]   m_axi_awaddr,
    output logic [7:0]      m_axi_awlen,
    output logic [2:0]      m_axi_awsize,
    output logic [1:0]      m_axi_awburst,
    output logic            m_axi_awlock,
    output logic [3:0]      m_axi_awcache,
    output logic [2:0]      m_axi_awprot,
    output logic [3:0]      m_axi_awqos,
    output logic [3:0]      m_axi_awregion,
    output logic [UW-1:0]   m_axi_awuser,
    output logic            m_axi_awvalid,
    input  logic            m_axi_awready,
    output logic [DW-1:0]   m_axi_wdata,
    output logic [SW-1:0]   m_axi_wstrb,
    output logic            m_axi_wlast,
    output logic [UW-1:0]   m_axi_wuser,
    output logic            m_axi_wvalid,
    input  logic            m_axi_wready,
    input  logic [IW-1:0]   m_axi_bid,
    input  logic [1:0]      m_axi_bresp,
    input  logic [UW-1:0]   m_axi_buser,
    input  logic            m_axi_bvalid,
    output logic            m_axi_bready,
    output logic [IW-1:0]   m_axi_arid,
    output logic [AW-1:0]   m_axi_araddr,
    output logic [7:0]      m_axi_arlen,
    output logic [2:0]      m_axi_arsize,
    output logic [1:0]      m_axi_arburst,
    output logic            m_axi_arlock,
    output logic [3:0]      m_axi_arcache,
    output logic [2:0]      m_axi_arprot,
    output logic [3:0]      m_axi_arqos,
    output logic [3:0]      m_axi_arregion,
    output logic [UW-1:0]   m_axi_aruser,
    output logic            m_axi_arvalid,
    input  logic            m_axi_arready,
    input  logic [IW-1:0]   m_axi_rid,
    input  logic [DW-1:0]   m_axi_rdata,
    input  logic [1:0]      m_axi_rresp,
    input  logic            m_axi_rlast,
    input  logic [UW-1:0]   m_axi_ruser,
    input  logic            m_axi_rvalid,
    output logic            m_axi_rready,

    // ---- status -----------------------------------------------------------
    output logic            o_tripped
);

    localparam logic [1:0] DECERR = 2'b11;

    //==========================================================================
    // State
    //==========================================================================
    logic            r_tripped;

    // AW table, in issue order
    logic [N-1:0]    aw_live, aw_wdone;
    logic [IW-1:0]   aw_id    [N];
    logic [N-1:0]    aw_older [N];
    logic [NW:0]     aw_wptr, aw_head, aw_wfill;   // alloc, retire, next AW owed W

    // AR table, in issue order
    logic [N-1:0]    ar_live;
    logic [IW-1:0]   ar_id    [N];
    logic [7:0]      ar_len   [N];
    logic [8:0]      ar_sent  [N];
    logic [N-1:0]    ar_older [N];
    logic [NW:0]     ar_wptr, ar_head;

    logic [TW-1:0]   r_timer;

    //==========================================================================
    // Occupancy and allocation
    //==========================================================================
    logic aw_full, ar_full;
    assign aw_full = (aw_wptr - aw_head) == (NW+1)'(N);
    assign ar_full = (ar_wptr - ar_head) == (NW+1)'(N);

    logic [NW-1:0] aw_slot, ar_slot, aw_wslot;
    assign aw_slot  = aw_wptr[NW-1:0];
    assign ar_slot  = ar_wptr[NW-1:0];
    assign aw_wslot = aw_wfill[NW-1:0];
    // A W beat belongs to the oldest AW whose burst is not yet complete.
    logic w_owed;
    assign w_owed = (aw_wfill != aw_wptr);

    //==========================================================================
    // Upstream handshakes (both modes) and the healthy pass-through
    //==========================================================================
    logic w_aw_acc, w_ar_acc, w_w_acc;   // accepted from upstream
    assign w_aw_acc = s_axi_awvalid && s_axi_awready;
    assign w_ar_acc = s_axi_arvalid && s_axi_arready;
    assign w_w_acc  = s_axi_wvalid  && s_axi_wready;

    assign m_axi_awid     = s_axi_awid;
    assign m_axi_awaddr   = s_axi_awaddr;
    assign m_axi_awlen    = s_axi_awlen;
    assign m_axi_awsize   = s_axi_awsize;
    assign m_axi_awburst  = s_axi_awburst;
    assign m_axi_awlock   = s_axi_awlock;
    assign m_axi_awcache  = s_axi_awcache;
    assign m_axi_awprot   = s_axi_awprot;
    assign m_axi_awqos    = s_axi_awqos;
    assign m_axi_awregion = s_axi_awregion;
    assign m_axi_awuser   = s_axi_awuser;
    assign m_axi_wdata    = s_axi_wdata;
    assign m_axi_wstrb    = s_axi_wstrb;
    assign m_axi_wlast    = s_axi_wlast;
    assign m_axi_wuser    = s_axi_wuser;
    assign m_axi_arid     = s_axi_arid;
    assign m_axi_araddr   = s_axi_araddr;
    assign m_axi_arlen    = s_axi_arlen;
    assign m_axi_arsize   = s_axi_arsize;
    assign m_axi_arburst  = s_axi_arburst;
    assign m_axi_arlock   = s_axi_arlock;
    assign m_axi_arcache  = s_axi_arcache;
    assign m_axi_arprot   = s_axi_arprot;
    assign m_axi_arqos    = s_axi_arqos;
    assign m_axi_arregion = s_axi_arregion;
    assign m_axi_aruser   = s_axi_aruser;

    assign m_axi_awvalid = !r_tripped && s_axi_awvalid && !aw_full;
    assign m_axi_arvalid = !r_tripped && s_axi_arvalid && !ar_full;
    assign m_axi_wvalid  = !r_tripped && s_axi_wvalid && w_owed;
    assign s_axi_awready = !aw_full && (r_tripped || m_axi_awready);
    assign s_axi_arready = !ar_full && (r_tripped || m_axi_arready);
    // W is taken only for an AW already recorded (W never leads its AW).
    assign s_axi_wready  = w_owed && (r_tripped || m_axi_wready);

    //==========================================================================
    // Response matching: the oldest live entry of the response's ID
    //==========================================================================
    logic [N-1:0] w_aw_same, w_ar_same;   // live entries sharing the new request's ID
    logic [N-1:0] w_b_hit, w_r_hit;       // the entry a slave B / R beat belongs to
    logic [N-1:0] w_b_gen_ok, w_r_gen_ok; // entries the generator may answer
    always_comb begin
        for (int i = 0; i < N; i++) begin
            w_aw_same[i]  = aw_live[i] && (aw_id[i] == s_axi_awid);
            w_ar_same[i]  = ar_live[i] && (ar_id[i] == s_axi_arid);
            w_b_hit[i]    = aw_live[i] && (aw_id[i] == m_axi_bid) &&
                            ((aw_older[i] & aw_live) == '0);
            w_r_hit[i]    = ar_live[i] && (ar_id[i] == m_axi_rid) &&
                            ((ar_older[i] & ar_live) == '0);
            w_b_gen_ok[i] = aw_live[i] && aw_wdone[i] && ((aw_older[i] & aw_live) == '0);
            w_r_gen_ok[i] = ar_live[i] && ((ar_older[i] & ar_live) == '0);
        end
    end

    // Generator picks: lowest-index eligible entry. Every eligible entry is
    // the oldest of its own ID, so any choice keeps per-ID order.
    logic [NW-1:0] w_b_pick, w_r_pick;
    logic          w_b_any, w_r_any;
    always_comb begin
        w_b_pick = '0; w_b_any = 1'b0;
        w_r_pick = '0; w_r_any = 1'b0;
        for (int i = N - 1; i >= 0; i--) begin
            if (w_b_gen_ok[i]) begin w_b_pick = NW'(i); w_b_any = 1'b1; end
            if (w_r_gen_ok[i]) begin w_r_pick = NW'(i); w_r_any = 1'b1; end
        end
    end

    // Index of a one-hot match (OR reduction).
    logic [NW-1:0] w_b_idx, w_r_idx;
    always_comb begin
        w_b_idx = '0; w_r_idx = '0;
        for (int i = 0; i < N; i++) begin
            if (w_b_hit[i]) w_b_idx = w_b_idx | NW'(i);
            if (w_r_hit[i]) w_r_idx = w_r_idx | NW'(i);
        end
    end

    //==========================================================================
    // Upstream B / R: the slave's (healthy) or generated (tripped)
    //==========================================================================
    localparam int FILL_REPS = (DW + 31) / 32;
    logic [FILL_REPS*32-1:0] w_fill_wide;
    logic [DW-1:0]           w_fill;
    assign w_fill_wide = {FILL_REPS{READ_FILL}};
    assign w_fill      = w_fill_wide[DW-1:0];

    always_comb begin
        if (!r_tripped) begin
            s_axi_bid    = m_axi_bid;
            s_axi_bresp  = m_axi_bresp;
            s_axi_buser  = m_axi_buser;
            s_axi_bvalid = m_axi_bvalid;
            m_axi_bready = s_axi_bready;
            s_axi_rid    = m_axi_rid;
            s_axi_rdata  = m_axi_rdata;
            s_axi_rresp  = m_axi_rresp;
            s_axi_rlast  = m_axi_rlast;
            s_axi_ruser  = m_axi_ruser;
            s_axi_rvalid = m_axi_rvalid;
            m_axi_rready = s_axi_rready;
        end else begin
            s_axi_bid    = aw_id[w_b_pick];
            s_axi_bresp  = DECERR;
            s_axi_buser  = '0;
            s_axi_bvalid = w_b_any;
            m_axi_bready = 1'b1;
            s_axi_rid    = ar_id[w_r_pick];
            s_axi_rdata  = w_fill;
            s_axi_rresp  = DECERR;
            s_axi_rlast  = (ar_sent[w_r_pick] == {1'b0, ar_len[w_r_pick]});
            s_axi_ruser  = '0;
            s_axi_rvalid = w_r_any;
            m_axi_rready = 1'b1;
        end
    end

    // Completions, from whichever source answers upstream this cycle.
    logic          w_b_done, w_r_beat;
    logic [NW-1:0] w_b_done_idx, w_r_beat_idx;
    assign w_b_done     = r_tripped ? (s_axi_bvalid && s_axi_bready)
                                    : (m_axi_bvalid && m_axi_bready && (|w_b_hit));
    assign w_b_done_idx = r_tripped ? w_b_pick : w_b_idx;
    assign w_r_beat     = r_tripped ? (s_axi_rvalid && s_axi_rready)
                                    : (m_axi_rvalid && m_axi_rready && (|w_r_hit));
    assign w_r_beat_idx = r_tripped ? w_r_pick : w_r_idx;

    //==========================================================================
    // Timer and trip
    //==========================================================================
    logic w_busy, w_progress, w_stalled;
    assign w_busy     = (|aw_live) || (|ar_live) ||
                        (s_axi_awvalid && !aw_full) || (s_axi_arvalid && !ar_full) ||
                        (s_axi_wvalid && w_owed);
    assign w_progress = (m_axi_awvalid && m_axi_awready) || (m_axi_wvalid && m_axi_wready) ||
                        (m_axi_arvalid && m_axi_arready) ||
                        m_axi_bvalid || m_axi_rvalid;
    assign w_stalled  = w_busy && !w_progress;

    //==========================================================================
    // Sequential
    //==========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_tripped <= 1'b0;
            r_timer   <= '0;
            aw_live   <= '0;
            aw_wdone  <= '0;
            aw_wptr   <= '0;
            aw_head   <= '0;
            aw_wfill  <= '0;
            ar_live   <= '0;
            ar_wptr   <= '0;
            ar_head   <= '0;
            for (int i = 0; i < N; i++) begin
                aw_id[i]    <= '0;
                aw_older[i] <= '0;
                ar_id[i]    <= '0;
                ar_len[i]   <= '0;
                ar_sent[i]  <= '0;
                ar_older[i] <= '0;
            end
        end else begin
            // ---- timer ------------------------------------------------------
            if (!r_tripped) begin
                if (!w_stalled)
                    r_timer <= '0;
                else if (r_timer == TW'(TIMEOUT_CYCLES - 1))
                    r_tripped <= 1'b1;   // w_stalled: no B/R VALID showing now
                else
                    r_timer <= r_timer + 1'b1;
            end

            // ---- AW: allocate, W fill, B completion, retire -------------------
            if (w_aw_acc) begin
                aw_live[aw_slot]  <= 1'b1;
                aw_wdone[aw_slot] <= 1'b0;
                aw_id[aw_slot]    <= s_axi_awid;
                for (int i = 0; i < N; i++)
                    aw_older[i][aw_slot] <= 1'b0;
                aw_older[aw_slot] <= w_aw_same;
                aw_wptr <= aw_wptr + 1'b1;
            end
            if (w_w_acc && s_axi_wlast) begin
                aw_wdone[aw_wslot] <= 1'b1;
                aw_wfill <= aw_wfill + 1'b1;
            end
            if (w_b_done)
                aw_live[w_b_done_idx] <= 1'b0;
            if ((aw_head != aw_wptr) && !aw_live[aw_head[NW-1:0]] &&
                !(w_aw_acc && (aw_slot == aw_head[NW-1:0])))
                aw_head <= aw_head + 1'b1;

            // ---- AR: allocate, R beats, completion, retire --------------------
            if (w_ar_acc) begin
                ar_live[ar_slot] <= 1'b1;
                ar_id[ar_slot]   <= s_axi_arid;
                ar_len[ar_slot]  <= s_axi_arlen;
                ar_sent[ar_slot] <= '0;
                for (int i = 0; i < N; i++)
                    ar_older[i][ar_slot] <= 1'b0;
                ar_older[ar_slot] <= w_ar_same;
                ar_wptr <= ar_wptr + 1'b1;
            end
            if (w_r_beat) begin
                if (ar_sent[w_r_beat_idx] == {1'b0, ar_len[w_r_beat_idx]})
                    ar_live[w_r_beat_idx] <= 1'b0;
                else
                    ar_sent[w_r_beat_idx] <= ar_sent[w_r_beat_idx] + 1'b1;
            end
            if ((ar_head != ar_wptr) && !ar_live[ar_head[NW-1:0]] &&
                !(w_ar_acc && (ar_slot == ar_head[NW-1:0])))
                ar_head <= ar_head + 1'b1;
        end
    )

    assign o_tripped = r_tripped;

endmodule : axi4_slave_watchdog
