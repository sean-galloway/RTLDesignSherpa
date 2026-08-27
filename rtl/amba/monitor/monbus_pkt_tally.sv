// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_pkt_tally
// Purpose: On-chip packet-type coverage histogram. Counts accepted monbus
//          packets into a count SRAM addressed by a CSR-loaded legal-set
//          dense index. (The direct-mapped {protocol, pkt_type, event_code}
//          path and the PROFILE_MODE switch were REMOVED -- the legal-set CAM
//          is always in the path. This banner described both for a while
//          after they were deleted; qc round_24.) Formerly: a
//          CSR-loaded legal-set dense index). This is the silicon twin of the
//          sim-side packet-type coverage matrix (bin/monbus_coverage_report +
//          TBClasses.monbus.parse): a bin count > 0 means "this message was
//          observed on hardware", dumped in one readback sweep.
//
//          A counter absorbs any arrival rate, so a coverage run can span
//          millions of cycles without a capture-bandwidth limit.
//
// Data model — DELIBERATELY SIMPLE
// --------------------------------
//   count(bin) = SRAM[bin]                (single source of truth; always live)
// Each accepted packet does one read-modify-write on its bin: read the current
// count, saturating-increment, write it back. No write-combining cache, no
// flush FSM, no "drain before you can read" contract -- a readback always sees
// the true count, at ANY arrival volume (the earlier LRU-cache design stranded
// low-volume counts in the cache until a flush that could silently no-op).
//
// The monbus reporter emits at most 1 packet / 2 cycles, which exactly matches
// this 2-cycle RMW (accept+read, then write); bursts simply backpressure via
// in_ready. All counts saturate (a pegged bin never wraps).
//
// Window protocol (host, over CSR/AXIL):
//   1. i_freeze = 1           stop counting (coherent read boundary)
//   2. read rd_addr -> rd_count  sweep every bin (valid while idle/frozen)
//   3. pulse i_clear          zero the SRAM + first-event latches (o_flush_busy
//                             high from the pulse until the clear walk ends).
//                             A one-cycle pulse is LATCHED, so it is honoured
//                             even when it lands mid read-modify-write.
//   i_flush is accepted for interface compatibility but is a no-op: there is
//   no cache to drain, so nothing needs flushing before a read.
//
// First-event latch: captures the full 128-bit packet + timestamp of the
// first NUM_LATCH accepted packets whose pkt_type is armed in
// i_watch_pkttype_mask, so a nonzero error bin on silicon yields the
// offending packet, not just a count.
//
// Documentation: projects/NexysA7/stream_characterization/
//                vault/handbook/fpga/Genesys2/stream-mon/monitor-board-coverage.md
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_pkt_tally #(
    parameter int PKT_WIDTH   = 128,     // monitor_packet_t width (locked)
    parameter int TS_WIDTH    = 64,      // side-band timestamp width (locked)
    parameter int COUNT_WIDTH = 32,      // saturating bin count width
    parameter int NUM_LATCH   = 4,       // first-event capture slots
    // Bin address = {protocol[3:0], pkt_type[3:0], event_code[7:0]} = 16 bits.
    // The legal-set CAM ALWAYS routes packets to a bin: it maps the tuple
    // {agent,protocol,pkt_type,event_code} to a DENSE bin index; any tuple not
    // in the loaded set lands in the single UNEXPECTED bin (index N_PROFILE).
    // There is no direct-mapped bypass -- the CAM is always in the path.
    // ADDR_BITS must be >= clog2(N_PROFILE+1).
    parameter int ADDR_BITS   = 7,
    parameter int N_PROFILE    = 64,       // legal-set entries (dense bins 0..N-1)
    // Derived
    parameter int SRAM_DEPTH  = (1 << ADDR_BITS),
    parameter int PROF_IDX_W  = (N_PROFILE > 1) ? $clog2(N_PROFILE) : 1,
    parameter int PROF_KEY_W  = 32,        // {agent[15:0],proto[3:0],type[3:0],event[7:0]}
    parameter int LSEL_WIDTH  = (NUM_LATCH > 1) ? $clog2(NUM_LATCH) : 1,
    parameter int LFILL_WIDTH = $clog2(NUM_LATCH + 1)
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // === Accepted-packet input (valid/ready). One packet per handshake. ===
    input  logic                    in_valid,
    output logic                    in_ready,
    input  logic [PKT_WIDTH-1:0]    in_packet,
    input  logic [TS_WIDTH-1:0]     in_ts,

    // === Window / snapshot control ===
    input  logic                    i_freeze,      // level: hold counting
    input  logic                    i_flush,       // no-op (no cache to drain)
    output logic                    o_flush_busy,  // high from the clear request until the walk ends
    input  logic                    i_clear,       // pulse: zero everything

    // === Count readback (registered; valid one cycle after rd_addr, idle only) ===
    input  logic [ADDR_BITS-1:0]    rd_addr,
    output logic [COUNT_WIDTH-1:0]  rd_count,

    // === First-event latch ===
    input  logic                    i_watch_arm,           // level: capture enable
    input  logic [15:0]             i_watch_pkttype_mask,  // bit p = watch pkt_type p
    input  logic [LSEL_WIDTH-1:0]   latch_sel,
    output logic                    latch_valid,
    output logic [PKT_WIDTH-1:0]    latch_packet,
    output logic [TS_WIDTH-1:0]     latch_ts,
    output logic [LFILL_WIDTH-1:0]  latch_fill,

    // === Profile (legal-set) load interface — ALWAYS live (there is no
    //     PROFILE_MODE switch; the legal-set CAM is unconditional) ===
    input  logic                    profile_clear,   // pulse: invalidate all entries
    input  logic                    profile_we,      // pulse: write one entry
    input  logic [PROF_IDX_W-1:0]   profile_waddr,   // entry index
    input  logic                    profile_wvalid,  // entry valid bit
    input  logic [PROF_KEY_W-1:0]   profile_wkey     // {agent[15:0],proto[3:0],type[3:0],event[7:0]}
);

    // ------------------------------------------------------------------------
    // Packet field extraction (positions locked by monitor_common_pkg).
    //   [127:124] pkt_type   [108:105] protocol   [104:97] event_code
    // ------------------------------------------------------------------------
    logic [3:0] w_pkt_type;
    logic [3:0] w_protocol;
    logic [7:0] w_event_code;
    assign w_pkt_type   = in_packet[127:124];
    assign w_protocol   = in_packet[108:105];
    assign w_event_code = in_packet[104:97];

    // Agent id: the legal-set CAM keys on it so rd vs wr (9/10), scheduler vs
    // descriptor-engine agents, etc. resolve into distinct dense bins.
    logic [15:0] w_agent_id;
    assign w_agent_id = in_packet[87:72];

    // The legal-set CAM ALWAYS routes the packet to a bin (no bypass). A hit
    // returns the entry's dense index; a miss routes to the UNEXPECTED bin
    // (index N_PROFILE) and is flagged for the first-event latch.
    localparam int UNEXPECTED_BIN = N_PROFILE;
    logic [ADDR_BITS-1:0]  w_bin_addr;   // which SRAM bin this packet increments
    logic                  w_prof_miss;  // key not in the legal set
    logic [PROF_KEY_W-1:0] w_in_key;
    assign w_in_key = {w_agent_id, w_protocol, w_pkt_type, w_event_code};

    logic                  w_hit;
    logic [PROF_IDX_W-1:0] w_hit_idx;

    monbus_legal_cam #(
        .N_ENTRIES (N_PROFILE),
        .KEY_WIDTH (PROF_KEY_W)
    ) u_legal_cam (
        .clk        (clk),
        .rst_n      (rst_n),
        .load_clear (profile_clear),
        .load_we    (profile_we),
        .load_addr  (profile_waddr),
        .load_valid (profile_wvalid),
        .load_key   (profile_wkey),
        .lookup_key (w_in_key),
        .lookup_hit (w_hit),
        .lookup_idx (w_hit_idx)
    );
    assign w_bin_addr  = w_hit ? ADDR_BITS'(w_hit_idx) : ADDR_BITS'(UNEXPECTED_BIN);
    assign w_prof_miss = !w_hit;

    localparam logic [COUNT_WIDTH-1:0] COUNT_MAX = {COUNT_WIDTH{1'b1}};

    // Saturating increment.
    function automatic logic [COUNT_WIDTH-1:0] sat_inc
            (input logic [COUNT_WIDTH-1:0] a);
        sat_inc = (a == COUNT_MAX) ? COUNT_MAX : (a + 1'b1);
    endfunction

    // ------------------------------------------------------------------------
    // Controller state (deliberately tiny).
    //   ST_RUN   : accept a packet -> read its bin (one cycle).
    //   ST_WR    : write the saturating-incremented count back (one cycle).
    //   ST_CLEAR : walk the SRAM writing 0 (host i_clear).
    // The single-port count SRAM has exactly one writer (ST_WR / ST_CLEAR).
    // ------------------------------------------------------------------------
    localparam logic [1:0] ST_RUN = 2'd0, ST_WR = 2'd1, ST_CLEAR = 2'd2;
    localparam int CIDX_W = ADDR_BITS + 1;             // holds 0..SRAM_DEPTH

    logic [1:0]              r_st;
    logic [ADDR_BITS-1:0]    r_wr_bin;                 // bin being RMW'd
    logic [CIDX_W-1:0]       r_clear_idx;              // 0..SRAM_DEPTH (extra for done)
    logic                    r_clear_pend;             // sticky clear request

    // i_clear is a ONE-CYCLE pulse from the host CSR block, but only ST_RUN
    // looks at it. Counting a packet is a two-cycle RMW, so under sustained
    // traffic the controller sits in ST_WR every other cycle and roughly half
    // of all clear pulses would be dropped -- leaving the host to sweep stale
    // counts it believes are zeroed. Latch the request instead of sampling it.
    // A pulse arriving DURING the clear walk is intentionally discarded: that
    // walk already zeroes every bin, and nothing can increment while it runs
    // (in_ready is low), so re-walking would be pure duplicate work.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n))  r_clear_pend <= 1'b0;
        else if (r_st == ST_CLEAR) r_clear_pend <= 1'b0;
        else if (i_clear)          r_clear_pend <= 1'b1;
    )

    // ------------------------------------------------------------------------
    // Accept path: consume a packet in ST_RUN when not frozen.
    // ------------------------------------------------------------------------
    logic w_accept;
    assign in_ready = (r_st == ST_RUN) && !i_freeze;
    assign w_accept = in_valid && in_ready;

    // ------------------------------------------------------------------------
    // Count SRAM (single-port, synchronous read + write).
    //   ST_RUN accept : read w_bin_addr  (RMW read phase)
    //   ST_WR         : write sat_inc(old) back to r_wr_bin
    //   ST_CLEAR      : write 0 to r_clear_idx
    //   idle          : serve host readback at rd_addr
    // ------------------------------------------------------------------------
    logic [COUNT_WIDTH-1:0] r_sram [SRAM_DEPTH];
    logic [ADDR_BITS-1:0]   w_sram_addr;
    logic                   w_sram_we;
    logic [COUNT_WIDTH-1:0] w_sram_wdata;
    logic [COUNT_WIDTH-1:0] r_sram_rdata;

    always_comb begin
        // Default: serve host readback.
        w_sram_addr  = rd_addr;
        w_sram_we    = 1'b0;
        w_sram_wdata = '0;
        if (r_st == ST_CLEAR) begin
            w_sram_addr  = r_clear_idx[ADDR_BITS-1:0];
            w_sram_we    = (r_clear_idx < CIDX_W'(SRAM_DEPTH));  // no write on done cycle
            w_sram_wdata = '0;
        end else if (r_st == ST_WR) begin
            w_sram_addr  = r_wr_bin;                 // commit the increment
            w_sram_we    = 1'b1;
            w_sram_wdata = sat_inc(r_sram_rdata);
        end else if (w_accept) begin
            w_sram_addr  = w_bin_addr;               // read the bin to increment
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sram_rdata <= '0;
        end else begin
            if (w_sram_we) r_sram[w_sram_addr] <= w_sram_wdata;
            r_sram_rdata <= r_sram[w_sram_addr];    // read-old on same-addr r/w
        end
    )

    assign rd_count = r_sram_rdata;

    // ------------------------------------------------------------------------
    // First-event latch bank.
    // ------------------------------------------------------------------------
    logic [PKT_WIDTH-1:0]   r_latch_pkt [NUM_LATCH];
    logic [TS_WIDTH-1:0]    r_latch_ts  [NUM_LATCH];
    logic [LFILL_WIDTH-1:0] r_latch_fill;

    logic w_watch_match;
    // Latch on an armed pkt_type OR (profile mode) any out-of-profile packet,
    // so the first UNEXPECTED offenders are captured for host inspection.
    assign w_watch_match = i_watch_arm && (i_watch_pkttype_mask[w_pkt_type] || w_prof_miss);

    assign latch_valid  = (LFILL_WIDTH'(latch_sel) < r_latch_fill);
    assign latch_packet = r_latch_pkt[latch_sel];
    assign latch_ts     = r_latch_ts [latch_sel];
    assign latch_fill   = r_latch_fill;

    // ------------------------------------------------------------------------
    // Controller. i_flush is a no-op (no cache); i_clear walks the SRAM to 0.
    // ------------------------------------------------------------------------
    // Busy from the moment the request is latched, not just once the walk
    // starts -- otherwise a host that pulses clear and immediately polls sees
    // busy=0 and reads bins the pending clear is about to zero.
    assign o_flush_busy = (r_st == ST_CLEAR) || r_clear_pend;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_st         <= ST_RUN;
            r_wr_bin     <= '0;
            r_clear_idx  <= '0;
            r_latch_fill <= '0;
        end else begin
            case (r_st)
                ST_RUN: begin
                    if (i_clear || r_clear_pend) begin
                        r_st        <= ST_CLEAR;
                        r_clear_idx <= '0;
                    end else if (w_accept) begin
                        r_wr_bin <= w_bin_addr;      // read issued this cycle
                        r_st     <= ST_WR;
                        // First-event capture on the accepted packet.
                        if (w_watch_match && (r_latch_fill < LFILL_WIDTH'(NUM_LATCH))) begin
                            r_latch_pkt[r_latch_fill[LSEL_WIDTH-1:0]] <= in_packet;
                            r_latch_ts [r_latch_fill[LSEL_WIDTH-1:0]] <= in_ts;
                            r_latch_fill <= r_latch_fill + 1'b1;
                        end
                    end
                end

                ST_WR: begin
                    r_st <= ST_RUN;                  // increment committed this cycle
                end

                ST_CLEAR: begin
                    if (r_clear_idx == CIDX_W'(SRAM_DEPTH)) begin
                        r_latch_fill <= '0;          // latches cleared with the window
                        r_st         <= ST_RUN;
                    end else begin
                        r_clear_idx <= r_clear_idx + 1'b1;
                    end
                end

                default: r_st <= ST_RUN;
            endcase
        end
    )

endmodule : monbus_pkt_tally
