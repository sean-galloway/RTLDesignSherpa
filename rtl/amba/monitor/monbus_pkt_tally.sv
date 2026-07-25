// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_pkt_tally
// Purpose: On-chip packet-type coverage histogram. Counts accepted monbus
//          packets into an SRAM matrix addressed by the message identity
//          {protocol, pkt_type, event_code}, fronted by a 32-entry LRU
//          write-combining cache so the common case (back-to-back hits on a
//          few hot bins) never touches the SRAM. This is the silicon twin of
//          the sim-side packet-type coverage matrix (bin/monbus_coverage_report
//          + TBClasses.monbus.parse): a bin count > 0 means "this message was
//          observed on hardware", dumped in one readback sweep.
//
//          A counter absorbs any arrival rate, so a coverage run can span
//          millions of cycles without a capture-bandwidth limit — unlike the
//          compressor+log path, which bounds capture to the log SRAM depth.
//
// Building blocks pulled together (all pre-existing on main):
//   - monbus_cam         : the 32-entry true-LRU cache front (payload
//                          repurposed from last_event_data to a partial count;
//                          the evict/dump/soft_clear ports were added additively
//                          for this consumer — the compressor path is untouched).
//   - monitor_common_pkg : the locked 128-bit packet field map.
//   - a synchronous single-port count SRAM (the backing histogram).
//
// Data model
// ----------
//   total(bin) = SRAM[bin] + (cache partial for bin, if resident)
// Hits increment the cache partial in place (no SRAM access). A cache miss
// installs a fresh partial (=1); if that eviction displaces an entry, the
// victim's partial is saturating-added back into its SRAM bin (evict RMW).
// A freeze/flush drains every resident partial into SRAM so a readback sees
// the coherent total. All counts saturate (a pegged bin never wraps, even
// across the cache/SRAM split).
//
// Snapshot protocol (host, over CSR/AXIL):
//   1. i_freeze = 1           stop counting (coherent boundary)
//   2. pulse i_flush          drain cache partials into SRAM (o_flush_busy=1
//                             until done; the cache is left empty)
//   3. read rd_addr -> rd_count  sweep every bin (valid only while idle)
//   4. pulse i_clear          zero SRAM + cache + first-event latches for the
//                             next window
//
// First-event latch: captures the full 128-bit packet + timestamp of the
// first NUM_LATCH accepted packets whose pkt_type is armed in
// i_watch_pkttype_mask, so a nonzero error bin on silicon yields the
// offending packet, not just a count.
//
// Documentation: projects/NexysA7/stream_characterization/
//                MONITOR_BOARD_VALIDATION_PLAN.md
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_pkt_tally #(
    parameter int PKT_WIDTH   = 128,     // monitor_packet_t width (locked)
    parameter int TS_WIDTH    = 64,      // side-band timestamp width (locked)
    parameter int COUNT_WIDTH = 32,      // saturating bin count width
    parameter int CACHE_DEPTH = 32,      // LRU write-combining cache entries
    parameter int NUM_LATCH   = 4,       // first-event capture slots
    // Bin address = {protocol[3:0], pkt_type[3:0], event_code[7:0]} = 16 bits.
    // Direct-mapped (no hashing) so a bin uniquely identifies the message
    // tuple and the hardware count matches the Python parse() count exactly.
    parameter int ADDR_BITS   = 16,
    // Derived
    parameter int SRAM_DEPTH  = (1 << ADDR_BITS),
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
    input  logic                    i_flush,       // pulse: drain cache -> SRAM
    output logic                    o_flush_busy,  // high while flush/clear runs
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
    output logic [LFILL_WIDTH-1:0]  latch_fill
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

    // Full 16-bit message identity; the bin address is its low ADDR_BITS bits
    // (ADDR_BITS = 16 in production keeps the whole tuple; a smaller test build
    // keeps {pkt_type, event_code} and must restrict protocol to stay unique).
    logic [15:0] w_bin_full;
    assign w_bin_full = {w_protocol, w_pkt_type, w_event_code};
    logic [ADDR_BITS-1:0] w_bin_addr;
    assign w_bin_addr = w_bin_full[ADDR_BITS-1:0];

    localparam logic [COUNT_WIDTH-1:0] COUNT_MAX = {COUNT_WIDTH{1'b1}};

    // Saturating add of two counts (a is a full count, b a partial).
    function automatic logic [COUNT_WIDTH-1:0] sat_add
            (input logic [COUNT_WIDTH-1:0] a, input logic [COUNT_WIDTH-1:0] b);
        logic [COUNT_WIDTH:0] sum;
        sum = {1'b0, a} + {1'b0, b};
        sat_add = sum[COUNT_WIDTH] ? COUNT_MAX : sum[COUNT_WIDTH-1:0];
    endfunction

    // Saturating increment.
    function automatic logic [COUNT_WIDTH-1:0] sat_inc
            (input logic [COUNT_WIDTH-1:0] a);
        sat_inc = (a == COUNT_MAX) ? COUNT_MAX : (a + 1'b1);
    endfunction

    // ------------------------------------------------------------------------
    // Controller state.
    //   ST_RUN   : count accepted packets; service evict RMW inline.
    //   ST_FLUSH : walk the cache, spill each live partial into SRAM.
    //   ST_CLEAR : walk the SRAM writing 0.
    // A small spill sub-sequence (SP_*) performs one saturating RMW; it is
    // shared by eviction and flush so there is exactly one SRAM writer.
    // ------------------------------------------------------------------------
    localparam logic [1:0] ST_RUN = 2'd0, ST_FLUSH = 2'd1, ST_CLEAR = 2'd2;
    localparam logic [1:0] SP_IDLE = 2'd0, SP_RD = 2'd1, SP_WR = 2'd2;

    logic [1:0] r_st;
    logic [1:0] r_sp;
    logic [ADDR_BITS-1:0]      r_spill_key;
    logic [COUNT_WIDTH-1:0]    r_spill_data;

    localparam int IDX_WIDTH = (CACHE_DEPTH > 1) ? $clog2(CACHE_DEPTH) : 1;
    localparam int FIDX_W    = IDX_WIDTH + 1;    // holds 0..CACHE_DEPTH
    localparam int CIDX_W    = ADDR_BITS + 1;    // holds 0..SRAM_DEPTH
    logic [FIDX_W-1:0]        r_flush_idx;   // 0..CACHE_DEPTH (one extra for done)
    logic [CIDX_W-1:0]        r_clear_idx;   // 0..SRAM_DEPTH   (one extra for done)

    logic spill_idle;
    assign spill_idle = (r_sp == SP_IDLE);

    // ------------------------------------------------------------------------
    // The 32-entry LRU cache (reused monbus_cam). Payload = partial count.
    // ------------------------------------------------------------------------
    logic                    cam_hit;
    logic [IDX_WIDTH-1:0]    cam_idx;
    logic [COUNT_WIDTH-1:0]  cam_old_data;
    logic [1:0]              cam_action;
    logic [COUNT_WIDTH-1:0]  cam_new_data;
    logic                    cam_full;
    logic                    cam_evicted;
    logic [ADDR_BITS-1:0]    cam_evict_key;
    logic [COUNT_WIDTH-1:0]  cam_evict_data;
    logic [IDX_WIDTH-1:0]    cam_dump_idx;
    logic                    cam_dump_valid;
    logic [ADDR_BITS-1:0]    cam_dump_key;
    logic [COUNT_WIDTH-1:0]  cam_dump_data;
    logic                    cam_soft_clear;
    logic                    cam_unused_old_ts;   // access_old_ts (TS unused here)
    logic [IDX_WIDTH:0]      cam_unused_count;    // cam_count (occupancy unused)

    localparam logic [1:0] ACTION_NONE = 2'b00, ACTION_TOUCH = 2'b01, ACTION_INSTALL = 2'b10;

    monbus_cam #(
        .KEY_WIDTH  (ADDR_BITS),
        .DATA_WIDTH (COUNT_WIDTH),
        .TS_WIDTH   (1),
        .DEPTH      (CACHE_DEPTH)
    ) u_cache (
        .clk             (clk),
        .rst_n           (rst_n),
        .access_key      (w_bin_addr),
        .access_hit      (cam_hit),
        .access_idx      (cam_idx),
        .access_old_data (cam_old_data),
        .access_old_ts   (cam_unused_old_ts),
        .access_action   (cam_action),
        .access_new_data (cam_new_data),
        .access_new_ts   (1'b0),
        .cam_full        (cam_full),
        .cam_count       (cam_unused_count),
        .evicted         (cam_evicted),
        .evict_key       (cam_evict_key),
        .evict_data      (cam_evict_data),
        .dump_idx        (cam_dump_idx),
        .dump_valid      (cam_dump_valid),
        .dump_key        (cam_dump_key),
        .dump_data       (cam_dump_data),
        .soft_clear      (cam_soft_clear)
    );

    // ------------------------------------------------------------------------
    // Accept path.
    // Accept only in ST_RUN, not frozen, and with the spill engine idle (an
    // in-flight RMW owns the SRAM port and must finish before a new eviction
    // can be created). This is the only place cam_action is driven.
    // ------------------------------------------------------------------------
    logic w_accept;
    assign in_ready = (r_st == ST_RUN) && !i_freeze && spill_idle;
    assign w_accept = in_valid && in_ready;

    always_comb begin
        cam_action   = ACTION_NONE;
        cam_new_data = '0;
        if (w_accept) begin
            if (cam_hit) begin
                cam_action   = ACTION_TOUCH;
                cam_new_data = sat_inc(cam_old_data);   // count this occurrence
            end else begin
                cam_action   = ACTION_INSTALL;
                cam_new_data = {{(COUNT_WIDTH-1){1'b0}}, 1'b1}; // first in cache
            end
        end
    end

    // ------------------------------------------------------------------------
    // SRAM (single-port, synchronous read + write). One writer (the spill /
    // clear path); reads serve the host readback and the spill RD phase.
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
            w_sram_we    = 1'b1;
            w_sram_wdata = '0;
        end else if (r_sp == SP_RD) begin
            w_sram_addr  = r_spill_key;             // read current bin count
        end else if (r_sp == SP_WR) begin
            w_sram_addr  = r_spill_key;
            w_sram_we    = 1'b1;
            w_sram_wdata = sat_add(r_sram_rdata, r_spill_data);
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
    logic [PKT_WIDTH-1:0] r_latch_pkt [NUM_LATCH];
    logic [TS_WIDTH-1:0]  r_latch_ts  [NUM_LATCH];
    logic [LFILL_WIDTH-1:0] r_latch_fill;

    logic w_watch_match;
    assign w_watch_match = i_watch_arm && i_watch_pkttype_mask[w_pkt_type];

    assign latch_valid  = (LFILL_WIDTH'(latch_sel) < r_latch_fill);
    assign latch_packet = r_latch_pkt[latch_sel];
    assign latch_ts     = r_latch_ts [latch_sel];
    assign latch_fill   = r_latch_fill;

    // ------------------------------------------------------------------------
    // Controller + spill sequencer.
    // ------------------------------------------------------------------------
    assign o_flush_busy = (r_st == ST_FLUSH) || (r_st == ST_CLEAR);

    // Dump index the flush walk is currently inspecting.
    assign cam_dump_idx   = r_flush_idx[IDX_WIDTH-1:0];
    // The CAM is invalidated at the end of a flush and on clear.
    assign cam_soft_clear = ((r_st == ST_FLUSH) && (r_flush_idx == FIDX_W'(CACHE_DEPTH)) && spill_idle)
                          || ((r_st == ST_CLEAR) && (r_clear_idx == CIDX_W'(SRAM_DEPTH)));

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_st          <= ST_RUN;
            r_sp          <= SP_IDLE;
            r_spill_key   <= '0;
            r_spill_data  <= '0;
            r_flush_idx   <= '0;
            r_clear_idx   <= '0;
            r_latch_fill  <= '0;
        end else begin
            // --- spill sub-sequence (shared RMW engine) ---
            case (r_sp)
                SP_RD: r_sp <= SP_WR;         // r_sram_rdata valid next cycle
                SP_WR: r_sp <= SP_IDLE;       // write committed this cycle
                default: ; // SP_IDLE: started by RUN eviction or FLUSH below
            endcase

            // --- main state machine ---
            case (r_st)
                ST_RUN: begin
                    // Kick a spill when an accept evicts a live victim.
                    if (w_accept && cam_evicted) begin
                        r_spill_key  <= cam_evict_key;
                        r_spill_data <= cam_evict_data;
                        r_sp         <= SP_RD;
                    end
                    // Enter flush/clear only from a quiescent spill engine.
                    if (i_clear && spill_idle) begin
                        r_st        <= ST_CLEAR;
                        r_clear_idx <= '0;
                    end else if (i_flush && spill_idle) begin
                        r_st        <= ST_FLUSH;
                        r_flush_idx <= '0;
                    end

                    // First-event capture.
                    if (w_accept && w_watch_match && (r_latch_fill < LFILL_WIDTH'(NUM_LATCH))) begin
                        r_latch_pkt[r_latch_fill[LSEL_WIDTH-1:0]] <= in_packet;
                        r_latch_ts [r_latch_fill[LSEL_WIDTH-1:0]] <= in_ts;
                        r_latch_fill <= r_latch_fill + 1'b1;
                    end
                end

                ST_FLUSH: begin
                    // Walk the cache; spill each live entry, one RMW at a time.
                    if (r_flush_idx == FIDX_W'(CACHE_DEPTH)) begin
                        // Wait for the final RMW to land, then finish (soft_clear
                        // fires this cycle via the comb assign above).
                        if (spill_idle) r_st <= ST_RUN;
                    end else if (spill_idle) begin
                        if (cam_dump_valid) begin
                            r_spill_key  <= cam_dump_key;
                            r_spill_data <= cam_dump_data;
                            r_sp         <= SP_RD;
                        end
                        r_flush_idx <= r_flush_idx + 1'b1;
                    end
                end

                ST_CLEAR: begin
                    if (r_clear_idx == CIDX_W'(SRAM_DEPTH)) begin
                        r_latch_fill <= '0;   // latches cleared with the window
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
