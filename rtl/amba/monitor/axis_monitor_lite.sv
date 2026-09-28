// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis_monitor_lite
// Purpose: the AXI4-Stream monitor in the lite discipline (amba/monitor-lite TASK-003).
//
// Documentation: docs/markdown/rtl-amba/monitor/axis_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-27
//
// ============================================================================
// There has never been an AXIS monitor in rtl/amba/monitor. axi_monitor_base
// and axi_monitor_lite are TRANSACTION trackers -- a command handshake opens
// a table entry, data beats and a response close it -- and a stream has no
// command, no response and no outstanding-transaction notion. What a stream
// HAS is packets (TLAST-delimited runs of beats), stalls (TVALID without
// TREADY), bubbles (TVALID withdrawn inside a packet), and a per-beat
// TID/TDEST that may change under a packet. This block watches those, and
// emits them as the AXIS packet classes the monbus package has always
// defined (Credit, Channel, Stream) plus the shared Error / Timeout /
// Completion classes, so the arbiter, group, tally and host tooling see one
// more producer and nothing new.
//
// The event set and payloads are the per-port tap of axis4_intf_observer
// (projects/components/misc), which was written in the lite discipline and
// validated on the board; they are lifted here unchanged so the observer can
// later instantiate this core instead of carrying its own copy. What this
// block adds over the tap is the lite's delivery contract: a 4-deep unreset
// output queue instead of a one-packet hold register, drop-and-count with the
// count REPORTED as Error/EVENT_DROPPED, a frequency-invariant microsecond
// tick for the timeouts, the lite's cfg pin set, and `clear`.
//
// Events (priority when several fire in one cycle: Error > Timeout >
// Completion > Credit > Channel > Stream; the losers are counted, never
// silently discarded):
//   Error/VALID_TIMING     TVALID withdrawn before the handshake (the AXIS rule:
//                          once asserted, TVALID holds until TREADY).
//   Error/STRB_INVALID     an accepted beat whose TSTRB is all zero (legal AXIS
//                          -- a position beat -- but a bug on a DMA stream, so
//                          behind cfg_strb_check_enable).
//   Timeout/HANDSHAKE      TVALID held without TREADY for cfg_timeout_cnt
//                          microseconds; once per stall.
//   Timeout/PACKET         inside a packet, no beat accepted for cfg_timeout_cnt
//                          microseconds; once per gap.
//   Completion/STREAM_END  the TLAST beat, with tid, tdest and the beat count.
//   Credit/BACKPRESSURE    a stall of cfg_stall_threshold CYCLES; once per stall.
//   Channel/ID_CHANGE,     TID or TDEST differs from the PREVIOUS accepted beat
//   Channel/DEST_CHANGE    inside a packet (against the previous beat, so a
//                          change reports once, not on every remaining beat).
//   Stream/START           the first beat of a packet that has more than one (a
//                          one-beat packet's START is implied by its STREAM_END).
//   Stream/PAUSE, RESUME   TVALID low inside a packet, and back again.
//   Error/EVENT_DROPPED    the drop count, sent when the queue has DRAINED and
//                          nothing else wants it (stricter than the lite's
//                          "has room": a report must never take the slot a live
//                          event needs while the bus is congested).
//
// This is a TAP. Nothing here drives or gates the stream: tready is an input
// like tvalid, and a packet the monbus will not take is dropped and counted.
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module axis_monitor_lite
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID      = 8'h09,
    parameter logic [15:0] AGENT_ID     = 16'h0064,
    parameter int          DATA_WIDTH   = 32,     // sizes TSTRB only; the monitor never sees TDATA
    parameter int          ID_WIDTH     = 8,      // 0 legal: tid is then a 1-bit tie-off
    parameter int          DEST_WIDTH   = 4,      // 0 legal: tdest is then a 1-bit tie-off
    parameter int          AGE_WIDTH    = 16,     // microsecond age (cfg_timeout_cnt is 16 bits)
    parameter int          OUT_DEPTH    = 4,      // output queue of event entries, a power of two
    // Frequency-invariant microsecond tick (same knobs as axi_monitor_lite)
    parameter int          CFI_MIN_FREQ_MHZ     = 5,
    parameter int          CFI_MAX_FREQ_MHZ     = 220,
    parameter int          CFI_NUM_FREQ_ENTRIES = 16,
    parameter int          CFI_FREQ_STRATEGY    = 0,
    // Short params (do not override)
    parameter int          SW    = DATA_WIDTH / 8,
    parameter int          IW    = (ID_WIDTH   > 0) ? ID_WIDTH   : 1,
    parameter int          DESTW = (DEST_WIDTH > 0) ? DEST_WIDTH : 1,
    parameter int          SELW  = (CFI_NUM_FREQ_ENTRIES > 1) ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,          // synchronous: forget the open packet and the stall, zero the counters. Legal only while idle -- no packet open, no stall, nothing queued (the same rule as axi_monitor_lite, amba ISSUE-002)

    // Side-band time, sampled into monbus_timestamp with every packet
    input  monbus_timestamp_t     i_mon_time,

    // The stream, tapped (both directions are inputs: this block drives nothing)
    input  logic                  axis_tvalid,
    input  logic                  axis_tready,
    input  logic                  axis_tlast,
    input  logic [IW-1:0]         axis_tid,
    input  logic [DESTW-1:0]      axis_tdest,
    input  logic [SW-1:0]         axis_tstrb,

    // Configuration (cfg_timeout_cnt is in MICROSECONDS, 16'hFFFF = never)
    input  logic [SELW-1:0]       cfg_freq_sel,
    input  logic [15:0]           cfg_timeout_cnt,
    input  logic                  cfg_error_enable,
    input  logic                  cfg_timeout_enable,
    input  logic                  cfg_compl_enable,
    input  logic                  cfg_credit_enable,
    input  logic                  cfg_channel_enable,
    input  logic                  cfg_stream_enable,
    input  logic                  cfg_strb_check_enable,    // Error/STRB_INVALID on an all-zero TSTRB beat
    input  logic [31:0]           cfg_stall_threshold,      // stall length in CYCLES above which Credit/BACKPRESSURE reports; 0 = off
    input  logic [15:0]           cfg_axis_pkt_mask,        // bit[type] = 1 drops that packet type

    // Monitor bus
    output logic                  monbus_valid,
    input  logic                  monbus_ready,
    output monitor_packet_t       monbus_packet,
    output monbus_timestamp_t     monbus_timestamp,

    // Status
    output logic                  busy,               // a packet is open, a stall is running, or a packet is queued
    output logic                  in_packet,          // a beat accepted, TLAST not yet seen
    output logic [31:0]           packet_count,       // packets completed (TLAST beats accepted)
    output logic [15:0]           error_count,        // error packets emitted (drop reports excluded)
    output logic [15:0]           dropped_count       // events lost to a full queue or a lost pick, since the last report
);

    // ------------------------------------------------------------------
    // The wire, this cycle
    // ------------------------------------------------------------------
    wire w_hs = axis_tvalid && axis_tready;

    // ------------------------------------------------------------------
    // Time: one microsecond counter shared by both timeouts. A stamp is
    // taken when a stall or a gap begins; the age is one subtraction.
    // ------------------------------------------------------------------
    logic [AGE_WIDTH-1:0] r_us;
    logic                 w_tick;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_us <= '0;
        else if (w_tick)            r_us <= r_us + 1'b1;
    )

    counter_freq_invariant #(
        .COUNTER_WIDTH    (1),
        .MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ),
        .NUM_FREQ_ENTRIES (CFI_NUM_FREQ_ENTRIES),
        .FREQ_STRATEGY    (CFI_FREQ_STRATEGY)
    ) u_tick (
        .clk          (aclk),
        .rst_n        (aresetn),
        .sync_reset_n (1'b1),
        .freq_sel     (cfg_freq_sel),
        .tick         (w_tick),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_counter    ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ------------------------------------------------------------------
    // Packet-level state: one open packet (a stream interleaving several
    // TIDs under one TLAST is reported as Channel/ID_CHANGE, not tracked
    // per ID -- that is the lite's trade, and the observer's).
    // ------------------------------------------------------------------
    logic                 r_in_pkt;        // a beat accepted, tlast not yet seen
    logic [31:0]          r_pkt_beats;     // beats accepted in the open packet
    logic [31:0]          r_pkt_count;     // packets completed
    logic [IW-1:0]        r_pkt_tid;       // tid on the previous accepted beat
    logic [DESTW-1:0]     r_pkt_tdest;     // tdest on the previous accepted beat
    logic                 r_paused;        // tvalid dropped inside a packet
    wire  [31:0]          w_pkt_beats_now = r_in_pkt ? (r_pkt_beats + 32'd1) : 32'd1;   // beats INCLUDING this handshake

    // ------------------------------------------------------------------
    // Stall-level state
    // ------------------------------------------------------------------
    logic                 r_valid_pend;    // tvalid high and not accepted last cycle
    logic [31:0]          r_stall_cycles;  // consecutive tvalid & ~tready cycles
    logic [AGE_WIDTH-1:0] r_stall_stamp;   // r_us when the stall began
    logic [AGE_WIDTH-1:0] r_beat_stamp;    // r_us at the last accepted beat
    logic                 r_tmo_hs_fired;  // one Timeout/HANDSHAKE per stall
    logic                 r_tmo_pkt_fired; // one Timeout/PACKET per gap
    logic                 r_credit_fired;  // one Credit/BACKPRESSURE per stall
    wire  [AGE_WIDTH-1:0] w_stall_age = r_us - r_stall_stamp;
    wire  [AGE_WIDTH-1:0] w_beat_age  = r_us - r_beat_stamp;
    wire                  w_never     = (cfg_timeout_cnt == 16'hFFFF);

    // ------------------------------------------------------------------
    // Candidate events, each gated by its class enable and the type mask
    // ------------------------------------------------------------------
    function automatic logic type_allowed(input logic [3:0] t);
        return !cfg_axis_pkt_mask[t];
    endfunction

    wire w_en_err    = cfg_error_enable   && type_allowed(PktTypeError);
    wire w_en_tmo    = cfg_timeout_enable && !w_never && type_allowed(PktTypeTimeout);
    wire w_en_compl  = cfg_compl_enable   && type_allowed(PktTypeCompletion);
    wire w_en_credit = cfg_credit_enable  && (cfg_stall_threshold != 32'd0) && type_allowed(PktTypeCredit);
    wire w_en_chan   = cfg_channel_enable && type_allowed(PktTypeChannel);
    wire w_en_stream = cfg_stream_enable  && type_allowed(PktTypeStream);

    // AXIS rule: once TVALID is asserted it holds until the handshake.
    // r_valid_pend remembers an unaccepted TVALID; a low TVALID the cycle
    // after is the violation.
    wire w_err_valid_drop = w_en_err && r_valid_pend && !axis_tvalid;
    wire w_err_strb0      = w_en_err && cfg_strb_check_enable && w_hs && (axis_tstrb == '0);

    wire w_tmo_hs  = w_en_tmo && axis_tvalid && !axis_tready && r_valid_pend &&
                     (w_stall_age >= cfg_timeout_cnt[AGE_WIDTH-1:0]) && !r_tmo_hs_fired;
    wire w_tmo_pkt = w_en_tmo && r_in_pkt && !w_hs &&
                     (w_beat_age >= cfg_timeout_cnt[AGE_WIDTH-1:0]) && !r_tmo_pkt_fired;

    wire w_compl   = w_en_compl && w_hs && axis_tlast;

    wire w_credit  = w_en_credit && axis_tvalid && !axis_tready &&
                     (r_stall_cycles >= cfg_stall_threshold) && !r_credit_fired;

    wire w_chan_id   = w_en_chan && w_hs && r_in_pkt && (axis_tid   != r_pkt_tid);
    wire w_chan_dest = w_en_chan && w_hs && r_in_pkt && (axis_tdest != r_pkt_tdest);

    // A one-beat packet (TLAST on its first beat) reports STREAM_END only: START
    // and END would fire in the same cycle, the pick takes one event a cycle, and
    // START would lose every time and be counted as a drop. Its start is implied
    // by a STREAM_END whose beat count is 1.
    wire w_strm_start  = w_en_stream && w_hs && !r_in_pkt && !axis_tlast;
    wire w_strm_pause  = w_en_stream && r_in_pkt && !axis_tvalid && !r_paused;
    wire w_strm_resume = w_en_stream && r_paused && axis_tvalid;

    // ------------------------------------------------------------------
    // The one event this cycle can queue: the pick, its payload, and how
    // many candidates fired (for the drop count).
    // ------------------------------------------------------------------
    logic        w_ev_fire;
    logic [3:0]  w_ev_type;
    logic [7:0]  w_ev_code;
    logic [63:0] w_ev_data;
    logic [3:0]  w_ev_n;

    always_comb begin
        w_ev_fire = 1'b0;
        w_ev_type = PktTypeError;
        w_ev_code = 8'h00;
        w_ev_data = 64'h0;
        w_ev_n    = 4'($countones({w_err_valid_drop, w_err_strb0, w_tmo_hs, w_tmo_pkt,
                                   w_compl, w_credit, w_chan_id, w_chan_dest,
                                   w_strm_start, w_strm_pause, w_strm_resume}));
        if (w_err_valid_drop) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeError;
            w_ev_code = 8'(AXIS_ERR_VALID_TIMING);
            w_ev_data = {r_stall_cycles, r_pkt_count};
        end else if (w_err_strb0) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeError;
            w_ev_code = 8'(AXIS_ERR_STRB_INVALID);
            w_ev_data = {w_pkt_beats_now, r_pkt_count};
        end else if (w_tmo_hs) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeTimeout;
            w_ev_code = 8'(AXIS_TIMEOUT_HANDSHAKE);
            w_ev_data = {r_stall_cycles, 16'(w_stall_age), cfg_timeout_cnt};
        end else if (w_tmo_pkt) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeTimeout;
            w_ev_code = 8'(AXIS_TIMEOUT_PACKET);
            w_ev_data = {r_pkt_beats, 16'(w_beat_age), cfg_timeout_cnt};
        end else if (w_compl) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeCompletion;
            w_ev_code = 8'(AXIS_COMPL_STREAM_END);
            w_ev_data = {16'(axis_tid), 16'(axis_tdest), w_pkt_beats_now};
        end else if (w_credit) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeCredit;
            w_ev_code = 8'(AXIS_CREDIT_BACKPRESSURE);
            w_ev_data = {r_stall_cycles, cfg_stall_threshold};
        end else if (w_chan_id) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeChannel;
            w_ev_code = 8'(AXIS_CHAN_ID_CHANGE);
            w_ev_data = {16'(r_pkt_tid), 16'(axis_tid), w_pkt_beats_now};
        end else if (w_chan_dest) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeChannel;
            w_ev_code = 8'(AXIS_CHAN_DEST_CHANGE);
            w_ev_data = {16'(r_pkt_tdest), 16'(axis_tdest), w_pkt_beats_now};
        end else if (w_strm_start) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeStream;
            w_ev_code = 8'(AXIS_STREAM_START);
            w_ev_data = {16'(axis_tid), 16'(axis_tdest), r_pkt_count};
        end else if (w_strm_pause) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeStream;
            w_ev_code = 8'(AXIS_STREAM_PAUSE);
            w_ev_data = {r_pkt_beats, r_pkt_count};
        end else if (w_strm_resume) begin
            w_ev_fire = 1'b1; w_ev_type = PktTypeStream;
            w_ev_code = 8'(AXIS_STREAM_RESUME);
            w_ev_data = {r_pkt_beats, r_pkt_count};
        end
        if (clear) begin
            w_ev_fire = 1'b0;
            w_ev_n    = 4'd0;
        end
    end

    // ------------------------------------------------------------------
    // State
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_in_pkt <= 1'b0; r_pkt_beats <= '0; r_pkt_count <= '0;
            r_pkt_tid <= '0; r_pkt_tdest <= '0; r_paused <= 1'b0;
            r_valid_pend <= 1'b0; r_stall_cycles <= '0; r_stall_stamp <= '0; r_beat_stamp <= '0;
            r_tmo_hs_fired <= 1'b0; r_tmo_pkt_fired <= 1'b0; r_credit_fired <= 1'b0;
        end else if (clear) begin
            r_in_pkt <= 1'b0; r_pkt_beats <= '0; r_pkt_count <= '0; r_paused <= 1'b0;
            r_valid_pend <= 1'b0; r_stall_cycles <= '0;
            r_tmo_hs_fired <= 1'b0; r_tmo_pkt_fired <= 1'b0; r_credit_fired <= 1'b0;
        end else begin
            // packet tracking
            if (w_hs) begin
                r_beat_stamp    <= r_us;
                r_tmo_pkt_fired <= 1'b0;
                r_pkt_tid       <= axis_tid;
                r_pkt_tdest     <= axis_tdest;
                if (axis_tlast) begin
                    r_in_pkt    <= 1'b0;
                    r_pkt_beats <= '0;
                    r_pkt_count <= r_pkt_count + 32'd1;
                end else begin
                    r_in_pkt    <= 1'b1;
                    r_pkt_beats <= w_pkt_beats_now;
                end
            end else if (w_tmo_pkt) begin
                r_tmo_pkt_fired <= 1'b1;
            end
            // source bubble inside a packet
            if (w_strm_pause)                 r_paused <= 1'b1;
            else if (axis_tvalid || !r_in_pkt) r_paused <= 1'b0;
            // stall tracking
            if (axis_tvalid && !axis_tready) begin
                r_valid_pend   <= 1'b1;
                r_stall_cycles <= r_stall_cycles + 32'd1;
                if (!r_valid_pend) r_stall_stamp <= r_us;
                if (w_tmo_hs)      r_tmo_hs_fired <= 1'b1;
                if (w_credit)      r_credit_fired <= 1'b1;
            end else begin
                r_valid_pend   <= 1'b0;
                r_stall_cycles <= '0;
                r_tmo_hs_fired <= 1'b0;
                r_credit_fired <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // Drop accounting and the pending drop report (the lite's rule): every
    // candidate the pick could not queue this cycle is counted; the count
    // goes out as Error/EVENT_DROPPED when the queue has room and nothing
    // else wants it, and is then zeroed.
    // ------------------------------------------------------------------
    logic        w_wr_ready;
    wire         w_take     = w_ev_fire && w_wr_ready;
    wire  [3:0]  w_lost     = w_ev_n - 4'(w_take);
    logic [15:0] r_dropped, r_errors;
    // The report goes only into an EMPTY queue: a report pushed into a queue
    // that is merely not full would take the slot the next live event needs
    // while the bus is congested -- which is exactly when drops happen -- and
    // each idle cycle would add another report. So it waits for the queue to
    // drain; the count keeps accumulating (saturating) until then.
    logic        w_q_empty;
    wire         w_drop_rpt = (r_dropped != 16'd0) && !w_ev_fire && w_q_empty && w_en_err && !clear;
    wire         w_err_take = w_take && (w_ev_type == PktTypeError);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_dropped <= '0; r_errors <= '0;
        end else if (clear) begin
            r_dropped <= '0; r_errors <= '0;
        end else begin
            // saturating: once the top twelve bits are set, pin (w_lost is at most 11)
            if (w_drop_rpt)            r_dropped <= '0;
            else if (&r_dropped[15:4]) r_dropped <= 16'hFFFF;
            else                       r_dropped <= r_dropped + 16'(w_lost);
            if (w_err_take && (r_errors != 16'hFFFF)) r_errors <= r_errors + 1'b1;
        end
    )

    // ------------------------------------------------------------------
    // The output queue: OUT_DEPTH entries in an UNRESET array with two
    // wrapping pointers (the lite's queue). The entry holds only what varies
    // -- type, code, channel (tid) and the 64-bit payload; protocol, unit and
    // agent are constants added at the output.
    // ------------------------------------------------------------------
    typedef struct packed {
        logic [3:0]  ptype;
        logic [7:0]  code;
        logic [8:0]  chan;
        logic [63:0] data;
    } axis_entry_t;

    axis_entry_t w_entry_in, w_entry_out;
    always_comb begin
        if (w_ev_fire)
            w_entry_in = '{ptype: w_ev_type, code: w_ev_code, chan: 9'(axis_tid), data: w_ev_data};
        else
            w_entry_in = '{ptype: PktTypeError, code: 8'(AXIS_ERR_EVENT_DROPPED), chan: 9'd0, data: 64'(r_dropped)};
    end

    localparam int OQW = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;
    logic [$bits(axis_entry_t)-1:0] r_q [OUT_DEPTH];
    logic [OQW:0] r_q_wp, r_q_rp;                         // one extra bit tells full from empty
    assign        w_q_empty = (r_q_wp == r_q_rp);
    wire          w_q_full  = (r_q_wp[OQW-1:0] == r_q_rp[OQW-1:0]) && (r_q_wp[OQW] != r_q_rp[OQW]);
    wire          w_q_push  = w_take || w_drop_rpt;
    wire          w_q_pop   = monbus_valid && monbus_ready;
    assign w_wr_ready  = !w_q_full;
    assign w_entry_out = r_q[r_q_rp[OQW-1:0]];

    always_ff @(posedge aclk) begin
        if (w_q_push) r_q[r_q_wp[OQW-1:0]] <= w_entry_in;
    end
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_q_wp <= '0; r_q_rp <= '0;
        end else begin
            if (w_q_push) r_q_wp <= r_q_wp + 1'b1;
            if (w_q_pop)  r_q_rp <= r_q_rp + 1'b1;
        end
    )

    assign monbus_valid     = !w_q_empty;
    assign monbus_packet    = create_monitor_packet(w_entry_out.ptype, PROTOCOL_AXIS, w_entry_out.code,
                                                    w_entry_out.chan, UNIT_ID, AGENT_ID, w_entry_out.data);
    assign monbus_timestamp = i_mon_time;   // side-band time, sampled by the consumer at the handshake

    assign busy          = r_in_pkt || r_valid_pend || monbus_valid;
    assign in_packet     = r_in_pkt;
    assign packet_count  = r_pkt_count;
    assign error_count   = r_errors;
    assign dropped_count = r_dropped;

endmodule : axis_monitor_lite
