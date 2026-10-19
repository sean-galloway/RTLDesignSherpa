// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cxs_monitor_lite
// Purpose: the CXS (Arm IHI 0079) ocelus in the lite discipline (amba TASK-044)
//
// Documentation: docs/markdown/rtl-amba/monitor/cxs_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-15
//
// ============================================================================
// A CXS link has no READY and no transactions: flits move on credits, packets
// are delimited inside flits by CXSCNTL, and the link is brought up and down
// by a four-phase ACTIVEREQ/ACTIVEACK handshake. axis_monitor_lite watches a
// valid/ready stream and does not fit; this block watches what a CXS endpoint
// actually does and emits it as the stream packet classes (Credit, Channel,
// Stream) plus Error / Timeout / Completion, tagged PROTOCOL_CXS with the
// ocelus_cxs_pkg event codes. The delivery contract is axis_monitor_lite's,
// unchanged: events decided and REGISTERED, up to two queued per cycle, a
// 4-deep unreset output queue, drop-and-count with the count reported as
// Error/EVENT_DROPPED into an empty queue, microsecond timeouts, `clear`.
//
// What it taps (all inputs; it drives nothing). The owner rule for monitors
// -- tap the FUB side, never the external bus I/O, for timing -- holds:
//   - the endpoint's FUB handshake (fub_valid / fub_ready and the flit's
//     CXSCNTL and stream fields), for packets, streams and backpressure;
//   - the endpoint's REGISTERED status outputs (link_state, credits,
//     credit_starved, protocol_error, parity_error), for everything that
//     only exists on the link. None of those is a raw pin.
//
// Events (priority when several fire in one cycle, highest first):
//   Error/PROTOCOL         protocol_error rose (the endpoint's sticky flag)
//   Error/PARITY           parity_error rose
//   Error/ENDERROR         a flit ended packets with ENDERROR
//   Timeout/CREDIT         credit_starved held cfg_timeout_cnt microseconds
//   Timeout/LINK           ACTIVATE or DEACTIVATE held cfg_timeout_cnt us
//   Timeout/PACKET         a packet open with no flit for cfg_timeout_cnt us
//   Completion/PACKET_END  a flit that ends one or more packets
//   Credit/STARVED         credit_starved held cfg_stall_threshold CYCLES
//   Credit/BACKPRESSURE    fub_valid without fub_ready for cfg_stall_threshold
//   Channel/STREAM_CHANGE  CXSPRCLTYPE/SRCID/TGTID differ from the last flit
//   Stream/LINK_*          the link entered ACTIVATE, RUN, DEACTIVATE, STOP
// Each timeout and credit event reports once per episode.
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module cxs_monitor_lite
    import ocelus_common_pkg::*;
    import ocelus_cxs_pkg::*;
    import cxs_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID              = 8'h0A,
    parameter logic [15:0] AGENT_ID             = 16'h00C0,
    // The interface the tapped endpoint was built with (sizes the CXSCNTL decode)
    parameter int          CXS_DATA_WIDTH       = 256,
    parameter int          CXS_MAX_PKT_PER_FLIT = 2,
    parameter int          CXS_START_ALIGN      = 16,
    parameter int          CXS_SRCID_WIDTH      = 0,
    parameter int          CXS_TGTID_WIDTH      = 0,
    parameter int          CXS_MAX_CREDIT       = 15,
    parameter int          CXS_STREAM_PRCL_BITS  = 0,  // per-stream packet tracking key, as the endpoint's
    parameter int          CXS_STREAM_SRCID_BITS = 0,
    parameter int          CXS_STREAM_TGTID_BITS = 0,
    parameter int          AGE_WIDTH            = 16,   // microsecond age (cfg_timeout_cnt is 16 bits)
    parameter int          OUT_DEPTH            = 4,    // output queue entries, two interleaved gaxi_fifo_sync banks, any depth >= 1
    parameter int          CFI_MIN_FREQ_MHZ     = 5,
    parameter int          CFI_MAX_FREQ_MHZ     = 220,
    parameter int          CFI_NUM_FREQ_ENTRIES = 16,
    parameter int          CFI_FREQ_STRATEGY    = 0,
    // Short params (do not override)
    parameter int          N        = CXS_MAX_PKT_PER_FLIT,
    parameter int          CNTL_W   = cntl_width(N, CXS_DATA_WIDTH, CXS_START_ALIGN),
    parameter int          CNTL_PW  = port_w(CNTL_W),
    parameter int          SRCID_PW = port_w(CXS_SRCID_WIDTH),
    parameter int          TGTID_PW = port_w(CXS_TGTID_WIDTH),
    parameter int          CRW      = $clog2(CXS_MAX_CREDIT + 1),
    parameter int          SELW     = (CFI_NUM_FREQ_ENTRIES > 1) ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,          // synchronous: forget open packets/episodes, zero the counters. Legal only while idle (as axis_monitor_lite)

    input  monbus_timestamp_t     i_mon_time,

    // The FUB handshake, tapped
    input  logic                  fub_valid,
    input  logic                  fub_ready,
    input  logic [CNTL_PW-1:0]    fub_cntl,
    input  logic [2:0]            fub_prcltype,
    input  logic [SRCID_PW-1:0]   fub_srcid,
    input  logic [TGTID_PW-1:0]   fub_tgtid,

    // The endpoint's registered status
    input  logic [1:0]            link_state,     // {ACTIVEREQ, ACTIVEACK}: 00 STOP 10 ACTIVATE 11 RUN 01 DEACTIVATE
    input  logic [CRW-1:0]        credits,        // held (TX) / outstanding (RX)
    input  logic                  credit_starved,
    input  logic                  protocol_error, // sticky
    input  logic                  parity_error,   // sticky

    // Configuration (cfg_timeout_cnt in MICROSECONDS, 16'hFFFF = never)
    input  logic [SELW-1:0]       cfg_freq_sel,
    input  logic [15:0]           cfg_timeout_cnt,
    input  logic                  cfg_error_enable,
    input  logic                  cfg_timeout_enable,
    input  logic                  cfg_compl_enable,
    input  logic                  cfg_credit_enable,
    input  logic                  cfg_channel_enable,
    input  logic                  cfg_stream_enable,
    input  logic [31:0]           cfg_stall_threshold,   // CYCLES; 0 = Credit events off
    input  logic [15:0]           cfg_cxs_pkt_mask,      // bit[type] = 1 drops that packet type

    // Ocelus bus
    output logic                  monbus_valid,
    input  logic                  monbus_ready,
    output monitor_packet_t       monbus_packet,
    output monbus_timestamp_t     monbus_timestamp,

    // Status
    output logic                  busy,
    output logic [31:0]           packet_count,   // packets ended on the FUB side
    output logic [31:0]           flit_count,     // flits accepted on the FUB side
    output logic [15:0]           error_count,    // error packets emitted (drop reports excluded)
    output logic [15:0]           dropped_count   // events lost since the last report
);

    // ------------------------------------------------------------------
    // The tap, this cycle
    // ------------------------------------------------------------------
    wire w_flit = fub_valid && fub_ready;
    wire w_bp   = fub_valid && !fub_ready;

    logic [2:0] w_ends, w_enderrs;
    if (N > 1) begin : g_cntl
        assign w_ends    = 3'($countones(fub_cntl[end_lsb(N, CXS_DATA_WIDTH, CXS_START_ALIGN) +: N]));
        assign w_enderrs = 3'($countones(fub_cntl[enderror_lsb(N, CXS_DATA_WIDTH, CXS_START_ALIGN) +: N]));
    end else begin : g_lite
        assign w_ends    = 3'd1;                  // CXS-Lite: every flit is one whole packet
        assign w_enderrs = 3'd0;
    end

    // Stream identity of a flit (2.5.2): protocol type, source and target ID
    wire [23:0] w_stream = {8'(fub_prcltype), 8'(fub_srcid), 8'(fub_tgtid)};

    // Packet-open state per stream, keyed like the endpoint's tracker; the
    // lite's per-packet flit count (PACKET timeout data) stays link-wide.
    localparam int SKEY_W  = CXS_STREAM_PRCL_BITS + CXS_STREAM_SRCID_BITS + CXS_STREAM_TGTID_BITS;
    localparam int SKEY_PW = (SKEY_W > 0) ? SKEY_W : 1;
    logic [SKEY_PW-1:0] w_stream_key;
    cxs_stream_key #(
        .PRCL_BITS  (CXS_STREAM_PRCL_BITS),
        .SRCID_BITS (CXS_STREAM_SRCID_BITS),
        .TGTID_BITS (CXS_STREAM_TGTID_BITS),
        .SRCID_PW   (SRCID_PW),
        .TGTID_PW   (TGTID_PW)
    ) u_stream_key (
        .i_prcltype (fub_prcltype),
        .i_srcid    (fub_srcid),
        .i_tgtid    (fub_tgtid),
        .o_key      (w_stream_key)
    );

    logic w_in_packet;
    /* verilator lint_off PINCONNECTEMPTY */
    cxs_cntl_track #(
        .N            (N),
        .CNTL_W       (CNTL_W),
        .END_LSB      (end_lsb(N, CXS_DATA_WIDTH, CXS_START_ALIGN)),
        .ENDERROR_LSB (enderror_lsb(N, CXS_DATA_WIDTH, CXS_START_ALIGN)),
        .KEY_W        (SKEY_W)
    ) u_track (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .i_valid     (w_flit && !clear),
        .i_cntl      (fub_cntl),
        .i_key       (w_stream_key),
        .o_in_packet (w_in_packet),
        .o_cntl_err  ()            // the endpoint's protocol_error already reports it
    );
    /* verilator lint_on PINCONNECTEMPTY */

    // ------------------------------------------------------------------
    // Time
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
    // State
    // ------------------------------------------------------------------
    logic [31:0]          r_flits, r_pkts, r_pkt_flits;     // totals; flits in the open packet
    logic [23:0]          r_prev_stream;
    logic                 r_have_prev;                      // a flit has been seen since reset/clear
    logic [1:0]           r_link;                           // link_state last cycle
    logic                 r_proto_q, r_parity_q;            // sticky flags last cycle
    logic [31:0]          r_starve_cycles, r_bp_cycles;
    logic [AGE_WIDTH-1:0] r_starve_stamp, r_link_stamp, r_flit_stamp;
    logic                 r_tmo_credit_fired, r_tmo_link_fired, r_tmo_pkt_fired;
    logic                 r_starve_fired, r_bp_fired;

    wire w_never     = (cfg_timeout_cnt == 16'hFFFF);
    wire w_transient = (link_state == 2'b10) || (link_state == 2'b01);
    wire [AGE_WIDTH-1:0] w_starve_age = r_us - r_starve_stamp;
    wire [AGE_WIDTH-1:0] w_link_age   = r_us - r_link_stamp;
    wire [AGE_WIDTH-1:0] w_flit_age   = r_us - r_flit_stamp;
    wire [AGE_WIDTH-1:0] w_tmo        = cfg_timeout_cnt[AGE_WIDTH-1:0];

    // ------------------------------------------------------------------
    // Candidates, each gated by its class enable and the type mask
    // ------------------------------------------------------------------
    function automatic logic type_allowed(input logic [3:0] t);
        return !cfg_cxs_pkt_mask[t];
    endfunction

    wire w_en_err    = cfg_error_enable   && type_allowed(PktTypeError);
    wire w_en_tmo    = cfg_timeout_enable && !w_never && type_allowed(PktTypeTimeout);
    wire w_en_compl  = cfg_compl_enable   && type_allowed(PktTypeCompletion);
    wire w_en_credit = cfg_credit_enable  && (cfg_stall_threshold != 32'd0) && type_allowed(PktTypeCredit);
    wire w_en_chan   = cfg_channel_enable && type_allowed(PktTypeChannel);
    wire w_en_stream = cfg_stream_enable  && type_allowed(PktTypeStream);

    wire w_err_proto  = w_en_err && protocol_error && !r_proto_q;
    wire w_err_parity = w_en_err && parity_error   && !r_parity_q;
    wire w_err_enderr = w_en_err && w_flit && (w_enderrs != 3'd0);

    // r_starve_cycles != 0: the episode's stamp is written on its FIRST
    // cycle, so in that cycle w_starve_age still measures from the previous
    // episode -- a one-cycle starvation 2 us after the last one fired a false
    // timeout (seen with a one-credit receiver, where every flit starves for a
    // cycle). The AXIS lite guards its stall timeout the same way (r_valid_pend).
    wire w_tmo_credit = w_en_tmo && credit_starved && (r_starve_cycles != 32'd0) &&
                        (w_starve_age >= w_tmo) && !r_tmo_credit_fired;
    wire w_tmo_link   = w_en_tmo && w_transient && (link_state == r_link) &&
                        (w_link_age >= w_tmo) && !r_tmo_link_fired;
    wire w_tmo_pkt    = w_en_tmo && w_in_packet && !w_flit && (w_flit_age >= w_tmo) && !r_tmo_pkt_fired;

    wire w_compl      = w_en_compl && w_flit && (w_ends != 3'd0);

    wire w_starved    = w_en_credit && credit_starved && (r_starve_cycles >= cfg_stall_threshold) && !r_starve_fired;
    wire w_backpress  = w_en_credit && w_bp && (r_bp_cycles >= cfg_stall_threshold) && !r_bp_fired;

    wire w_chan       = w_en_chan && w_flit && r_have_prev && (w_stream != r_prev_stream);
    wire w_link_evt   = w_en_stream && (link_state != r_link);

    localparam int NC = 11;
    logic [NC-1:0] w_cand;      // MSB is the highest priority
    assign w_cand = {w_err_proto, w_err_parity, w_err_enderr, w_tmo_credit, w_tmo_link, w_tmo_pkt,
                     w_compl, w_starved, w_backpress, w_chan, w_link_evt};

    typedef struct packed {
        logic [3:0]  ptype;
        logic [7:0]  code;
        logic [8:0]  chan;
        logic [63:0] data;
    } cxs_entry_t;

    function automatic logic [3:0] first_idx(input logic [NC-1:0] c);
        logic [3:0] r;
        r = '0;
        for (int i = 0; i < NC; i++) if (c[i]) r = 4'(i);
        return r;
    endfunction

    // ------------------------------------------------------------------
    // Event stage: candidates and their payload sources, registered
    // ------------------------------------------------------------------
    logic [NC-1:0] r_e_cand;
    logic [23:0]   r_e_stream, r_e_prev_stream;
    logic [2:0]    r_e_ends, r_e_enderrs;
    logic [1:0]    r_e_link, r_e_prev_link;
    logic [15:0]   r_e_credits;
    logic [31:0]   r_e_flits, r_e_pkts, r_e_pkt_flits, r_e_starve, r_e_bp;
    logic [15:0]   r_e_starve_age, r_e_link_age, r_e_flit_age;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_e_cand <= '0; r_e_stream <= '0; r_e_prev_stream <= '0; r_e_ends <= '0; r_e_enderrs <= '0;
            r_e_link <= '0; r_e_prev_link <= '0; r_e_credits <= '0; r_e_flits <= '0; r_e_pkts <= '0;
            r_e_pkt_flits <= '0; r_e_starve <= '0; r_e_bp <= '0;
            r_e_starve_age <= '0; r_e_link_age <= '0; r_e_flit_age <= '0;
        end else begin
            r_e_cand        <= clear ? '0 : w_cand;
            r_e_stream      <= w_stream;
            r_e_prev_stream <= r_prev_stream;
            r_e_ends        <= w_ends;
            r_e_enderrs     <= w_enderrs;
            r_e_link        <= link_state;
            r_e_prev_link   <= r_link;
            r_e_credits     <= 16'(credits);
            r_e_flits       <= r_flits + 32'(w_flit);
            r_e_pkts        <= r_pkts + 32'(w_flit ? w_ends : 3'd0);
            r_e_pkt_flits   <= r_pkt_flits;
            r_e_starve      <= r_starve_cycles;
            r_e_bp          <= r_bp_cycles;
            r_e_starve_age  <= 16'(w_starve_age);
            r_e_link_age    <= 16'(w_link_age);
            r_e_flit_age    <= 16'(w_flit_age);
        end
    )

    function automatic cxs_entry_t cand_entry(input logic [3:0] idx);
        cxs_entry_t e;
        e = '{ptype: PktTypeError, code: 8'h00, chan: 9'h0, data: 64'h0};
        case (idx)
            4'd10: begin e.ptype = PktTypeError;      e.code = 8'(CXS_ERR_PROTOCOL);
                         e.data = {r_e_credits, 14'h0, r_e_link, r_e_flits}; end
            4'd9:  begin e.ptype = PktTypeError;      e.code = 8'(CXS_ERR_PARITY);
                         e.data = {r_e_credits, 14'h0, r_e_link, r_e_flits}; end
            4'd8:  begin e.ptype = PktTypeError;      e.code = 8'(CXS_ERR_ENDERROR);
                         e.chan = {r_e_stream[18:16], r_e_stream[5:0]};
                         e.data = {8'(r_e_enderrs), 8'(r_e_ends), 16'h0, r_e_pkts}; end
            4'd7:  begin e.ptype = PktTypeTimeout;    e.code = 8'(CXS_TIMEOUT_CREDIT);
                         e.data = {r_e_starve, r_e_starve_age, cfg_timeout_cnt}; end
            4'd6:  begin e.ptype = PktTypeTimeout;    e.code = 8'(CXS_TIMEOUT_LINK);
                         e.data = {r_e_credits, 14'h0, r_e_link, r_e_link_age, cfg_timeout_cnt}; end
            4'd5:  begin e.ptype = PktTypeTimeout;    e.code = 8'(CXS_TIMEOUT_PACKET);
                         e.data = {r_e_pkt_flits, r_e_flit_age, cfg_timeout_cnt}; end
            4'd4:  begin e.ptype = PktTypeCompletion; e.code = 8'(CXS_COMPL_PACKET_END);
                         e.chan = {r_e_stream[18:16], r_e_stream[5:0]};
                         e.data = {r_e_stream, 8'(r_e_ends), r_e_pkts}; end
            4'd3:  begin e.ptype = PktTypeCredit;     e.code = 8'(CXS_CREDIT_STARVED);
                         e.data = {r_e_starve, cfg_stall_threshold}; end
            4'd2:  begin e.ptype = PktTypeCredit;     e.code = 8'(CXS_CREDIT_BACKPRESSURE);
                         e.data = {r_e_bp, cfg_stall_threshold}; end
            4'd1:  begin e.ptype = PktTypeChannel;    e.code = 8'(CXS_CHAN_STREAM_CHANGE);
                         e.chan = {r_e_stream[18:16], r_e_stream[5:0]};
                         e.data = {r_e_prev_stream, 8'h0, r_e_stream, 8'h0}; end
            default: begin
                         e.ptype = PktTypeStream;
                         case (r_e_link)
                             2'b10:   e.code = 8'(CXS_STREAM_LINK_ACTIVATE);
                             2'b11:   e.code = 8'(CXS_STREAM_LINK_UP);
                             2'b01:   e.code = 8'(CXS_STREAM_LINK_DEACTIVATE);
                             default: e.code = 8'(CXS_STREAM_LINK_DOWN);
                         endcase
                         e.data = {r_e_credits, 14'h0, r_e_prev_link, r_e_flits};
                     end
        endcase
        return e;
    endfunction

    logic [NC-1:0] w_cand2;
    logic [3:0]    w_i1, w_i2;
    logic          w_fire1, w_fire2;
    logic [3:0]    w_ev_n;
    assign w_i1    = first_idx(r_e_cand);
    assign w_cand2 = r_e_cand & ~(NC'(1) << w_i1);
    assign w_i2    = first_idx(w_cand2);
    assign w_fire1 = (|r_e_cand) && !clear;
    assign w_fire2 = (|w_cand2)  && !clear;
    assign w_ev_n  = clear ? 4'd0 : 4'($countones(r_e_cand));
    cxs_entry_t w_e1, w_e2;
    assign w_e1 = cand_entry(w_i1);
    assign w_e2 = cand_entry(w_i2);

    // ------------------------------------------------------------------
    // Tracking state
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_flits <= '0; r_pkts <= '0; r_pkt_flits <= '0; r_prev_stream <= '0; r_have_prev <= 1'b0;
            r_link <= 2'b00; r_proto_q <= 1'b0; r_parity_q <= 1'b0;
            r_starve_cycles <= '0; r_bp_cycles <= '0;
            r_starve_stamp <= '0; r_link_stamp <= '0; r_flit_stamp <= '0;
            r_tmo_credit_fired <= 1'b0; r_tmo_link_fired <= 1'b0; r_tmo_pkt_fired <= 1'b0;
            r_starve_fired <= 1'b0; r_bp_fired <= 1'b0;
        end else if (clear) begin
            r_flits <= '0; r_pkts <= '0; r_pkt_flits <= '0; r_have_prev <= 1'b0;
            r_link <= link_state; r_proto_q <= protocol_error; r_parity_q <= parity_error;
            r_starve_cycles <= '0; r_bp_cycles <= '0;
            r_tmo_credit_fired <= 1'b0; r_tmo_link_fired <= 1'b0; r_tmo_pkt_fired <= 1'b0;
            r_starve_fired <= 1'b0; r_bp_fired <= 1'b0;
        end else begin
            r_proto_q  <= protocol_error;
            r_parity_q <= parity_error;
            // flits and packets
            if (w_flit) begin
                r_flits         <= r_flits + 32'd1;
                r_pkts          <= r_pkts + 32'(w_ends);
                r_prev_stream   <= w_stream;
                r_have_prev     <= 1'b1;
                r_flit_stamp    <= r_us;
                r_tmo_pkt_fired <= 1'b0;
                r_pkt_flits     <= w_in_packet ? (r_pkt_flits + 32'd1) : 32'd1;
            end else if (w_tmo_pkt) begin
                r_tmo_pkt_fired <= 1'b1;
            end
            // link state episodes
            r_link <= link_state;
            if (link_state != r_link) begin
                r_link_stamp     <= r_us;
                r_tmo_link_fired <= 1'b0;
            end else if (w_tmo_link) begin
                r_tmo_link_fired <= 1'b1;
            end
            // credit starvation episodes
            if (credit_starved) begin
                if (r_starve_cycles == '0) r_starve_stamp <= r_us;
                if (r_starve_cycles != 32'hFFFF_FFFF) r_starve_cycles <= r_starve_cycles + 32'd1;
                if (w_tmo_credit) r_tmo_credit_fired <= 1'b1;
                if (w_starved)    r_starve_fired     <= 1'b1;
            end else begin
                r_starve_cycles    <= '0;
                r_tmo_credit_fired <= 1'b0;
                r_starve_fired     <= 1'b0;
            end
            // FUB backpressure episodes
            if (w_bp) begin
                if (r_bp_cycles != 32'hFFFF_FFFF) r_bp_cycles <= r_bp_cycles + 32'd1;
                if (w_backpress) r_bp_fired <= 1'b1;
            end else begin
                r_bp_cycles <= '0;
                r_bp_fired  <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // Output queue, drop accounting and the drop report: axis_monitor_lite's
    // structure, unchanged (see that block for the reasoning).
    // ------------------------------------------------------------------
    // The output queue: two interleaved gaxi_fifo_sync banks (unreset
    // storage, mux read). Two picks can be queued in one cycle and gaxi has
    // one write port, so entry k goes to bank k mod 2 and reads alternate:
    // the same entries in the same order as one two-write queue. r_q_count
    // is the registered occupancy and the only capacity gate, so capacity is
    // exactly OUT_DEPTH (any value >= 1); each bank holds ceil(OUT_DEPTH/2),
    // at least the 2 gaxi_fifo_sync needs, so a bank never refuses a write
    // the count admits. Gating on gaxi's own count would close a loop: in mux
    // mode it is combinational from the next-state pointers.
    localparam int OQW   = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;
    localparam int OQ_BD = ((OUT_DEPTH + 1) / 2 < 2) ? 2 : (OUT_DEPTH + 1) / 2;
    logic [OQW:0] r_q_count;
    logic         r_q_wb, r_q_rb;                         // bank the next write / read uses
    wire  [OQW:0] w_q_count = r_q_count;
    wire          w_q_empty = (w_q_count == '0);
    wire          w_room1   = (w_q_count <= (OQW+1)'(OUT_DEPTH - 1));
    wire          w_room2   = (OUT_DEPTH >= 2) && (w_q_count <= (OQW+1)'(OUT_DEPTH - 2));

    wire         w_take1    = w_fire1 && w_room1;
    wire         w_take2    = w_fire2 && w_room2;
    wire  [3:0]  w_lost     = w_ev_n - 4'(w_take1) - 4'(w_take2);
    logic [3:0]  r_lost;
    logic [15:0] r_dropped, r_errors;
    wire         w_drop_rpt = (r_dropped != 16'd0) && (r_lost == 4'd0) && !w_fire1 && w_q_empty && w_en_err && !clear;
    wire  [1:0]  w_err_take = 2'(w_take1 && (w_e1.ptype == PktTypeError)) + 2'(w_take2 && (w_e2.ptype == PktTypeError));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_lost <= '0; r_dropped <= '0; r_errors <= '0;
        end else if (clear) begin
            r_lost <= '0; r_dropped <= '0; r_errors <= '0;
        end else begin
            r_lost <= w_lost;
            if (w_drop_rpt)            r_dropped <= '0;
            else if (&r_dropped[15:4]) r_dropped <= 16'hFFFF;
            else                       r_dropped <= r_dropped + 16'(r_lost);
            if ((w_err_take != 2'd0) && (r_errors < 16'hFFFE)) r_errors <= r_errors + 16'(w_err_take);
        end
    )

    cxs_entry_t w_slot1, w_entry_out;
    assign w_slot1 = w_fire1 ? w_e1
                             : '{ptype: PktTypeError, code: 8'(CXS_ERR_EVENT_DROPPED), chan: 9'd0, data: 64'(r_dropped)};
    wire w_push1 = w_take1 || w_drop_rpt;
    wire w_push2 = w_take2;
    wire w_q_pop = monbus_valid && monbus_ready;

    // push1 (slot 1) goes to bank r_q_wb, push2 to the other; a push2 never
    // happens without a push1 (room2 implies room1, the second pick implies
    // the first, and a drop report only goes out with no live pick)
    logic [1:0]                    w_bank_wr, w_bank_rd_valid;
    logic [$bits(cxs_entry_t)-1:0]    w_bank_wr_data [2];
    logic [$bits(cxs_entry_t)-1:0]    w_bank_rd_data [2];
    assign w_entry_out = cxs_entry_t'(w_bank_rd_data[r_q_rb]);
    for (genvar b = 0; b < 2; b++) begin : g_bank
        wire w_mine1 = (r_q_wb == 1'(b));
        assign w_bank_wr[b]      = w_mine1 ? w_push1 : w_push2;
        assign w_bank_wr_data[b] = w_mine1 ? w_slot1 : w_e2;
        gaxi_fifo_sync #(
            .REGISTERED (0),
            .DATA_WIDTH ($bits(cxs_entry_t)),
            .DEPTH      (OQ_BD)
        ) u_out_q (
            .axi_aclk    (aclk),
            .axi_aresetn (aresetn),
            .wr_valid    (w_bank_wr[b]),
            /* verilator lint_off PINCONNECTEMPTY */
            .wr_ready    (),
            .count       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .wr_data     (w_bank_wr_data[b]),
            .rd_ready    (w_q_pop && (r_q_rb == 1'(b))),
            .rd_valid    (w_bank_rd_valid[b]),
            .rd_data     (w_bank_rd_data[b])
        );
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_bank_rd_valid = ^w_bank_rd_valid;   // r_q_count is the occupancy; a bank is non-empty whenever it says so
    /* verilator lint_on UNUSEDSIGNAL */

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_q_count <= '0; r_q_wb <= 1'b0; r_q_rb <= 1'b0;
        end else begin
            r_q_count <= r_q_count + (OQW+1)'(w_push1) + (OQW+1)'(w_push2) - (OQW+1)'(w_q_pop);
            r_q_wb    <= r_q_wb ^ (w_push1 ^ w_push2);
            if (w_q_pop) r_q_rb <= !r_q_rb;
        end
    )

    assign monbus_valid     = !w_q_empty;
    assign monbus_packet    = create_monitor_packet(w_entry_out.ptype, PROTOCOL_CXS, w_entry_out.code,
                                                    w_entry_out.chan, UNIT_ID, AGENT_ID, w_entry_out.data);
    assign monbus_timestamp = i_mon_time;

    assign busy          = w_in_packet || credit_starved || w_bp || w_transient ||
                           (|r_e_cand) || (r_lost != 4'd0) || monbus_valid;
    assign packet_count  = r_pkts;
    assign flit_count    = r_flits;
    assign error_count   = r_errors;
    assign dropped_count = r_dropped;

endmodule : cxs_monitor_lite
