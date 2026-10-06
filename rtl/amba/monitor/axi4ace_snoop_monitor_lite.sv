// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4ace_snoop_monitor_lite
// Purpose: ACE snoop-channel lite monitor (AC/CR/CD) for cache-ip.
//
// Documentation: docs/markdown/rtl-amba/monitor/axi4ace_snoop_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-05
//
// ============================================================================
// ACE adds three snoop channels that do NOT fit axi_monitor_lite:
//   AC  -- snoop address/command (no ID, no LEN):  ACADDR, ACSNOOP, ACPROT
//   CR  -- snoop response            :  CRRESP
//   CD  -- snoop data                :  CDDATA, CDLAST
//
// This monitor tracks outstanding snoops in AC-issue order.  CR and CDLAST
// are correlated with the OLDEST outstanding snoop, matching ACE's per-channel
// ordering rules.  Multiple outstanding snoops are allowed.
//
// Packet encoding (all packets carry protocol = PROTOCOL_AXI):
//   Completion (PktTypeCompletion):
//     event_code = {CRRESP[3:0], ACSNOOP[3:0]}
//     channel_id = CDLAST beat count for this snoop (saturated to 9 bits).
//                  The snoop type is already in event_code.
//     event_data = {latency[15:0], ACADDR[AW-1:0]}
//                  latency (cycles) occupies [63:48]; AC address [AW-1:0].
//                  For AW > 48 the top address bits share event_data[63:48]
//                  with latency, the same trade-off axi_monitor_lite makes.
//     latency    = i_mon_time - AC handshake i_mon_time (cycles)
//   Error (PktTypeError):
//     CRRESP[1] (Error) set           -> AXI_ERR_PROTOCOL
//     CR handshake with no AC pending -> AXI_ERR_RESP_ORPHAN
//     CDLAST handshake with no AC     -> AXI_ERR_DATA_ORPHAN
//   Timeout (PktTypeTimeout):
//     head entry older than cfg_timeout_cycles us -> AXI_TIMEOUT_RESP
//
// Event precedence on the monbus (same as axi_monitor_lite):
//   ERROR > TIMEOUT > COMPLETION.
// When CRRESP[1] is set and cfg_error_enable is high, an ERROR packet is
// emitted and the COMPLETION packet is suppressed for that snoop.
//
// The monitor never stalls the observed channels.  Events that cannot be
// queued are dropped and counted; the count is emitted as an
// AXI_ERR_EVENT_DROPPED packet when the queue has room and nothing else
// wants the bus.  A snoop that arrives when the table is full is counted
// (refused) and left untracked; any later CR/CD for it reports as an orphan.
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

// Existing shared packages contain unused helper constants/functions that are
// not touched by this module; suppress the resulting warnings locally so the
// lint report stays clean for this new file.
/* verilator lint_off UNUSEDPARAM */
/* verilator lint_off UNUSEDSIGNAL */

module axi4ace_snoop_monitor_lite
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID          = 8'h01,
    parameter logic [15:0] AGENT_ID         = 16'h000A,
    parameter int          MAX_SNOOPS       = 8,      // outstanding-snoop table depth
    parameter int          OUT_DEPTH        = 4,      // monbus output queue, a power of two
    parameter int          ACLK_MHZ         = 100,
    parameter int          CFI_MIN_FREQ_MHZ = ACLK_MHZ,
    parameter int          CFI_MAX_FREQ_MHZ = ACLK_MHZ,
    parameter int          CFI_NUM_FREQ_ENTRIES = 16,
    parameter int          CFI_FREQ_STRATEGY    = 0,
    parameter int          ADDR_WIDTH       = 32,
    parameter int          DATA_WIDTH       = 32,
    // Short params (do not override)
    parameter int          AW               = ADDR_WIDTH,
    parameter int          DW               = DATA_WIDTH,
    parameter int          N                = MAX_SNOOPS,
    parameter int          SW               = (N > 1) ? $clog2(N) : 1,
    parameter int          CW               = $clog2(N + 1),
    parameter int          SELW             = (CFI_NUM_FREQ_ENTRIES > 1) ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1,
    parameter int          TS_WIDTH         = 16,
    parameter int          AGE_WIDTH        = 16
)
(
    input  logic                       aclk,
    input  logic                       aresetn,
    input  logic                       clear,               // sync clear; also driven by ~cfg_monitor_enable

    input  monbus_timestamp_t          i_mon_time,

    input  logic                       cfg_monitor_enable,
    input  logic                       cfg_error_enable,
    input  logic                       cfg_compl_enable,
    input  logic                       cfg_timeout_enable,
    input  logic [15:0]                cfg_timeout_cycles,  // microseconds at full width, 0 = never
    input  logic [SELW-1:0]            cfg_freq_sel,

    output logic                       monbus_valid,
    input  logic                       monbus_ready,
    output monitor_packet_t            monbus_packet,
    output monbus_timestamp_t          monbus_timestamp,

    output logic [7:0]                 active_transactions,
    output logic [15:0]                error_count,
    output logic [31:0]                transaction_count,
    output logic [15:0]                dropped_count,

    // AC observation taps (manager -> cache / CCU -> peer)
    input  logic [AW-1:0]              ac_addr,
    input  logic [3:0]                 ac_snoop,
    input  logic                       ac_valid,
    input  logic                       ac_ready,

    // CR observation taps
    input  logic [4:0]                 cr_resp,
    input  logic                       cr_valid,
    input  logic                       cr_ready,

    // CD observation taps
    input  logic                       cd_last,
    input  logic                       cd_valid,
    input  logic                       cd_ready
);

    // ------------------------------------------------------------------
    // Gating and handshakes: the monitor NEVER drives these channels.
    // ------------------------------------------------------------------
    wire        w_ac_hs = ac_valid  && ac_ready  && cfg_monitor_enable;
    wire        w_cr_hs = cr_valid  && cr_ready  && cfg_monitor_enable;
    wire        w_cd_hs = cd_valid  && cd_ready  && cd_last && cfg_monitor_enable;

    // ------------------------------------------------------------------
    // Time: internal cycle counter for latency, frequency-invariant us tick
    // for timeout.
    // ------------------------------------------------------------------
    logic [AGE_WIDTH-1:0] r_us;
    logic                 w_tick;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_us  <= '0;
        end else begin
            if (w_tick) r_us <= r_us + 1'b1;
        end
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
    // Outstanding-snoop table: a circular FIFO in AC-issue order.
    // r_rd_ptr -> oldest, r_wr_ptr -> next free tail.
    // ------------------------------------------------------------------
    logic [N-1:0]                r_valid;
    logic [N-1:0][AW-1:0]        r_addr;
    logic [N-1:0][3:0]           r_snoop;
    logic [N-1:0][15:0]          r_beats;   // CDLAST beats seen for this snoop
    logic [N-1:0]                r_tmo;     // timeout already reported
    logic [N-1:0][TS_WIDTH-1:0]  r_ts0;     // i_mon_time at AC handshake
    logic [N-1:0][AGE_WIDTH-1:0] r_us0;     // r_us at last progress / AC

    logic [SW-1:0] r_wr_ptr;
    logic [SW-1:0] r_rd_ptr;
    logic [CW-1:0] r_count;

    wire        w_full  = (r_count == CW'(N));
    wire        w_empty = (r_count == '0);
    wire [SW-1:0] w_head = r_rd_ptr;
    wire [SW-1:0] w_tail = r_wr_ptr;

    wire        w_alloc   = w_ac_hs && !w_full;
    wire        w_refused = w_ac_hs && w_full;

    // CR is correlated with the oldest outstanding snoop.
    wire        w_cr_hit = w_cr_hs && !w_empty;

    // CDLAST is also attributed to the oldest outstanding snoop.
    wire        w_cd_hit = w_cd_hs && !w_empty;

    // Timeout: only the head can age out, preserving order.  A handshake on
    // the head resets its progress stamp, so suppress timeout in the same
    // cycle a response or data beat arrives.
    wire [AGE_WIDTH-1:0] w_head_age = r_us - r_us0[w_head];
    wire                 w_never    = (cfg_timeout_cycles == 16'hFFFF);
    wire [AGE_WIDTH-1:0] w_tmo_lim  = (cfg_timeout_cycles == 16'h0) ? 16'hFFFF : cfg_timeout_cycles[AGE_WIDTH-1:0];
    wire                 w_tmo_head  = cfg_timeout_enable && !w_never && !w_empty &&
                                       r_valid[w_head] && !r_tmo[w_head] &&
                                       (w_head_age >= w_tmo_lim) &&
                                       !w_cr_hs && !w_cd_hs;

    // Completion is a CR that matches a live entry and is not promoted to error.
    wire        w_cr_err     = w_cr_hit && cr_resp[1];
    wire        w_compl_fire = w_cr_hit && (!w_cr_err || !cfg_error_enable) && cfg_compl_enable;

    // Latency and beat count for the completion payload.
    wire [TS_WIDTH-1:0] w_latency          = TS_WIDTH'(i_mon_time) - r_ts0[w_head];
    wire [15:0]         w_head_beats_plus  = r_beats[w_head] + 16'(w_cd_hit);

    // ------------------------------------------------------------------
    // Table update
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_valid   <= '0;
            r_addr    <= '0;
            r_snoop   <= '0;
            r_beats   <= '0;
            r_tmo     <= '0;
            r_ts0     <= '0;
            r_us0     <= '0;
            r_wr_ptr  <= '0;
            r_rd_ptr  <= '0;
            r_count   <= '0;
        end else if (clear) begin
            r_valid   <= '0;
            r_tmo     <= '0;
            r_wr_ptr  <= '0;
            r_rd_ptr  <= '0;
            r_count   <= '0;
        end else begin
            // allocate a new snoop at the tail
            if (w_alloc) begin
                r_valid[w_tail] <= 1'b1;
                r_addr[w_tail]  <= ac_addr;
                r_snoop[w_tail] <= ac_snoop;
                r_beats[w_tail] <= 16'd0;
                r_tmo[w_tail]   <= 1'b0;
                r_ts0[w_tail]   <= TS_WIDTH'(i_mon_time);
                r_us0[w_tail]   <= r_us;
            end

            // CDLAST on the head: count a data beat and record progress
            if (w_cd_hit) begin
                r_beats[w_head] <= r_beats[w_head] + 16'd1;
                r_us0[w_head]   <= r_us;
            end

            // Free the head on CR completion or timeout
            if (w_compl_fire || w_tmo_head) begin
                r_valid[w_head] <= 1'b0;
                r_tmo[w_head]   <= 1'b0;
                r_rd_ptr        <= (r_rd_ptr == SW'(N-1)) ? '0 : r_rd_ptr + 1'b1;
            end

            // pointer/count bookkeeping for allocate+free combinations
            case ({w_alloc, (w_compl_fire || w_tmo_head)})
                2'b10: r_count <= r_count + 1'b1;
                2'b01: r_count <= r_count - 1'b1;
                default: ;
            endcase

            if (w_alloc) begin
                r_wr_ptr <= (r_wr_ptr == SW'(N-1)) ? '0 : r_wr_ptr + 1'b1;
            end

            // mark timeout reported so we do not repeat it
            if (w_tmo_head) r_tmo[w_head] <= 1'b1;
        end
    )

    // ------------------------------------------------------------------
    // Event selection: at most one packet is generated per cycle.
    // Priority: ERROR > TIMEOUT > COMPLETION.
    // ------------------------------------------------------------------
    wire        w_err_en  = cfg_error_enable;
    wire        w_tmo_en  = cfg_timeout_enable;
    wire        w_cmp_en  = cfg_compl_enable;

    logic          w_evt_v;
    logic [3:0]    w_evt_type;
    logic [7:0]    w_evt_code;
    logic [8:0]    w_evt_chan;
    logic [AW-1:0] w_evt_addr;
    logic [15:0]   w_evt_hi;

    always_comb begin
        w_evt_v    = 1'b0;
        w_evt_type = '0;
        w_evt_code = '0;
        w_evt_chan = '0;
        w_evt_addr = '0;
        w_evt_hi   = '0;

        if (w_err_en) begin
            if (w_cr_err) begin
                w_evt_v    = 1'b1;
                w_evt_type = PktTypeError;
                w_evt_code = AXI_ERR_PROTOCOL;
                w_evt_chan = {5'b0, r_snoop[w_head]};
                w_evt_addr = r_addr[w_head];
            end else if (w_cr_hs && !w_cr_hit) begin
                w_evt_v    = 1'b1;
                w_evt_type = PktTypeError;
                w_evt_code = AXI_ERR_RESP_ORPHAN;
                w_evt_addr = ac_addr;   // best effort: the AC bus at this cycle
            end else if (w_cd_hs && !w_cd_hit) begin
                w_evt_v    = 1'b1;
                w_evt_type = PktTypeError;
                w_evt_code = AXI_ERR_DATA_ORPHAN;
                w_evt_addr = ac_addr;
            end
        end

        if (!w_evt_v && w_tmo_en && w_tmo_head) begin
            w_evt_v    = 1'b1;
            w_evt_type = PktTypeTimeout;
            w_evt_code = AXI_TIMEOUT_RESP;
            w_evt_chan = {5'b0, r_snoop[w_head]};
            w_evt_addr = r_addr[w_head];
        end

        if (!w_evt_v && w_cmp_en && w_compl_fire) begin
            w_evt_v    = 1'b1;
            w_evt_type = PktTypeCompletion;
            w_evt_code = {cr_resp[3:0], r_snoop[w_head]};
            w_evt_chan = w_head_beats_plus[8:0];
            w_evt_addr = r_addr[w_head];
            w_evt_hi   = 16'(w_latency);
        end
    end

    // ------------------------------------------------------------------
    // Counters
    // ------------------------------------------------------------------
    logic [15:0] r_dropped;
    logic [15:0] r_refused;
    logic [15:0] r_completed;
    logic [15:0] r_errors;

    // ------------------------------------------------------------------
    // Output queue: inline unreset array with two wrapping pointers.
    // ------------------------------------------------------------------
    typedef struct packed {
        logic [3:0]    ptype;
        logic [7:0]    code;
        logic [8:0]    chan;
        logic [15:0]   hi;
        logic [AW-1:0] addr;
    } lite_entry_t;

    localparam int OQW = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;
    logic [$bits(lite_entry_t)-1:0] r_q [OUT_DEPTH];
    logic [OQW:0] r_q_wp, r_q_rp;

    wire          w_q_empty = (r_q_wp == r_q_rp);
    wire          w_q_full  = (r_q_wp[OQW-1:0] == r_q_rp[OQW-1:0]) && (r_q_wp[OQW] != r_q_rp[OQW]);
    wire          w_wr_ready = !w_q_full;
    wire          w_take     = w_evt_v && w_wr_ready;
    wire [3:0]    w_offered  = 4'(w_evt_v);
    wire [3:0]    w_lost     = w_offered - 4'(w_take);

    // Pending drop report: emitted when the queue has room and nothing else
    // wants it.  Masked by the error packet type allow bit.
    wire w_drop_rpt = (r_dropped != 16'd0) && !w_evt_v && w_wr_ready && w_err_en;

    lite_entry_t w_entry_in, w_entry_out;
    always_comb begin
        if (w_evt_v)
            w_entry_in = '{ptype: w_evt_type, code: w_evt_code, chan: w_evt_chan,
                           hi: w_evt_hi, addr: w_evt_addr};
        else
            w_entry_in = '{ptype: PktTypeError, code: AXI_ERR_EVENT_DROPPED,
                           chan: 9'd0, hi: 16'd0, addr: AW'(r_dropped)};
    end

    always_ff @(posedge aclk) begin
        if (w_take || w_drop_rpt) r_q[r_q_wp[OQW-1:0]] <= w_entry_in;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_q_wp <= '0;
            r_q_rp <= '0;
        end else begin
            if (w_take || w_drop_rpt) r_q_wp <= r_q_wp + 1'b1;
            if (w_q_pop)              r_q_rp <= r_q_rp + 1'b1;
        end
    )

    assign w_entry_out = r_q[r_q_rp[OQW-1:0]];

    // Source hold: once a packet is presented to the monbus it stays stable
    // until the consumer takes it.
    logic r_presented;
    lite_entry_t r_present_entry;

    wire w_q_valid = !w_q_empty;
    wire w_present_take = (w_q_valid || w_drop_rpt) && !r_presented;
    wire w_q_pop = r_presented ? (monbus_valid && monbus_ready)
                               : (w_q_valid && !(w_drop_rpt && !w_q_valid));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_presented <= 1'b0;
            r_present_entry <= '0;
        end else begin
            if (monbus_valid && monbus_ready) begin
                r_presented <= 1'b0;
            end else if (w_present_take) begin
                r_presented <= 1'b1;
                r_present_entry <= w_drop_rpt ? w_entry_in : w_entry_out;
            end
        end
    )

    lite_entry_t w_out_entry;
    assign w_out_entry = r_presented ? r_present_entry
                                     : (w_drop_rpt ? w_entry_in : w_entry_out);

    logic [63:0] w_out_data;
    always_comb begin
        w_out_data = '0;
        w_out_data[AW-1:0] = w_out_entry.addr;
        w_out_data[63:48]  = w_out_entry.hi;
    end

    monitor_packet_t w_q_packet;
    assign w_q_packet = create_monitor_packet(w_out_entry.ptype, PROTOCOL_AXI, w_out_entry.code,
                                              w_out_entry.chan, UNIT_ID, AGENT_ID, w_out_data);

    assign monbus_valid     = r_presented || w_q_valid || w_drop_rpt;
    assign monbus_packet    = w_q_packet;
    assign monbus_timestamp = i_mon_time;

    // ------------------------------------------------------------------
    // Counter updates
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_dropped   <= '0;
            r_refused   <= '0;
            r_completed <= '0;
            r_errors    <= '0;
        end else if (clear) begin
            r_dropped   <= '0;
            r_refused   <= '0;
            r_completed <= '0;
            r_errors    <= '0;
        end else begin
            if (w_drop_rpt)               r_dropped <= '0;
            else if (&r_dropped[15:4])    r_dropped <= 16'hFFFF;
            else                          r_dropped <= r_dropped + 16'(w_lost);

            if (w_refused && (r_refused != 16'hFFFF)) r_refused <= r_refused + 1'b1;
            if (w_compl_fire && (r_completed != 16'hFFFF)) r_completed <= r_completed + 1'b1;
            if ((w_evt_v && w_evt_type == PktTypeError) && (r_errors != 16'hFFFF)) r_errors <= r_errors + 1'b1;
            if (w_tmo_head && (r_errors != 16'hFFFF)) r_errors <= r_errors + 1'b1;
        end
    )

    // ------------------------------------------------------------------
    // Status outputs
    // ------------------------------------------------------------------
    assign active_transactions = 8'(r_count);
    assign error_count         = r_errors;
    assign transaction_count   = {16'h0, r_completed};
    assign dropped_count       = r_dropped;

endmodule : axi4ace_snoop_monitor_lite

/* verilator lint_on UNUSEDPARAM */
/* verilator lint_on UNUSEDSIGNAL */
