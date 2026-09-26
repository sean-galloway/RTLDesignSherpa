// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_lite
// Purpose: the AXI transaction monitor at a fifth of the gates (TASK-098).
//
// Documentation: docs/markdown/rtl-amba/monitor-lite/axi_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-25
//
// ============================================================================
// What it keeps of axi_monitor_base (the "75%"): error packets for response
// errors, orphan beats and burst-length violations, each with the
// transaction's ID and address; completion packets with latency; timeout
// packets naming the stuck phase; the active-count threshold; the same
// 128-bit monitor_packet_t + 64-bit side-band timestamp on the same monbus
// handshake, with the same UNIT/AGENT ids, so the arbiter, group, tally and
// host tooling do not know the difference.
//
// What it drops (the "25%"): performance packets and windows (axi_bus_meter
// is the perf path), debug state-change packets, the address-range checker
// and report-time address filter, the ID-range filter, the latency
// threshold, three independent per-phase timers (one "no progress"
// threshold; the phase is in the event code), the block_ready admission
// stall (the lite never touches the traffic it watches: an event it cannot
// deliver is dropped and COUNTED, and the count is reported; a command that
// finds no free slot is counted too, and its beats then surface as ORPHAN
// errors, which name it), and a table
// of data-before-address transactions (ONE early write burst is buffered
// as a beat count).
//
// Why it is small: nothing is scanned. There is one allocation port (the
// command handshake), one lookup (R or B by ID, the head of that ID's list
// -- AXI returns same-ID responses in order, so "oldest with this ID" is
// exact), and the W beats of a write follow an AW-order FIFO of slot
// indices, so they need no lookup at all. Every event is computed at the
// handshake that causes it and goes into a 4-deep queue of 66-bit event
// entries, formatted into the 128-bit packet on the way out (the full
// monitor keeps an 8-deep FIFO of the same entries plus a copy of the table).
// An entry holds stamps, not counters: a cycle stamp (latency) and a
// microsecond stamp (timeout), each a copy of a shared counter; every
// subtraction happens once after the read mux. Same-ID entries form a
// linked list in allocation order, so the beat or response for an ID goes to
// the ONE entry flagged as that list's head -- a one-hot match, no age
// compare. The events of a cycle are registered before the packet pick, so
// the attribution and the formatting are two short cycles, not one long
// one. No per-entry state machine, no CAM ports, no reporter-side table
// copy.
//
// Measured against the full monitor in the same fixture, same flow
// (bridge_1x2_rd_mon, Artix-7 100T -1, error+compl): see the module page.
// ============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module axi_monitor_lite
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID          = 8'h09,
    parameter logic [15:0] AGENT_ID         = 16'h0063,
    parameter int          MAX_TRANSACTIONS = 8,     // table slots (outstanding transactions tracked)
    parameter int          ADDR_WIDTH       = 32,
    parameter int          ID_WIDTH         = 8,     // 0 for AXI-Lite
    parameter bit          IS_READ          = 1'b1,  // 1: AR/R monitor, 0: AW/W/B monitor
    parameter bit          IS_AXI           = 1'b1,  // 0: AXI-Lite (single beat, no ID)
    parameter int          TS_WIDTH         = 16,    // cycle timestamp: ordering + latency
    parameter int          AGE_WIDTH        = 16,    // microsecond age: timeout (cfg is 16 bits)
    parameter int          OUT_DEPTH        = 4,     // output queue of event entries, a power of two; deeper absorbs longer stalls
    // Frequency-invariant microsecond tick (same knobs as axi_monitor_timer)
    parameter int          CFI_MIN_FREQ_MHZ     = 5,
    parameter int          CFI_MAX_FREQ_MHZ     = 220,
    parameter int          CFI_NUM_FREQ_ENTRIES = 16,
    parameter int          CFI_FREQ_STRATEGY    = 0,
    // Short params (do not override)
    parameter int          N   = MAX_TRANSACTIONS,
    parameter int          AW  = ADDR_WIDTH,
    parameter int          IW  = (ID_WIDTH > 0) ? ID_WIDTH : 1,
    parameter int          SW  = (N > 1) ? $clog2(N) : 1,
    parameter int          CW  = $clog2(N + 1),
    parameter int          SELW = (CFI_NUM_FREQ_ENTRIES > 1) ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,          // synchronous: empty the table, zero the counters

    // Side-band time, sampled into monbus_timestamp with every packet
    input  monbus_timestamp_t     i_mon_time,

    // Command channel tap (AR or AW)
    input  logic [AW-1:0]         cmd_addr,
    input  logic [IW-1:0]         cmd_id,
    input  logic [7:0]            cmd_len,
    input  logic                  cmd_valid,
    input  logic                  cmd_ready,

    // Data channel tap (R, or W with data_id unused)
    input  logic [IW-1:0]         data_id,
    input  logic                  data_last,
    input  logic [1:0]            data_resp,      // RRESP; wrappers tie 0 for W
    input  logic                  data_valid,
    input  logic                  data_ready,

    // Response channel tap (B; wrappers tie the R signals here on a read monitor)
    input  logic [IW-1:0]         resp_id,
    input  logic [1:0]            resp_code,
    input  logic                  resp_valid,
    input  logic                  resp_ready,

    // Configuration (the wrapper's names; cfg_timeout_cnt is in MICROSECONDS,
    // 16'hFFFF = never)
    input  logic [SELW-1:0]       cfg_freq_sel,
    input  logic [15:0]           cfg_timeout_cnt,
    input  logic                  cfg_error_enable,
    input  logic                  cfg_compl_enable,
    input  logic                  cfg_timeout_enable,
    input  logic                  cfg_threshold_enable,
    input  logic [15:0]           cfg_active_trans_threshold,
    input  logic [15:0]           cfg_axi_pkt_mask,   // bit[type] = 1 drops that packet type

    // Monitor bus
    output logic                  monbus_valid,
    input  logic                  monbus_ready,
    output monitor_packet_t       monbus_packet,
    output monbus_timestamp_t     monbus_timestamp,

    // Status
    output logic [7:0]            active_count,       // live table entries
    output logic                  busy,               // table not empty or a packet pending
    output logic [15:0]           perf_completed_count,
    output logic [15:0]           perf_error_count,
    output logic [15:0]           dropped_count,      // events lost to monbus backpressure
    output logic [15:0]           refused_count       // commands that found no free slot
);

    // ------------------------------------------------------------------
    // Handshakes (a tap is a handshake, never a valid alone)
    // ------------------------------------------------------------------
    wire cmd_hs  = cmd_valid  && cmd_ready;
    wire data_hs = data_valid && data_ready;
    wire resp_hs = resp_valid && resp_ready && !IS_READ;   // B only exists on writes

    // ------------------------------------------------------------------
    // Time. Two counters shared by every entry, so no entry counts:
    //   r_now   cycle stamp     -> latency (completion minus allocation)
    //   r_us    microsecond stamp (frequency-invariant tick) -> timeout age
    // An entry stores the value of each at the moment that matters; every
    // subtraction happens once, after the read mux, never per slot.
    // ------------------------------------------------------------------
    logic [TS_WIDTH-1:0]  r_now;
    logic [AGE_WIDTH-1:0] r_us;
    logic                 w_tick;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_now <= '0; r_us <= '0;
        end else begin
            r_now <= r_now + 1'b1;
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
    // The table. One entry per outstanding transaction, allocated at the
    // command handshake, freed at the last data beat (read) or the B (write).
    //   phase: 0 = waiting for data beats, 1 = waiting for B (writes only)
    // Every field is written whole (allocation) or by one shared value
    // (the beat count, the progress stamp) selected into one slot -- no
    // per-slot arithmetic. Packed arrays throughout: the formal flow
    // flattens through sv2v, and yosys rejects an unpacked array named whole
    // in a sensitivity list (the trans_mgr's w_age_flat exists for the same
    // reason).
    // ------------------------------------------------------------------
    logic [N-1:0]                 r_valid;
    logic [N-1:0][IW-1:0]         r_id;
    logic [N-1:0][AW-1:0]         r_addr;
    logic [N-1:0][7:0]            r_beats;   // data beats still expected (len for a fresh entry)
    logic [N-1:0]                 r_phase;
    logic [N-1:0]                 r_err;     // an error was already reported for this entry
    logic [N-1:0]                 r_tmo;     // a timeout was already reported for this entry
    logic [N-1:0][TS_WIDTH-1:0]   r_ts0;     // cycle stamp of allocation (latency)
    logic [N-1:0][AGE_WIDTH-1:0]  r_us0;     // microsecond stamp of the last progress (timeout)
    // Ordering: the live entries of one ID form a LINKED LIST in allocation
    // order. head marks the oldest (the one the next same-ID beat or
    // response belongs to -- AXI returns them in order), tail the youngest
    // (the one a new same-ID command links behind), next points down the
    // list. So "the oldest matching entry" is the ONE entry with the ID and
    // the head flag: a one-hot match, no age compare at all. An allocation
    // links behind the tail (compares against cmd_id, off the data path);
    // a free passes the head flag down its next pointer. Earlier builds
    // ordered by stamp and by dense rank, both needing a log2(N)-deep
    // tournament of compares in front of every table read; this needs none.
    logic [N-1:0]                 r_head;
    logic [N-1:0]                 r_tail;
    logic [N-1:0]                 r_has_next;
    logic [N-1:0][SW-1:0]         r_next;

    // Free-slot pick: lowest free index.
    logic          w_have_free;
    logic [SW-1:0] w_free_idx;
    always_comb begin
        w_have_free = 1'b0;
        w_free_idx  = '0;
        for (int i = N-1; i >= 0; i--) begin
            if (!r_valid[i]) begin
                w_have_free = 1'b1;
                w_free_idx  = SW'(i);
            end
        end
    end

    // ------------------------------------------------------------------
    // Data-beat attribution.
    //   Read:  the OLDEST valid entry whose id matches RID.
    //   Write: the head of the AW-order FIFO (AXI4 W beats carry no ID and
    //          arrive in AW issue order); no lookup.
    // ------------------------------------------------------------------
    logic [N-1:0]  w_dmatch;    // one-hot: the head of data_id's list, still in the data phase
    always_comb begin
        for (int i = 0; i < N; i++)
            w_dmatch[i] = r_valid[i] && r_head[i] && !r_phase[i] &&
                          (!IS_AXI || (r_id[i] == data_id));
    end

    // One-hot to index. The match vectors are one-hot by construction (one
    // head per ID), so this is an OR of index constants -- two LUT levels,
    // not a priority chain.
    function automatic logic [SW-1:0] onehot_idx(input logic [N-1:0] oh);
        logic [SW-1:0] r;
        r = '0;
        for (int i = 0; i < N; i++) r |= oh[i] ? SW'(i) : '0;
        return r;
    endfunction

    logic          w_dhit;
    logic [SW-1:0] w_dslot;

    // AW-order FIFO of slot indices (writes only). Depth N: there can never be
    // more AWs awaiting W than table entries.
    logic [N-1:0][SW-1:0] r_wq;
    logic [SW-1:0] r_wq_wp, r_wq_rp;
    logic [CW-1:0] r_wq_cnt;
    wire           w_wq_empty = (r_wq_cnt == '0);
    wire [SW-1:0]  w_wq_head  = r_wq[r_wq_rp];

    // One early write burst (W before its AW), kept as a count.
    logic [7:0] r_early_beats;
    logic       r_early_last;
    logic       r_early_any;

    generate
        if (IS_READ) begin : g_rd_attr
            assign w_dhit  = |w_dmatch;
            assign w_dslot = onehot_idx(w_dmatch);
        end else begin : g_wr_attr
            assign w_dhit  = !w_wq_empty && r_valid[w_wq_head];
            assign w_dslot = w_wq_head;
        end
    endgenerate

    // Response (B) attribution: the head of resp_id's list, in the response
    // phase. A B whose head is still taking W beats is a response before its
    // data and reports as an orphan.
    logic [N-1:0]  w_bmatch;
    logic          w_bhit;
    logic [SW-1:0] w_bslot;
    always_comb begin
        for (int i = 0; i < N; i++)
            w_bmatch[i] = r_valid[i] && r_head[i] && r_phase[i] &&
                          (!IS_AXI || (r_id[i] == resp_id));
    end
    assign w_bhit  = |w_bmatch;
    assign w_bslot = onehot_idx(w_bmatch);

    // Beats: an 8-bit decrement per slot is a handful of LUTs, and it keeps
    // the 8:1 read mux and the compare off the attribution path -- the beat
    // that lands only needs "was this the last one expected", a one-bit read.
    logic [N-1:0] w_beats_zero;
    always_comb begin
        for (int i = 0; i < N; i++) w_beats_zero[i] = (r_beats[i] == 8'd0);
    end
    wire w_dbeats_zero = w_beats_zero[w_dslot];

    // ------------------------------------------------------------------
    // Events, computed at the handshake that causes them.
    // ------------------------------------------------------------------
    wire w_data_err   = data_hs &&  w_dhit && IS_READ && (data_resp[1]) && !r_err[w_dslot];
    wire w_data_orph  = data_hs && !w_dhit && IS_READ;                  // R with no owner
    wire w_last_early = data_hs &&  w_dhit && data_last  && !w_dbeats_zero;
    wire w_last_late  = data_hs &&  w_dhit && !data_last &&  w_dbeats_zero;
    wire w_data_done  = data_hs &&  w_dhit && data_last;
    wire w_early_w    = data_hs && !w_dhit && !IS_READ;                 // W ahead of its AW
    wire w_early_ovf  = w_early_w && r_early_last;                      // a second early burst
    wire w_resp_err   = resp_hs &&  w_bhit && resp_code[1] && !r_err[w_bslot];
    wire w_resp_orph  = resp_hs && !w_bhit;
    wire w_resp_done  = resp_hs &&  w_bhit;
    wire w_refused    = cmd_hs  && !w_have_free;

    // Completion: a read's last beat, or a write's B.
    wire           w_compl      = IS_READ ? w_data_done : w_resp_done;
    wire [SW-1:0]  w_compl_slot = IS_READ ? w_dslot     : w_bslot;
    wire           w_compl_clean = w_compl && !r_err[w_compl_slot] &&
                                   !(IS_READ ? (data_resp[1] || w_last_early) : resp_code[1]);
    wire [TS_WIDTH-1:0] w_latency = r_now - r_ts0[w_compl_slot];   // the one latency subtractor
    // the freed head hands its flag to the next entry of its ID, if any
    wire           w_free_has_next = r_has_next[w_compl_slot];
    wire [SW-1:0]  w_free_next     = r_next[w_compl_slot];

    // Timeout: one rotating pointer checks one slot per cycle with one
    // subtractor -- age in microseconds since that entry's last progress.
    logic [SW-1:0] r_scan;
    wire [AGE_WIDTH-1:0] w_scan_age = r_us - r_us0[r_scan];
    wire           w_never   = (cfg_timeout_cnt == 16'hFFFF);
    wire           w_scan_hit = cfg_timeout_enable && !w_never && r_valid[r_scan] && !r_tmo[r_scan] &&
                                (w_scan_age >= cfg_timeout_cnt[AGE_WIDTH-1:0]);
    // The command channel itself stalled (valid without ready) for cfg ticks.
    logic [AGE_WIDTH-1:0] r_cmd_stall_us0;
    logic                 r_cmd_stalling;
    logic                 r_cmd_stall_rpt;
    wire [AGE_WIDTH-1:0] w_cmd_stall_age = r_us - r_cmd_stall_us0;
    wire w_cmd_tmo = cfg_timeout_enable && !w_never && cmd_valid && !cmd_ready && r_cmd_stalling &&
                     !r_cmd_stall_rpt && (w_cmd_stall_age >= cfg_timeout_cnt[AGE_WIDTH-1:0]);

    // Threshold: active count crossing upward.
    logic [CW-1:0] w_occupancy;
    always_comb begin
        w_occupancy = '0;
        for (int i = 0; i < N; i++) w_occupancy = w_occupancy + CW'(r_valid[i]);
    end
    logic r_over_thresh;
    wire  w_over_thresh = (16'(w_occupancy) >= cfg_active_trans_threshold) && (cfg_active_trans_threshold != 16'd0);
    wire  w_thresh_evt  = cfg_threshold_enable && w_over_thresh && !r_over_thresh;

    // ------------------------------------------------------------------
    // Table update
    // ------------------------------------------------------------------
    wire w_alloc = cmd_hs && w_have_free;
    // A write whose AW finds counted early beats absorbs them.
    wire [7:0] w_alloc_beats = (!IS_READ && r_early_any) ? (cmd_len - r_early_beats + 8'd1) : cmd_len;
    wire       w_alloc_done  = (!IS_READ && r_early_any && r_early_last);   // early burst was complete
    wire       w_dprogress   = data_hs && w_dhit;

    // The live tail of cmd_id's list (one-hot; empty if no live same-ID entry).
    // If that tail is itself being freed this cycle, the list is emptying
    // and the new entry starts a fresh one as head.
    logic [N-1:0] w_same_tail;
    always_comb begin
        for (int i = 0; i < N; i++)
            w_same_tail[i] = r_valid[i] && r_tail[i] && (!IS_AXI || (r_id[i] == cmd_id));
    end
    wire          w_tail_freeing = w_compl && w_same_tail[w_compl_slot];
    wire          w_link         = (|w_same_tail) && !w_tail_freeing;   // new entry goes behind the tail
    wire [SW-1:0] w_tail_slot    = onehot_idx(w_same_tail);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_valid <= '0; r_phase <= '0; r_err <= '0; r_tmo <= '0;
            r_id <= '0; r_addr <= '0; r_beats <= '0; r_ts0 <= '0; r_us0 <= '0;
            r_head <= '0; r_tail <= '0; r_has_next <= '0; r_next <= '0;
            r_wq <= '0; r_wq_wp <= '0; r_wq_rp <= '0; r_wq_cnt <= '0;
            r_early_beats <= '0; r_early_last <= 1'b0; r_early_any <= 1'b0;
            r_scan <= '0; r_cmd_stall_us0 <= '0; r_cmd_stalling <= 1'b0; r_cmd_stall_rpt <= 1'b0; r_over_thresh <= 1'b0;
        end else if (clear) begin
            r_valid <= '0; r_err <= '0; r_tmo <= '0;
            r_wq_wp <= '0; r_wq_rp <= '0; r_wq_cnt <= '0;
            r_early_beats <= '0; r_early_last <= 1'b0; r_early_any <= 1'b0;
            r_scan <= '0; r_cmd_stalling <= 1'b0; r_cmd_stall_rpt <= 1'b0; r_over_thresh <= 1'b0;
        end else begin
            // allocate: the whole entry from the command
            if (w_alloc) begin
                r_valid[w_free_idx] <= 1'b1;
                r_id[w_free_idx]    <= cmd_id;
                r_addr[w_free_idx]  <= cmd_addr;
                r_beats[w_free_idx] <= w_alloc_beats;
                r_phase[w_free_idx] <= w_alloc_done;          // write with its data already seen
                r_err[w_free_idx]   <= 1'b0;
                r_tmo[w_free_idx]   <= 1'b0;
                r_ts0[w_free_idx]   <= r_now;
                r_us0[w_free_idx]   <= r_us;
                // join cmd_id's list: behind its tail, or as a new head
                r_head[w_free_idx]     <= !w_link;
                r_tail[w_free_idx]     <= 1'b1;
                r_has_next[w_free_idx] <= 1'b0;
                if (w_link) begin
                    r_tail[w_tail_slot]     <= 1'b0;
                    r_has_next[w_tail_slot] <= 1'b1;
                    r_next[w_tail_slot]     <= w_free_idx;
                end
                if (!IS_READ) begin
                    if (!w_alloc_done) begin
                        r_wq[r_wq_wp] <= w_free_idx;
                        r_wq_wp       <= r_wq_wp + 1'b1;
                    end
                    r_early_beats <= '0; r_early_last <= 1'b0; r_early_any <= 1'b0;
                end
            end

            // data beat on an owned entry: one shared next value into one slot
            if (w_dprogress) begin
                r_us0[w_dslot] <= r_us;
                if (!w_dbeats_zero) r_beats[w_dslot] <= r_beats[w_dslot] - 8'd1;
                if (w_data_err || w_last_early || w_last_late) r_err[w_dslot] <= 1'b1;
                if (data_last) begin
                    if (IS_READ) begin
                        r_valid[w_dslot] <= 1'b0;                // read done
                    end else begin
                        r_phase[w_dslot] <= 1'b1;                // wait for B
                        r_wq_rp          <= r_wq_rp + 1'b1;
                    end
                end
            end
            // early write data (no AW yet)
            if (w_early_w && !w_early_ovf) begin
                r_early_any   <= 1'b1;
                r_early_beats <= r_early_beats + 8'd1;
                if (data_last) r_early_last <= 1'b1;
            end

            // response on an owned entry
            if (resp_hs && w_bhit) begin
                r_valid[w_bslot] <= 1'b0;
            end

            // a freed head passes the flag to the next entry of its ID
            if (w_compl && w_free_has_next) r_head[w_free_next] <= 1'b1;

            // AW-order FIFO count
            case ({(w_alloc && !IS_READ && !w_alloc_done), (w_dprogress && data_last && !IS_READ)})
                2'b10: r_wq_cnt <= r_wq_cnt + 1'b1;
                2'b01: r_wq_cnt <= r_wq_cnt - 1'b1;
                default: ;
            endcase

            // timeout bookkeeping
            r_scan <= (r_scan == SW'(N-1)) ? '0 : r_scan + 1'b1;
            if (w_scan_hit) r_tmo[r_scan] <= 1'b1;
            if (cmd_valid && !cmd_ready) begin
                if (!r_cmd_stalling) begin
                    r_cmd_stalling  <= 1'b1;
                    r_cmd_stall_us0 <= r_us;
                end
                if (w_cmd_tmo) r_cmd_stall_rpt <= 1'b1;
            end else begin
                r_cmd_stalling  <= 1'b0;
                r_cmd_stall_rpt <= 1'b0;
            end
            r_over_thresh <= w_over_thresh;
        end
    )

    // ------------------------------------------------------------------
    // Event stage. Everything the attribution decided this cycle -- which
    // events fired and on which slot -- is REGISTERED here, and the packet
    // is picked and formatted next cycle from flops. The third synthesis of
    // this block had the tournament, the 8:1 payload muxes, the priority
    // pick, the queue write and the drop counter in one 23-level cycle; the
    // register halves it. Reading r_id/r_addr a cycle late is safe: a slot
    // is only rewritten by an allocation, and a slot freed in cycle t cannot
    // be picked free before t+1, so its contents survive through t+1.
    // ------------------------------------------------------------------
    logic               r_e_resp_err, r_e_data_err, r_e_last_early, r_e_last_late;
    logic               r_e_resp_orph, r_e_data_orph, r_e_early_ovf;
    logic               r_e_scan_hit, r_e_cmd_tmo, r_e_compl, r_e_thresh;
    logic               r_e_scan_phase, r_e_data_decerr, r_e_resp_decerr;
    logic [SW-1:0]      r_e_dslot, r_e_bslot, r_e_tslot, r_e_cslot;
    logic [IW-1:0]      r_e_data_id, r_e_resp_id, r_e_cmd_id;
    logic [AW-1:0]      r_e_cmd_addr;
    logic [15:0]        r_e_latency;
    logic [CW-1:0]      r_e_occupancy;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_e_resp_err <= 1'b0; r_e_data_err <= 1'b0; r_e_last_early <= 1'b0; r_e_last_late <= 1'b0;
            r_e_resp_orph <= 1'b0; r_e_data_orph <= 1'b0; r_e_early_ovf <= 1'b0;
            r_e_scan_hit <= 1'b0; r_e_cmd_tmo <= 1'b0; r_e_compl <= 1'b0; r_e_thresh <= 1'b0;
            r_e_scan_phase <= 1'b0; r_e_data_decerr <= 1'b0; r_e_resp_decerr <= 1'b0;
            r_e_dslot <= '0; r_e_bslot <= '0; r_e_tslot <= '0; r_e_cslot <= '0;
            r_e_data_id <= '0; r_e_resp_id <= '0; r_e_cmd_id <= '0; r_e_cmd_addr <= '0;
            r_e_latency <= '0; r_e_occupancy <= '0;
        end else begin
            r_e_resp_err   <= w_resp_err   && !clear;
            r_e_data_err   <= w_data_err   && !clear;
            r_e_last_early <= w_last_early && !clear;
            r_e_last_late  <= w_last_late  && !clear;
            r_e_resp_orph  <= w_resp_orph  && !clear;
            r_e_data_orph  <= w_data_orph  && !clear;
            r_e_early_ovf  <= w_early_ovf  && !clear;
            r_e_scan_hit   <= w_scan_hit   && !clear;
            r_e_cmd_tmo    <= w_cmd_tmo    && !clear;
            r_e_compl      <= w_compl_clean && !clear;
            r_e_thresh     <= w_thresh_evt && !clear;
            r_e_scan_phase <= r_phase[r_scan];
            r_e_data_decerr <= data_resp[0];
            r_e_resp_decerr <= resp_code[0];
            r_e_dslot      <= w_dslot;
            r_e_bslot      <= w_bslot;
            r_e_tslot      <= r_scan;
            r_e_cslot      <= w_compl_slot;
            r_e_data_id    <= data_id;
            r_e_resp_id    <= resp_id;
            r_e_cmd_id     <= cmd_id;
            r_e_cmd_addr   <= cmd_addr;
            r_e_latency    <= 16'(w_latency);
            r_e_occupancy  <= w_occupancy;
        end
    )

    // ------------------------------------------------------------------
    // Packet pick, from the registered events. Priority when events collide:
    // error > timeout > completion > threshold. An event that arrives while
    // the queue is full, or loses the pick, is dropped and counted; the count
    // goes out as an Error/EVENT_DROPPED packet the next time the queue has
    // room and nothing else wants it. ONE table read serves every class:
    // the winner names a slot, and that slot's id and address are muxed once.
    // ------------------------------------------------------------------
    function automatic logic type_allowed(input logic [3:0] t);
        return !cfg_axi_pkt_mask[t];
    endfunction

    wire w_err_en = cfg_error_enable && type_allowed(PktTypeError);
    wire w_tmo_en = type_allowed(PktTypeTimeout);
    wire w_cmp_en = cfg_compl_enable && type_allowed(PktTypeCompletion);
    wire w_thr_en = type_allowed(PktTypeThreshold);

    logic          w_err_v;
    logic [7:0]    w_err_code;
    logic [SW-1:0] w_err_slot;
    logic          w_err_has_slot;
    logic [IW-1:0] w_err_id;
    always_comb begin
        w_err_v = 1'b0; w_err_code = '0; w_err_slot = '0; w_err_has_slot = 1'b0; w_err_id = '0;
        if (r_e_resp_err)        begin w_err_v = 1'b1; w_err_code = r_e_resp_decerr ? AXI_ERR_RESP_DECERR : AXI_ERR_RESP_SLVERR; w_err_slot = r_e_bslot; w_err_has_slot = 1'b1; end
        else if (r_e_data_err)   begin w_err_v = 1'b1; w_err_code = r_e_data_decerr ? AXI_ERR_RESP_DECERR : AXI_ERR_RESP_SLVERR; w_err_slot = r_e_dslot; w_err_has_slot = 1'b1; end
        else if (r_e_last_early) begin w_err_v = 1'b1; w_err_code = AXI_ERR_BURST_LENGTH; w_err_slot = r_e_dslot; w_err_has_slot = 1'b1; end
        else if (r_e_last_late)  begin w_err_v = 1'b1; w_err_code = AXI_ERR_LAST_MISSING; w_err_slot = r_e_dslot; w_err_has_slot = 1'b1; end
        else if (r_e_resp_orph)  begin w_err_v = 1'b1; w_err_code = AXI_ERR_RESP_ORPHAN;  w_err_id = r_e_resp_id; end
        else if (r_e_data_orph)  begin w_err_v = 1'b1; w_err_code = AXI_ERR_DATA_ORPHAN;  w_err_id = r_e_data_id; end
        else if (r_e_early_ovf)  begin w_err_v = 1'b1; w_err_code = AXI_ERR_WRITE_BEFORE_ADDR; end
        w_err_v = w_err_v && w_err_en;
    end
    // how many error-class events fired (for the drop count)
    logic [3:0] w_err_fired;
    always_comb begin
        w_err_fired = 4'(r_e_resp_err) + 4'(r_e_data_err) + 4'(r_e_last_early) + 4'(r_e_last_late)
                    + 4'(r_e_resp_orph) + 4'(r_e_data_orph) + 4'(r_e_early_ovf);
        if (!w_err_en) w_err_fired = '0;
    end

    wire       w_tmo_v    = (r_e_scan_hit || r_e_cmd_tmo) && w_tmo_en;
    wire [7:0] w_tmo_code = r_e_scan_hit ? (r_e_scan_phase ? AXI_TIMEOUT_RESP : AXI_TIMEOUT_DATA) : AXI_TIMEOUT_CMD;
    wire [1:0] w_tmo_fired = w_tmo_en ? (2'(r_e_scan_hit) + 2'(r_e_cmd_tmo)) : 2'd0;
    wire       w_cmp_v = r_e_compl  && w_cmp_en;
    wire       w_thr_v = r_e_thresh && w_thr_en;

    // the winner: class, code, and where its id/address come from
    logic          w_evt_v;
    logic [3:0]    w_evt_type;
    logic [7:0]    w_evt_code;
    logic          w_evt_from_slot;      // payload from the table (else from the registered fields)
    logic [SW-1:0] w_evt_slot;
    logic [IW-1:0] w_evt_id_alt;         // id when not from the table
    logic [AW-1:0] w_evt_addr_alt;       // address when not from the table
    logic [15:0]   w_evt_hi;             // data[63:48]: latency on a completion
    always_comb begin
        w_evt_v = 1'b0; w_evt_type = '0; w_evt_code = '0; w_evt_from_slot = 1'b0; w_evt_slot = '0;
        w_evt_id_alt = '0; w_evt_addr_alt = '0; w_evt_hi = '0;
        if (w_err_v) begin
            w_evt_v = 1'b1; w_evt_type = PktTypeError; w_evt_code = w_err_code;
            w_evt_from_slot = w_err_has_slot; w_evt_slot = w_err_slot; w_evt_id_alt = w_err_id;
        end else if (w_tmo_v) begin
            w_evt_v = 1'b1; w_evt_type = PktTypeTimeout; w_evt_code = w_tmo_code;
            w_evt_from_slot = r_e_scan_hit; w_evt_slot = r_e_tslot;
            w_evt_id_alt = r_e_cmd_id; w_evt_addr_alt = r_e_cmd_addr;
        end else if (w_cmp_v) begin
            w_evt_v = 1'b1; w_evt_type = PktTypeCompletion; w_evt_code = AXI_COMPL_TRANS_COMPLETE;
            w_evt_from_slot = 1'b1; w_evt_slot = r_e_cslot; w_evt_hi = r_e_latency;
        end else if (w_thr_v) begin
            w_evt_v = 1'b1; w_evt_type = PktTypeThreshold; w_evt_code = AXI_THRESH_ACTIVE_COUNT;
            w_evt_addr_alt = AW'(r_e_occupancy);
        end
    end
    // the one table read for the payload
    wire [IW-1:0] w_evt_id   = w_evt_from_slot ? r_id[w_evt_slot]   : w_evt_id_alt;
    wire [AW-1:0] w_evt_addr = w_evt_from_slot ? r_addr[w_evt_slot] : w_evt_addr_alt;

    // events offered this cycle vs the one that can go out
    logic            w_wr_ready;
    wire [3:0] w_offered = w_err_fired + 4'(w_tmo_fired) + 4'(w_cmp_v) + 4'(w_thr_v);
    wire       w_take    = w_evt_v && w_wr_ready;
    wire [3:0] w_lost    = w_offered - 4'(w_take);

    logic [15:0] r_dropped, r_refused, r_completed, r_errors;
    // pending drop report: emitted when the queue has room and nothing else wants it
    wire w_drop_rpt = (r_dropped != 16'd0) && !w_evt_v && w_wr_ready && w_err_en;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_dropped <= '0; r_refused <= '0; r_completed <= '0; r_errors <= '0;
        end else if (clear) begin
            r_dropped <= '0; r_refused <= '0; r_completed <= '0; r_errors <= '0;
        end else begin
            // saturating: once the top twelve bits are set, pin (w_lost is at most 11)
            if (w_drop_rpt)               r_dropped <= '0;
            else if (&r_dropped[15:4])    r_dropped <= 16'hFFFF;
            else                          r_dropped <= r_dropped + 16'(w_lost);
            if (w_refused && (r_refused != 16'hFFFF)) r_refused <= r_refused + 1'b1;
            if (r_e_compl && (r_completed != 16'hFFFF)) r_completed <= r_completed + 1'b1;
            if ((w_err_fired != '0) && (r_errors != 16'hFFFF)) r_errors <= r_errors + 1'b1;
        end
    )

    // Compact entry through the queue: {type, code, channel id, data[63:48],
    // data[AW-1:0]} -- the packet's constant fields (protocol, unit, agent)
    // and its zero padding are added at the output, so the queue holds only
    // what varies. AW=32 gives 66 bits against the full reporter's 85.
    typedef struct packed {
        logic [3:0]    ptype;
        logic [7:0]    code;
        logic [5:0]    chan;
        logic [15:0]   hi;
        logic [AW-1:0] addr;
    } lite_entry_t;

    lite_entry_t w_entry_in, w_entry_out;
    always_comb begin
        if (w_evt_v)
            w_entry_in = '{ptype: w_evt_type, code: w_evt_code, chan: 6'(w_evt_id), hi: w_evt_hi, addr: w_evt_addr};
        else
            w_entry_in = '{ptype: PktTypeError, code: AXI_ERR_EVENT_DROPPED, chan: 6'd0, hi: 16'd0, addr: AW'(r_dropped)};
    end

    logic [63:0] w_out_data;
    always_comb begin
        w_out_data = '0;
        w_out_data[AW-1:0] = w_entry_out.addr;
        w_out_data[63:48]  = w_entry_out.hi;
    end

    // The output queue: OUT_DEPTH entries in an UNRESET array with two
    // wrapping pointers. Storage without a reset infers distributed RAM (or
    // plain flops with no reset mux); a generic skid buffer at this width
    // and depth synthesized to 346 LUTs -- forty percent of the whole block
    // -- which is what this replaces. The read is a mux (data valid with
    // rd_valid in the same cycle), as the monbus consumers expect.
    localparam int OQW = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;
    logic [$bits(lite_entry_t)-1:0] r_q [OUT_DEPTH];
    logic [OQW:0] r_q_wp, r_q_rp;                         // one extra bit tells full from empty
    wire          w_q_empty = (r_q_wp == r_q_rp);
    wire          w_q_full  = (r_q_wp[OQW-1:0] == r_q_rp[OQW-1:0]) && (r_q_wp[OQW] != r_q_rp[OQW]);
    wire          w_q_push  = (w_take || w_drop_rpt);
    wire          w_q_pop   = monbus_valid && monbus_ready;
    assign w_wr_ready  = !w_q_full;
    assign monbus_valid = !w_q_empty;
    assign w_entry_out  = r_q[r_q_rp[OQW-1:0]];

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

    assign monbus_packet    = create_monitor_packet(w_entry_out.ptype, PROTOCOL_AXI, w_entry_out.code,
                                                    {3'b0, w_entry_out.chan}, UNIT_ID, AGENT_ID, w_out_data);
    assign monbus_timestamp = i_mon_time;   // side-band time, sampled by the consumer at the handshake

    assign active_count         = 8'(w_occupancy);
    assign busy                 = (|r_valid) || monbus_valid;
    assign perf_completed_count = r_completed;
    assign perf_error_count     = r_errors;
    assign dropped_count        = r_dropped;
    assign refused_count        = r_refused;

endmodule : axi_monitor_lite
