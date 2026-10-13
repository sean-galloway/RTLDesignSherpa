// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_lite
// Purpose: the AXI transaction ocelus at a fifth of the gates (amba/ocelus-lite TASK-001).
//
// Documentation: docs/markdown/rtl-amba/monitor/axi_monitor_lite.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-25
//
// ============================================================================
// What it keeps of axi_monitor_base (the "75%"): error packets for response
// errors, orphan beats and burst-length violations, each with the
// transaction's ID and address; completion packets with latency; timeout
// packets naming the stuck phase; the active-count and latency thresholds; the same
// 128-bit monitor_packet_t + 64-bit side-band timestamp on the same monbus
// handshake, with the same UNIT/AGENT ids, so the arbiter, group, tally and
// host tooling do not know the difference.
//
// What it drops (the "25%"): performance packets and windows (axi_bus_meter
// is the perf path), debug state-change packets, the report-time address
// filter, the ID-range filter, three independent per-phase timers (one "no progress"
// threshold; the phase is in the event code), the block_ready admission
// stall (the lite never touches the traffic it watches: an event it cannot
// deliver is dropped and COUNTED, and the count is reported; a command that
// finds no free slot is counted too, and its beats then surface as ORPHAN
// errors, which name it), and a table
// of data-before-address transactions (ONE early write burst is buffered
// as a beat count). The address-range checker is KEPT as an option: the full
// ocelus's axi_monitor_addr_check, built only when N_ADDR_RANGES > 0, its
// Error/ADDR_RANGE and AddrMatch packets muxed onto the same monbus
// (Sean, 2026-09-26: STREAM's data ports use it).
//
// Why it is small: nothing is scanned. There is one allocation port (the
// command handshake), one lookup (R or B by ID, the head of that ID's list
// -- AXI returns same-ID responses in order, so "oldest with this ID" is
// exact), and the W beats of a write follow an AW-order FIFO of slot
// indices, so they need no lookup at all. Every event is computed at the
// handshake that causes it and goes into a 4-deep queue of 66-bit event
// entries, formatted into the 128-bit packet on the way out (the full
// ocelus keeps an 8-deep FIFO of the same entries plus a copy of the table).
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
// Measured against the full ocelus in the same fixture, same flow
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
    parameter bit          IS_READ          = 1'b1,  // 1: AR/R ocelus, 0: AW/W/B ocelus
    parameter bit          IS_AXI           = 1'b1,  // 0: AXI-Lite (single beat, no ID)
    parameter int          TS_WIDTH         = 16,    // cycle timestamp: ordering + latency
    parameter int          AGE_WIDTH        = 16,    // microsecond age: timeout (cfg is 16 bits)
    parameter int          OUT_DEPTH        = 4,     // output queue of event entries, a power of two; deeper absorbs longer stalls
    // Write monitors: width of the AW/W burst sequence numbers that let the W
    // stream skip the bursts of REFUSED AWs (amba #105). AW may lead W by up
    // to 2**(WSEQ_WIDTH-1)-1 bursts, refused ones included (minimum width 2);
    // unused on reads.
    parameter int          WSEQ_WIDTH       = 8,
    // Write monitors: W bursts kept ahead of their AW (W before AW is legal
    // AXI), a power of two. 1 suffices where the tap sees AW first, as a bus
    // port fed by an AW-first master does. A tap on a slave's FUB (backend)
    // side sees W lead AW by up to the bus-side lead plus the slave's AW skid
    // depth (the AW waits in its skid while W passes its own), so slave write
    // wrappers set this to cover SKID_DEPTH_AW + 1. A burst further ahead than
    // this is still counted but not length-checked, and reported as
    // WRITE_BEFORE_ADDR. Unused on reads.
    parameter int          EARLY_BURSTS     = 1,
    // Address-range checker (axi_monitor_addr_check, the full ocelus's): built
    // when N_ADDR_RANGES > 0, zero area otherwise. Per range, ADDR_RANGE_IS_ERROR
    // = 1 makes a MISS an Error/ADDR_RANGE packet, 0 makes a HIT an AddrMatch packet.
    parameter int          N_ADDR_RANGES    = 0,
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] ADDR_RANGE_IS_ERROR = '0,
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
    parameter int          SELW = (CFI_NUM_FREQ_ENTRIES > 1) ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1,
    parameter int          NAR  = (N_ADDR_RANGES > 0) ? N_ADDR_RANGES : 1
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic                  clear,          // synchronous: empty the table, zero the counters. Legal only while idle -- no outstanding transactions, nothing queued (amba ISSUE-002)

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

    // Response channel tap (B; wrappers tie the R signals here on a read ocelus)
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
    input  logic [31:0]           cfg_latency_threshold,   // completion latency (cycles) above this -> Threshold/LATENCY; the full ocelus's knob
    input  logic [15:0]           cfg_axi_pkt_mask,   // bit[type] = 1 drops that packet type
    // Address-range checker config (used only when N_ADDR_RANGES > 0)
    input  logic                  cfg_addr_check_enable,
    input  logic                  cfg_addr_match_enable,   // a hit in a match range emits AddrMatch
    input  logic [NAR-1:0]        cfg_addr_range_enable,
    input  logic [NAR-1:0][AW-1:0] cfg_addr_range_low,
    input  logic [NAR-1:0][AW-1:0] cfg_addr_range_high,

    // Ocelus bus
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
    // more TRACKED AWs awaiting W than table entries.
    logic [N-1:0][SW-1:0] r_wq;
    logic [SW-1:0] r_wq_wp, r_wq_rp;
    logic [CW-1:0] r_wq_cnt;
    wire           w_wq_empty = (r_wq_cnt == '0);
    wire [SW-1:0]  w_wq_head  = r_wq[r_wq_rp];
    // The pointers wrap at N, not at 2**SW: with a table that is not a power
    // of two (MAX_TRANSACTIONS=12) a plain increment walked them onto indices
    // 12..15, which do not exist -- the slot index written there was lost and
    // the read returned slot 0, so entries waited for W beats that went
    // elsewhere and the table wedged full (amba #105).
    wire [SW-1:0]  w_wq_wp_next = (r_wq_wp == SW'(N-1)) ? '0 : r_wq_wp + 1'b1;
    wire [SW-1:0]  w_wq_rp_next = (r_wq_rp == SW'(N-1)) ? '0 : r_wq_rp + 1'b1;

    // Burst sequence numbers (writes only, amba #105). W carries no ID and
    // follows AW order, so the W stream is a sequence of bursts numbered by
    // the AW they belong to -- and that includes the AWs that found no free
    // slot. Those are refused and never enter the FIFO above, so without a
    // number their W bursts went to the FIFO head (a LATER AW's entry) or into
    // the early-burst register, every attribution after them shifted by one,
    // and entries starved of W sat in the table for good: at depth 12 under
    // load the table wedged full after a few refusals and refused nearly every
    // command from then on. Now:
    //   r_aw_seq  the number of the NEXT AW (every handshake, tracked or not)
    //   r_w_seq   the number of the burst the next W beat belongs to (every
    //             W burst whose last beat was taken, INCLUDING one lost to an
    //             early-burst overflow -- skip it and every later burst is
    //             numbered one short, so every entry's W is skipped)
    //   r_wq_seq  the AW number of each FIFO entry
    // A W beat goes to the FIFO head only when the head's number is r_w_seq;
    // a beat whose AW has been seen (r_aw_seq ahead of r_w_seq) but is not at
    // the head belongs to a refused AW and is consumed silently -- its B then
    // reports as an orphan, which names it. A beat whose AW has not been seen
    // is early: the burst of the NEXT AW is kept in the one early-burst
    // register, any later one overflows (reported) but is still counted.
    localparam int QW = (WSEQ_WIDTH > 1) ? WSEQ_WIDTH : 2;
    logic [N-1:0][QW-1:0] r_wq_seq;
    logic [QW-1:0] r_aw_seq, r_w_seq;
    wire  [QW-1:0] w_seq_gap  = r_aw_seq - r_w_seq;                  // AWs seen whose W has not finished
    wire           w_aw_ahead = (w_seq_gap != '0) && !w_seq_gap[QW-1]; // this beat's AW has been seen
    wire           w_w_next   = (w_seq_gap == '0);                    // this beat is the next AW's burst
    wire           w_w_after  = (w_seq_gap == '1);                    // ...the one after it
    wire           w_w_past   = w_seq_gap[QW-1];                      // the next AW's burst has fully passed

    // Early write bursts (W before its AW), kept as counts. Burst number b
    // lives in slot b mod EB; the next AW's burst is slot(r_aw_seq), the
    // burst the next W beat belongs to is slot(r_w_seq).
    localparam int EB  = (EARLY_BURSTS > 0) ? EARLY_BURSTS : 1;
    localparam int EBW = (EB > 1) ? $clog2(EB) : 1;
    logic [EB-1:0][7:0] r_early_beats;
    logic [EB-1:0]      r_early_last;
    logic [EB-1:0]      r_early_any;
    wire  [EBW-1:0]     w_eslot_aw = (EB > 1) ? EBW'(r_aw_seq) : '0;   // next AW's early burst
    wire  [EBW-1:0]     w_eslot_w  = (EB > 1) ? EBW'(r_w_seq)  : '0;   // this W beat's burst
    wire  [QW-1:0]      w_w_lead   = r_w_seq - r_aw_seq;              // complete early bursts pending
    wire                w_eslot_reuse = cmd_hs && (w_eslot_w == w_eslot_aw); // AW frees the slot this beat writes
    // Elaboration-time checks (generate-scope $error): slots index by burst
    // number mod EB, and the lead compare needs EB inside the sequence window.
    generate
        if (!IS_READ && ((EB & (EB - 1)) != 0)) begin : g_bad_early_pow2
            $error("axi_monitor_lite: EARLY_BURSTS must be a power of two, got %0d", EARLY_BURSTS);
        end
        if (!IS_READ && (EB >= (1 << (QW - 1)))) begin : g_bad_early_window
            $error("axi_monitor_lite: EARLY_BURSTS (%0d) must be below 2**(WSEQ_WIDTH-1)", EARLY_BURSTS);
        end
    endgenerate

    generate
        if (IS_READ) begin : g_rd_attr
            assign w_dhit  = |w_dmatch;
            assign w_dslot = onehot_idx(w_dmatch);
        end else begin : g_wr_attr
            assign w_dhit  = !w_wq_empty && r_valid[w_wq_head] && (r_wq_seq[r_wq_rp] == r_w_seq);
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
    // A W beat in the SAME cycle as an AW, with no AW already awaiting data,
    // belongs to the AW being allocated now (AXI4 write data is in AW order).
    // It is absorbed at allocation, not counted as early: counted, it would
    // sit in the early-burst register while its own entry waited in the
    // AW-order queue for beats that had already passed, and the B would then
    // report a response orphan (found by the inherited same-cycle suite,
    // amba/ocelus-lite TASK-002). While an EARLIER early burst is pending
    // the same-cycle beat is a later transaction's and is queued as early.
    // A W beat whose AW was seen (w_aw_ahead) but is not at the FIFO head
    // belongs to a refused AW (amba #105): it falls through every class below
    // and is consumed, attributed to nobody.
    // A beat of the next AW's burst during that AW's handshake belongs to
    // THAT AW: absorbed by the entry if one is free, consumed silently if the
    // AW is refused. That includes the next beat of a partial early burst the
    // AW is taking this cycle -- same burst, so it goes where the burst goes.
    wire w_w_at_cmd   = cmd_hs && data_hs && !w_dhit && !IS_READ && w_w_next;
    wire w_same_w     = w_w_at_cmd &&  w_have_free;
    wire w_same_skip  = w_w_at_cmd && !w_have_free;
    wire [7:0] w_early_seen = r_early_any[w_eslot_aw] ? r_early_beats[w_eslot_aw] : 8'd0;     // beats of this AW's burst already counted
    wire w_last_early = data_hs && ((w_dhit && data_last && !w_dbeats_zero) ||
                                    (w_same_w && data_last && (cmd_len != w_early_seen)));
    wire w_last_late  = data_hs &&  w_dhit && !data_last &&  w_dbeats_zero;
    wire w_data_done  = data_hs &&  w_dhit && data_last;
    // W ahead of its AW, kept: the next AW's burst, or -- while an AW takes
    // the pending one this cycle (absorbed if tracked, discarded if refused)
    // -- the burst after it, which starts the register afresh
    // (EB = 1: the next AW's burst, or the one after while an AW takes it.)
    wire w_early_w    = data_hs && !w_dhit && !IS_READ &&
                        (( !cmd_hs && (w_w_lead <  QW'(EB))) ||
                         (  cmd_hs && (w_w_lead != '0) && (w_w_lead <= QW'(EB))));
    // W further ahead than that: not kept, reported, still counted
    wire w_early_ovf  = data_hs && !w_dhit && !IS_READ && !w_aw_ahead &&
                        !w_same_w && !w_same_skip && !w_early_w;
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
    // Latency threshold (the full ocelus's second Threshold flavour): a clean
    // completion whose latency crossed cfg_latency_threshold. Gated by the same
    // runtime enable as the active-count threshold; STREAM arms it per port.
    // The threshold compare itself is taken a cycle later, from the registered
    // completion (r_e_compl / r_e_latency) -- see w_lat_hit in the event stage.
    // Done here, it chained the RRESP decode, the slot pick, this subtract, a
    // 32-bit compare and the drop-count adder into one cycle: 21 logic levels,
    // 11.7 ns on an Artix-7 -1 (amba/ocelus-lite ISSUE-002).
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
    // r_beats holds the beats still expected AFTER the next one (cmd_len for a
    // fresh burst: AXI len is beats-1). A write whose AW finds e counted early
    // beats has len+1-e beats left, so len-e after the next; a write taking
    // its first beat this same cycle has len left, so len-1 after the next
    // (0 when that beat was the last -- the entry goes straight to phase 1).
    // A same-cycle beat may also follow a partial early burst (amba #105): the
    // beats already seen are then the early count plus this one.
    wire [7:0] w_alloc_beats = (w_same_w && (cmd_len != w_early_seen)) ? (cmd_len - w_early_seen - 8'd1) :
                               (!IS_READ && r_early_any[w_eslot_aw])   ? (cmd_len - r_early_beats[w_eslot_aw]) : cmd_len;
    wire       w_alloc_done  = (!IS_READ && w_w_past)                         // its burst already passed: kept early, or overflowed (amba #105)
                            || (w_same_w && data_last);                        // single-beat AW+W together
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
            r_wq_seq <= '0; r_aw_seq <= '0; r_w_seq <= '0;
            r_early_beats <= '0; r_early_last <= '0; r_early_any <= '0;
            r_scan <= '0; r_cmd_stall_us0 <= '0; r_cmd_stalling <= 1'b0; r_cmd_stall_rpt <= 1'b0; r_over_thresh <= 1'b0;
        end else if (clear) begin
            r_valid <= '0; r_err <= '0; r_tmo <= '0;
            r_wq_wp <= '0; r_wq_rp <= '0; r_wq_cnt <= '0;
            r_aw_seq <= '0; r_w_seq <= '0;
            r_early_beats <= '0; r_early_last <= '0; r_early_any <= '0;
            r_scan <= '0; r_cmd_stalling <= 1'b0; r_cmd_stall_rpt <= 1'b0; r_over_thresh <= 1'b0;
        end else begin
            // allocate: the whole entry from the command
            if (w_alloc) begin
                r_valid[w_free_idx] <= 1'b1;
                r_id[w_free_idx]    <= cmd_id;
                r_addr[w_free_idx]  <= cmd_addr;
                r_beats[w_free_idx] <= w_alloc_beats;
                r_phase[w_free_idx] <= w_alloc_done;          // write with its data already seen
                r_err[w_free_idx]   <= w_same_w && w_last_early;   // LAST on the first beat of a longer burst
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
                        r_wq[r_wq_wp]     <= w_free_idx;
                        r_wq_seq[r_wq_wp] <= r_aw_seq;            // this AW's burst number
                        r_wq_wp           <= w_wq_wp_next;
                    end
                    r_early_beats[w_eslot_aw] <= '0; r_early_last[w_eslot_aw] <= 1'b0; r_early_any[w_eslot_aw] <= 1'b0;
                end
            end
            // a refused AW owned any pending early burst: discard it, so the
            // next AW does not absorb beats that were never its own (amba #105)
            if (w_refused && !IS_READ) begin
                r_early_beats[w_eslot_aw] <= '0; r_early_last[w_eslot_aw] <= 1'b0; r_early_any[w_eslot_aw] <= 1'b0;
            end
            // burst numbering: every AW, tracked or refused, takes the next
            // number; every W burst whose last beat was taken -- owned,
            // skipped, absorbed, kept early or overflowed -- advances the W side.
            if (!IS_READ) begin
                if (cmd_hs)                                 r_aw_seq <= r_aw_seq + 1'b1;
                if (data_hs && data_last)                   r_w_seq  <= r_w_seq + 1'b1;
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
                        r_wq_rp          <= w_wq_rp_next;
                    end
                end
            end
            // early write data (no AW yet). If an AW is consuming the pending
            // burst this cycle -- absorbing it, or discarding it as refused --
            // this beat starts a fresh one (the branches above cleared the
            // registers; do not add to the stale count).
            if (w_early_w && !w_early_ovf) begin
                r_early_any[w_eslot_w]   <= 1'b1;
                r_early_beats[w_eslot_w] <= (w_eslot_reuse ? 8'd0 : r_early_beats[w_eslot_w]) + 8'd1;
                r_early_last[w_eslot_w]  <= data_last || (r_early_last[w_eslot_w] && !w_eslot_reuse);
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
    // The latency-threshold event always coincides with its completion, and the
    // pick takes one event a cycle: so it is HELD here and offered on the
    // following cycles. It is decided one stage after the completion, from the
    // registered latency, and holds its own PAYLOAD (id, address, latency)
    // rather than a slot index: the completed slot is free from the next cycle
    // and may be reallocated while the event waits. A second one arriving while
    // one waits is lost and counted, like any event the queue could not take.
    logic               r_lat_pend;
    logic [IW-1:0]      r_lat_id;
    logic [AW-1:0]      r_lat_addr;
    logic [15:0]        r_lat_latency;
    logic               w_lat_take;   // the pick queued the held latency event this cycle
    logic               w_lat_hit;    // stage 2: the registered completion crossed the threshold
    // A timeout is a one-cycle pulse from the rotating scan (or the command
    // stall detector), and an Error fired in the same cycle outranks it. Under
    // a sustained error stream it was lost and counted every time (the
    // inherited starvation suite, ocelus-lite TASK-004). One fired timeout the
    // pick could not take is HELD here with its payload (code, id, address)
    // and offered on the following cycles, oldest first; a second one arriving
    // while the hold is full is still lost and counted.
    logic               r_tmo_pend;
    logic [7:0]         r_tmo_code;
    logic [IW-1:0]      r_tmo_id;
    logic [AW-1:0]      r_tmo_addr;
    logic               w_tmo_held_take;   // the pick queued the held timeout this cycle
    logic               w_tmo_saved;       // a fresh timeout went into the hold this cycle
    logic               w_tmo_save_scan;   // ...and it was the scan hit (else the command stall)
    // A completion is registered for exactly one cycle (r_e_compl), and it
    // collides with higher classes in ordinary traffic -- an SLVERR beat on
    // one ID lands the same cycle a clean read completes on another, and the
    // queue can be full at exactly that moment. Before this hold, that
    // completion was dropped and counted, so arming the error cone made the
    // queue lossy against an unrelated class (board-measured as ~90% of
    // completions lost, amba BUG-039). A fresh completion the pick could not
    // queue -- it lost to a higher class, or won while the queue was full --
    // is HELD here with its payload (id, address, latency) and offered on the
    // following cycles, oldest first, at the completion rung; a second one
    // arriving while the hold is full and not draining is still lost and
    // counted. Same contract as the TASK-004 timeout/latency holds: class
    // priority is unchanged, only the one-cycle-transit loss is removed.
    logic               r_cmp_pend;
    logic [IW-1:0]      r_cmp_id;
    logic [AW-1:0]      r_cmp_addr;
    logic [15:0]        r_cmp_latency;
    logic               w_cmp_held_take;   // the pick queued the held completion this cycle
    logic               w_cmp_saved;       // a fresh completion went into the hold this cycle
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
            r_lat_pend <= 1'b0; r_lat_id <= '0; r_lat_addr <= '0; r_lat_latency <= '0;
            r_tmo_pend <= 1'b0; r_tmo_code <= '0; r_tmo_id <= '0; r_tmo_addr <= '0;
            r_cmp_pend <= 1'b0; r_cmp_id <= '0; r_cmp_addr <= '0; r_cmp_latency <= '0;
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
            if (clear)                          r_lat_pend <= 1'b0;
            else if (w_lat_hit && (!r_lat_pend || w_lat_take)) begin   // take the new one (the held one leaves or none held)
                r_lat_pend    <= 1'b1;
                r_lat_id      <= r_id[r_e_cslot];      // the slot still holds it: freed at t, rewritable from t+1's edge
                r_lat_addr    <= r_addr[r_e_cslot];
                r_lat_latency <= r_e_latency;
            end else if (w_lat_take)            r_lat_pend <= 1'b0;
            // held timeout: load the fresh one the pick left behind (the slot
            // still holds the timed-out entry this cycle), else release on take
            if (clear)                          r_tmo_pend <= 1'b0;
            else if (w_tmo_saved) begin
                r_tmo_pend <= 1'b1;
                if (w_tmo_save_scan) begin
                    r_tmo_code <= r_e_scan_phase ? AXI_TIMEOUT_RESP : AXI_TIMEOUT_DATA;
                    r_tmo_id   <= r_id[r_e_tslot];
                    r_tmo_addr <= r_addr[r_e_tslot];
                end else begin
                    r_tmo_code <= AXI_TIMEOUT_CMD;
                    r_tmo_id   <= r_e_cmd_id;
                    r_tmo_addr <= r_e_cmd_addr;
                end
            end else if (w_tmo_held_take)       r_tmo_pend <= 1'b0;
            // held completion: load the fresh one the pick left behind (the
            // slot still holds the completed entry this cycle), else release
            if (clear)                          r_cmp_pend <= 1'b0;
            else if (w_cmp_saved) begin
                r_cmp_pend    <= 1'b1;
                r_cmp_id      <= r_id[r_e_cslot];
                r_cmp_addr    <= r_addr[r_e_cslot];
                r_cmp_latency <= r_e_latency;
            end else if (w_cmp_held_take)       r_cmp_pend <= 1'b0;
            r_e_scan_phase <= r_phase[r_scan];
            r_e_data_decerr <= data_resp[0];
            r_e_resp_decerr <= resp_code[0];
            r_e_dslot      <= w_dhit ? w_dslot : w_free_idx;   // same-cycle LAST-early names the new entry
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

    // Stage 2 of the latency event: flops and quasi-static config only.
    assign w_lat_hit = r_e_compl && cfg_threshold_enable &&
                       ({{(32-16){1'b0}}, r_e_latency} > cfg_latency_threshold);

    // ------------------------------------------------------------------
    // Packet pick, from the registered events. Priority when events collide:
    // error > timeout > completion > threshold. A completion the pick could
    // not queue is HELD one deep (r_cmp_pend, same contract as the timeout
    // and latency holds) instead of dropped; every other event that arrives
    // while the queue is full, or loses the pick, is dropped and counted; the
    // count goes out as an Error/EVENT_DROPPED packet once the queue has
    // DRAINED and nothing else wants it. ONE table read serves every class:
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

    wire       w_tmo_fresh = (r_e_scan_hit || r_e_cmd_tmo) && w_tmo_en;
    wire       w_tmo_v     = w_tmo_fresh || (r_tmo_pend && w_tmo_en);
    // held first (oldest), then the scan hit, then the command stall
    wire [7:0] w_tmo_code = r_tmo_pend   ? r_tmo_code :
                            r_e_scan_hit ? (r_e_scan_phase ? AXI_TIMEOUT_RESP : AXI_TIMEOUT_DATA) : AXI_TIMEOUT_CMD;
    wire [1:0] w_tmo_fired = w_tmo_en ? (2'(r_e_scan_hit) + 2'(r_e_cmd_tmo)) : 2'd0;
    wire       w_cmp_fresh = r_e_compl && w_cmp_en;                     // a fresh completion fired this cycle
    wire       w_cmp_v     = (w_cmp_fresh || r_cmp_pend) && w_cmp_en;   // the completion rung: held first, then fresh
    wire       w_thr_v = (r_e_thresh || r_lat_pend) && w_thr_en;
    wire [1:0] w_thr_fired = w_thr_en ? 2'(r_e_thresh) : 2'd0;   // the held latency event is offered, not fired, each cycle

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
            if (r_tmo_pend) begin
                w_evt_id_alt = r_tmo_id; w_evt_addr_alt = r_tmo_addr;        // held: its own payload
            end else begin
                w_evt_from_slot = r_e_scan_hit; w_evt_slot = r_e_tslot;
                w_evt_id_alt = r_e_cmd_id; w_evt_addr_alt = r_e_cmd_addr;
            end
        end else if (w_cmp_v) begin
            w_evt_v = 1'b1; w_evt_type = PktTypeCompletion; w_evt_code = AXI_COMPL_TRANS_COMPLETE;
            // held: its own captured payload, the slot may already be reused;
            // fresh: the one table read serves it
            w_evt_from_slot = !r_cmp_pend; w_evt_slot = r_e_cslot;
            w_evt_id_alt = r_cmp_id; w_evt_addr_alt = r_cmp_addr;
            w_evt_hi = r_cmp_pend ? r_cmp_latency : r_e_latency;
        end else if (w_thr_v) begin
            w_evt_v = 1'b1; w_evt_type = PktTypeThreshold;
            if (r_e_thresh) begin
                w_evt_code = AXI_THRESH_ACTIVE_COUNT;
                w_evt_addr_alt = AW'(r_e_occupancy);
            end else begin
                // held latency event: its own captured payload, not a table read
                w_evt_code = AXI_THRESH_LATENCY;
                w_evt_id_alt = r_lat_id; w_evt_addr_alt = r_lat_addr; w_evt_hi = r_lat_latency;
            end
        end
    end
    // the one table read for the payload
    wire [IW-1:0] w_evt_id   = w_evt_from_slot ? r_id[w_evt_slot]   : w_evt_id_alt;
    wire [AW-1:0] w_evt_addr = w_evt_from_slot ? r_addr[w_evt_slot] : w_evt_addr_alt;

    // events offered this cycle vs the one that can go out. Offered counts
    // FRESH events only; a held event going out is not a fired event, so it
    // does not count against the offered total (the earlier form subtracted
    // it and underflowed the 4-bit count by 15 when a held event went out).
    logic            w_wr_ready;
    wire [3:0] w_offered = w_err_fired + 4'(w_tmo_fired) + 4'(w_cmp_fresh) + 4'(w_thr_fired);
    wire       w_take    = w_evt_v && w_wr_ready;
    assign     w_lat_take = w_take && w_thr_v && !w_err_v && !w_tmo_v && !w_cmp_v && !r_e_thresh;   // the winner was the held latency event
    // timeout class won the pick: the held one goes first, else one fresh one
    wire       w_tmo_take  = w_take && w_tmo_v && !w_err_v;
    assign     w_tmo_held_take = w_tmo_take && r_tmo_pend;
    wire       w_tmo_fresh_taken = w_tmo_take && !r_tmo_pend;              // the scan hit if it fired, else the stall
    wire [1:0] w_tmo_left  = w_tmo_fired - 2'(w_tmo_fresh_taken);           // fresh timeouts the pick did not take
    assign     w_tmo_saved = (w_tmo_left != 2'd0) && (!r_tmo_pend || w_tmo_held_take);
    // which fresh one is saved: the scan hit unless it was the one just taken
    assign     w_tmo_save_scan = r_e_scan_hit && !(w_tmo_fresh_taken && r_e_scan_hit);
    // completion class won the pick: the held one goes first, else the fresh
    // one. A fresh completion the pick left behind -- it lost to a higher
    // class, or it won while the queue was full -- is HELD if the hold is
    // free (the held one left this cycle, or none was held); only a fresh
    // completion arriving at a full hold that is not draining is lost.
    wire       w_cmp_take  = w_take && w_cmp_v && !w_err_v && !w_tmo_v;
    assign     w_cmp_held_take = w_cmp_take && r_cmp_pend;
    wire       w_cmp_fresh_taken = w_cmp_take && !r_cmp_pend;
    assign     w_cmp_saved = w_cmp_fresh && !w_cmp_fresh_taken && (!r_cmp_pend || w_cmp_held_take);
    wire       w_cmp_lost  = w_cmp_fresh && !w_cmp_fresh_taken && !w_cmp_saved;
    // lost: every FIRED event the pick could not queue and the hold could not
    // keep, plus a latency hit that arrived while one was already held and not
    // leaving. A held event going out is not a fired event, so it does not
    // count against the offered total.
    wire       w_take_fresh = w_take && !w_lat_take && !w_tmo_held_take && !w_cmp_held_take;
    wire       w_lat_lost = w_lat_hit && r_lat_pend && !w_lat_take;
    wire [3:0] w_lost    = w_offered - 4'(w_take_fresh) - 4'(w_tmo_saved) - 4'(w_cmp_saved) + 4'(w_lat_lost);

    logic [15:0] r_dropped, r_refused, r_completed, r_errors;
    // Pending drop report: emitted only when the queue has DRAINED and nothing
    // else wants it -- the axis_monitor_lite rule (amba BUG-039). The earlier
    // "has room" form let a report take a slot ahead of live events while the
    // bus was congested (which is exactly when drops happen), and each idle
    // cycle added another, so the report stream itself amplified the
    // congestion it reported. Emitted into an EMPTY queue, one report can
    // never evict a live event, and the count keeps accumulating (saturating)
    // until the queue drains.
    wire w_drop_rpt = (r_dropped != 16'd0) && !w_evt_v && w_q_empty && w_err_en && !clear;

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
    wire          w_q_pop   = w_q_valid && w_q_ready;           // w_q_ready from the monbus mux below
    assign w_wr_ready  = !w_q_full;
    assign w_entry_out  = r_q[r_q_rp[OQW-1:0]];
    logic w_q_valid;
    assign w_q_valid    = !w_q_empty;

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

    monitor_packet_t w_q_packet;
    assign w_q_packet = create_monitor_packet(w_entry_out.ptype, PROTOCOL_AXI, w_entry_out.code,
                                              {3'b0, w_entry_out.chan}, UNIT_ID, AGENT_ID, w_out_data);

    // ------------------------------------------------------------------
    // Address-range checker and the monbus mux. The checker is the full
    // ocelus's axi_monitor_addr_check, unchanged: it snoops the command
    // handshake and builds its own Error/ADDR_RANGE or AddrMatch packets
    // (same UNIT/AGENT ids). Two sources share the monbus; whichever is
    // presented first holds the bus until taken, so a presented packet never
    // changes under the consumer (the same rule axi_monitor_base applies).
    // ------------------------------------------------------------------
    logic              w_q_ready;
    logic              w_addr_valid, w_addr_ready;
    monitor_packet_t   w_addr_packet;
    monbus_timestamp_t w_addr_ts;

    if (N_ADDR_RANGES > 0) begin : gen_addr_check
        axi_monitor_addr_check #(
            .N_ADDR_RANGES       (N_ADDR_RANGES),
            .ADDR_WIDTH          (AW),
            .ID_WIDTH            (IW),
            .UNIT_ID             (UNIT_ID),
            .AGENT_ID            (AGENT_ID),
            .IS_READ             (IS_READ),
            .ADDR_RANGE_IS_ERROR (ADDR_RANGE_IS_ERROR)
        ) u_addr_check (
            .clk                   (aclk),
            .aresetn               (aresetn),
            .i_mon_time            (i_mon_time),
            .cmd_addr              (cmd_addr),
            .cmd_id                (cmd_id),
            .cmd_valid             (cmd_valid),
            .cmd_ready             (cmd_ready),
            .cfg_addr_check_enable (cfg_addr_check_enable),
            .cfg_debug_enable      (cfg_addr_match_enable),
            .cfg_error_enable      (cfg_error_enable),
            .cfg_addr_range_enable (cfg_addr_range_enable),
            .cfg_addr_range_low    (cfg_addr_range_low),
            .cfg_addr_range_high   (cfg_addr_range_high),
            .addr_pkt_valid        (w_addr_valid),
            .addr_pkt_ready        (w_addr_ready),
            .addr_pkt_data         (w_addr_packet),
            .addr_pkt_timestamp    (w_addr_ts)
        );
    end else begin : gen_no_addr_check
        assign w_addr_valid  = 1'b0;
        assign w_addr_packet = '0;
        assign w_addr_ts     = '0;
    end

    // Source hold: r_src_addr says the checker's packet is the one on the bus.
    // A new selection is made only while nothing is presented.
    logic r_presented, r_src_addr;
    wire  w_sel_addr = r_presented ? r_src_addr : w_addr_valid;   // idle: the checker wins the tie
    assign monbus_valid     = w_sel_addr ? w_addr_valid  : w_q_valid;
    assign monbus_packet    = w_sel_addr ? w_addr_packet : w_q_packet;
    assign monbus_timestamp = w_sel_addr ? w_addr_ts     : i_mon_time;   // side-band time, sampled by the consumer at the handshake
    assign w_addr_ready     =  w_sel_addr && monbus_ready;
    assign w_q_ready        = !w_sel_addr && monbus_ready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_presented <= 1'b0; r_src_addr <= 1'b0;
        end else begin
            if (monbus_valid && monbus_ready)      r_presented <= 1'b0;   // taken: free to reselect
            else if (monbus_valid && !r_presented) begin                  // first cycle on the bus: lock the source
                r_presented <= 1'b1; r_src_addr <= w_sel_addr;
            end
        end
    )

    assign active_count         = 8'(w_occupancy);
    assign busy                 = (|r_valid) || monbus_valid || w_addr_valid || r_lat_pend || r_tmo_pend || r_cmp_pend;
    assign perf_completed_count = r_completed;
    assign perf_error_count     = r_errors;
    assign dropped_count        = r_dropped;
    assign refused_count        = r_refused;

endmodule : axi_monitor_lite
