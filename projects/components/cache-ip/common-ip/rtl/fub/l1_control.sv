// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_control
// Purpose:
//   Blocking-pipeline control FSM for the cache-ip shared MESI L1 (MAS ch02_blocks/01):
//   the cache's only state machine. Owns the tag-array port-A schedule, the
//   snoop port-B service (CTRL_SNOOP), the victim-way selection handshake,
//   the pending-fill bypass register (leaf: l1_pending_fill_bypass), and
//   the start/done handshakes to l1_fill / l1_drain / l1_victim /
//   l1_snoop_resp. Exactly one CPU transaction is in flight at any time
//   (the blocking contract); snoops are serviced concurrently on port B.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/01_amber_control.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: l1_control
//==============================================================================
// Description:
//   One-hot FSM, one bit per pkg ctrl_state_t code; unique case decode with
//   an explicit illegal/multi-hot default into sticky CTRL_ERROR (reset is
//   the only exit, MAS ch02). Per CPU request:
//
//     IDLE        accept the request (req_valid, the GAXI handshake; the
//                 front end holds the fields in the accept cycle and this
//                 module latches them) -- a pending snoop has priority and
//                 detours through CTRL_SNOOP first, the request then
//                 classified in LOOKUP. The accept cycle classifies the
//                 ARRIVING request (amber TASK-005, the 1-cycle hit): port
//                 A's tag set is the arriving set, the tag compare runs on
//                 the arriving tag, and the data array (DATA_SYNC_READ)
//                 is read at the arriving {set, beat}. A read hit goes
//                 straight to HIT_RD and an E/M write hit to HIT_WR; every
//                 other outcome (miss, S-write upgrade) goes to LOOKUP,
//                 which re-classifies from the latched request exactly as
//                 before, so the miss path is unchanged
//     LOOKUP      combinational tag/state compare on port A for the
//                 latched request (replay, snoop return, a non-hit
//                 accept); hit service or miss classification (I-read ->
//                 READ_NOT_SHARED_DIRTY, I-write -> READ_UNIQUE, S-write ->
//                 CLEAN_UNIQUE upgrade straight to MISS_FILL -- an upgrade
//                 installs no data and evicts no victim; MAS ch02_blocks/06)
//     HIT_RD      the response is valid in this cycle: the port-A word
//                 (registered read at the accept edge, way-selected by
//                 hit_way_q). A new request may be accepted here (ready
//                 is high with no snoop window due, see HIT_RUN_MAX), and
//                 it is classified exactly as in IDLE -- back-to-back
//                 read hits run one per cycle
//     HIT_WR      the response (the request's own data) is valid in this
//                 cycle; the byte merge and the E->M promotion (tag write
//                 suppressed when already M) land at the end of it. Ready
//                 is low here: a read accepted in this cycle would read
//                 the array at the write's edge and get the old word, so a
//                 write hit occupies the port for 2 cycles
//     MISS_VICTIM repl victim way sampled on the first cycle (repl_req is a
//                 one-cycle pulse so RANDOM-policy state advances exactly
//                 once per miss); dirty (Modified) victim: gather the whole
//                 line from data-array port A into the victim-line register,
//                 then victim_load; clean victim: straight to the fill
//     MISS_DRAIN  drain_start pulse, wait drain_done
//     MISS_FILL   fill_start pulse + line address + request class, wait
//                 fill_done / fill_pass_dirty; the pending-fill bypass
//                 register arms here on TRUE FILLS ONLY (an upgrade carries
//                 no fill data and does NOT arm it -- MAS ch02/02, MINOR-1
//                 decision)
//     FILL_WRITE  install {tag, state} at the victim way (the fill FUB has
//                 already written the raw beats into the data array); S for
//                 ReadNotSharedDirty fills unless PassDirty is returned,
//                 M otherwise -- unless a snoop's post-commit effect is
//                 pending (downgrade S / invalidation I), which is applied
//                 here instead (invalidation-sticks; gem5 IS_I .sm:1390,
//                 mapping-notes divergences 3/8)
//     REPLAY      re-present the latched request; the next LOOKUP hits and
//                 the replayed write merges the CPU bytes via be (DECISION
//                 D-4: the GAXI slave sees one request, one response)
//
//   Snoop service (CTRL_SNOOP, MAS ch02/01 + ch02_blocks/02):
//     A snoop is granted at safe boundaries only -- IDLE, MISS_FILL (with
//     the bypass armed or an upgrade in flight), MISS_DRAIN -- never
//     mid-burst; l1_snoop_resp holds ctrl_snoop_req until
//     ctrl_snoop_ready and latches ctrl_crresp in the grant cycle, so the
//     response is combinational on the port-B tag lookup. The reference
//     state resolution order is: pending-fill bypass match (post-fill
//     pf_state; the data array serves the fill way, each CD beat gated by
//     pf_data_valid and stalled until it arrives) > the stale-victim entry
//     during a fill (no transfer: the WB completed before the fill started,
//     gem5 M_I x WB_Ack -> I, .sm:1315) > the victim-buffer match while
//     the drain is outstanding (the buffer owns the line until the WB ack,
//     answered at M with CD sourced from victim_data, SINK_WB_ACK, gem5
//     .sm:1352/.sm:1357) > the port-B tag hit (installed state). A state
//     change on an installed line is written on port A inside the service;
//     a state change on the pending line is remembered (pend_vld/pend_state)
//     and applied at fill commit. CD beats flow on cdvalid && cdready with
//     cdlast on the final beat; CR presentation is l1_snoop_resp's
//     concern (after CDLAST).
//
//   The miss-path launch decision is the workbook K-map cover, evaluated in
//   CTRL_MISS_VICTIM (hit is 0 by construction there):
//     start_drain = victim_dirty & !pending_bypass_match
//     start_fill  = !victim_dirty & !pending_bypass_match
//     replay_now  = pending_bypass_match        (defensive: the blocking
//                  pipeline never looks up while a bypass is armed)
//
//   INIT (DECISION D-3): post-reset walk writing STATE_I to every way of
//   every set, one set per cycle (the all-ones way select writes all ways
//   at once); ctrl_req_ready stays low until the walk completes.
//
//   Clean-all (amber TASK-004, peregrine's fence.i; MAS ch02_blocks/01):
//   a request with req_maint set (we = 0) writes every Modified line back
//   and leaves it valid and clean. LOOKUP sends it to the walk; the walk
//   cursor is req_addr_q's set field (set 0 first):
//     CLEAN_SCAN   port-A tag read of the cursor set; a snoop has
//                  priority (the walk's snoop-safe point, once per set and
//                  once per cleaned line). The first Modified way is
//                  latched as the victim and gathered; a set with no M way
//                  advances the cursor; the last set with no M way ends
//                  the walk
//     CLEAN_GATHER the MISS_VICTIM gather (FILL_BEATS port-A reads into
//                  victim_line_mem), then victim_load
//     MISS_DRAIN   the ordinary drain: drain_start, wait drain_done (the B
//                  response); ctrl_drain_clean marks it WriteClean. The
//                  victim-buffer snoop bypass is OFF for a clean drain:
//                  the line is still installed (M), so a snoop resolves on
//                  the port-B tag and its downgrade is written there
//     CLEAN_COMMIT the B has arrived: the victim way goes M -> E unless a
//                  snoop during the drain already moved it (S / I); back to
//                  CLEAN_SCAN on the same set (its next M way, if any)
//     CLEAN_RSP    the response (req_wdata_q echoed), then IDLE
//   Every cleaned line leaves M and nothing creates M during the walk (no
//   CPU request is accepted, a snoop never installs M), so the walk ends.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per l1_pkg defaults (HAS Table 5.0)
//     Type: int
//   HIT_RUN_MAX:
//     Description: the most back-to-back requests accepted in HIT_RD
//       before ready drops for one cycle. A snoop is only accepted in a
//       snoop-safe state (IDLE among them, never HIT_RD), so an unbroken
//       read-hit stream would hold off a snoop forever; the forced IDLE
//       cycle bounds the wait to HIT_RUN_MAX + 1 cycles
//     Type: int, >= 1. Default 8
//
//------------------------------------------------------------------------------
// Notes:
//   - Tag/data lookups are combinational (landed array contract); a lookup
//     sees a same-set write after the clock edge.
//   - fill_done / drain_done are one-cycle pulses; they are latched
//     (fill_done_q / drain_done_q) so a snoop detour can never miss them.
//   - The data array receives fill beats from l1_fill directly (Task 5);
//     this module's data-array write port serves CPU merges only. Fill
//     beats also strobe ctrl_fill_beat_valid/idx, which the bypass register
//     accumulates into pf_data_valid (MAS ch02/06).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: l1_core (test harness: dv/tb/amber_control_th.sv)
//   - Instantiated: l1_pending_fill_bypass (the bypass register leaf),
//     l1_victim (the depth-1 victim buffer leaf)
//   - Package: l1_pkg (ctrl_state_t, cache_state_t, amber_ace_req_t,
//     amber_snoop_crresp / amber_snoop_next_state decode authority)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py -v
//
//==============================================================================

module l1_control
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    // BUG-002 guard: when the cache sits behind a coherence fabric that
    // can hold its fill AR unaccepted (pair rig / any snoopy interconnect),
    // a snoop granted against a fill whose AR has not been accepted yet is
    // answered from the installed tag (I, no data) instead of promising
    // fill data that can never arrive while the fabric parks on this very
    // response. Standalone benches (direct l1_control instantiation, no
    // fabric) keep the classic always-answer-from-armed-fill behavior.
    parameter bit PF_GUARD   = 1'b0,
    // Data-array read latency the controller is wired to (l1_data_array
    // SYNC_READ). 0: combinational read, the port address is the word
    // consumed this cycle. 1: registered read, the address must lead the
    // consumer by one cycle -- the controller presents the beat the NEXT
    // cycle consumes (hit data during LOOKUP, gather beat k+1 during
    // gather beat k, the post-handshake snoop beat) and gates the
    // pending-fill snoop bypass on a one-cycle-delayed beat-valid so a
    // beat landing at the same edge as its read is re-read before it
    // streams. Cycle behaviour is otherwise identical.
    parameter bit DATA_SYNC_READ = 1'b0,
    parameter int HIT_RUN_MAX    = 8,
    localparam int SET_INDEX_WIDTH   = $clog2(SETS),
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int TAG_WIDTH         = ADDR_WIDTH - SET_INDEX_WIDTH - LINE_OFFSET_WIDTH,
    localparam int TAG_STATE_WIDTH   = TAG_WIDTH + 3,
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH  = $clog2(FILL_BEATS),
    localparam int WAY_INDEX_WIDTH   = $clog2(WAYS),
    localparam int MEM_ADDR_WIDTH    = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH,
    localparam int LINE_ADDR_WIDTH   = TAG_WIDTH + SET_INDEX_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // CPU request: single valid pulse from the frontend latch; the front
    // end holds {addr, we, be, wdata} until the response returns
    input  logic                        req_valid,
    input  logic [ADDR_WIDTH-1:0]       req_addr,
    input  logic                        req_we,
    input  logic [STRB_W-1:0]           req_be,
    input  logic [BUS_WIDTH-1:0]        req_wdata,
    // clean-all request (TASK-004): with req_we = 0, write back every
    // Modified line and respond when the last B is in. Tie 0 where the
    // cache has no maintenance op (every harness but amber's planes).
    input  logic                        req_maint,
    output logic                        ctrl_req_ready,
    output logic                        ctrl_rsp_valid,
    output logic [BUS_WIDTH-1:0]        ctrl_rsp_data,

    // tag array port A (CPU/fill lookup + write)
    output logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_set,
    input  logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_a_tag_state,
    output logic                                  ctrl_tag_a_wr_en,
    output logic [WAYS-1:0]                       ctrl_tag_a_wr_way_onehot,
    output logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_wr_set,
    output logic [TAG_STATE_WIDTH-1:0]            ctrl_tag_a_wr_tag_state,

    // data array port A (CPU hit/replay read + CPU write merge)
    output logic [MEM_ADDR_WIDTH-1:0]   ctrl_data_a_addr,
    output logic [WAY_INDEX_WIDTH-1:0]  ctrl_data_a_way,
    input  logic [BUS_WIDTH-1:0]        ctrl_data_a_rdata,
    output logic                        ctrl_data_a_wr_en,
    output logic [WAYS-1:0]             ctrl_data_a_wr_way_onehot,
    output logic [MEM_ADDR_WIDTH-1:0]   ctrl_data_a_wr_addr,
    output logic [BUS_WIDTH-1:0]        ctrl_data_a_wr_wdata,
    output logic [STRB_W-1:0]           ctrl_data_a_wr_be,

    // tag array port B (snoop lookup; ctrl_tag_b_req marks the grant
    // cycle + CTRL_SNOOP as control-owned for the harness mux)
    output logic                                  ctrl_tag_b_req,
    output logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_b_set,
    input  logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_b_tag_state,

    // data array port B (snoop CD beat read: hit way / fill way)
    output logic [MEM_ADDR_WIDTH-1:0]   ctrl_data_b_addr,
    output logic [WAY_INDEX_WIDTH-1:0]  ctrl_data_b_way,
    input  logic [BUS_WIDTH-1:0]        ctrl_data_b_rdata,

    // replacement engine
    output logic                        ctrl_repl_req,
    output logic [SET_INDEX_WIDTH-1:0]  ctrl_repl_set,
    input  logic [WAY_INDEX_WIDTH-1:0]  ctrl_repl_way,
    output logic                        ctrl_repl_hit,
    output logic                        ctrl_repl_update,
    output logic [WAY_INDEX_WIDTH-1:0]  ctrl_repl_hit_way,

    // depth-1 victim buffer leaf (l1_victim, MAS ch02_blocks/05):
    // the load strobe + staged address in; the buffer fields are consumed
    // internally (snoop bypass match + CD source) and observed by the TB.
    // The victim LINE is a beat-addressed store here (victim_line_mem):
    // the drain presents ctrl_victim_beat_idx and reads the word back the
    // same cycle; no line-wide payload bus leaves this module.
    output logic                        ctrl_victim_load,
    output logic [ADDR_WIDTH-1:0]       ctrl_victim_addr_in,
    input  logic [BEAT_INDEX_WIDTH-1:0] ctrl_victim_beat_idx,
    output logic [BUS_WIDTH-1:0]        ctrl_victim_beat_data,

    // fill / drain partners
    output logic                        ctrl_fill_start,
    output logic [ADDR_WIDTH-1:0]       ctrl_fill_addr,
    output logic [2:0]                  ctrl_req_class,
    input  logic                        ctrl_fill_done,
    input  logic                        ctrl_fill_pass_dirty,
    // l1_fill fill_inflight: AR accepted, response phase begun. Qualifies
    // the pending-fill snoop bypass (see sn_pf_gnt_match).
    input  logic                        ctrl_fill_inflight,
    input  logic                        ctrl_fill_beat_valid,
    input  logic [BEAT_INDEX_WIDTH-1:0] ctrl_fill_beat_idx,
    output logic                        ctrl_drain_start,
    input  logic                        ctrl_drain_done,
    // the drain in flight is a clean-all write-back (WriteClean, line
    // kept), not an eviction (WriteBack); stable from drain_start to done
    output logic                        ctrl_drain_clean,

    // snoop responder interface (l1_snoop_resp core-facing contract:
    // req held until ready; CRRESP latched at the grant; CD beats on
    // cdvalid && cdready; CR is presented by the adapter after CDLAST)
    input  logic                        ctrl_snoop_req,
    output logic                        ctrl_snoop_ready,
    output logic                        ctrl_snoop_safe,
    input  logic [2:0]                  ctrl_snoop_type,
    input  logic [ADDR_WIDTH-1:0]       ctrl_snoop_addr,
    output logic [AMBER_CRRESP_WIDTH-1:0] ctrl_crresp,
    output logic [BUS_WIDTH-1:0]        ctrl_cddata,
    output logic                        ctrl_cdlast,
    output logic                        ctrl_cdvalid,
    input  logic                        ctrl_cdready,

    // init-walk status + FSM observability
    output logic                        ctrl_init_busy,
    output logic [SET_INDEX_WIDTH-1:0]  ctrl_init_set,
    output logic [3:0]                  ctrl_state
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("l1_control: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("l1_control: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("l1_control: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("l1_control: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("l1_control: WAYS must be >= 2");
        if (HIT_RUN_MAX < 1)
            $error("l1_control: HIT_RUN_MAX must be >= 1");
    end

    // ------------------------------------------------------------------
    // One-hot FSM: bit index == pkg ctrl_state_t code; multi-hot or
    // unmapped encodings decode to sticky CTRL_ERROR.
    // ------------------------------------------------------------------
    localparam int CTRL_BITS = 16;

    localparam logic [CTRL_BITS-1:0] OH_IDLE         = 16'h0001;
    localparam logic [CTRL_BITS-1:0] OH_INIT         = 16'h0002;
    localparam logic [CTRL_BITS-1:0] OH_LOOKUP       = 16'h0004;
    localparam logic [CTRL_BITS-1:0] OH_HIT_RD       = 16'h0008;
    localparam logic [CTRL_BITS-1:0] OH_HIT_WR       = 16'h0010;
    localparam logic [CTRL_BITS-1:0] OH_MISS_VICTIM  = 16'h0020;
    localparam logic [CTRL_BITS-1:0] OH_MISS_DRAIN   = 16'h0040;
    localparam logic [CTRL_BITS-1:0] OH_MISS_FILL    = 16'h0080;
    localparam logic [CTRL_BITS-1:0] OH_FILL_WRITE   = 16'h0100;
    localparam logic [CTRL_BITS-1:0] OH_REPLAY       = 16'h0200;
    localparam logic [CTRL_BITS-1:0] OH_SNOOP        = 16'h0400;
    localparam logic [CTRL_BITS-1:0] OH_ERROR        = 16'h0800;
    localparam logic [CTRL_BITS-1:0] OH_CLEAN_SCAN   = 16'h1000;
    localparam logic [CTRL_BITS-1:0] OH_CLEAN_GATHER = 16'h2000;
    localparam logic [CTRL_BITS-1:0] OH_CLEAN_COMMIT = 16'h4000;
    localparam logic [CTRL_BITS-1:0] OH_CLEAN_RSP    = 16'h8000;

    logic [CTRL_BITS-1:0] state_q, state_d;

    // latched request (front end presents one pulse; the request context
    // lives here through the miss/replay sequence)
    logic [ADDR_WIDTH-1:0]  req_addr_q;
    logic                   req_we_q;
    logic [STRB_W-1:0]      req_be_q;
    logic [BUS_WIDTH-1:0]   req_wdata_q;
    logic                   req_maint_q;     // clean-all in progress

    // LOOKUP results / miss classification
    logic [WAY_INDEX_WIDTH-1:0] hit_way_q;
    logic [2:0]                 hit_state_q;
    logic [2:0]                 req_class_q;
    logic                       upgr_q;

    // MISS_VICTIM sampling
    logic [WAY_INDEX_WIDTH-1:0] victim_way_q;
    logic [TAG_WIDTH-1:0]       victim_tag_q;
    logic [2:0]                 victim_state_q;
    // the gathered victim line, one word per beat (a small distributed
    // RAM: written by the gather, read by beat by the drain and the snoop
    // CD bypass -- never as a whole line)
    (* ram_style = "distributed" *)
    /* synthesis ramstyle = "MLAB" */
    logic [BUS_WIDTH-1:0]       victim_line_mem [FILL_BEATS];
    logic [BUS_WIDTH-1:0]       victim_sn_word;   // the bypass's current CD beat
    logic [BEAT_INDEX_WIDTH:0]  mv_cnt_q;
    // MISS_VICTIM gather schedule. Combinational read (MV_LEAD = 0): gather
    // cycle k (mv_cnt_q = k) reads and captures beat k. Registered read
    // (MV_LEAD = 1): cycle 0 presents beat 0's address, cycle k presents
    // beat k and captures beat k-1, so victim_load lands at FILL_BEATS + 1.
    // The lead cycle is the 75 MHz timing fix (peregrine TASK-006): LOOKUP
    // no longer moves the data-array address on its own next-state decode
    // (hit compare -> miss -> beat 0), which was amber's critical path.
    localparam int MV_LEAD = DATA_SYNC_READ ? 1 : 0;
    localparam logic [BEAT_INDEX_WIDTH:0] MV_END =
        (BEAT_INDEX_WIDTH+1)'(FILL_BEATS + MV_LEAD);
    // CLEAN_COMMIT's "still M" check, sampled in MISS_DRAIN (the only
    // predecessor; nothing writes the tag array in MISS_DRAIN, and a snoop
    // detour's tag write lands before it returns there), so the tag
    // compare is a flop away from the tag-array write enable
    logic cl_commit_m_q;

    // transaction-completion handshake flags (start pulses are one cycle;
    // done may only be honoured after the start has been presented; the
    // done pulses are latched so a CTRL_SNOOP detour cannot miss them)
    logic fill_seen_q, fill_done_q, drain_seen_q, drain_done_q;
    // PassDirty is carried on the RRESP beat(s); the fill stub pulses it
    // during the burst, so capture it once seen and hold until commit.
    logic fill_pass_dirty_q;

    // back-to-back accept bookkeeping (TASK-005): the run length of
    // requests accepted in HIT_RD (the snoop window, HIT_RUN_MAX), and a
    // flag for a HIT_RD entered from HIT_RD -- a new hit the state alone
    // does not show (the l1_monlite hit event tap)
    localparam int RUN_W = $clog2(HIT_RUN_MAX + 1);
    logic [RUN_W-1:0]       hit_run_q;
    logic                   hit_again_q;

    // init walk (D-3)
    logic [SET_INDEX_WIDTH-1:0] init_cnt_q;

    // snoop service context (latched at the grant)
    logic [ADDR_WIDTH-1:0]      sn_addr_q;
    logic [2:0]                 sn_type_q;
    logic [BEAT_INDEX_WIDTH-1:0] sn_beat_q;
    logic [CTRL_BITS-1:0]       sn_return_q;
    logic                       sn_back_to_lookup_q;
    logic                       sn_pf_q;         // answered from the bypass
    logic                       sn_hit_any_q;    // port-B tag hit
    logic [WAY_INDEX_WIDTH-1:0] sn_hit_way_q;
    logic [2:0]                 sn_hit_state_q;
    logic [TAG_WIDTH-1:0]       sn_hit_tag_q;
    logic                       sn_stale_q;      // stale victim entry
    logic                       sn_victim_q;     // draining-victim match
    logic                       sn_upgr_line_q;  // upgrade's own line
    logic                       sn_dt_q;         // CRRESP.DataTransfer
    logic [2:0]                 sn_ref_q;        // resolved reference state

    // post-commit snoop effect, applied at CTRL_FILL_WRITE
    // (invalidation-sticks: once armed, later snoops do not clear it)
    logic       pend_vld_q;
    logic [2:0] pend_state_q;

    // ------------------------------------------------------------------
    // Request address slicing
    // ------------------------------------------------------------------
    logic [TAG_WIDTH-1:0]        req_tag;
    logic [SET_INDEX_WIDTH-1:0]  req_set;
    logic [BEAT_INDEX_WIDTH-1:0] req_beat;
    logic [LINE_ADDR_WIDTH-1:0]  req_line_addr;
    logic [ADDR_WIDTH-1:0]       req_line_base;

    assign req_tag       = req_addr_q[ADDR_WIDTH-1 -: TAG_WIDTH];
    assign req_set       = req_addr_q[LINE_OFFSET_WIDTH +: SET_INDEX_WIDTH];
    assign req_beat      = req_addr_q[LINE_OFFSET_WIDTH-1 -: BEAT_INDEX_WIDTH];
    assign req_line_addr = req_addr_q[ADDR_WIDTH-1:LINE_OFFSET_WIDTH];
    assign req_line_base = {req_line_addr, {LINE_OFFSET_WIDTH{1'b0}}};

    // the arriving request (accept cycle, TASK-005)
    logic [TAG_WIDTH-1:0]        acc_tag;
    logic [SET_INDEX_WIDTH-1:0]  acc_set;
    logic [BEAT_INDEX_WIDTH-1:0] acc_beat;

    assign acc_tag  = req_addr[ADDR_WIDTH-1 -: TAG_WIDTH];
    assign acc_set  = req_addr[LINE_OFFSET_WIDTH +: SET_INDEX_WIDTH];
    assign acc_beat = req_addr[LINE_OFFSET_WIDTH-1 -: BEAT_INDEX_WIDTH];

    // ready (registers only: the state and the run counter) and the
    // accept. req_valid is the front end's handshake, so it is only high
    // while ready is; the AND keeps the classification honest against a
    // harness that pulses req_valid on its own.
    logic acc_ok, acc;
    assign acc_ok = (state_q == OH_IDLE)
                    || ((state_q == OH_HIT_RD)
                        && (hit_run_q < RUN_W'(HIT_RUN_MAX)));
    assign acc    = req_valid && acc_ok;

    // the tag the port-A compare runs on: the arriving request's in a
    // state that can accept, the latched one otherwise (LOOKUP). The
    // select is acc_ok, not acc (peregrine TASK-006, 75 MHz): req_valid
    // comes from the CPU and, behind it, from ready, so selecting on acc
    // put the whole handshake in front of the tag LUTRAM address. In an
    // accepting state with no request the port reads a don't-care set:
    // nothing consumes port A there unless acc (the accept latch and the
    // fast-path decode are both qualified by it).
    logic [TAG_WIDTH-1:0] cmp_tag;
    assign cmp_tag = acc_ok ? acc_tag : req_tag;

    // ------------------------------------------------------------------
    // LOOKUP: combinational hit/miss across the ways (tag match on a
    // valid MESI state; reserved encodings never hit -- benign absorbed)
    // ------------------------------------------------------------------
    logic                       hit_any;
    logic [WAY_INDEX_WIDTH-1:0] hit_way;
    logic [2:0]                 hit_state;

    always_comb begin
        hit_any   = 1'b0;
        hit_way   = '0;
        hit_state = AMBER_STATE_I;
        for (int w = 0; w < WAYS; w++) begin
            if (!hit_any
                && (ctrl_tag_a_tag_state[w][TAG_STATE_WIDTH-1 -: TAG_WIDTH]
                        == cmp_tag)
                && (ctrl_tag_a_tag_state[w][2:0] == AMBER_STATE_S
                    || ctrl_tag_a_tag_state[w][2:0] == AMBER_STATE_E
                    || ctrl_tag_a_tag_state[w][2:0] == AMBER_STATE_M)) begin
                hit_any   = 1'b1;
                hit_way   = WAY_INDEX_WIDTH'(w);
                hit_state = ctrl_tag_a_tag_state[w][2:0];
            end
        end
    end

    // accept-cycle fast path: a read hit, or a write hit on an owned
    // (E/M) line; everything else goes through LOOKUP
    logic acc_fast_rd, acc_fast_wr;
    assign acc_fast_rd = !req_maint && !req_we && hit_any;
    assign acc_fast_wr = !req_maint && req_we
                         && (hit_state == AMBER_STATE_E
                             || hit_state == AMBER_STATE_M);

    // one-hot way selects for the array write ports
    logic [WAYS-1:0] hit_way_onehot, victim_way_onehot, sn_hit_way_onehot;

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            hit_way_onehot[w]    = (hit_way_q    == WAY_INDEX_WIDTH'(w));
            victim_way_onehot[w] = (victim_way_q == WAY_INDEX_WIDTH'(w));
            sn_hit_way_onehot[w] = (sn_hit_way_q == WAY_INDEX_WIDTH'(w));
        end
    end

    // ------------------------------------------------------------------
    // Snoop address slicing (grant cycle: the live request; CTRL_SNOOP:
    // the latched context). Declared ahead of the bypass leaf: the leaf's
    // match input follows the address being resolved this cycle.
    // ------------------------------------------------------------------
    logic [LINE_ADDR_WIDTH-1:0]  w_sn_line_addr;
    logic [SET_INDEX_WIDTH-1:0]  sn_set_grant, sn_set_q;
    logic [TAG_WIDTH-1:0]        sn_tag_grant;

    assign sn_set_grant  = ctrl_snoop_addr[LINE_OFFSET_WIDTH +: SET_INDEX_WIDTH];
    assign sn_tag_grant  = ctrl_snoop_addr[ADDR_WIDTH-1 -: TAG_WIDTH];
    assign sn_set_q      = sn_addr_q[LINE_OFFSET_WIDTH +: SET_INDEX_WIDTH];

    // the leaf's match input follows the address being resolved: the
    // latched snoop inside CTRL_SNOOP, the live request at the grant
    assign w_sn_line_addr = (state_q == OH_SNOOP)
                            ? sn_addr_q[ADDR_WIDTH-1:LINE_OFFSET_WIDTH]
                            : ctrl_snoop_addr[ADDR_WIDTH-1:LINE_OFFSET_WIDTH];

    // ------------------------------------------------------------------
    // Pending-fill bypass register (leaf, MAS ch02_blocks/02). Loaded when
    // a TRUE fill launches in CTRL_MISS_FILL; an upgrade (CLEAN_UNIQUE)
    // carries no fill data in flight and does NOT arm it (MINOR-1
    // decision, pinned by the UpgradeNoBypassArm directed test). Cleared
    // at fill commit (CTRL_FILL_WRITE).
    // ------------------------------------------------------------------
    logic                        pf_active;
    logic [LINE_ADDR_WIDTH-1:0]  pf_addr;
    logic [2:0]                  pf_state;
    logic [FILL_BEATS-1:0]       pf_data_valid;
    logic                        pf_match;
    logic                        pf_beat_valid;
    logic                        pf_load, pf_clear;

    // install state at FILL_WRITE / bypass load: ReadNotSharedDirty fills
    // install Shared unless the interconnect returned PassDirty (RRESP[2]),
    // in which case the cache owns the dirty data and must install Modified
    // so the write-back responsibility is not lost. All write, upgrade, and
    // MakeUnique transactions install Modified (MAS ch02_blocks/02) -- unless
    // a snoop's post-commit effect (downgrade S / invalidation I) is pending;
    // an armed I is never overwritten by a later S.
    logic [2:0] install_state, install_state_eff;

    assign install_state =
        (req_class_q == AMBER_ACE_READ_NOT_SHARED_DIRTY && !fill_pass_dirty_q)
            ? AMBER_STATE_S : AMBER_STATE_M;
    assign install_state_eff = pend_vld_q ? pend_state_q : install_state;

    assign pf_load = (state_q == OH_MISS_FILL) && !upgr_q && !pf_active;
    assign pf_clear = (state_q == OH_FILL_WRITE);

    l1_pending_fill_bypass #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_pf (
        .clk           (clk),
        .rst_n         (rst_n),
        .pf_load       (pf_load),
        .pf_load_addr  (req_line_addr),
        .pf_load_state (install_state),
        .pf_beat_set   (ctrl_fill_beat_valid),
        .pf_beat_idx   (ctrl_fill_beat_idx),
        .pf_snoop_addr (w_sn_line_addr),
        .pf_match      (pf_match),
        .pf_active     (pf_active),
        .pf_addr       (pf_addr),
        .pf_state      (pf_state),
        .pf_data_valid (pf_data_valid),
        .pf_beat_valid (pf_beat_valid),
        .pf_clear      (pf_clear)
    );

    // ------------------------------------------------------------------
    // Depth-1 victim buffer (leaf, MAS ch02_blocks/05). l1_control
    // gathers the dirty victim line over FILL_BEATS data-array port-A
    // read cycles (DECISION D-5: the array port is BUS_WIDTH wide, so the
    // single-cycle full-line load of MAS ch02 is unreachable); the
    // victim_load strobe marks the gather-complete cycle (the final
    // beat's capture) and the buffer owns the line until the write-back
    // completes (victim_clear on ctrl_drain_done). The buffer never loads
    // while busy -- the single-outstanding property makes the strobe
    // unreachable before the retire, and the leaf guards it (Review
    // Focus 2).
    // ------------------------------------------------------------------
    logic                      victim_busy_unused, victim_empty_unused;
    logic                      victim_valid;
    logic [ADDR_WIDTH-1:0]     victim_buf_addr;

    // address + valid only; the line is victim_line_mem (one copy, read
    // by beat) -- FPGA review 2026-11-07
    l1_victim #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_victim (
        .clk            (clk),
        .rst_n          (rst_n),
        .victim_load    (ctrl_victim_load),
        .victim_addr_in (ctrl_victim_addr_in),
        .victim_clear   (ctrl_drain_done),
        .victim_busy    (victim_busy_unused),
        .victim_empty   (victim_empty_unused),
        .victim_valid   (victim_valid),
        .victim_addr    (victim_buf_addr)
    );

    // beat reads of the victim line: the drain's word (its beat index
    // arrives through ctrl_victim_beat_idx) and the snoop bypass's word
    assign ctrl_victim_beat_data = victim_line_mem[ctrl_victim_beat_idx];
    assign victim_sn_word        = victim_line_mem[sn_beat_q];

    // ------------------------------------------------------------------
    // Snoop port-B lookup (combinational, grant cycle) and reference
    // state resolution
    // ------------------------------------------------------------------
    logic       sn_hit_any;
    logic [WAY_INDEX_WIDTH-1:0] sn_hit_way;
    logic [2:0] sn_hit_state;
    logic [TAG_WIDTH-1:0] sn_hit_tag;

    always_comb begin
        sn_hit_any   = 1'b0;
        sn_hit_way   = '0;
        sn_hit_state = AMBER_STATE_I;
        sn_hit_tag   = '0;
        for (int w = 0; w < WAYS; w++) begin
            if (!sn_hit_any
                && (ctrl_tag_b_tag_state[w][TAG_STATE_WIDTH-1 -: TAG_WIDTH]
                        == sn_tag_grant)
                && (ctrl_tag_b_tag_state[w][2:0] == AMBER_STATE_S
                    || ctrl_tag_b_tag_state[w][2:0] == AMBER_STATE_E
                    || ctrl_tag_b_tag_state[w][2:0] == AMBER_STATE_M)) begin
                sn_hit_any   = 1'b1;
                sn_hit_way   = WAY_INDEX_WIDTH'(w);
                sn_hit_state = ctrl_tag_b_tag_state[w][2:0];
                sn_hit_tag   = ctrl_tag_b_tag_state[w]
                                    [TAG_STATE_WIDTH-1 -: TAG_WIDTH];
            end
        end
    end

    // pending-fill bypass match (only meaningful while a fill is armed).
    // The bypass answer path may only promise snoop data when the fill is
    // actually in flight (its AR has been accepted and the response phase
    // begun). A fill whose AR is still seeking acceptance can never produce
    // beats while the pair fabric parks in F_RESP waiting for this very
    // snoop's response -- promising data from it deadlocks the rig
    // (BUG-002: same-line miss in both caches, snoop granted against a
    // pre-AR fill). Pre-acceptance, answer from the installed tag state
    // instead; the fabric then passes the requester to memory and
    // serializes the two fills through its pending/kill logic. Environments
    // without such a fabric (PF_GUARD=0) keep the classic behavior.
    logic sn_pf_gnt_match;
    assign sn_pf_gnt_match = pf_match && (state_q == OH_MISS_FILL)
                             && (!PF_GUARD || ctrl_fill_inflight);

    // stale victim entry: during a fill the tag still shows the evicted
    // victim at the fill way, and the fill beats are overwriting its data
    // -- the WB completed before the fill started (drain_done < fill_start
    // ordering), so the line is answered Invalid, no transfer (gem5 M_I x
    // WB_Ack -> I, .sm:1315). The match is (way, tag, SET)-exact: the
    // victim way/tag name a slot of the PENDING transaction's set, and a
    // same-way+tag hit in any other set is an ordinary installed hit (the
    // Task 7 closed loop caught the missing set term as a false stale on a
    // cross-set collision).
    logic sn_stale_gnt;
    assign sn_stale_gnt = (state_q == OH_MISS_FILL) && !upgr_q
                          && sn_hit_any
                          && (sn_set_grant == req_set)
                          && (sn_hit_way == victim_way_q)
                          && (sn_hit_tag == victim_tag_q);

    // victim-buffer match (MAS ch02/05 bypass): while the drain is
    // outstanding the buffer owns the line (SINK_WB_ACK; gem5
    // .sm:1352/.sm:1357) -- victim_valid && (snoop line address ==
    // victim_addr), line offset ignored. Self-gating: valid is high
    // exactly from the gather-complete strobe to the drain-done edge, so
    // no state qualifier is needed (the pf and stale resolutions above
    // are state-gated to MISS_FILL, exclusive with the valid window).
    // The buffer only ever holds a dirty victim, so the reference state
    // is M with CD sourced from victim_data.
    //
    // A clean-all drain (req_maint_q) keeps the line installed at M in the
    // tag and data arrays, so the buffer is NOT the owner there: the snoop
    // resolves on the port-B tag hit (same M row, same data -- the array
    // is unchanged during the walk) and its downgrade is written to the
    // installed line, which CLEAN_COMMIT then leaves alone.
    logic victim_match;
    assign victim_match = victim_valid && !req_maint_q
                          && (w_sn_line_addr
                              == victim_buf_addr[ADDR_WIDTH-1:LINE_OFFSET_WIDTH]);

    // the upgrade's own line (installed S during the upgrade): an
    // invalidating snoop kills the upgrade (gem5 SM x Inv -> IM,
    // .sm:1526), realized as a post-commit Invalid install. upgr_q is
    // only meaningful while the upgrade fill waits, so the match is
    // state-gated -- a stale upgr_q must not suppress tag writes for
    // unrelated IDLE-time snoops (FULL soak found this)
    logic sn_upgr_line_gnt;
    assign sn_upgr_line_gnt = (state_q == OH_MISS_FILL) && upgr_q
                              && sn_hit_any
                              && ({sn_hit_tag, sn_set_grant} == req_line_addr);

    // grant-cycle reference state (CRRESP is combinational at the grant)
    logic [2:0] sn_ref_grant;
    assign sn_ref_grant = sn_pf_gnt_match  ? pf_state
                        : sn_stale_gnt     ? AMBER_STATE_I
                        : victim_match     ? AMBER_STATE_M
                        : sn_hit_any       ? sn_hit_state
                        :                    AMBER_STATE_I;

    // ------------------------------------------------------------------
    // Snoop grant: safe boundaries only (never mid-burst). In MISS_FILL
    // the first cycle cannot grant (the bypass arms at the cycle's edge)
    // and an upgrade grants against the installed S entry.
    // ------------------------------------------------------------------
    logic sn_idle_ok, sn_fill_ok, sn_drain_ok, sn_clean_ok, snoop_gnt;

    assign sn_idle_ok  = (state_q == OH_IDLE);
    assign sn_fill_ok  = (state_q == OH_MISS_FILL) && (upgr_q || pf_active);
    assign sn_drain_ok = (state_q == OH_MISS_DRAIN);
    // the clean-all walk's snoop-safe point (no fill, no bypass)
    assign sn_clean_ok = (state_q == OH_CLEAN_SCAN);
    assign snoop_gnt   = ctrl_snoop_req && (sn_idle_ok || sn_fill_ok
                                            || sn_drain_ok || sn_clean_ok);

    assign ctrl_snoop_ready = snoop_gnt;
    // snoop-safe: the states in which a newly accepted AC can be granted
    // immediately (no skid-delayed state change that could arm a same-line
    // bypass before the grant). Independent of ctrl_snoop_req to avoid a
    // combinational loop with the snoop responder.
    assign ctrl_snoop_safe  = sn_idle_ok || sn_fill_ok || sn_drain_ok
                              || sn_clean_ok;
    assign ctrl_tag_b_req   = snoop_gnt || (state_q == OH_SNOOP);
    assign ctrl_tag_b_set   = (state_q == OH_SNOOP) ? sn_set_q
                                                    : sn_set_grant;

    // ------------------------------------------------------------------
    // Miss-path K-map (workbook "K-maps amber control"), evaluated in
    // CTRL_MISS_VICTIM where hit == 0 by construction. The bypass axis is
    // real logic; on the CPU path it is constant-0 by construction (the
    // pf register's lifetime is exactly CTRL_MISS_FILL..CTRL_FILL_WRITE of
    // the single outstanding transaction), so replay_now is defensive.
    // ------------------------------------------------------------------
    logic [2:0] mv_victim_state;
    logic       bypass_match;
    logic       kmap_victim_dirty;
    logic       kmap_start_drain;
    logic       kmap_start_fill;
    logic       kmap_replay_now;

    assign mv_victim_state   = ctrl_tag_a_tag_state[32'(ctrl_repl_way)][2:0];
    assign bypass_match      = pf_active && (req_line_addr == pf_addr);
    assign kmap_victim_dirty = (mv_cnt_q == '0)
                               ? (mv_victim_state == AMBER_STATE_M)
                               : (victim_state_q == AMBER_STATE_M);
    assign kmap_start_drain  = kmap_victim_dirty && !bypass_match;
    assign kmap_start_fill   = !kmap_victim_dirty && !bypass_match;
    assign kmap_replay_now   = bypass_match;

    // grant-cycle CRRESP, latched into sn_dt_q at the grant
    logic [AMBER_CRRESP_WIDTH-1:0] sn_crresp_grant;

    assign sn_crresp_grant = amber_snoop_crresp(sn_ref_grant,
                                                ctrl_snoop_type);

    // snoop-side decode of the latched context (final service cycle).
    // pend_eff chaining (BUG-004): on a pending-fill / upgrade-line
    // resolution with an armed post-commit effect, the next state
    // resolves against the ARMED state -- the state the commit will
    // install -- not the original post-fill reference (gem5 _im_step
    // chaining; mapping-notes divergence 3: the armed effect is sticky).
    // The grant-cycle CRRESP stays at the post-fill row (sn_ref_grant
    // above): the bypass answers at pf_state, never at the pending
    // effect.  Scoped to the pending line only: an installed-line tag
    // write (sn_wr_tag) has !sn_pf_q && !sn_upgr_line_q, so it still
    // resolves against the array hit state.  I-sticks falls out: armed I
    // -> effective I -> every next state is I.
    logic [2:0] sn_eff_ref;
    logic [2:0] w_sn_nxt;
    assign sn_eff_ref = ((sn_pf_q || sn_upgr_line_q) && pend_vld_q)
                        ? pend_state_q : sn_ref_q;
    assign w_sn_nxt = amber_snoop_next_state(sn_eff_ref, sn_type_q);

    // tag downgrade/invalidate write on an installed line, applied on the
    // port-A cycle inside the service
    logic sn_wr_tag;
    assign sn_wr_tag = sn_hit_any_q && !sn_pf_q && !sn_stale_q
                       && !sn_victim_q && !sn_upgr_line_q
                       && (w_sn_nxt != sn_hit_state_q);

    // CD beat channel + service completion
    logic sn_beat_gated, sn_complete;

    // DATA_SYNC_READ: a fill beat landing at edge e collides with the
    // registered port-B read of the same beat at e (read-before-write ->
    // old word), so the beat streams one cycle later, after a clean
    // re-read. The delayed valid is exactly that cycle.
    logic [FILL_BEATS-1:0] pf_data_valid_d1;
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) pf_data_valid_d1 <= '0;
        else                      pf_data_valid_d1 <= pf_data_valid;
    )
    wire [FILL_BEATS-1:0] pf_data_valid_rd =
        DATA_SYNC_READ ? pf_data_valid_d1 : pf_data_valid;

    assign sn_beat_gated = sn_dt_q
                           && (sn_pf_q ? pf_data_valid_rd[32'(sn_beat_q)]
                                       : 1'b1);
    assign sn_complete   = sn_dt_q
                           ? (sn_beat_gated && ctrl_cdready
                              && (sn_beat_q == BEAT_INDEX_WIDTH'(FILL_BEATS-1)))
                           : 1'b1;

    wire init_last = (init_cnt_q == SET_INDEX_WIDTH'(SETS - 1));

    // ------------------------------------------------------------------
    // Clean-all walk (TASK-004): the first Modified way of the cursor set
    // (port A reads req_set), the last-set flag, and the commit check
    // (the victim way still holds the cleaned line at M -- a snoop
    // granted during the drain may have moved it)
    // ------------------------------------------------------------------
    logic                       cl_m_any;
    logic [WAY_INDEX_WIDTH-1:0] cl_m_way;
    logic [TAG_WIDTH-1:0]       cl_m_tag;

    always_comb begin
        cl_m_any = 1'b0;
        cl_m_way = '0;
        cl_m_tag = '0;
        for (int w = 0; w < WAYS; w++) begin
            if (!cl_m_any
                && ctrl_tag_a_tag_state[w][2:0] == AMBER_STATE_M) begin
                cl_m_any = 1'b1;
                cl_m_way = WAY_INDEX_WIDTH'(w);
                cl_m_tag = ctrl_tag_a_tag_state[w][TAG_STATE_WIDTH-1 -: TAG_WIDTH];
            end
        end
    end

    wire cl_last = (req_set == SET_INDEX_WIDTH'(SETS - 1));
    wire cl_commit_m = (ctrl_tag_a_tag_state[32'(victim_way_q)]
                        == {victim_tag_q, AMBER_STATE_M});

    // ------------------------------------------------------------------
    // Next-state logic
    // ------------------------------------------------------------------
    always_comb begin
        state_d = OH_ERROR;   // illegal / multi-hot / reserved default
        unique case (state_q)
            OH_IDLE: begin
                if (snoop_gnt) state_d = OH_SNOOP;   // snoop priority
                else if (acc)  state_d = acc_fast_rd ? OH_HIT_RD
                                       : acc_fast_wr ? OH_HIT_WR
                                       :               OH_LOOKUP;
                else           state_d = OH_IDLE;
            end
            OH_INIT: begin
                if (init_last) state_d = OH_IDLE;
                else           state_d = OH_INIT;
            end
            OH_LOOKUP: begin
                if (req_maint_q) begin
                    state_d = OH_CLEAN_SCAN;                   // clean-all
                end else if (!req_we_q && hit_any) begin
                    state_d = OH_HIT_RD;                       // read hit
                end else if (req_we_q
                             && (hit_state == AMBER_STATE_E
                                 || hit_state == AMBER_STATE_M)) begin
                    state_d = OH_HIT_WR;                       // write hit
                end else if (req_we_q && hit_state == AMBER_STATE_S) begin
                    state_d = OH_MISS_FILL;                    // upgrade
                end else begin
                    state_d = OH_MISS_VICTIM;                  // miss
                end
            end
            OH_HIT_RD: begin
                // back-to-back: a request accepted here is classified as
                // in IDLE (no snoop can be granted in HIT_RD)
                if (acc)       state_d = acc_fast_rd ? OH_HIT_RD
                                       : acc_fast_wr ? OH_HIT_WR
                                       :               OH_LOOKUP;
                else           state_d = OH_IDLE;
            end
            OH_HIT_WR: state_d = OH_IDLE;
            OH_MISS_VICTIM: begin
                if (kmap_replay_now) begin
                    state_d = OH_REPLAY;                       // defensive
                end else if (mv_cnt_q == '0 && kmap_start_fill) begin
                    state_d = OH_MISS_FILL;                    // clean victim
                end else if (mv_cnt_q == MV_END) begin
                    state_d = OH_MISS_DRAIN;                   // victim staged
                end else begin
                    state_d = OH_MISS_VICTIM;                  // gathering
                end
            end
            OH_MISS_DRAIN: begin
                if (snoop_gnt) state_d = OH_SNOOP;
                else if (drain_seen_q && drain_done_q)
                    state_d = req_maint_q ? OH_CLEAN_COMMIT : OH_MISS_FILL;
                else                               state_d = OH_MISS_DRAIN;
            end
            OH_MISS_FILL: begin
                if (snoop_gnt) state_d = OH_SNOOP;
                else if (fill_seen_q && fill_done_q) state_d = OH_FILL_WRITE;
                else                             state_d = OH_MISS_FILL;
            end
            OH_FILL_WRITE: state_d = OH_REPLAY;
            OH_REPLAY:     state_d = OH_LOOKUP;
            OH_SNOOP: begin
                if (sn_complete) begin
                    state_d = sn_back_to_lookup_q ? OH_LOOKUP : sn_return_q;
                end else begin
                    state_d = OH_SNOOP;
                end
            end
            OH_CLEAN_SCAN: begin
                if (snoop_gnt)     state_d = OH_SNOOP;         // yield
                else if (cl_m_any) state_d = OH_CLEAN_GATHER;
                else if (cl_last)  state_d = OH_CLEAN_RSP;
                else               state_d = OH_CLEAN_SCAN;    // next set
            end
            OH_CLEAN_GATHER: begin
                if (mv_cnt_q == (BEAT_INDEX_WIDTH+1)'(FILL_BEATS))
                    state_d = OH_MISS_DRAIN;                   // staged
                else
                    state_d = OH_CLEAN_GATHER;
            end
            OH_CLEAN_COMMIT: state_d = OH_CLEAN_SCAN;          // same set
            OH_CLEAN_RSP:    state_d = OH_IDLE;
            OH_ERROR: state_d = OH_ERROR;                      // sticky
            default:  state_d = OH_ERROR;
        endcase
    end

    // ------------------------------------------------------------------
    // State + context registers
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            state_q        <= OH_INIT;
            req_addr_q     <= '0;
            req_we_q       <= 1'b0;
            req_be_q       <= '0;
            req_wdata_q    <= '0;
            req_maint_q    <= 1'b0;
            hit_way_q      <= '0;
            hit_state_q    <= AMBER_STATE_I;
            req_class_q    <= AMBER_ACE_READ_SHARED;
            upgr_q         <= 1'b0;
            victim_way_q   <= '0;
            victim_tag_q   <= '0;
            victim_state_q <= AMBER_STATE_I;
            mv_cnt_q       <= '0;
            fill_seen_q    <= 1'b0;
            fill_done_q    <= 1'b0;
            fill_pass_dirty_q <= 1'b0;
            drain_seen_q   <= 1'b0;
            drain_done_q   <= 1'b0;
            hit_run_q      <= '0;
            hit_again_q    <= 1'b0;
            init_cnt_q     <= '0;
            sn_addr_q      <= '0;
            sn_type_q      <= '0;
            sn_beat_q      <= '0;
            sn_return_q    <= OH_IDLE;
            sn_back_to_lookup_q <= 1'b0;
            sn_pf_q        <= 1'b0;
            sn_hit_any_q   <= 1'b0;
            sn_hit_way_q   <= '0;
            sn_hit_state_q <= AMBER_STATE_I;
            sn_hit_tag_q   <= '0;
            sn_stale_q     <= 1'b0;
            sn_victim_q    <= 1'b0;
            sn_upgr_line_q <= 1'b0;
            sn_dt_q        <= 1'b0;
            sn_ref_q       <= AMBER_STATE_I;
            pend_vld_q     <= 1'b0;
            pend_state_q   <= AMBER_STATE_I;
        end else begin
            state_q <= state_d;

            // run of back-to-back accepts in HIT_RD (cleared by any other
            // cycle), and the HIT_RD-from-HIT_RD flag
            hit_run_q   <= (state_q == OH_HIT_RD && acc)
                           ? hit_run_q + 1'b1 : '0;
            hit_again_q <= (state_q == OH_HIT_RD) && acc;

            // partner done pulses are latched cycle-exact, from any state,
            // so a CTRL_SNOOP detour can never miss them
            if (ctrl_fill_done)  fill_done_q  <= 1'b1;
            if (ctrl_drain_done) drain_done_q <= 1'b1;

            // snoop context is latched at the grant (cycle-exact)
            if (snoop_gnt) begin
                sn_addr_q      <= ctrl_snoop_addr;
                sn_type_q      <= ctrl_snoop_type;
                sn_beat_q      <= '0;
                sn_return_q    <= state_q;
                sn_back_to_lookup_q <= (state_q == OH_IDLE) && req_valid;
                sn_pf_q        <= sn_pf_gnt_match;
                sn_hit_any_q   <= sn_hit_any;
                sn_hit_way_q   <= sn_hit_way;
                sn_hit_state_q <= sn_hit_state;
                sn_hit_tag_q   <= sn_hit_tag;
                sn_stale_q     <= sn_stale_gnt;
                sn_victim_q    <= victim_match;
                sn_upgr_line_q <= sn_upgr_line_gnt;
                sn_dt_q        <= sn_crresp_grant[AMBER_CRRESP_DT];
                sn_ref_q       <= sn_ref_grant;
            end else if (state_q == OH_SNOOP) begin
                if (sn_beat_gated && ctrl_cdready) begin
                    sn_beat_q <= sn_beat_q + 1'b1;
                end
            end

            // post-commit snoop effect on the pending line: armed at the
            // end of the snoop service, consumed at fill commit. Only a
            // snoop that CHANGES the resolved reference state arms the
            // register (a fixed-point snoop -- e.g. READ_SHARED on an
            // installed/pending S -- is a no-op); the resolution chains
            // against the armed state (sn_eff_ref above, BUG-004), so an
            // armed downgrade survives a later READ_ONCE and an armed
            // invalidation is never overwritten (invalidation-sticks).
            if (state_q == OH_SNOOP && sn_complete
                && (sn_return_q == OH_MISS_FILL)
                && (sn_pf_q || sn_upgr_line_q)
                && (w_sn_nxt != sn_ref_q)) begin
                if (w_sn_nxt == AMBER_STATE_I) begin
                    pend_vld_q   <= 1'b1;
                    pend_state_q <= AMBER_STATE_I;
                end else if (w_sn_nxt == AMBER_STATE_S && !pend_vld_q) begin
                    pend_vld_q   <= 1'b1;
                    pend_state_q <= AMBER_STATE_S;
                end
            end

            // the accept (IDLE or HIT_RD): latch the request and its
            // accept-cycle classification (LOOKUP re-classifies a non-hit).
            // IDLE latches on req_valid even under a snoop grant (the
            // request is then classified in LOOKUP after the snoop).
            if (((state_q == OH_IDLE) && req_valid) || acc) begin
                req_addr_q  <= req_addr;
                req_we_q    <= req_we;
                req_be_q    <= req_be;
                req_wdata_q <= req_wdata;
                req_maint_q <= req_maint;
                hit_way_q   <= hit_way;
                hit_state_q <= hit_state;
            end

            unique case (state_q)
                OH_IDLE: ;   // the accept is latched above
                OH_HIT_RD: ;
                OH_INIT: begin
                    if (!init_last) init_cnt_q <= init_cnt_q + 1'b1;
                end
                OH_LOOKUP: begin
                    hit_way_q   <= hit_way;
                    hit_state_q <= hit_state;
                    upgr_q      <= 1'b0;
                    // clean-all: the walk cursor is req_addr_q's set field
                    // (beat and offset 0), starting at set 0
                    if (req_maint_q) req_addr_q <= '0;
                    if (req_we_q && hit_state == AMBER_STATE_S) begin
                        req_class_q <= AMBER_ACE_CLEAN_UNIQUE;  // upgrade
                        upgr_q      <= 1'b1;
                    end else if (!hit_any) begin
                        // true miss (I, or no tag match)
                        req_class_q <= req_we_q ? AMBER_ACE_READ_UNIQUE
                                                : AMBER_ACE_READ_NOT_SHARED_DIRTY;
                    end
                end
                OH_MISS_VICTIM: begin
                    if (mv_cnt_q == '0) begin
                        victim_way_q   <= ctrl_repl_way;
                        victim_tag_q   <=
                            ctrl_tag_a_tag_state[32'(ctrl_repl_way)]
                                                [TAG_STATE_WIDTH-1 -: TAG_WIDTH];
                        victim_state_q <= mv_victim_state;
                        mv_cnt_q       <= mv_cnt_q + 1'b1;
                    end else if (mv_cnt_q < MV_END) begin
                        mv_cnt_q <= mv_cnt_q + 1'b1;
                    end else begin
                        mv_cnt_q <= '0;
                    end
                end
                OH_MISS_FILL: begin
                    fill_seen_q <= 1'b1;
                    // Gate the PassDirty capture with fill_seen_q: the
                    // first cycle of MISS_FILL is entered while l1_fill is
                    // still in F_IDLE and its pass_dirty_q still carries the
                    // previous transaction's value; wait one cycle for
                    // l1_fill to latch the new class and reset pass_dirty_q.
                    if (fill_seen_q && ctrl_fill_pass_dirty)
                        fill_pass_dirty_q <= 1'b1;
                end
                OH_MISS_DRAIN: begin
                    drain_seen_q <= 1'b1;
                end
                OH_CLEAN_SCAN: begin
                    if (!snoop_gnt) begin
                        if (cl_m_any) begin
                            victim_way_q   <= cl_m_way;
                            victim_tag_q   <= cl_m_tag;
                            victim_state_q <= AMBER_STATE_M;
                            mv_cnt_q       <= '0;
                        end else if (!cl_last) begin
                            req_addr_q[LINE_OFFSET_WIDTH +: SET_INDEX_WIDTH]
                                <= req_set + 1'b1;
                        end
                    end
                end
                OH_CLEAN_GATHER: begin
                    if (mv_cnt_q < (BEAT_INDEX_WIDTH+1)'(FILL_BEATS))
                        mv_cnt_q <= mv_cnt_q + 1'b1;
                    else
                        mv_cnt_q <= '0;
                end
                OH_CLEAN_COMMIT: begin
                    drain_seen_q <= 1'b0;
                    drain_done_q <= 1'b0;
                end
                OH_FILL_WRITE: begin
                    mv_cnt_q     <= '0;
                    fill_seen_q  <= 1'b0;
                    fill_done_q  <= 1'b0;
                    fill_pass_dirty_q <= 1'b0;
                    drain_seen_q <= 1'b0;
                    drain_done_q <= 1'b0;
                    pend_vld_q   <= 1'b0;
                end
                default: ;   // ERROR / SNOOP / illegal: context already latched
            endcase
        end
    )

    // ------------------------------------------------------------------
    // Victim line payload (the ONE copy of the dirty victim line). Gathered
    // a beat per MISS_VICTIM cycle from data-array port A; held unchanged
    // from the gather-complete strobe through the drain's last W beat
    // (single-outstanding miss flow: MISS_VICTIM -> MISS_DRAIN -> MISS_FILL,
    // and a snoop detour never writes it). Qualified by mv_cnt_q /
    // victim_valid, so it carries no reset: a payload register under the
    // async reset macro cannot be a RAM and costs a recovery-timed reset
    // net on the FPGA for no functional gain (GLOBAL_REQUIREMENTS 1.4
    // shape; FPGA review 2026-11-07). The drain and the snoop CD bypass
    // both read it by beat (ctrl_victim_beat_data / victim_sn_word), so
    // the store is one word per beat and maps to distributed RAM.
    // ------------------------------------------------------------------
    // the registered read's lead cycle (mv_cnt_q == 0) captures nothing
    wire mv_cap = (state_q == OH_MISS_VICTIM)
                  && !(DATA_SYNC_READ && mv_cnt_q == '0)
                  && mv_cnt_q < MV_END;
    wire cg_cap = (state_q == OH_CLEAN_GATHER)
                  && mv_cnt_q < (BEAT_INDEX_WIDTH+1)'(FILL_BEATS);
    wire [BEAT_INDEX_WIDTH-1:0] cap_beat = mv_cap
        ? BEAT_INDEX_WIDTH'(mv_cnt_q - (BEAT_INDEX_WIDTH+1)'(MV_LEAD))
        : mv_cnt_q[BEAT_INDEX_WIDTH-1:0];

    always_ff @(posedge clk) begin
        if (mv_cap || cg_cap) begin
            victim_line_mem[cap_beat] <= ctrl_data_a_rdata;
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) cl_commit_m_q <= 1'b0;
        else                      cl_commit_m_q <= cl_commit_m;
    )

    // ------------------------------------------------------------------
    // Outputs
    // ------------------------------------------------------------------
    always_comb begin
        // tag array port A: the arriving request's set in a state that
        // can accept (classified there; see cmp_tag for why the select is
        // acc_ok), the latched set otherwise
        ctrl_tag_a_set           = acc_ok ? acc_set : req_set;
        ctrl_tag_a_wr_en         = 1'b0;
        ctrl_tag_a_wr_way_onehot = '0;
        ctrl_tag_a_wr_set        = req_set;
        ctrl_tag_a_wr_tag_state  = '0;

        // data array port A. Registered read: the arriving request's word
        // is read at its accept edge and consumed in HIT_RD the next
        // cycle; selected on acc_ok like the tag port (a read in an
        // accepting state with no request lands in IDLE or SNOOP, which
        // never consume port A). Combinational read: HIT_RD reads its own
        // latched address in its own cycle, so an accept there must not
        // move the port.
        ctrl_data_a_addr = (DATA_SYNC_READ && acc_ok) ? {acc_set, acc_beat}
                                                      : {req_set, req_beat};
        ctrl_data_a_way  = hit_way_q;
        ctrl_data_a_wr_en         = 1'b0;
        ctrl_data_a_wr_way_onehot = hit_way_onehot;
        ctrl_data_a_wr_addr       = {req_set, req_beat};
        ctrl_data_a_wr_wdata      = req_wdata_q;
        ctrl_data_a_wr_be         = req_be_q;

        // data array port B (snoop CD beat read: the bypass serves the
        // fill way -- the fill's beats -- an installed hit its own way)
        ctrl_data_b_addr = {sn_set_q, sn_beat_q};
        ctrl_data_b_way  = sn_pf_q ? victim_way_q : sn_hit_way_q;
        if (DATA_SYNC_READ) begin
            // registered read: present the beat the NEXT cycle streams --
            // beat 0 of the granted line at the grant, the post-handshake
            // beat during the stream (held while the beat is gated)
            if (snoop_gnt)
                ctrl_data_b_addr = {sn_set_grant, {BEAT_INDEX_WIDTH{1'b0}}};
            else if (state_q == OH_SNOOP && sn_beat_gated && ctrl_cdready)
                ctrl_data_b_addr = {sn_set_q,
                                    BEAT_INDEX_WIDTH'(sn_beat_q + 1'b1)};
        end

        // replacement
        ctrl_repl_req     = 1'b0;
        ctrl_repl_set     = req_set;
        ctrl_repl_hit     = 1'b0;
        ctrl_repl_update  = 1'b0;
        ctrl_repl_hit_way = hit_way_q;

        // victim / fill / drain
        ctrl_victim_load    = 1'b0;
        ctrl_victim_addr_in = {victim_tag_q, req_set,
                               {LINE_OFFSET_WIDTH{1'b0}}};
        ctrl_fill_start     = 1'b0;
        ctrl_fill_addr      = req_line_base;
        ctrl_drain_start    = 1'b0;

        // snoop responder channel
        ctrl_crresp  = amber_snoop_crresp(
            (state_q == OH_SNOOP) ? sn_ref_q : sn_ref_grant,
            (state_q == OH_SNOOP) ? sn_type_q : ctrl_snoop_type);
        // CD data: a victim-buffer hit is sourced from the buffer (MAS
        // ch02/05 bypass -- the line is owned there while the drain is
        // outstanding); every other transfer reads the data array on
        // port B
        ctrl_cddata  = sn_victim_q ? victim_sn_word : ctrl_data_b_rdata;
        ctrl_cdlast  = 1'b0;
        ctrl_cdvalid = 1'b0;

        unique case (state_q)
            OH_INIT: begin
                // The walk starts with the first cycle after reset
                // deassertion: exactly SETS writes, one per cycle, and no
                // write while reset is asserted (crisp observable contract).
                ctrl_tag_a_wr_en         = !`RST_ASSERTED(rst_n);
                ctrl_tag_a_wr_way_onehot = {WAYS{1'b1}};
                ctrl_tag_a_wr_set        = init_cnt_q;
                ctrl_tag_a_wr_tag_state  = { {TAG_WIDTH{1'b0}}, AMBER_STATE_I };
            end
            OH_LOOKUP: begin
                // the default {req_set, req_beat}: read at this edge,
                // consumed in HIT_RD. A miss does NOT move the address
                // here (that put the hit compare and the next-state decode
                // in front of the array address); MISS_VICTIM's lead cycle
                // presents beat 0 instead
            end
            OH_HIT_WR: begin
                // byte-merge write; promote E->M (M keeps its tag entry).
                // The promotion write targets the hit way -- the one-hot
                // must be driven here (a zero one-hot is a silent drop:
                // found by the Task 7 closed loop's E-seeded write hits).
                ctrl_data_a_wr_en = 1'b1;
                ctrl_tag_a_wr_en  = (hit_state_q != AMBER_STATE_M);
                ctrl_tag_a_wr_way_onehot = hit_way_onehot;
                ctrl_tag_a_wr_tag_state = {req_tag, AMBER_STATE_M};
                ctrl_repl_hit     = 1'b1;
            end
            OH_HIT_RD: begin
                ctrl_repl_hit = 1'b1;
            end
            OH_MISS_VICTIM: begin
                // cycle k presents beat k on both read flavours; the
                // registered read captures it at k+1 (MV_LEAD). The way
                // select is after the register: cycle 0 captures only on a
                // combinational read, from the way the engine names now
                if (mv_cnt_q == '0) begin
                    ctrl_repl_req = 1'b1;
                    ctrl_data_a_addr = {req_set, {BEAT_INDEX_WIDTH{1'b0}}};
                    ctrl_data_a_way  = ctrl_repl_way;
                end else if (mv_cnt_q < MV_END) begin
                    ctrl_data_a_addr = {req_set, mv_cnt_q[BEAT_INDEX_WIDTH-1:0]};
                    ctrl_data_a_way  = victim_way_q;
                end else begin
                    ctrl_victim_load = 1'b1;
                end
            end
            OH_CLEAN_GATHER: begin
                // the MISS_VICTIM gather on the latched M way (the way was
                // latched in CLEAN_SCAN; beat 0's address was presented
                // there -- req_beat is 0 on the walk cursor)
                ctrl_data_a_way = victim_way_q;
                if (mv_cnt_q < (BEAT_INDEX_WIDTH+1)'(FILL_BEATS))
                    ctrl_data_a_addr = {req_set,
                        DATA_SYNC_READ ? BEAT_INDEX_WIDTH'(mv_cnt_q + 1'b1)
                                       : mv_cnt_q[BEAT_INDEX_WIDTH-1:0]};
                else
                    ctrl_victim_load = 1'b1;
            end
            OH_CLEAN_COMMIT: begin
                // the WriteClean's B is in: M -> E, unless a snoop during
                // the drain already moved the line
                ctrl_tag_a_wr_en         = cl_commit_m_q;
                ctrl_tag_a_wr_way_onehot = victim_way_onehot;
                ctrl_tag_a_wr_tag_state  = {victim_tag_q, AMBER_STATE_E};
            end
            OH_MISS_FILL: begin
                ctrl_fill_start = !fill_seen_q;
            end
            OH_MISS_DRAIN: begin
                ctrl_drain_start = !drain_seen_q;
            end
            OH_FILL_WRITE: begin
                ctrl_tag_a_wr_en         = 1'b1;
                ctrl_tag_a_wr_way_onehot = upgr_q ? hit_way_onehot
                                                  : victim_way_onehot;
                ctrl_tag_a_wr_tag_state  = {req_tag, install_state_eff};
                if (upgr_q) begin
                    ctrl_repl_hit     = 1'b1;   // upgrade = an access
                    ctrl_repl_hit_way = hit_way_q;
                end else begin
                    ctrl_repl_update  = 1'b1;   // install into victim way
                    ctrl_repl_hit_way = victim_way_q;
                end
            end
            OH_SNOOP: begin
                // CD beats: each beat is presented only when servable (the
                // bypass gates on pf_data_valid and stalls until the fill
                // delivers the beat); cdlast marks the final beat
                ctrl_cdvalid = sn_beat_gated;
                ctrl_cdlast  = (sn_beat_q == BEAT_INDEX_WIDTH'(FILL_BEATS-1));
                // downgrade/invalidate on an installed line: applied on
                // this port-A cycle (the waiting states never write port A)
                if (sn_complete && sn_wr_tag) begin
                    ctrl_tag_a_wr_en         = 1'b1;
                    ctrl_tag_a_wr_way_onehot = sn_hit_way_onehot;
                    ctrl_tag_a_wr_set        = sn_set_q;
                    ctrl_tag_a_wr_tag_state  = {sn_hit_tag_q, w_sn_nxt};
                end
            end
            default: ;
        endcase
    end

    // request/response + init status
    // ready: registers only (the state and the run counter). The response
    // is valid IN the hit state (TASK-005; it was registered a cycle later
    // before): HIT_RD's word comes straight off port A (registered read,
    // way-selected by hit_way_q), HIT_WR echoes the request's data.
    assign ctrl_req_ready = acc_ok;
    assign ctrl_rsp_valid = (state_q == OH_HIT_RD) || (state_q == OH_HIT_WR)
                            || (state_q == OH_CLEAN_RSP);
    // a clean-all response echoes the request's wdata (the CPU drives 0)
    assign ctrl_rsp_data  = (state_q == OH_HIT_WR || state_q == OH_CLEAN_RSP)
                            ? req_wdata_q : ctrl_data_a_rdata;
    assign ctrl_drain_clean = req_maint_q;
    assign ctrl_init_busy = (state_q == OH_INIT);
    assign ctrl_init_set  = init_cnt_q;

    // the request class of the in-flight miss, for l1_fill/amber_ace_issue
    assign ctrl_req_class = req_class_q;

    // FSM observability: one-hot -> pkg ctrl_state_t encoding
    always_comb begin
        unique case (state_q)
            OH_IDLE:        ctrl_state = 4'(AMBER_CTRL_IDLE);
            OH_INIT:        ctrl_state = 4'(AMBER_CTRL_INIT);
            OH_LOOKUP:      ctrl_state = 4'(AMBER_CTRL_LOOKUP);
            OH_HIT_RD:      ctrl_state = 4'(AMBER_CTRL_HIT_RD);
            OH_HIT_WR:      ctrl_state = 4'(AMBER_CTRL_HIT_WR);
            OH_MISS_VICTIM: ctrl_state = 4'(AMBER_CTRL_MISS_VICTIM);
            OH_MISS_DRAIN:  ctrl_state = 4'(AMBER_CTRL_MISS_DRAIN);
            OH_MISS_FILL:   ctrl_state = 4'(AMBER_CTRL_MISS_FILL);
            OH_FILL_WRITE:  ctrl_state = 4'(AMBER_CTRL_FILL_WRITE);
            OH_REPLAY:      ctrl_state = 4'(AMBER_CTRL_REPLAY);
            OH_SNOOP:       ctrl_state = 4'(AMBER_CTRL_SNOOP);
            OH_ERROR:       ctrl_state = 4'(AMBER_CTRL_ERROR);
            OH_CLEAN_SCAN:  ctrl_state = 4'(AMBER_CTRL_CLEAN_SCAN);
            OH_CLEAN_GATHER:ctrl_state = 4'(AMBER_CTRL_CLEAN_GATHER);
            OH_CLEAN_COMMIT:ctrl_state = 4'(AMBER_CTRL_CLEAN_COMMIT);
            OH_CLEAN_RSP:   ctrl_state = 4'(AMBER_CTRL_CLEAN_RSP);
            default:        ctrl_state = 4'(AMBER_CTRL_ERROR);
        endcase
    end

endmodule : l1_control
