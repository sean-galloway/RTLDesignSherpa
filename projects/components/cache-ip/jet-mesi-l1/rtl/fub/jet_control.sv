// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_control
// Purpose:
//   Lookup + commit control core of the jet (lockup-free MESI L1) -- the
//   two halves of the lookup/commit split that replaces amber's blocking
//   l1_control FSM (MAS ch02_blocks/01).  Lookup: one request, one window
//   (the tag read on port A, the MSHR CAM match, the WB-buffer match, and
//   the set's victim-way claim count all visible in the same cycle, the
//   PoS), classified HIT / MERGE / MISS_ALLOC / STALL with the J6 stall
//   sub-reasons.  Commit: on fill_done for the head of the completion
//   queue (fill-engine order = launch order, single AXI4 read ID), the
//   four MAS steps in order -- D-4 store-data merge onto the just-filled
//   beats, tag install (S for RNSD unless PassDirty, M otherwise: amber's
//   #106 rule; M for a write fill), deferred snoop effect applied AFTER
//   the install, then the response deposits (one per merge-list sequence
//   tag, in tag order) and the MSHR retire.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch02_blocks/01_jet_control.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_control
//==============================================================================
// Description:
//   The lookup stage is combinational classify + accept around a small
//   amount of sequential state (the init walk, the victim-capture engine,
//   the fill-launch hold register, the drain-arbiter stub, the
//   single-outstanding upgrade tracker, and the claimed-way scoreboard).
//   There is no global FSM: each MSHR entry independently walks its own
//   progress, and a stalled request is simply not accepted -- the front
//   end holds it and the next cycle's classify retries (this is also what
//   makes jet_mshr's no-grant-bypass-on-retire bubble harmless).
//
//   Classify (evaluated in this order; the first match wins):
//     0. UPGRADE-LINE WAIT -- any hit on the in-flight upgrade's line
//        stalls cross_class_wait until the upgrade's CU commit lands: the
//        write's data merge happens only at that commit, so a read
//        overtaking it would return stale data (request-order violation).
//     1. HIT -- line resident (S/E/M) and its way is not claimed by an
//        outstanding MSHR entry (the pending-fill hazard: a doomed
//        victim's tag is still installed until the fill's commit, but its
//        data is being captured/overwritten, so the hit is suppressed and
//        the request falls through to the miss path).  Read hits serve
//        from port A and deposit immediately.  Write hits (E/M) merge
//        through the data-array W port and promote E->M on the tag port;
//        they YIELD the W port to an in-flight fill beat stream or a
//        commit store-merge (fill beats > commit merge > write hits, both
//        bounded) by holding the request unaccepted.  A write hit on S is
//        an upgrade: JET_CLS_CU is launched to the fabric and the
//        single-outstanding upgrade tracker holds the line until the CU
//        commit (step 0).  Hit accepts are also held for the cycles the
//        commit pipeline owns the deposit port or the port-A read address
//        (commit deposits win; hits retry -- bounded by the merge-list
//        depth).
//     2. MERGE -- no hit, MSHR match, compatible class (a read joins any
//        fill; a write joins only an RU fill): the request's sequence tag
//        is appended to the entry's merge list and its we/beat/be/wdata
//        are recorded in the commit sideband table.  A write behind an
//        RNSD fill is the cross-class wait (STALL, J3).  A merge onto an
//        entry whose merge list is full stalls mshr_full.  A merge onto an
//        entry whose fill has completed stalls commit_in_progress (the
//        merge list is snapshot at commit start; release is the retire).
//     3. MISS_ALLOC -- no hit, no match, resources free: the MSHR entry
//        allocates (jet_mshr's alloc-first same-cycle rule makes it
//        visible to the snoop probe from this cycle), the victim way is
//        claimed from l1_repl AND the policy is updated at the alloc (so
//        back-to-back allocs in one set claim distinct ways; the commit
//        pipeline must NOT repl_update again at install), a dirty victim
//        opens a WB capture, and the fill launch is presented (held until
//        fill_accept_i).  Stall sub-reasons, in priority order:
//        cross_class_wait, WB drain-race (the request line is in the WB
//        buffer or being captured -- the fill must not race the
//        outstanding writeback; release: drain_done), mshr_full,
//        set_oversubscribed (WAYS claims in this set, the victim way is
//        the in-flight upgrade's way, OR the proposed victim way is
//        already claimed by a live entry -- the claim-aware victim check
//        that makes RANDOM (and LRU under hit reordering) safe without a
//        mask input on l1_repl; release: the conflicting entry's commit),
//        wb_full_dirty_victim (WB full or a capture is streaming AND the
//        victim is dirty -- clean-victim misses allocate freely with the
//        WB full, J6), tag_full (the response sequencer ring has no free
//        slot).
//     4. STALL -- lkup_stall_o + lkup_stall_reason_o report the reason;
//        the request is retried next cycle.  Holds that are not
//        congestion stalls (write-hit W-port yield, fill-launch register
//        busy, upgrade pipe busy, commit port ownership) depress
//        lkup_ready_o without raising lkup_stall_o.
//
//   Commit pipeline (one fill completion at a time, in completion order):
//   a small FSM walks C_MERGE -> C_INSTALL -> [C_PEND] -> C_DEPOSIT ->
//   C_RETIRE.  The completing entry is identified by the launch-order
//   completion queue (single AXI4 read ID: fills, including the
//   no-data CLEAN_UNIQUE upgrades, complete in launch order).  At the
//   commit start the entry's line/pend_eff/merge-list are snapshot from
//   the jet_mshr commit read port (one cycle; merges hold that cycle --
//   the port is otherwise the lookup stage's merge-room probe).  The
//   requester sideband table (we/beat/be/wdata per merge slot, recorded
//   at the alloc/merge accepts) drives C_MERGE: write slots merge their
//   store data onto the just-filled beats through the W port (amber D-4
//   byte-enable semantics, in requester order); read slots capture their
//   response beat from port A at their own position in the order, so a
//   read observes exactly the writes that precede it.  C_INSTALL writes
//   {tag, install_state}; C_PEND writes the deferred snoop effect
//   (downgrade-S / invalidate-I) AFTER the install (amber pending
//   semantics); C_DEPOSIT hands one response per merge-list tag to
//   jet_rsp_seq (write requesters echo their store data, read requesters
//   the captured beat); C_RETIRE retires the entry and frees the claim.
//   A CU completion walks C_CU_MERGE -> C_CU_INSTALL -> C_CU_DEPOSIT from
//   the upgrade tracker (merge the held write, install M, echo), clearing
//   the tracker -- the tracker clear is qualified by the completing
//   fill's identity through the completion queue.
//
//   Port arbitration (all holds bounded; commit progress is the liveness
//   anchor -- fills retiring is what frees MSHR entries):
//     data W port : fill beats > commit store merge > write-hit merge
//     tag W port  : init walk > commit install/pend > E->M promotion
//     deposit     : commit deposits > hit deposits (hits held)
//     port A read : commit read-beat capture > read hits (held)
//
//   Fill-engine contract: the engine must not write an entry's fill beats
//   before that entry's victim capture has completed.  Since captures run
//   in alloc order and fills launch in the same order, the simple engine
//   rule is: start no beat stream while cap_busy_o is high.  jet_control
//   owns the launch but cannot gate the engine's W-port drives, so the
//   contract is enforced by the engine (the unit-TB stub models it and
//   the scenario suite exercises it end-to-end).
//
//   The snoop path (Task 7, MAS ch02_blocks/05): one snoop at a time on
//   the l1_snoop_resp core-facing contract (the AC accept cycle is the
//   grant; CRRESP is combinational on the three probes -- WB snarf CAM,
//   MSHR snoop probe, tag port B -- in the fixed match order WB > MSHR >
//   array).  A WB match answers at M from a grant-cycle snapshot of the
//   buffer line (the BRESP-cycle ships-in-the-night corner).  An MSHR
//   match answers at the entry's post-fill install state (M for an RU
//   fill, S for RNSD -- never the Invalid row) with PF_GUARD:
//   DataTransfer/PassDirty are promised only when every fill beat has
//   landed at the grant (a snoop never waits on a fill), and the state
//   effect is recorded in the entry's pend_eff (invalidate dominates a
//   later downgrade -- I-sticks, via the shadow this module keeps as the
//   record's only driver).  An array hit answers at the installed state
//   with the downgrade/invalidate on the tag write port at the end of the
//   service; a tag hit on a claimed way is the doomed victim's stale tag
//   (amber's stale-victim rule: the Invalid row, no effect).  Snoops
//   arbitrate ahead of new CPU accepts (the lookup stage holds through
//   the grant and the service), and the commit pipeline never starts
//   during a service (the pend record must land before the commit's
//   snapshot).  sn_safe_o deasserts only in bounded windows: the init
//   walk, an active service, a fill-done-unretired entry (the commit
//   window), a victim capture streaming on port B, and the grant cycle of
//   a CLEAN_UNIQUE completion -- which with the commit window is the
//   anti-livelock hold-off (ch02/01: snoop service to the upgraded line
//   resumes when the granted write's commit lands; the bound is the CU
//   commit's own length, never event-dependent).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per l1_pkg defaults (shared with the arrays)
//     Type: int
//
//   MSHR_COUNT / VICTIM_DEPTH:
//     Description: J1/J5 geometry (forwarded to jet_mshr / jet_wb_buffer)
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - The D-3 init walk writes STATE_I to every way of every set, one set
//     per cycle; lookups are not accepted until it completes.
//   - lkup_ready_o is valid-qualified and combinational: the accept lands
//     on the posedge ending the presenting cycle.
//   - The stall reasons are the whole congestion story (J6): each has a
//     bounded release (an entry retires, a drain completes, a fill
//     commits, a response releases).
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: jet_control_th (unit DV); jet_top (Task 8)
//   - Drives: l1_tag_array / l1_data_array port A, l1_repl, jet_mshr,
//     jet_wb_buffer capture, jet_rsp_seq tag-alloc + deposit
//   - Package: jet_pkg (JET_CLS_*, JET_PEND_*, RSP_DEPTH derivation), l1_pkg
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_control.py
//   Plan: dv/testplans/jet_control_testplan.yaml
//   Run: pytest projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_control.py -v
//
//==============================================================================

module jet_control
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH   = AMBER_ADDR_WIDTH,
    parameter int SETS         = AMBER_SETS,
    parameter int WAYS         = AMBER_WAYS,
    parameter int LINE_BYTES   = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH    = AMBER_BUS_WIDTH,
    parameter int MSHR_COUNT   = jet_pkg::MSHR_COUNT,
    parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH,
    localparam int SET_W      = $clog2(SETS),
    localparam int OFF_W      = $clog2(LINE_BYTES),
    localparam int TAG_W      = ADDR_WIDTH - SET_W - OFF_W,
    localparam int TSW        = TAG_W + 3,
    localparam int STRB_W     = BUS_WIDTH / 8,
    localparam int FILL_BEATS = LINE_BYTES / STRB_W,
    localparam int BEAT_W     = $clog2(FILL_BEATS),
    localparam int WAY_W      = $clog2(WAYS),
    localparam int MEM_ADDR_W = SET_W + BEAT_W,
    localparam int LINE_W     = ADDR_WIDTH - OFF_W,
    localparam int MW         = $clog2(MSHR_COUNT),
    localparam int RSP_DEPTH  = MSHR_COUNT + 2,
    localparam int SEQ_W      = $clog2(RSP_DEPTH),
    localparam int WB_W       = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH),
    localparam int LINE_BITS  = LINE_BYTES * 8
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // init-walk status (D-3)
    output logic                        init_busy_o,

    // front-end lookup request (accept = lkup_valid_i & lkup_ready_o)
    input  logic                        lkup_valid_i,
    input  logic [ADDR_WIDTH-1:0]       lkup_addr_i,
    input  logic                        lkup_we_i,
    input  logic [STRB_W-1:0]           lkup_be_i,
    input  logic [BUS_WIDTH-1:0]        lkup_wdata_i,
    output logic                        lkup_ready_o,

    // classify observability (DV / MonBus taps): one-cycle accept pulses
    output logic                        lkup_hit_o,
    output logic                        lkup_merge_o,
    output logic                        lkup_miss_alloc_o,
    output logic                        lkup_upgrade_o,
    output logic                        lkup_stall_o,
    output logic [2:0]                  lkup_stall_reason_o,
    output logic                        lkup_wr_yield_o,
    output logic                        cap_busy_o,

    // response sequencer front end (jet_rsp_seq)
    output logic                        tag_req_o,
    input  logic                        tag_gnt_i,
    input  logic [SEQ_W-1:0]            tag_i,
    output logic                        cpl_valid_o,
    output logic [SEQ_W-1:0]            cpl_tag_o,
    output logic [BUS_WIDTH-1:0]        cpl_data_o,

    // tag array port A (lookup + init walk + E->M promotion)
    output logic [SET_W-1:0]            tag_a_set_o,
    input  logic [WAYS-1:0][TSW-1:0]    tag_a_tag_state_i,
    output logic                        tag_a_wr_en_o,
    output logic [WAYS-1:0]             tag_a_wr_way_onehot_o,
    output logic [SET_W-1:0]            tag_a_wr_set_o,
    output logic [TSW-1:0]              tag_a_wr_tag_state_o,

    // data array port A (hit read + write-hit merge)
    output logic [MEM_ADDR_W-1:0]       dat_a_addr_o,
    output logic [WAY_W-1:0]            dat_a_way_o,
    input  logic [BUS_WIDTH-1:0]        dat_a_rdata_i,
    output logic                        dat_a_wr_en_o,
    output logic [WAYS-1:0]             dat_a_wr_way_onehot_o,
    output logic [MEM_ADDR_W-1:0]       dat_a_wr_addr_o,
    output logic [BUS_WIDTH-1:0]        dat_a_wr_wdata_o,
    output logic [STRB_W-1:0]           dat_a_wr_be_o,

    // data array port B (victim capture + the snoop CD read, Task 7)
    output logic [MEM_ADDR_W-1:0]       dat_b_addr_o,
    output logic [WAY_W-1:0]            dat_b_way_o,
    input  logic [BUS_WIDTH-1:0]        dat_b_rdata_i,

    // replacement engine (victim claimed AND policy-updated at alloc)
    output logic                        repl_req_o,
    output logic [SET_W-1:0]            repl_set_o,
    input  logic [WAY_W-1:0]            repl_victim_way_i,
    output logic                        repl_hit_o,
    output logic                        repl_update_o,
    output logic [WAY_W-1:0]            repl_hit_way_o,

    // MSHR file (jet_mshr)
    output logic                        mshr_alloc_o,
    output logic [LINE_W-1:0]           mshr_alloc_line_o,
    output logic [SET_W-1:0]            mshr_alloc_set_o,
    output logic [1:0]                  mshr_alloc_cls_o,
    output logic                        mshr_alloc_install_o,
    output logic [WAY_W-1:0]            mshr_alloc_victim_way_o,
    output logic [WB_W-1:0]             mshr_alloc_wb_slot_o,
    output logic                        mshr_alloc_wb_valid_o,
    output logic [SEQ_W-1:0]            mshr_alloc_seq_o,
    input  logic                        mshr_alloc_gnt_i,
    input  logic [MW-1:0]               mshr_alloc_idx_i,
    input  logic                        mshr_full_i,
    input  logic                        mshr_set_full_i,
    output logic [LINE_W-1:0]           mshr_lkup_line_o,
    input  logic                        mshr_lkup_reg_match_i,
    input  logic [MW-1:0]               mshr_lkup_reg_match_idx_i,
    input  logic [1:0]                  mshr_lkup_reg_match_cls_i,
    output logic [MW-1:0]               mshr_cpl_idx_o,
    input  logic [MW:0]                 mshr_cpl_merge_count_i,
    input  logic [LINE_W-1:0]           mshr_cpl_line_i,
    input  logic [1:0]                  mshr_cpl_pend_eff_i,
    input  logic [MSHR_COUNT*SEQ_W-1:0] mshr_cpl_merge_seqs_i,
    output logic                        mshr_merge_o,
    output logic [MW-1:0]               mshr_merge_idx_o,
    output logic [SEQ_W-1:0]            mshr_merge_seq_o,
    output logic                        mshr_beat_o,
    output logic [MW-1:0]               mshr_beat_idx_o,
    output logic [BEAT_W-1:0]           mshr_beat_num_o,
    output logic                        mshr_retire_o,
    output logic [MW-1:0]               mshr_retire_idx_o,

    // WB buffer (jet_wb_buffer)
    output logic                        wb_cap_o,
    output logic [LINE_W-1:0]           wb_cap_line_o,
    output logic                        wb_cap_beat_o,
    output logic [BUS_WIDTH-1:0]        wb_cap_beat_data_o,
    input  logic                        wb_cap_gnt_i,
    input  logic [WB_W-1:0]             wb_cap_slot_i,
    input  logic                        wb_full_i,
    output logic [LINE_W-1:0]           wb_sn_line_o,
    input  logic                        wb_sn_hit_i,
    output logic [1:0]                  wb_sn_eff_o,
    input  logic [LINE_BITS-1:0]        wb_sn_data_i,
    input  logic                        wb_sn_bresp_cycle_i,
    input  logic                        wb_drain_valid_i,
    output logic                        drain_start_o,
    input  logic                        drain_done_i,

    // tag array port B (snoop lookup probe; the harness muxes the TB
    // backdoor read when tag_b_req_o is low)
    output logic                        tag_b_req_o,
    output logic [SET_W-1:0]            tag_b_set_o,
    input  logic [WAYS-1:0][TSW-1:0]    tag_b_tag_state_i,

    // MSHR snoop probe + deferred-effect record (jet_mshr sn_*)
    output logic [LINE_W-1:0]           mshr_sn_line_o,
    input  logic                        mshr_sn_match_i,
    input  logic [MW-1:0]               mshr_sn_match_idx_i,
    input  logic [FILL_BEATS-1:0]       mshr_sn_beats_rcvd_i,
    input  logic                        mshr_sn_install_i,
    output logic                        mshr_sn_eff_o,
    output logic [MW-1:0]               mshr_sn_eff_idx_o,
    output logic [1:0]                  mshr_sn_eff_value_o,

    // snoop responder (the l1_snoop_resp core-facing contract: the AC
    // accept cycle IS the grant; CRRESP is combinational that cycle; CD
    // beats handshake on cdvalid/cdready with cdlast on the final beat)
    input  logic                        sn_req_i,
    input  logic [ADDR_WIDTH-1:0]       sn_addr_i,
    input  logic [2:0]                  sn_type_i,
    output logic                        sn_ready_o,
    output logic                        sn_safe_o,
    output logic [AMBER_CRRESP_WIDTH-1:0] sn_crresp_o,
    output logic [BUS_WIDTH-1:0]        sn_cddata_o,
    output logic                        sn_cdlast_o,
    output logic                        sn_cdvalid_o,
    input  logic                        sn_cdready_i,

    // fill engine launch + beat-stream observation + completion
    output logic                        fill_start_o,
    output logic [ADDR_WIDTH-1:0]       fill_addr_o,
    output logic [1:0]                  fill_cls_o,
    input  logic                        fill_accept_i,
    input  logic                        fill_pass_dirty_i,
    input  logic                        fill_beat_valid_i,
    input  logic [MW-1:0]               fill_beat_idx_i,
    input  logic [BEAT_W-1:0]           fill_beat_num_i,
    input  logic                        fill_done_i,

    // commit pipeline observability
    output logic                        cmt_busy_o
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("jet_control: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("jet_control: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("jet_control: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("jet_control: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("jet_control: WAYS must be >= 2");
        if (MSHR_COUNT < 2 || MSHR_COUNT > 16)
            $error("jet_control: MSHR_COUNT must be in 2..16 (J1)");
        if (VICTIM_DEPTH < 1 || VICTIM_DEPTH > 4)
            $error("jet_control: VICTIM_DEPTH must be in 1..4 (J5)");
    end

    // ------------------------------------------------------------------
    // Stall sub-reasons (J6 congestion story).  STALL_WB covers both
    // WB-induced stalls: the buffer cannot take this miss's dirty victim
    // (wb_full_dirty_victim), and the drain race (the request line itself
    // sits in the WB buffer or is mid-capture; release is drain_done).
    // ------------------------------------------------------------------
    localparam logic [2:0] STALL_NONE        = 3'd0;
    localparam logic [2:0] STALL_MSHR_FULL   = 3'd1;
    localparam logic [2:0] STALL_WB          = 3'd2;   // wb_full_dirty_victim / drain race
    localparam logic [2:0] STALL_SET_OVERSUB = 3'd3;
    localparam logic [2:0] STALL_XCLASS      = 3'd4;
    localparam logic [2:0] STALL_TAG_FULL    = 3'd5;
    localparam logic [2:0] STALL_COMMIT      = 3'd6;   // merge onto a fill-done entry

    // Commit FSM (one fill completion at a time, completion-queue order)
    localparam logic [3:0] C_IDLE       = 4'd0;
    localparam logic [3:0] C_MERGE      = 4'd1;   // D-4 store merge + read capture
    localparam logic [3:0] C_INSTALL    = 4'd2;   // tag install (amber #106 state)
    localparam logic [3:0] C_PEND       = 4'd3;   // deferred snoop effect, after install
    localparam logic [3:0] C_DEPOSIT    = 4'd4;   // one response per merge-list tag
    localparam logic [3:0] C_RETIRE     = 4'd5;   // retire entry, free the claim
    localparam logic [3:0] C_CU_MERGE   = 4'd6;   // upgrade: merge the held write
    localparam logic [3:0] C_CU_INSTALL = 4'd7;   // upgrade: install M
    localparam logic [3:0] C_CU_DEPOSIT = 4'd8;   // upgrade: echo response, clear tracker

    // Fill-completion queue depth: every MSHR entry plus the single
    // outstanding upgrade (CU)
    localparam int FQ_DEPTH = MSHR_COUNT + 1;
    localparam int FQ_W     = $clog2(FQ_DEPTH);

    // Snoop service FSM (one snoop at a time, MAS ch02_blocks/05)
    localparam logic [1:0] SN_IDLE   = 2'd0;
    localparam logic [1:0] SN_DATA   = 2'd1;   // CD beat stream (DT answers)
    localparam logic [1:0] SN_EFFECT = 2'd2;   // tag write / pend / WB record
    // snoop answer sources (the fixed match order: WB > MSHR > array)
    localparam logic [1:0] SRC_NONE  = 2'd0;
    localparam logic [1:0] SRC_WB    = 2'd1;
    localparam logic [1:0] SRC_MSHR  = 2'd2;
    localparam logic [1:0] SRC_ARRAY = 2'd3;
    // PF_GUARD: a pending-fill answer suppresses DataTransfer and PassDirty
    // (keeps IsShared/WasUnique -- the post-fill row, never the Invalid row)
    localparam logic [AMBER_CRRESP_WIDTH-1:0] CRRESP_NO_DT = 5'b11000;

    // ------------------------------------------------------------------
    // State
    // ------------------------------------------------------------------
    // D-3 init walk
    logic                    r_init_busy;
    logic [SET_W-1:0]        r_init_cnt;
    // victim capture engine (data-array port B -> WB buffer)
    logic                    r_cap_busy;
    logic [SET_W-1:0]        r_cap_set;
    logic [WAY_W-1:0]        r_cap_way;
    logic [LINE_W-1:0]       r_cap_line;
    logic [BEAT_W-1:0]       r_cap_beat;
    // fill launch hold (one launch awaits fill_accept_i at a time)
    logic                    r_fill_pend;
    logic [ADDR_WIDTH-1:0]   r_fill_addr;
    logic [1:0]              r_fill_cls;
    logic [MW-1:0]           r_fill_idx;
    // drain-arbiter stub (Task 8: the real l1_drain handshake)
    logic                    r_drain_busy;
    // single-outstanding upgrade (CLEAN_UNIQUE) tracker: the full request
    // context -- the CU commit merges the held write and echoes it
    logic                    r_upgr_valid;
    logic [LINE_W-1:0]       r_upgr_line;
    logic [SET_W-1:0]        r_upgr_set;
    logic [WAY_W-1:0]        r_upgr_way;
    logic [SEQ_W-1:0]        r_upgr_seq;
    logic [BEAT_W-1:0]       r_upgr_beat;
    logic [STRB_W-1:0]       r_upgr_be;
    logic [BUS_WIDTH-1:0]    r_upgr_wdata;
    // claimed-way scoreboard: which (set, way) each live MSHR entry's fill
    // will install into -- the pending-fill hazard for hit suppression
    logic [MSHR_COUNT-1:0]   r_claim_vld;
    logic [SET_W-1:0]        r_claim_set [MSHR_COUNT];
    logic [WAY_W-1:0]        r_claim_way [MSHR_COUNT];
    // per-entry fill-done flags: an entry whose fill completed is
    // committing (or queued to) -- merges onto it are the commit stall
    logic [MSHR_COUNT-1:0]   r_efill_done;
    // fill-completion queue (launch order == completion order, single
    // AXI4 read ID): which entry/upgrade each fill_done_i belongs to
    logic [FQ_W-1:0]         r_fq_head;
    logic [FQ_W-1:0]         r_fq_tail;
    logic [FQ_W-1:0]         r_fq_done_ptr;
    logic [FQ_W:0]           r_fq_cnt;
    logic [FQ_W:0]           r_fq_undone;
    logic [MW-1:0]           r_fq_idx  [FQ_DEPTH];
    logic [1:0]              r_fq_cls  [FQ_DEPTH];
    logic                    r_fq_pd   [FQ_DEPTH];
    logic                    r_fq_done [FQ_DEPTH];
    // requester sideband: per entry, per merge-list slot, the data the
    // commit needs -- the D-4 store payload for writes, the beat for reads
    logic                    r_req_we    [MSHR_COUNT * MSHR_COUNT];
    logic [BEAT_W-1:0]       r_req_beat  [MSHR_COUNT * MSHR_COUNT];
    logic [STRB_W-1:0]       r_req_be    [MSHR_COUNT * MSHR_COUNT];
    logic [BUS_WIDTH-1:0]    r_req_wdata [MSHR_COUNT * MSHR_COUNT];
    // commit pipeline registers (the entry snapshot + walk state)
    logic [3:0]              r_cmt_state;
    logic [MW-1:0]           r_cmt_idx;
    logic [LINE_W-1:0]       r_cmt_line;
    logic [1:0]              r_cmt_cls;
    logic                    r_cmt_pd;
    logic [1:0]              r_cmt_pend;
    logic [WAY_W-1:0]        r_cmt_way;
    logic [MW:0]             r_cmt_count;
    logic [SEQ_W-1:0]        r_cmt_seqs [MSHR_COUNT];
    logic [MW:0]             r_cmt_k;
    logic [BUS_WIDTH-1:0]    r_cmt_rdata [MSHR_COUNT];
    // snoop service (MAS ch02_blocks/05): grant-cycle context + stream
    logic [1:0]              r_sn_state;
    logic [LINE_W-1:0]       r_sn_line;
    logic [SET_W-1:0]        r_sn_set;
    logic [TAG_W-1:0]        r_sn_tag;
    logic [1:0]              r_sn_src;
    logic                    r_sn_allb;   // every fill beat landed at grant
    logic [WAY_W-1:0]        r_sn_way;    // array hit way / MSHR claimed way
    logic [MW-1:0]           r_sn_idx;    // the matched MSHR entry
    logic [2:0]              r_sn_ref;
    logic [2:0]              r_sn_nxt;
    logic [BEAT_W-1:0]       r_sn_beat;
    logic [LINE_BITS-1:0]    r_sn_wb_data;  // WB snarf snapshot (BRESP race)
    // pend_eff I-sticks shadow: the recorded effect per entry (invalidate
    // dominates a later downgrade; the MSHR write port is unconditional)
    logic [1:0]              r_sn_pend [MSHR_COUNT];

    // ------------------------------------------------------------------
    // Request address decode
    // ------------------------------------------------------------------
    logic [TAG_W-1:0]   w_req_tag;
    logic [SET_W-1:0]   w_req_set;
    logic [BEAT_W-1:0]  w_req_beat;
    logic [LINE_W-1:0]  w_req_line;

    assign w_req_tag  = lkup_addr_i[ADDR_WIDTH-1 -: TAG_W];
    assign w_req_set  = lkup_addr_i[OFF_W +: SET_W];
    assign w_req_beat = lkup_addr_i[OFF_W-1 -: BEAT_W];
    assign w_req_line = lkup_addr_i[ADDR_WIDTH-1:OFF_W];

    // ------------------------------------------------------------------
    // Tag hit decode (the amber LOOKUP compare: S/E/M only; reserved
    // encodings never hit)
    // ------------------------------------------------------------------
    logic                w_hit;
    logic [WAY_W-1:0]    w_hit_way;
    logic [2:0]          w_hit_state;
    logic [WAYS-1:0]     w_hit_way_onehot;
    logic                w_hit_claimed;

    always_comb begin
        w_hit       = 1'b0;
        w_hit_way   = '0;
        w_hit_state = AMBER_STATE_I;
        for (int w = 0; w < WAYS; w++) begin
            if (!w_hit
                && (tag_a_tag_state_i[w][TSW-1 -: TAG_W] == w_req_tag)
                && (tag_a_tag_state_i[w][2:0] == AMBER_STATE_S
                    || tag_a_tag_state_i[w][2:0] == AMBER_STATE_E
                    || tag_a_tag_state_i[w][2:0] == AMBER_STATE_M)) begin
                w_hit       = 1'b1;
                w_hit_way   = WAY_W'(w);
                w_hit_state = tag_a_tag_state_i[w][2:0];
            end
        end
    end

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            w_hit_way_onehot[w] = (w_hit_way == WAY_W'(w));
        end
    end

    // Pending-fill hazard: the hit way is claimed by an outstanding MSHR
    // entry of this set -- the tag is the doomed victim's and the data is
    // being captured/overwritten, so the hit is illusory.
    always_comb begin
        w_hit_claimed = 1'b0;
        for (int e = 0; e < MSHR_COUNT; e++) begin
            if (r_claim_vld[e] && (r_claim_set[e] == w_req_set)
                && (r_claim_way[e] == w_hit_way)) begin
                w_hit_claimed = 1'b1;
            end
        end
    end

    // ------------------------------------------------------------------
    // Classify inputs
    // ------------------------------------------------------------------
    logic           w_serve_hit;
    logic           w_hit_rd;
    logic           w_hit_wr;
    logic           w_hit_upgr;
    logic           w_xclass;
    logic           w_merge_room;
    logic [2:0]     w_victim_state;
    logic [TAG_W-1:0] w_victim_tag;
    logic           w_victim_dirty;
    logic           w_victim_claimed;
    logic           w_wb_race;
    logic           w_wb_block;
    logic           w_upgr_victim_block;
    logic           w_upgr_line_stall;

    assign w_serve_hit = w_hit & ~w_hit_claimed;
    assign w_hit_rd    = w_serve_hit & ~lkup_we_i;
    assign w_hit_wr    = w_serve_hit & lkup_we_i
                         & (w_hit_state != AMBER_STATE_S);
    assign w_hit_upgr  = w_serve_hit & lkup_we_i
                         & (w_hit_state == AMBER_STATE_S);

    // J3: a read joins any outstanding fill; a write joins only an RU
    // fill; a write behind an RNSD fill is the cross-class wait (the only
    // incompatible combination, so it is also the merge gate's complement).
    assign w_xclass       = mshr_lkup_reg_match_i & lkup_we_i
                            & (mshr_lkup_reg_match_cls_i == JET_CLS_RNSD);
    assign w_merge_room   = (mshr_cpl_merge_count_i < (MW+1)'(MSHR_COUNT));

    assign w_victim_state = tag_a_tag_state_i[repl_victim_way_i][2:0];
    assign w_victim_tag   = tag_a_tag_state_i[repl_victim_way_i][TSW-1 -: TAG_W];
    assign w_victim_dirty = (w_victim_state == AMBER_STATE_M);

    // Claim-aware victim check: the proposed victim way must not be
    // claimed by a live entry of this set.  LRU/FIFO propose distinct
    // ways under update-at-alloc only until hits reorder the ranks (and
    // RANDOM may repeat a way at any time); without a mask input on
    // l1_repl the miss stalls (bounded by the conflicting entry's
    // commit).  This is the RANDOM-policy safety fix.
    always_comb begin
        w_victim_claimed = 1'b0;
        for (int e = 0; e < MSHR_COUNT; e++) begin
            if (r_claim_vld[e] && (r_claim_set[e] == w_req_set)
                && (r_claim_way[e] == repl_victim_way_i)) begin
                w_victim_claimed = 1'b1;
            end
        end
    end

    // Drain race: the request line itself sits in the WB buffer (or is
    // mid-capture) -- its refetch must wait for the writeback (the
    // address is held until BRESP, Chinnakonda 10.10.1).
    assign w_wb_race = wb_sn_hit_i
                       | (r_cap_busy & (r_cap_line == w_req_line));

    // WB-full stalls ONLY dirty-victim misses (J6); a busy capture stream
    // is the same one-slot-at-a-time resource.
    assign w_wb_block = w_victim_dirty & (wb_full_i | r_cap_busy);

    // The in-flight upgrade's way is claimed (its commit installs M
    // there); the set-claim accounting counts it.
    assign w_upgr_victim_block = r_upgr_valid & (r_upgr_set == w_req_set)
                                 & (r_upgr_way == repl_victim_way_i);

    // Any hit on the in-flight upgrade's own line waits for the CU
    // commit: the held write's data merge lands only there, so a read
    // overtaking it would return stale data (request-order violation).
    assign w_upgr_line_stall = w_serve_hit & r_upgr_valid
                               & (r_upgr_line == w_req_line);

    // ------------------------------------------------------------------
    // Snoop service (MAS ch02_blocks/05: the three answer sources in the
    // fixed match order WB > MSHR > array -- the newest claim on the line
    // answers).  The l1_snoop_resp transport accepts an AC only while
    // sn_safe_o, and the accept cycle IS the grant: the CRRESP is
    // combinational on the three probes that cycle (sn_safe is therefore
    // necessarily address-agnostic -- an address-dependent safe would
    // close a combinational loop through the transport's accept mux).
    // Bounded safe windows: the init walk, an active service (one snoop
    // at a time), a fill-done-unretired entry (the commit window: the
    // array answer is the post-commit state only after the install/pend
    // writes land -- ch02/05 rule 5 -- and a pend record must precede the
    // commit's snapshot), a victim capture streaming on port B (the
    // capture completes, then the WB snarf answers), and the grant cycle
    // of a CLEAN_UNIQUE completion (the anti-livelock hold-off, ch02/01:
    // the fabric granted ownership but the tag still shows S until the CU
    // commit lands).
    // ------------------------------------------------------------------
    logic [TAG_W-1:0]   w_sn_tag;
    logic [SET_W-1:0]   w_sn_set;
    logic [LINE_W-1:0]  w_sn_line;
    logic               w_sn_thit;
    logic [WAY_W-1:0]   w_sn_tway;
    logic [2:0]         w_sn_tstate;
    logic               w_sn_tclaimed;
    logic               w_src_wb;
    logic               w_src_mshr;
    logic               w_src_array;
    logic [1:0]         w_sn_src;
    logic [2:0]         w_sn_ref;
    logic [2:0]         w_sn_nxt;
    logic               w_sn_deliver;
    logic [AMBER_CRRESP_WIDTH-1:0] w_crresp_raw;
    logic [AMBER_CRRESP_WIDTH-1:0] w_sn_crresp;
    logic               w_any_done;
    logic               w_cu_completing;
    logic               w_sn_gnt;
    logic               w_sn_block_cpu;
    logic               w_sn_eff_needed;
    logic               w_sn_eff_done;
    logic [1:0]         w_sn_eff_new;
    logic               w_sn_tagwr;
    logic               w_sn_portb;
    logic [WAYS-1:0]    w_sn_way_onehot;

    assign w_sn_tag  = sn_addr_i[ADDR_WIDTH-1 -: TAG_W];
    assign w_sn_set  = sn_addr_i[OFF_W +: SET_W];
    assign w_sn_line = sn_addr_i[ADDR_WIDTH-1:OFF_W];

    // the snoop probes carry the snoop line at the grant and through the
    // service; the WB probe serves the lookup drain-race check otherwise
    assign tag_b_req_o   = sn_req_i;
    assign tag_b_set_o   = w_sn_set;
    assign wb_sn_line_o   = sn_req_i ? w_sn_line
                            : (r_sn_state != SN_IDLE) ? r_sn_line
                            : w_req_line;
    assign mshr_sn_line_o = sn_req_i ? w_sn_line : r_sn_line;

    // port-B tag hit decode (the amber LOOKUP compare on the snoop set)
    always_comb begin
        w_sn_thit   = 1'b0;
        w_sn_tway   = '0;
        w_sn_tstate = AMBER_STATE_I;
        for (int w = 0; w < WAYS; w++) begin
            if (!w_sn_thit
                && (tag_b_tag_state_i[w][TSW-1 -: TAG_W] == w_sn_tag)
                && (tag_b_tag_state_i[w][2:0] == AMBER_STATE_S
                    || tag_b_tag_state_i[w][2:0] == AMBER_STATE_E
                    || tag_b_tag_state_i[w][2:0] == AMBER_STATE_M)) begin
                w_sn_thit   = 1'b1;
                w_sn_tway   = WAY_W'(w);
                w_sn_tstate = tag_b_tag_state_i[w][2:0];
            end
        end
    end

    // claimed-way suppression (amber's stale-victim rule): a tag hit on a
    // way claimed by a live MSHR entry of the set is the doomed victim's
    // stale tag -- the line is dead (a dirty victim matched the WB first;
    // a clean one is current in memory), so the answer is the Invalid row
    // with no effect.  The upgrade's way is NOT here: its line is
    // legitimately resident S until the CU commit.
    always_comb begin
        w_sn_tclaimed = 1'b0;
        for (int e = 0; e < MSHR_COUNT; e++) begin
            if (r_claim_vld[e] && (r_claim_set[e] == w_sn_set)
                && (r_claim_way[e] == w_sn_tway)) begin
                w_sn_tclaimed = 1'b1;
            end
        end
    end

    // the match order: the WB buffer owns a draining line (SINK_WB_ACK --
    // that data exists NOW), then the pending fill (the post-fill state --
    // the fill's answer would otherwise be a promise), then the arrays
    assign w_src_wb    = wb_sn_hit_i;
    assign w_src_mshr  = ~w_src_wb & mshr_sn_match_i;
    assign w_src_array = ~w_src_wb & ~w_src_mshr & w_sn_thit
                         & ~w_sn_tclaimed;
    assign w_sn_src    = w_src_wb    ? SRC_WB
                         : w_src_mshr  ? SRC_MSHR
                         : w_src_array ? SRC_ARRAY
                         :               SRC_NONE;
    assign w_sn_ref    = w_src_wb    ? AMBER_STATE_M
                         : w_src_mshr  ? (mshr_sn_install_i
                                          ? AMBER_STATE_M : AMBER_STATE_S)
                         : w_src_array ? w_sn_tstate
                         :               AMBER_STATE_I;
    assign w_sn_nxt    = amber_snoop_next_state(w_sn_ref, sn_type_i);

    // PF_GUARD: the bypass promises data only when the fill can actually
    // deliver it -- every beat landed at the grant (a snoop never waits
    // on a fill, HAS J4); the guarded answer keeps the post-fill row's
    // IsShared/WasUnique (never the Invalid row).
    assign w_sn_deliver = w_src_wb | w_src_array
                          | (w_src_mshr & (&mshr_sn_beats_rcvd_i));
    assign w_crresp_raw = amber_snoop_crresp(w_sn_ref, sn_type_i);
    assign w_sn_crresp  = w_sn_deliver ? w_crresp_raw
                                       : (w_crresp_raw & CRRESP_NO_DT);
    assign sn_crresp_o  = w_sn_crresp;

    // safe (AC-accept) windows: all bounded; the commit window expression
    // is "some fill is done but its commit hasn't retired" (covers the
    // active commit too -- the pop lands at the retire), plus the grant
    // cycle of a CU completion (fill_done_i marks the oldest un-done fill
    // -- the completion queue resolves its class combinationally)
    assign w_any_done      = (r_fq_cnt != r_fq_undone);
    assign w_cu_completing = fill_done_i
                             & (r_fq_cls[r_fq_done_ptr] == JET_CLS_CU);
    assign sn_safe_o  = ~r_init_busy & (r_sn_state == SN_IDLE)
                        & ~w_any_done & ~r_cap_busy & ~w_cu_completing;
    assign w_sn_gnt   = sn_req_i & sn_safe_o;
    assign sn_ready_o = w_sn_gnt;

    // snoop priority over new CPU accepts (J6): the lookup stage holds the
    // request (no accept, no stall reason) through the grant and the
    // service -- bounded by the service length (<= FILL_BEATS + 2 in CD
    // handshakes, extended by cdready backpressure)
    assign w_sn_block_cpu = w_sn_gnt | (r_sn_state != SN_IDLE);

    // the effect to apply at the end of the service: a state change on the
    // resolved reference (a fixed-point snoop is a no-op); the WB/MSHR
    // record encodes downgrade-S / invalidate-I, the array path writes
    // the tag with the resolved next state
    assign w_sn_eff_needed =
        ((w_sn_src == SRC_WB) | (w_sn_src == SRC_MSHR)
         | (w_sn_src == SRC_ARRAY)) & (w_sn_nxt != w_sn_ref);
    assign w_sn_eff_done  =
        ((r_sn_src == SRC_WB) | (r_sn_src == SRC_MSHR)
         | (r_sn_src == SRC_ARRAY)) & (r_sn_nxt != r_sn_ref);
    assign w_sn_eff_new   = (r_sn_nxt == AMBER_STATE_I)
                            ? JET_PEND_INVALIDATE_I : JET_PEND_DOWNGRADE_S;

    // pend_eff I-sticks: an armed invalidate dominates a later downgrade
    // (the shadow mirrors the MSHR record exactly -- this module is its
    // only driver; the alloc clears the reused entry's)
    assign mshr_sn_eff_o       = (r_sn_state == SN_EFFECT)
                                 & (r_sn_src == SRC_MSHR)
                                 & (r_sn_nxt != r_sn_ref)
                                 & (r_sn_pend[r_sn_idx]
                                    != JET_PEND_INVALIDATE_I);
    assign mshr_sn_eff_idx_o   = r_sn_idx;
    assign mshr_sn_eff_value_o = w_sn_eff_new;
    // The WB effect may arrive after a mid-service BRESP retired the
    // snarfed entry (the grant can land in the entry's BRESP cycle; the
    // effect slot follows the CD stream).  jet_wb_buffer records only on
    // a CURRENT CAM match of the snoop line, so the effect of a retired
    // entry is dropped -- semantically moot: the drain completed, memory
    // holds the data, the fabric took its answer.  Misapplication to a
    // reused slot is impossible: CPU accepts (hence new captures) are
    // suppressed for the whole service, and a line occupies at most one
    // WB slot at a time (the lookup drain-race stall).
    assign wb_sn_eff_o         = ((r_sn_state == SN_EFFECT)
                                  & (r_sn_src == SRC_WB)
                                  & (r_sn_nxt != r_sn_ref))
                                 ? w_sn_eff_new : JET_PEND_NONE;
    assign w_sn_tagwr          = (r_sn_state == SN_EFFECT)
                                 & (r_sn_src == SRC_ARRAY)
                                 & (r_sn_nxt != r_sn_ref);

    // CD beat stream: a WB snarf serves the grant-cycle snapshot (the
    // entry may retire mid-stream -- the BRESP-cycle corner); the other
    // sources read the data array on port B (the fill way for a pending
    // fill, the hit way otherwise), pausing the victim capture
    assign sn_cdvalid_o = (r_sn_state == SN_DATA);
    assign sn_cdlast_o  = (r_sn_state == SN_DATA)
                          & (r_sn_beat == BEAT_W'(FILL_BEATS - 1));
    assign sn_cddata_o  = (r_sn_src == SRC_WB)
                          ? r_sn_wb_data[32'(r_sn_beat) * BUS_WIDTH
                                         +: BUS_WIDTH]
                          : dat_b_rdata_i;
    assign w_sn_portb   = (r_sn_state == SN_DATA) & (r_sn_src != SRC_WB);

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            w_sn_way_onehot[w] = (r_sn_way == WAY_W'(w));
        end
    end

    // ------------------------------------------------------------------
    // Commit pipeline: completion-queue head and FSM decodes
    // ------------------------------------------------------------------
    logic           w_fq_head_done;
    logic           w_fq_push;
    logic           w_fq_pop;
    logic           w_cmt_snap;
    logic           w_cmt_cpl;
    logic           w_cmt_datrd;
    logic           w_cmt_datwr;
    logic           w_cmt_tagwr;
    logic           w_cmt_retire;
    logic           w_slot_done;
    logic           w_slot_we;
    logic [BEAT_W-1:0] w_slot_beat;
    logic [STRB_W-1:0] w_slot_be;
    logic [BUS_WIDTH-1:0] w_slot_wdata;
    logic [SEQ_W-1:0]  w_cmt_cpl_tag;
    logic [BUS_WIDTH-1:0] w_cmt_cpl_data;
    logic [2:0]        w_install_state;
    logic [WAYS-1:0]   w_cmt_way_onehot;
    logic [WAYS-1:0]   w_upgr_way_onehot;
    logic [SET_W-1:0]  w_cmt_set;
    logic [TAG_W-1:0]  w_cmt_tag;
    logic [TAG_W-1:0]  w_upgr_tag;

    // a fill_done_i always lands on the oldest un-done in-flight fill
    // (in-order completion); the commit starts when the head is done
    assign w_fq_head_done = (r_fq_cnt != '0) & r_fq_done[r_fq_head];

    // the snapshot cycle drives the jet_mshr commit read port with the
    // head entry's index (the lookup stage owns the port otherwise)
    assign w_cmt_snap = (r_cmt_state == C_IDLE) & w_fq_head_done
                        & (r_fq_cls[r_fq_head] != JET_CLS_CU);

    assign w_slot_done = (r_cmt_k == r_cmt_count);
    assign w_slot_we    = r_req_we[32'(r_cmt_idx) * MSHR_COUNT
                                   + 32'(r_cmt_k[MW-1:0])];
    assign w_slot_beat  = r_req_beat[32'(r_cmt_idx) * MSHR_COUNT
                                     + 32'(r_cmt_k[MW-1:0])];
    assign w_slot_be    = r_req_be[32'(r_cmt_idx) * MSHR_COUNT
                                   + 32'(r_cmt_k[MW-1:0])];
    assign w_slot_wdata = r_req_wdata[32'(r_cmt_idx) * MSHR_COUNT
                                      + 32'(r_cmt_k[MW-1:0])];

    // port ownership decodes (see the arbitration table in the header)
    assign w_cmt_datwr = ((r_cmt_state == C_MERGE) & ~w_slot_done
                          & w_slot_we & ~fill_beat_valid_i)
                         | ((r_cmt_state == C_CU_MERGE) & ~fill_beat_valid_i);
    assign w_cmt_datrd = (r_cmt_state == C_MERGE) & ~w_slot_done
                         & ~w_slot_we;
    assign w_cmt_cpl   = (r_cmt_state == C_DEPOSIT)
                         | (r_cmt_state == C_CU_DEPOSIT);
    assign w_cmt_tagwr = (r_cmt_state == C_INSTALL)
                         | (r_cmt_state == C_PEND)
                         | (r_cmt_state == C_CU_INSTALL);
    assign w_cmt_retire = (r_cmt_state == C_RETIRE);

    // install state: S for a ReadNotSharedDirty fill unless PassDirty was
    // received (amber's #106 rule); M for a write fill -- and M for an
    // upgrade (C_CU_INSTALL).  The deferred snoop effect writes AFTER the
    // install (amber pending semantics).
    assign w_install_state =
        ((r_cmt_cls == JET_CLS_RNSD) && !r_cmt_pd) ? AMBER_STATE_S
                                                   : AMBER_STATE_M;

    assign w_cmt_set = r_cmt_line[SET_W-1:0];
    assign w_cmt_tag = r_cmt_line[LINE_W-1 -: TAG_W];
    assign w_upgr_tag = r_upgr_line[LINE_W-1 -: TAG_W];

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            w_cmt_way_onehot[w]  = (r_cmt_way == WAY_W'(w));
            w_upgr_way_onehot[w] = (r_upgr_way == WAY_W'(w));
        end
    end

    assign w_cmt_cpl_tag  = (r_cmt_state == C_CU_DEPOSIT)
                            ? r_upgr_seq
                            : r_cmt_seqs[r_cmt_k[MW-1:0]];
    assign w_cmt_cpl_data = (r_cmt_state == C_CU_DEPOSIT)
                            ? r_upgr_wdata
                            : (w_slot_we ? w_slot_wdata
                                         : r_cmt_rdata[r_cmt_k[MW-1:0]]);

    // ------------------------------------------------------------------
    // Classify (one request, one window)
    // ------------------------------------------------------------------
    logic           w_acceptable;
    logic           w_stall;
    logic [2:0]     w_reason;
    logic           w_yield;

    always_comb begin
        w_acceptable = 1'b0;
        w_stall      = 1'b0;
        w_reason     = STALL_NONE;
        w_yield      = 1'b0;
        if (lkup_valid_i && !r_init_busy && !w_sn_block_cpu) begin
            if (w_upgr_line_stall) begin
                // any access to the in-flight upgrade's line waits for
                // the CU commit (the held write merges only there)
                w_stall  = 1'b1;
                w_reason = STALL_XCLASS;
            end else if (w_hit_rd) begin
                // read hits hold while the commit owns the deposit port
                // or the port-A read address (bounded: the walk length)
                if (!(w_cmt_cpl | w_cmt_datrd)) begin
                    w_acceptable = 1'b1;
                end
            end else if (w_hit_wr) begin
                // write hits take the W port subject to fill beats and a
                // commit store-merge (fill beats > commit merge > write
                // hits, both bounded); the E->M promotion also needs the
                // tag port, which a commit install owns for its cycle
                if (w_cmt_cpl) begin
                    // deposit port owned: hold (not a yield -- no W-port
                    // write is competing)
                end else if (fill_beat_valid_i | w_cmt_datwr) begin
                    w_yield = 1'b1;
                end else if ((w_hit_state == AMBER_STATE_E) & w_cmt_tagwr) begin
                    // tag port owned by a commit install: hold
                end else begin
                    w_acceptable = 1'b1;
                end
            end else if (w_hit_upgr) begin
                if (!r_upgr_valid && !r_fill_pend) begin
                    w_acceptable = 1'b1;
                end
                // upgrade pipe / launch register busy: hold (not a stall)
            end else if (mshr_lkup_reg_match_i) begin
                if (w_xclass) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_XCLASS;
                end else if (r_efill_done[mshr_lkup_reg_match_idx_i]) begin
                    // the entry's fill completed: its merge list is
                    // snapshot at the commit start -- no more joins
                    w_stall  = 1'b1;
                    w_reason = STALL_COMMIT;
                end else if (w_cmt_snap) begin
                    // the snapshot cycle owns the merge-room probe: hold
                end else if (!w_merge_room) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_MSHR_FULL;
                end else begin
                    w_acceptable = 1'b1;   // merge
                end
            end else begin
                // true miss
                if (w_wb_race) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_WB;
                end else if (mshr_full_i) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_MSHR_FULL;
                end else if (mshr_set_full_i | w_upgr_victim_block
                             | w_victim_claimed) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_SET_OVERSUB;
                end else if (w_wb_block) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_WB;
                end else if (!r_fill_pend) begin
                    w_acceptable = 1'b1;   // miss_alloc
                end
                // fill-launch register busy: hold (not a stall)
            end
        end
    end

    // ------------------------------------------------------------------
    // Accept and per-class accept decodes
    // ------------------------------------------------------------------
    logic w_accept;
    logic w_accept_rd;
    logic w_accept_wr;
    logic w_accept_upgr;
    logic w_accept_merge;
    logic w_accept_alloc;

    assign tag_req_o     = lkup_valid_i & ~r_init_busy & w_acceptable;
    assign w_accept      = tag_req_o & tag_gnt_i;
    assign lkup_ready_o  = w_accept;

    assign lkup_stall_o  = lkup_valid_i & ~r_init_busy & ~w_accept
                           & (w_stall | (w_acceptable & ~tag_gnt_i));
    assign lkup_stall_reason_o = w_stall ? w_reason
            : (lkup_valid_i & ~r_init_busy & w_acceptable & ~tag_gnt_i)
              ? STALL_TAG_FULL : STALL_NONE;
    assign lkup_wr_yield_o   = w_yield;

    assign w_accept_rd    = w_accept & w_hit_rd;
    assign w_accept_wr    = w_accept & w_hit_wr;
    assign w_accept_upgr  = w_accept & w_hit_upgr;
    assign w_accept_merge = w_accept & ~w_serve_hit & mshr_lkup_reg_match_i;
    assign w_accept_alloc = w_accept & ~w_serve_hit & ~mshr_lkup_reg_match_i;

    assign lkup_hit_o        = w_accept_rd | w_accept_wr;
    assign lkup_merge_o      = w_accept_merge;
    assign lkup_miss_alloc_o = w_accept_alloc;
    assign lkup_upgrade_o    = w_accept_upgr;
    assign cap_busy_o        = r_cap_busy;
    assign init_busy_o       = r_init_busy;

    // ------------------------------------------------------------------
    // Fill launch (held until fill_accept_i) + completion-queue push.
    // Fills complete in launch order (single AXI4 read ID), so the queue
    // tells the commit pipeline which entry/upgrade each fill_done_i
    // belongs to.
    // ------------------------------------------------------------------
    logic                  w_launch;
    logic [ADDR_WIDTH-1:0] w_launch_addr;
    logic [1:0]            w_launch_cls;

    assign w_launch      = w_accept_alloc | w_accept_upgr;
    assign w_launch_addr = {w_req_line, {OFF_W{1'b0}}};
    assign w_launch_cls  = w_accept_upgr ? JET_CLS_CU
                           : lkup_we_i   ? JET_CLS_RU
                           :               JET_CLS_RNSD;

    assign fill_start_o = r_fill_pend | w_launch;
    assign fill_addr_o  = r_fill_pend ? r_fill_addr : w_launch_addr;
    assign fill_cls_o   = r_fill_pend ? r_fill_cls  : w_launch_cls;

    assign w_fq_push = fill_start_o & fill_accept_i;
    assign w_fq_pop  = w_cmt_retire | (r_cmt_state == C_CU_DEPOSIT);

    // ------------------------------------------------------------------
    // Response deposit: the commit pipeline wins the port; hit accepts
    // are held in those cycles, so no deposit is ever lost.
    // ------------------------------------------------------------------
    assign cpl_valid_o = w_cmt_cpl | w_accept_rd | w_accept_wr;
    assign cpl_tag_o   = w_cmt_cpl ? w_cmt_cpl_tag : tag_i;
    assign cpl_data_o  = w_cmt_cpl ? w_cmt_cpl_data
                         : w_accept_rd ? dat_a_rdata_i : lkup_wdata_i;

    // ------------------------------------------------------------------
    // Array port A
    // ------------------------------------------------------------------
    assign tag_a_set_o = r_init_busy ? r_init_cnt : w_req_set;
    assign tag_a_wr_en_o = (r_init_busy & ~`RST_ASSERTED(rst_n))
                           | w_cmt_tagwr
                           | w_sn_tagwr
                           | (w_accept_wr & (w_hit_state == AMBER_STATE_E));
    assign tag_a_wr_way_onehot_o = r_init_busy ? {WAYS{1'b1}}
                           : w_cmt_tagwr
                             ? ((r_cmt_state == C_CU_INSTALL)
                                ? w_upgr_way_onehot : w_cmt_way_onehot)
                           : w_sn_tagwr
                             ? w_sn_way_onehot
                           : w_hit_way_onehot;
    assign tag_a_wr_set_o        = r_init_busy ? r_init_cnt
                           : w_cmt_tagwr
                             ? ((r_cmt_state == C_CU_INSTALL)
                                ? r_upgr_set : w_cmt_set)
                           : w_sn_tagwr
                             ? r_sn_set
                           : w_req_set;
    assign tag_a_wr_tag_state_o  = r_init_busy
                                   ? {{TAG_W{1'b0}}, AMBER_STATE_I}
                           : (r_cmt_state == C_INSTALL)
                             ? {w_cmt_tag, w_install_state}
                           : (r_cmt_state == C_PEND)
                             ? {w_cmt_tag,
                                (r_cmt_pend == JET_PEND_INVALIDATE_I)
                                ? AMBER_STATE_I : AMBER_STATE_S}
                           : (r_cmt_state == C_CU_INSTALL)
                             ? {w_upgr_tag, AMBER_STATE_M}
                           : w_sn_tagwr
                             ? {r_sn_tag, r_sn_nxt}
                           : {w_req_tag, AMBER_STATE_M};

    assign dat_a_addr_o         = w_cmt_datrd ? {w_cmt_set, w_slot_beat}
                                              : {w_req_set, w_req_beat};
    assign dat_a_way_o          = w_cmt_datrd ? r_cmt_way : w_hit_way;
    assign dat_a_wr_en_o        = w_accept_wr | w_cmt_datwr;
    assign dat_a_wr_way_onehot_o = w_cmt_datwr
                                   ? ((r_cmt_state == C_CU_MERGE)
                                      ? w_upgr_way_onehot
                                      : w_cmt_way_onehot)
                                   : w_hit_way_onehot;
    assign dat_a_wr_addr_o      = w_cmt_datwr
                                  ? ((r_cmt_state == C_CU_MERGE)
                                     ? {r_upgr_set, r_upgr_beat}
                                     : {w_cmt_set, w_slot_beat})
                                  : {w_req_set, w_req_beat};
    assign dat_a_wr_wdata_o     = w_cmt_datwr
                                  ? ((r_cmt_state == C_CU_MERGE)
                                     ? r_upgr_wdata : w_slot_wdata)
                                  : lkup_wdata_i;
    assign dat_a_wr_be_o        = w_cmt_datwr
                                  ? ((r_cmt_state == C_CU_MERGE)
                                     ? r_upgr_be : w_slot_be)
                                  : lkup_be_i;

    // ------------------------------------------------------------------
    // Array port B: the snoop's CD read owns the port while a data-carrying
    // snoop streams from the array (MSHR/array sources); the victim capture
    // stream pauses for it (jet_wb_buffer tolerates capture pauses; the
    // snoop service is bounded, so the pause is bounded).
    // ------------------------------------------------------------------
    assign dat_b_addr_o = w_sn_portb ? {r_sn_set, r_sn_beat}
                                     : {r_cap_set, r_cap_beat};
    assign dat_b_way_o  = w_sn_portb ? r_sn_way : r_cap_way;

    // ------------------------------------------------------------------
    // Replacement engine: the victim way is claimed AND the policy
    // updated at the alloc (the commit pipeline must not repl_update at
    // install); hits (and the upgrade launch) touch the policy with
    // repl_hit.
    // ------------------------------------------------------------------
    assign repl_req_o      = w_accept_alloc;
    assign repl_set_o      = w_req_set;
    assign repl_hit_o      = w_accept_rd | w_accept_wr | w_accept_upgr;
    assign repl_update_o   = w_accept_alloc;
    assign repl_hit_way_o  = w_accept_alloc ? repl_victim_way_i : w_hit_way;

    // ------------------------------------------------------------------
    // MSHR file
    // ------------------------------------------------------------------
    assign mshr_alloc_o            = w_accept_alloc;
    assign mshr_alloc_line_o       = w_req_line;
    assign mshr_alloc_set_o        = w_req_set;
    assign mshr_alloc_cls_o        = lkup_we_i ? JET_CLS_RU : JET_CLS_RNSD;
    assign mshr_alloc_install_o    = lkup_we_i;
    assign mshr_alloc_victim_way_o = repl_victim_way_i;
    assign mshr_alloc_wb_slot_o    = wb_cap_slot_i;
    assign mshr_alloc_wb_valid_o   = w_victim_dirty;
    assign mshr_alloc_seq_o        = tag_i;
    assign mshr_lkup_line_o        = w_req_line;
    assign mshr_cpl_idx_o          = w_cmt_snap ? r_fq_idx[r_fq_head]
                                                : mshr_lkup_reg_match_idx_i;
    assign mshr_merge_o            = w_accept_merge;
    assign mshr_merge_idx_o        = mshr_lkup_reg_match_idx_i;
    assign mshr_merge_seq_o        = tag_i;
    assign mshr_beat_o             = fill_beat_valid_i;
    assign mshr_beat_idx_o         = fill_beat_idx_i;
    assign mshr_beat_num_o         = fill_beat_num_i;
    assign mshr_retire_o           = w_cmt_retire;
    assign mshr_retire_idx_o       = r_cmt_idx;
    assign cmt_busy_o              = (r_cmt_state != C_IDLE) | w_fq_head_done;

    // ------------------------------------------------------------------
    // WB buffer: capture open + beat stream (paused while a snoop's CD
    // stream owns port B) + the snarf probe (the snoop line during a
    // grant/service, the lookup line for the drain-race check otherwise)
    // ------------------------------------------------------------------
    assign wb_cap_o          = (w_accept_alloc & w_victim_dirty) | r_cap_busy;
    assign wb_cap_line_o     = r_cap_busy ? r_cap_line
                                          : {w_victim_tag, w_req_set};
    assign wb_cap_beat_o     = r_cap_busy & ~w_sn_portb;
    assign wb_cap_beat_data_o = dat_b_rdata_i;

    // Drain-arbiter stub: present drain_start when the head is valid and
    // no drain is outstanding (l1_drain samples victim_valid in D_IDLE).
    assign drain_start_o = wb_drain_valid_i & ~r_drain_busy;

    // ------------------------------------------------------------------
    // Sequential state
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_init_busy  <= 1'b1;
            r_init_cnt   <= '0;
            r_cap_busy   <= 1'b0;
            r_cap_set    <= '0;
            r_cap_way    <= '0;
            r_cap_line   <= '0;
            r_cap_beat   <= '0;
            r_fill_pend  <= 1'b0;
            r_fill_addr  <= '0;
            r_fill_cls   <= '0;
            r_fill_idx   <= '0;
            r_drain_busy <= 1'b0;
            r_upgr_valid <= 1'b0;
            r_upgr_line  <= '0;
            r_upgr_set   <= '0;
            r_upgr_way   <= '0;
            r_upgr_seq   <= '0;
            r_upgr_beat  <= '0;
            r_upgr_be    <= '0;
            r_upgr_wdata <= '0;
            r_claim_vld  <= '0;
            r_efill_done <= '0;
            r_fq_head    <= '0;
            r_fq_tail    <= '0;
            r_fq_done_ptr <= '0;
            r_fq_cnt     <= '0;
            r_fq_undone  <= '0;
            r_cmt_state  <= C_IDLE;
            r_cmt_idx    <= '0;
            r_cmt_line   <= '0;
            r_cmt_cls    <= '0;
            r_cmt_pd     <= 1'b0;
            r_cmt_pend   <= JET_PEND_NONE;
            r_cmt_way    <= '0;
            r_cmt_count  <= '0;
            r_cmt_k      <= '0;
            r_sn_state   <= SN_IDLE;
            r_sn_line    <= '0;
            r_sn_set     <= '0;
            r_sn_tag     <= '0;
            r_sn_src     <= SRC_NONE;
            r_sn_allb    <= 1'b0;
            r_sn_way     <= '0;
            r_sn_idx     <= '0;
            r_sn_ref     <= '0;
            r_sn_nxt     <= '0;
            r_sn_beat    <= '0;
            r_sn_wb_data <= '0;
            for (int e = 0; e < MSHR_COUNT; e++) begin
                r_claim_set[e] <= '0;
                r_claim_way[e] <= '0;
                r_cmt_seqs[e]  <= '0;
                r_cmt_rdata[e] <= '0;
                r_sn_pend[e]   <= JET_PEND_NONE;
            end
            for (int q = 0; q < FQ_DEPTH; q++) begin
                r_fq_idx[q]  <= '0;
                r_fq_cls[q]  <= '0;
                r_fq_pd[q]   <= 1'b0;
                r_fq_done[q] <= 1'b0;
            end
            for (int k = 0; k < MSHR_COUNT * MSHR_COUNT; k++) begin
                r_req_we[k]    <= 1'b0;
                r_req_beat[k]  <= '0;
                r_req_be[k]    <= '0;
                r_req_wdata[k] <= '0;
            end
        end else begin
            // D-3 init walk: one set per cycle
            if (r_init_busy) begin
                if (r_init_cnt == SET_W'(SETS - 1)) begin
                    r_init_busy <= 1'b0;
                end else begin
                    r_init_cnt <= r_init_cnt + 1'b1;
                end
            end
            // victim capture: opened by a dirty-victim alloc, then
            // FILL_BEATS consecutive port-B reads, pausing while a snoop's
            // CD stream owns the port (the snoop service is bounded, so
            // the pause is bounded)
            if (w_accept_alloc & w_victim_dirty) begin
                r_cap_busy <= 1'b1;
                r_cap_set  <= w_req_set;
                r_cap_way  <= repl_victim_way_i;
                r_cap_line <= {w_victim_tag, w_req_set};
                r_cap_beat <= '0;
            end else if (r_cap_busy & ~w_sn_portb) begin
                if (r_cap_beat == BEAT_W'(FILL_BEATS - 1)) begin
                    r_cap_busy <= 1'b0;
                    r_cap_beat <= '0;
                end else begin
                    r_cap_beat <= r_cap_beat + 1'b1;
                end
            end
            // fill launch hold (a launch implies the register was free);
            // the entry index rides along for the completion-queue push
            if (w_launch & ~fill_accept_i) begin
                r_fill_pend <= 1'b1;
                r_fill_addr <= w_launch_addr;
                r_fill_cls  <= w_launch_cls;
                r_fill_idx  <= w_accept_upgr ? '0 : mshr_alloc_idx_i;
            end else if (fill_accept_i) begin
                r_fill_pend <= 1'b0;
            end
            // drain arbiter stub
            if (drain_start_o) begin
                r_drain_busy <= 1'b1;
            end else if (drain_done_i) begin
                r_drain_busy <= 1'b0;
            end
            // upgrade tracker: set at the launch, cleared by the CU's own
            // commit (the completion queue qualifies the clear by the
            // completing fill's identity -- never by another fill's done)
            if (w_accept_upgr) begin
                r_upgr_valid <= 1'b1;
                r_upgr_line  <= w_req_line;
                r_upgr_set   <= w_req_set;
                r_upgr_way   <= w_hit_way;
                r_upgr_seq   <= tag_i;
                r_upgr_beat  <= w_req_beat;
                r_upgr_be    <= lkup_be_i;
                r_upgr_wdata <= lkup_wdata_i;
            end else if (r_cmt_state == C_CU_DEPOSIT) begin
                r_upgr_valid <= 1'b0;
            end
            // claimed-way scoreboard (pending-fill hazard): set at the
            // alloc, cleared by the commit's retire -- hits on the way
            // stay suppressed until the tag install + pend effect have
            // landed and the entry is gone
            if (w_accept_alloc) begin
                r_claim_vld[mshr_alloc_idx_i] <= 1'b1;
                r_claim_set[mshr_alloc_idx_i] <= w_req_set;
                r_claim_way[mshr_alloc_idx_i] <= repl_victim_way_i;
            end
            if (w_cmt_retire) begin
                r_claim_vld[r_cmt_idx]  <= 1'b0;
                r_efill_done[r_cmt_idx] <= 1'b0;
            end
            // requester sideband: slot 0 at the alloc, the append slot
            // (the pre-append merge count) at a merge
            if (w_accept_alloc) begin
                r_req_we[32'(mshr_alloc_idx_i) * MSHR_COUNT]    <= lkup_we_i;
                r_req_beat[32'(mshr_alloc_idx_i) * MSHR_COUNT]  <= w_req_beat;
                r_req_be[32'(mshr_alloc_idx_i) * MSHR_COUNT]    <= lkup_be_i;
                r_req_wdata[32'(mshr_alloc_idx_i) * MSHR_COUNT] <= lkup_wdata_i;
            end
            if (w_accept_merge) begin
                r_req_we[32'(mshr_lkup_reg_match_idx_i) * MSHR_COUNT
                         + 32'(mshr_cpl_merge_count_i[MW-1:0])]    <= lkup_we_i;
                r_req_beat[32'(mshr_lkup_reg_match_idx_i) * MSHR_COUNT
                           + 32'(mshr_cpl_merge_count_i[MW-1:0])]  <= w_req_beat;
                r_req_be[32'(mshr_lkup_reg_match_idx_i) * MSHR_COUNT
                         + 32'(mshr_cpl_merge_count_i[MW-1:0])]    <= lkup_be_i;
                r_req_wdata[32'(mshr_lkup_reg_match_idx_i) * MSHR_COUNT
                            + 32'(mshr_cpl_merge_count_i[MW-1:0])] <= lkup_wdata_i;
            end
            // fill-completion queue: push at the launch accept, mark done
            // at fill_done_i (oldest un-done, in order), pop at the
            // commit's retire (or the CU deposit)
            if (w_fq_push) begin
                r_fq_idx[r_fq_tail]  <= r_fill_pend ? r_fill_idx
                                                    : mshr_alloc_idx_i;
                r_fq_cls[r_fq_tail]  <= r_fill_pend ? r_fill_cls
                                                    : w_launch_cls;
                r_fq_done[r_fq_tail] <= 1'b0;
                if (r_fq_tail == FQ_W'(FQ_DEPTH - 1))
                    r_fq_tail <= '0;
                else
                    r_fq_tail <= r_fq_tail + 1'b1;
            end
            if (fill_done_i) begin
                r_fq_done[r_fq_done_ptr] <= 1'b1;
                r_fq_pd[r_fq_done_ptr]   <= fill_pass_dirty_i;
                if (r_fq_cls[r_fq_done_ptr] != JET_CLS_CU)
                    r_efill_done[r_fq_idx[r_fq_done_ptr]] <= 1'b1;
                if (r_fq_done_ptr == FQ_W'(FQ_DEPTH - 1))
                    r_fq_done_ptr <= '0;
                else
                    r_fq_done_ptr <= r_fq_done_ptr + 1'b1;
            end
            if (w_fq_pop) begin
                if (r_fq_head == FQ_W'(FQ_DEPTH - 1))
                    r_fq_head <= '0;
                else
                    r_fq_head <= r_fq_head + 1'b1;
            end
            case ({w_fq_push, w_fq_pop})
                2'b10:   r_fq_cnt <= r_fq_cnt + 1'b1;
                2'b01:   r_fq_cnt <= r_fq_cnt - 1'b1;
                default: ;  // 00: no event; 11: push+pop net to hold
            endcase
            case ({w_fq_push, fill_done_i})
                2'b10:   r_fq_undone <= r_fq_undone + 1'b1;
                2'b01:   r_fq_undone <= r_fq_undone - 1'b1;
                default: ;
            endcase
            // snoop service: the grant latches the context (a WB snarf
            // snapshots the whole line -- the entry may retire mid-stream
            // in its BRESP cycle); SN_DATA streams the CD beats; SN_EFFECT
            // applies the state effect (array tag write / MSHR pend record
            // with I-sticks / WB record).  The commit pipeline never runs
            // during a service (below), so the effect cycle's tag port and
            // the pend record's snapshot ordering are contention-free.
            if (w_sn_gnt) begin
                r_sn_line <= w_sn_line;
                r_sn_set  <= w_sn_set;
                r_sn_tag  <= w_sn_tag;
                r_sn_src  <= w_sn_src;
                r_sn_allb <= &mshr_sn_beats_rcvd_i;
                r_sn_way  <= w_src_mshr ? r_claim_way[mshr_sn_match_idx_i]
                                        : w_sn_tway;
                r_sn_idx  <= mshr_sn_match_idx_i;
                r_sn_ref  <= w_sn_ref;
                r_sn_nxt  <= w_sn_nxt;
                r_sn_beat <= '0;
                if (w_src_wb) begin
                    r_sn_wb_data <= wb_sn_data_i;
                end
                if (w_sn_crresp[AMBER_CRRESP_DT]) begin
                    r_sn_state <= SN_DATA;
                end else if (w_sn_eff_needed) begin
                    r_sn_state <= SN_EFFECT;
                end
            end else if (r_sn_state == SN_DATA) begin
                if (sn_cdready_i) begin
                    if (r_sn_beat == BEAT_W'(FILL_BEATS - 1)) begin
                        r_sn_state <= w_sn_eff_done ? SN_EFFECT : SN_IDLE;
                    end else begin
                        r_sn_beat <= r_sn_beat + 1'b1;
                    end
                end
            end else if (r_sn_state == SN_EFFECT) begin
                r_sn_state <= SN_IDLE;
                if ((r_sn_src == SRC_MSHR) && (r_sn_nxt != r_sn_ref)
                    && (r_sn_pend[r_sn_idx] != JET_PEND_INVALIDATE_I)) begin
                    r_sn_pend[r_sn_idx] <= w_sn_eff_new;
                end
            end
            // the alloc clears the reused entry's pend shadow (the MSHR
            // clears its own record at the alloc; this module is the only
            // sn_eff driver, so the shadow is exact)
            if (w_accept_alloc) begin
                r_sn_pend[mshr_alloc_idx_i] <= JET_PEND_NONE;
            end
            // commit FSM: the four MAS commit steps in order
            case (r_cmt_state)
                C_IDLE: begin
                    // the commit never starts during a snoop service: the
                    // pend record of a snoop matching the about-to-commit
                    // entry must land BEFORE the snapshot (and the effect
                    // cycle's tag write needs the port)
                    if (w_fq_head_done && (r_sn_state == SN_IDLE)) begin
                        if (r_fq_cls[r_fq_head] == JET_CLS_CU) begin
                            r_cmt_state <= C_CU_MERGE;
                        end else begin
                            // snapshot the entry (the commit read port is
                            // driven with the head index this cycle)
                            r_cmt_state <= C_MERGE;
                            r_cmt_idx   <= r_fq_idx[r_fq_head];
                            r_cmt_cls   <= r_fq_cls[r_fq_head];
                            r_cmt_pd    <= r_fq_pd[r_fq_head];
                            r_cmt_line  <= mshr_cpl_line_i;
                            r_cmt_pend  <= mshr_cpl_pend_eff_i;
                            r_cmt_count <= mshr_cpl_merge_count_i;
                            r_cmt_way   <= r_claim_way[r_fq_idx[r_fq_head]];
                            for (int k = 0; k < MSHR_COUNT; k++) begin
                                r_cmt_seqs[k] <=
                                    mshr_cpl_merge_seqs_i[k*SEQ_W +: SEQ_W];
                            end
                            r_cmt_k <= '0;
                        end
                    end
                end
                C_MERGE: begin
                    // step 1: D-4 store-data merge onto the just-filled
                    // beats, in requester order; read slots capture their
                    // response beat at their own position, so a read
                    // observes exactly the writes that precede it
                    if (w_slot_done) begin
                        r_cmt_state <= C_INSTALL;
                    end else if (w_slot_we) begin
                        if (!fill_beat_valid_i) begin
                            r_cmt_k <= r_cmt_k + 1'b1;
                        end
                        // fill beats own the W port: hold the cursor
                    end else begin
                        r_cmt_rdata[r_cmt_k[MW-1:0]] <= dat_a_rdata_i;
                        r_cmt_k <= r_cmt_k + 1'b1;
                    end
                end
                C_INSTALL: begin
                    // step 2: the tag install (combinational drive)
                    r_cmt_k <= '0;
                    if (r_cmt_pend != JET_PEND_NONE) begin
                        r_cmt_state <= C_PEND;
                    end else begin
                        r_cmt_state <= C_DEPOSIT;
                    end
                end
                C_PEND: begin
                    // step 3: the deferred snoop effect, AFTER the install
                    r_cmt_state <= C_DEPOSIT;
                end
                C_DEPOSIT: begin
                    // step 4a: one deposit per merge-list tag, in order
                    // (the deposit port is never backpressured; count >= 1
                    // by construction -- slot 0 is the allocator)
                    if (r_cmt_k == r_cmt_count - 1'b1) begin
                        r_cmt_state <= C_RETIRE;
                    end else begin
                        r_cmt_k <= r_cmt_k + 1'b1;
                    end
                end
                C_RETIRE: begin
                    // step 4b: retire the entry, free the claim, pop
                    r_cmt_state <= C_IDLE;
                end
                C_CU_MERGE: begin
                    // upgrade commit: merge the held write (D-4 on the
                    // resident line), subject to fill-beat priority
                    if (!fill_beat_valid_i) begin
                        r_cmt_state <= C_CU_INSTALL;
                    end
                end
                C_CU_INSTALL: begin
                    r_cmt_state <= C_CU_DEPOSIT;
                end
                C_CU_DEPOSIT: begin
                    r_cmt_state <= C_IDLE;
                end
                default: begin
                    r_cmt_state <= C_IDLE;   // defensive (amber engines)
                end
            endcase
        end
    )

    // ------------------------------------------------------------------
    // Simulation-only contract checks
    // ------------------------------------------------------------------
    // pragma translate_off
    // A dirty-victim alloc must find the WB buffer able to open a slot
    // (the classify guarantees it; this pins the integration).
    assert property (@(posedge clk) disable iff (!rst_n)
        ((w_accept_alloc & w_victim_dirty) |-> wb_cap_gnt_i))
        else $error("jet_control: dirty-victim alloc refused by the WB buffer");

    // The classify only drives an alloc it has proven grantable.
    assert property (@(posedge clk) disable iff (!rst_n)
        (mshr_alloc_o |-> mshr_alloc_gnt_i))
        else $error("jet_control: alloc driven but refused by the MSHR file");

    // fill_done always matches an outstanding un-done fill (in-order
    // completion, single AXI4 read ID).
    assert property (@(posedge clk) disable iff (!rst_n)
        (fill_done_i |-> (r_fq_undone != '0)))
        else $error("jet_control: fill_done with no outstanding un-done fill");

    // The completion queue never overflows: an MSHR entry is free (so the
    // head was popped, freeing its queue slot) before an alloc can launch
    // a fill, and the single upgrade's slot frees with the tracker.
    assert property (@(posedge clk) disable iff (!rst_n)
        ((w_fq_push & ~w_fq_pop) |-> (r_fq_cnt < (FQ_W+1)'(FQ_DEPTH))))
        else $error("jet_control: fill-completion queue overflow");

    // fill_accept without a launch presented is a contract violation.
    assert property (@(posedge clk) disable iff (!rst_n)
        (fill_accept_i |-> fill_start_o))
        else $error("jet_control: fill_accept with no launch presented");

    // Fill beats land only on an entry with a live way claim (they write
    // the claimed victim way).
    assert property (@(posedge clk) disable iff (!rst_n)
        (fill_beat_valid_i |-> r_claim_vld[fill_beat_idx_i]))
        else $error("jet_control: fill beat for an entry with no live claim");

    // The commit retires only an entry whose way claim is live.
    assert property (@(posedge clk) disable iff (!rst_n)
        (mshr_retire_o |-> r_claim_vld[mshr_retire_idx_o]))
        else $error("jet_control: retire of an entry with no live way claim");

    // A CU commit requires the upgrade tracker to be live.
    assert property (@(posedge clk) disable iff (!rst_n)
        ((r_cmt_state == C_CU_MERGE) |-> r_upgr_valid))
        else $error("jet_control: CU commit with no in-flight upgrade");

    // No two live claims share a (set, way) -- the claim-aware victim
    // check makes a double claim impossible for every policy (incl.
    // RANDOM repeats and LRU hit reordering).
    logic w_claim_dup;
    always_comb begin
        w_claim_dup = 1'b0;
        for (int e1 = 0; e1 < MSHR_COUNT; e1++) begin
            for (int e2 = e1 + 1; e2 < MSHR_COUNT; e2++) begin
                if (r_claim_vld[e1] && r_claim_vld[e2]
                    && (r_claim_set[e1] == r_claim_set[e2])
                    && (r_claim_way[e1] == r_claim_way[e2])) begin
                    w_claim_dup = 1'b1;
                end
            end
        end
    end

    assert property (@(posedge clk) disable iff (!rst_n)
        (!w_claim_dup))
        else $error("jet_control: two live entries claim the same (set, way)");

    // The transport presents a snoop only in a safe cycle (l1_snoop_resp
    // accepts the AC only while ctrl_snoop_safe).
    assert property (@(posedge clk) disable iff (!rst_n)
        (sn_req_i |-> sn_safe_o))
        else $error("jet_control: snoop presented while not safe");

    // A snoop service never overlaps the commit pipeline (the interlock
    // that lands a pend record before the commit's snapshot and keeps the
    // effect cycle's tag write contention-free).
    assert property (@(posedge clk) disable iff (!rst_n)
        ((r_sn_state != SN_IDLE) |-> (r_cmt_state == C_IDLE)))
        else $error("jet_control: snoop service overlaps the commit pipeline");

    // PF_GUARD: a data-carrying pending-fill answer had every fill beat
    // landed at the grant (no CD beat is ever presented for a beat the
    // fill has not landed).
    assert property (@(posedge clk) disable iff (!rst_n)
        (((r_sn_state == SN_DATA) && (r_sn_src == SRC_MSHR)) |-> r_sn_allb))
        else $error("jet_control: PF_GUARD violated (CD before the fill beat landed)");

    // A deferred effect is recorded only on a live (claimed) entry -- the
    // matched entry cannot retire mid-service (commits are blocked).
    assert property (@(posedge clk) disable iff (!rst_n)
        (mshr_sn_eff_o |-> r_claim_vld[mshr_sn_eff_idx_o]))
        else $error("jet_control: pend record targets a dead entry");

    // No entry retires during a snoop service.
    assert property (@(posedge clk) disable iff (!rst_n)
        (mshr_retire_o |-> (r_sn_state == SN_IDLE)))
        else $error("jet_control: retire during a snoop service");

    // The snoop effect's tag write never collides with a commit tag write.
    assert property (@(posedge clk) disable iff (!rst_n)
        (!(w_sn_tagwr & w_cmt_tagwr)))
        else $error("jet_control: tag port collision (snoop effect vs commit)");
    // pragma translate_on

endmodule : jet_control
