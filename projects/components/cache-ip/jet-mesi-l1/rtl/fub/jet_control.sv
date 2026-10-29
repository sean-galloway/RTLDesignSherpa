// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_control
// Purpose:
//   Lookup stage of the jet (lockup-free MESI L1) control core -- the
//   lookup half of the lookup/commit split that replaces amber's blocking
//   l1_control FSM (MAS ch02_blocks/01).  One request, one window: the tag
//   read (port A), the MSHR CAM match, the WB-buffer match, and the set's
//   victim-way claim count are all visible in the same cycle (the PoS).
//   Outcome classes: HIT / MERGE / MISS_ALLOC / STALL with the J6 stall
//   sub-reasons.
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
//     1. HIT -- line resident (S/E/M) and its way is not claimed by an
//        outstanding MSHR entry (the pending-fill hazard: a doomed
//        victim's tag is still installed until the fill's commit, but its
//        data is being captured/overwritten, so the hit is suppressed and
//        the request falls through to the miss path).  Read hits serve
//        from port A and deposit immediately.  Write hits (E/M) merge
//        through the data-array W port and promote E->M on the tag port;
//        they YIELD the W port to an in-flight fill beat stream (fill
//        beats > write hits, bounded by FILL_BEATS) by holding the
//        request unaccepted until the stream releases the port.  A write
//        hit on S is an upgrade: JET_CLS_CU is launched to the fabric and
//        the single-outstanding upgrade tracker holds same-line writes
//        (cross-class wait) until the upgrade's fill_done (the commit
//        side of upgrades is Task 6).
//     2. MERGE -- no hit, MSHR match, compatible class (a read joins any
//        fill; a write joins only an RU fill): the request's sequence tag
//        is appended to the entry's merge list.  A write behind an RNSD
//        fill is the cross-class wait (STALL, J3).  A merge onto an entry
//        whose merge list is full stalls mshr_full.
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
//        set_oversubscribed (WAYS claims in this set, or the victim way is
//        the in-flight upgrade's way), wb_full_dirty_victim (WB full or a
//        capture is streaming AND the victim is dirty -- clean-victim
//        misses allocate freely with the WB full, J6), tag_full (the
//        response sequencer ring has no free slot).
//     4. STALL -- lkup_stall_o + lkup_stall_reason_o report the reason;
//        the request is retried next cycle.  Holds that are not
//        congestion stalls (write-hit W-port yield, fill-launch register
//        busy, upgrade pipe busy) depress lkup_ready_o without raising
//        lkup_stall_o.
//
//   W-port arbitration: fill_beat_valid_i marks the fill engine's W-port
//   cycles; the lookup stage never presents a write-hit merge in those
//   cycles, so the integrator's mux can give fill beats unconditional
//   priority.  The victim capture reads data-array port B (the snoop port
//   is Task 7); the fill engine must not write an entry's beats before
//   its victim capture completes (cap_busy_o).
//
//   Task 5 scope: the commit pipeline is stubbed -- cmt_retire_i is the
//   TB/partner retire strobe forwarded to jet_mshr (and the claim
//   scoreboard); fill_done_i only clears the upgrade tracker.  The snoop
//   path (Task 7) is unwired: the WB snarf probe is driven with the
//   lookup line for the drain-race check and sn_eff is held NONE.
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
//     jet_wb_buffer capture, jet_rsp_seq tag-alloc + hit deposit
//   - Package: jet_pkg (JET_CLS_*, RSP_DEPTH derivation), l1_pkg
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
    localparam int WB_W       = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH)
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

    // data array port B (victim capture; the snoop path is Task 7)
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
    output logic                        mshr_merge_o,
    output logic [MW-1:0]               mshr_merge_idx_o,
    output logic [SEQ_W-1:0]            mshr_merge_seq_o,
    output logic                        mshr_beat_o,
    output logic [MW-1:0]               mshr_beat_idx_o,
    output logic [BEAT_W-1:0]           mshr_beat_num_o,
    output logic                        mshr_retire_o,
    output logic [MW-1:0]               mshr_retire_idx_o,

    // commit stub (Task 6 replaces with the internal commit pipeline)
    input  logic                        cmt_retire_i,
    input  logic [MW-1:0]               cmt_retire_idx_i,

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
    input  logic                        wb_drain_valid_i,
    output logic                        drain_start_o,
    input  logic                        drain_done_i,

    // fill engine launch + beat-stream observation
    output logic                        fill_start_o,
    output logic [ADDR_WIDTH-1:0]       fill_addr_o,
    output logic [1:0]                  fill_cls_o,
    input  logic                        fill_accept_i,
    input  logic                        fill_beat_valid_i,
    input  logic [MW-1:0]               fill_beat_idx_i,
    input  logic [BEAT_W-1:0]           fill_beat_num_i,
    input  logic                        fill_done_i
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
    // drain-arbiter stub (Task 6/8: the real l1_drain handshake)
    logic                    r_drain_busy;
    // single-outstanding upgrade (CLEAN_UNIQUE) tracker
    logic                    r_upgr_valid;
    logic [LINE_W-1:0]       r_upgr_line;
    logic [SET_W-1:0]        r_upgr_set;
    logic [WAY_W-1:0]        r_upgr_way;
    // claimed-way scoreboard: which (set, way) each live MSHR entry's fill
    // will install into -- the pending-fill hazard for hit suppression
    logic [MSHR_COUNT-1:0]   r_claim_vld;
    logic [SET_W-1:0]        r_claim_set [MSHR_COUNT];
    logic [WAY_W-1:0]        r_claim_way [MSHR_COUNT];

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
    logic           w_miss;
    logic [2:0]     w_victim_state;
    logic [TAG_W-1:0] w_victim_tag;
    logic           w_victim_dirty;
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

    assign w_miss         = ~w_serve_hit & ~mshr_lkup_reg_match_i;
    assign w_victim_state = tag_a_tag_state_i[repl_victim_way_i][2:0];
    assign w_victim_tag   = tag_a_tag_state_i[repl_victim_way_i][TSW-1 -: TAG_W];
    assign w_victim_dirty = (w_victim_state == AMBER_STATE_M);

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

    // A write to the in-flight upgrade's own line waits for the commit.
    assign w_upgr_line_stall = w_hit_upgr & r_upgr_valid
                               & (r_upgr_line == w_req_line);

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
        if (lkup_valid_i && !r_init_busy) begin
            if (w_hit_rd) begin
                w_acceptable = 1'b1;
            end else if (w_hit_wr) begin
                // write hits take the W port subject to fill-beat
                // priority (J2): yield (hold, unaccepted) while the fill
                // engine owns the port -- bounded by FILL_BEATS
                if (fill_beat_valid_i) begin
                    w_yield = 1'b1;
                end else begin
                    w_acceptable = 1'b1;
                end
            end else if (w_hit_upgr) begin
                if (w_upgr_line_stall) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_XCLASS;
                end else if (!r_upgr_valid && !r_fill_pend) begin
                    w_acceptable = 1'b1;
                end
                // upgrade pipe / launch register busy: hold (not a stall)
            end else if (mshr_lkup_reg_match_i) begin
                if (w_xclass) begin
                    w_stall  = 1'b1;
                    w_reason = STALL_XCLASS;
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
                end else if (mshr_set_full_i | w_upgr_victim_block) begin
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
    // Fill launch (held until fill_accept_i)
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

    // ------------------------------------------------------------------
    // Response deposit (hits only; fills/merges deposit at commit, Task 6)
    // ------------------------------------------------------------------
    assign cpl_valid_o = w_accept_rd | w_accept_wr;
    assign cpl_tag_o   = tag_i;
    assign cpl_data_o  = w_accept_rd ? dat_a_rdata_i : lkup_wdata_i;

    // ------------------------------------------------------------------
    // Array port A
    // ------------------------------------------------------------------
    assign tag_a_set_o = r_init_busy ? r_init_cnt : w_req_set;
    assign tag_a_wr_en_o = (r_init_busy & ~`RST_ASSERTED(rst_n))
                           | (w_accept_wr & (w_hit_state == AMBER_STATE_E));
    assign tag_a_wr_way_onehot_o = r_init_busy ? {WAYS{1'b1}}
                                               : w_hit_way_onehot;
    assign tag_a_wr_set_o        = r_init_busy ? r_init_cnt : w_req_set;
    assign tag_a_wr_tag_state_o  = r_init_busy
                                   ? {{TAG_W{1'b0}}, AMBER_STATE_I}
                                   : {w_req_tag, AMBER_STATE_M};

    assign dat_a_addr_o         = {w_req_set, w_req_beat};
    assign dat_a_way_o          = w_hit_way;
    assign dat_a_wr_en_o        = w_accept_wr;
    assign dat_a_wr_way_onehot_o = w_hit_way_onehot;
    assign dat_a_wr_addr_o      = {w_req_set, w_req_beat};
    assign dat_a_wr_wdata_o     = lkup_wdata_i;
    assign dat_a_wr_be_o        = lkup_be_i;

    // ------------------------------------------------------------------
    // Array port B: the victim capture stream
    // ------------------------------------------------------------------
    assign dat_b_addr_o = {r_cap_set, r_cap_beat};
    assign dat_b_way_o  = r_cap_way;

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
    assign mshr_cpl_idx_o          = mshr_lkup_reg_match_idx_i;
    assign mshr_merge_o            = w_accept_merge;
    assign mshr_merge_idx_o        = mshr_lkup_reg_match_idx_i;
    assign mshr_merge_seq_o        = tag_i;
    assign mshr_beat_o             = fill_beat_valid_i;
    assign mshr_beat_idx_o         = fill_beat_idx_i;
    assign mshr_beat_num_o         = fill_beat_num_i;
    assign mshr_retire_o           = cmt_retire_i;
    assign mshr_retire_idx_o       = cmt_retire_idx_i;

    // ------------------------------------------------------------------
    // WB buffer: capture open + beat stream + snarf probe (lookup use
    // only; Task 7 muxes the snoop line)
    // ------------------------------------------------------------------
    assign wb_cap_o          = (w_accept_alloc & w_victim_dirty) | r_cap_busy;
    assign wb_cap_line_o     = r_cap_busy ? r_cap_line
                                          : {w_victim_tag, w_req_set};
    assign wb_cap_beat_o     = r_cap_busy;
    assign wb_cap_beat_data_o = dat_b_rdata_i;
    assign wb_sn_line_o      = w_req_line;
    assign wb_sn_eff_o       = JET_PEND_NONE;

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
            r_drain_busy <= 1'b0;
            r_upgr_valid <= 1'b0;
            r_upgr_line  <= '0;
            r_upgr_set   <= '0;
            r_upgr_way   <= '0;
            r_claim_vld  <= '0;
            for (int e = 0; e < MSHR_COUNT; e++) begin
                r_claim_set[e] <= '0;
                r_claim_way[e] <= '0;
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
            // FILL_BEATS consecutive port-B reads (never paused in the
            // lookup stage -- port B is lookup-exclusive until Task 7)
            if (w_accept_alloc & w_victim_dirty) begin
                r_cap_busy <= 1'b1;
                r_cap_set  <= w_req_set;
                r_cap_way  <= repl_victim_way_i;
                r_cap_line <= {w_victim_tag, w_req_set};
                r_cap_beat <= '0;
            end else if (r_cap_busy) begin
                if (r_cap_beat == BEAT_W'(FILL_BEATS - 1)) begin
                    r_cap_busy <= 1'b0;
                    r_cap_beat <= '0;
                end else begin
                    r_cap_beat <= r_cap_beat + 1'b1;
                end
            end
            // fill launch hold (a launch implies the register was free)
            if (w_launch & ~fill_accept_i) begin
                r_fill_pend <= 1'b1;
                r_fill_addr <= w_launch_addr;
                r_fill_cls  <= w_launch_cls;
            end else if (fill_accept_i) begin
                r_fill_pend <= 1'b0;
            end
            // drain arbiter stub
            if (drain_start_o) begin
                r_drain_busy <= 1'b1;
            end else if (drain_done_i) begin
                r_drain_busy <= 1'b0;
            end
            // upgrade tracker: set at the launch, cleared by the
            // upgrade's fill_done (the commit-side clear is Task 6)
            if (w_accept_upgr) begin
                r_upgr_valid <= 1'b1;
                r_upgr_line  <= w_req_line;
                r_upgr_set   <= w_req_set;
                r_upgr_way   <= w_hit_way;
            end else if (fill_done_i) begin
                r_upgr_valid <= 1'b0;
            end
            // claimed-way scoreboard (pending-fill hazard)
            if (w_accept_alloc) begin
                r_claim_vld[mshr_alloc_idx_i] <= 1'b1;
                r_claim_set[mshr_alloc_idx_i] <= w_req_set;
                r_claim_way[mshr_alloc_idx_i] <= repl_victim_way_i;
            end
            if (cmt_retire_i) begin
                r_claim_vld[cmt_retire_idx_i] <= 1'b0;
            end
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

    // The commit stub may only retire an entry whose way claim is live.
    assert property (@(posedge clk) disable iff (!rst_n)
        (cmt_retire_i |-> r_claim_vld[cmt_retire_idx_i]))
        else $error("jet_control: retire of an entry with no live way claim");

    // The classify only drives an alloc it has proven grantable.
    assert property (@(posedge clk) disable iff (!rst_n)
        (mshr_alloc_o |-> mshr_alloc_gnt_i))
        else $error("jet_control: alloc driven but refused by the MSHR file");
    // pragma translate_on

endmodule : jet_control
