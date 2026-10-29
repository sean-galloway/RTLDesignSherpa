// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_mshr
// Purpose:
//   The jet MSHR file -- a MAB (miss address buffer) in Chinnakonda's
//   terms: it holds no line data; fill beats write the data array
//   directly (the small-area scheme). Fully-associative CAM keyed by line
//   address tracking MSHR_COUNT outstanding misses (J1: 2-16, default 8).
//   Carries the hazard state jet_control acts on: the fill class (cross-
//   class wait, J3), the per-set victim-way claim counters (set
//   oversubscription), the PF_GUARD beat bitmask, the deferred post-commit
//   snoop effect, and the merge list of requester sequence tags waiting
//   on each fill.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch02_blocks/02_jet_mshr.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_mshr
//==============================================================================
// Description:
//   Entry fields are per-entry unpacked arrays (control state, so they
//   carry a reset; valid/claims reset to empty). The two CAM probes
//   (lookup side, snoop side) are combinational; the grant/index of the
//   alloc port are combinational so the alloc/match same-cycle rule holds:
//   a granted alloc is visible to both probes FROM THE ALLOC CYCLE, with
//   any existing matching entry winning the index over the incoming alloc.
//
//   Set oversubscription: SETS claim counters, $clog2(WAYS+1) bits each
//   (3 bits at 4 ways; the counter must represent WAYS itself). An alloc
//   to a set whose claim count is WAYS is refused (set_full_o) until one
//   of that set's entries retires. A same-cycle alloc+retire to the same
//   set nets the counter (both events apply; the count is unchanged).
//   Grant is computed on the current state only -- a same-cycle retire
//   does not unblock a stalled alloc until the next cycle.
//
//   The merge list is a per-entry MSHR_COUNT-deep tag list; slot 0 is the
//   allocator's own sequence tag. The aggregate live-tag bound (RSP_DEPTH)
//   is enforced by the front-end tag allocator (jet_control), not here;
//   this module only refuses appends past the per-entry depth.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   MSHR_COUNT:
//     Description: Outstanding misses tracked (J1)
//     Type: int
//     Range: 2 to 16 (elaboration $error outside)
//     Default: jet_pkg.MSHR_COUNT (8)
//
//   SETS:
//     Description: Number of cache sets (claim-counter bank size)
//     Type: int
//     Range: power of two
//     Default: l1_pkg.AMBER_SETS (128)
//
//   WAYS:
//     Description: Associativity (per-set claim cap)
//     Type: int
//     Range: power of two, >= 2
//     Default: l1_pkg.AMBER_WAYS (4)
//
//   LINE_W:
//     Description: Miss line-address width (the CAM key): address minus
//                  the line-offset bits
//     Type: int
//     Default: l1_pkg AMBER_ADDR_WIDTH - clog2(AMBER_LINE_BYTES) (26)
//
//   SEQ_W:
//     Description: Requester sequence-tag width (merge list element)
//     Type: int
//     Default: jet_pkg.SEQ_W
//
//   VICTIM_DEPTH:
//     Description: WB-buffer rows (sizes the per-entry wb_slot field, J5)
//     Type: int
//     Range: 1 to 4
//     Default: jet_pkg.VICTIM_DEPTH (2)
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - alloc_set_i is the claim-bank index, driven by jet_control (it owns
//     the address decode); the retire-side decrement derives the set from
//     the retiring entry's stored line (set = line[SET_W-1:0]).
//   - merge/beat/sn_eff to an entry that retires in the same cycle are a
//     contract violation; retire wins and the field writes land in a dead
//     entry.
//   - retire_i to an invalid entry does not decrement a claim counter
//     (guarded), so a control bug cannot silently corrupt the bank.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: jet_mshr_th (unit DV); jet_control (Tasks 5-7)
//   - Package: jet_pkg (MSHR_COUNT/VICTIM_DEPTH/SEQ_W, cls/pend enums),
//              l1_pkg (geometry defaults, FILL_BEATS)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_mshr.py
//   Run: pytest projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_mshr.py -v
//
//==============================================================================

module jet_mshr
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int MSHR_COUNT   = jet_pkg::MSHR_COUNT,
    parameter int SETS         = AMBER_SETS,
    parameter int WAYS         = AMBER_WAYS,
    parameter int LINE_W       = AMBER_ADDR_WIDTH - $clog2(AMBER_LINE_BYTES),
    parameter int SEQ_W        = jet_pkg::SEQ_W,
    parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH,
    localparam int SET_W      = $clog2(SETS),
    localparam int WAY_W      = $clog2(WAYS),
    localparam int MW         = $clog2(MSHR_COUNT),
    localparam int FILL_BEATS = AMBER_FILL_BEATS,
    localparam int BEAT_W     = $clog2(FILL_BEATS),
    localparam int WB_W       = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH),
    localparam int CLAIM_W    = $clog2(WAYS + 1)
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // Alloc request (grant/index combinational on current state)
    input  logic                        alloc_i,
    input  logic [LINE_W-1:0]           alloc_line_i,
    input  logic [SET_W-1:0]            alloc_set_i,
    input  logic [1:0]                  alloc_cls_i,
    input  logic                        alloc_install_i,
    input  logic [WAY_W-1:0]            alloc_victim_way_i,
    input  logic [WB_W-1:0]             alloc_wb_slot_i,
    input  logic                        alloc_wb_valid_i,
    input  logic [SEQ_W-1:0]            alloc_seq_i,
    output logic                        alloc_gnt_o,
    output logic [MW-1:0]               alloc_idx_o,
    output logic                        full_o,
    output logic                        set_full_o,

    // Lookup-side CAM probe (merge? / cross-class wait classify)
    input  logic [LINE_W-1:0]           lkup_line_i,
    output logic                        lkup_match_o,
    output logic                        lkup_reg_match_o,
    output logic [MW-1:0]               lkup_reg_match_idx_o,
    output logic [1:0]                  lkup_reg_match_cls_o,
    output logic [MW-1:0]               lkup_match_idx_o,
    output logic [1:0]                  lkup_match_cls_o,

    // Snoop-side CAM probe (pending-fill hazard + PF_GUARD)
    input  logic [LINE_W-1:0]           sn_line_i,
    output logic                        sn_match_o,
    output logic [MW-1:0]               sn_match_idx_o,
    output logic [FILL_BEATS-1:0]       sn_beats_rcvd_o,
    output logic                        sn_install_o,

    // Merge: append a waiter sequence tag to an entry
    input  logic                        merge_i,
    input  logic [MW-1:0]               merge_idx_i,
    input  logic [SEQ_W-1:0]            merge_seq_i,

    // Fill beat landed (drives PF_GUARD)
    input  logic                        beat_i,
    input  logic [MW-1:0]               beat_idx_i,
    input  logic [BEAT_W-1:0]           beat_num_i,

    // Deferred post-commit snoop effect (none / downgrade-S / invalidate-I)
    input  logic                        sn_eff_i,
    input  logic [MW-1:0]               sn_eff_idx_i,
    input  logic [1:0]                  sn_eff_value_i,

    // Retire on commit: frees the entry and its victim-way claim
    input  logic                        retire_i,
    input  logic [MW-1:0]               retire_idx_i,

    // Commit read port
    input  logic [MW-1:0]               cpl_idx_i,
    output logic [LINE_W-1:0]           cpl_line_o,
    output logic                        cpl_install_o,
    output logic [1:0]                  cpl_pend_eff_o,
    output logic [MSHR_COUNT*SEQ_W-1:0] cpl_merge_seqs_o,
    output logic [MW:0]                 cpl_merge_count_o,
    output logic [WB_W-1:0]             cpl_wb_slot_o,
    output logic                        cpl_wb_valid_o,

    // MonBus occupancy gauge (J7)
    output logic [MW:0]                 occupancy_o
);

    // Elaboration-time range checks (house idiom, cf. l1_tag_array). The
    // MSHR_COUNT 2-16 bound is J1; the package carries only the default
    // because SV package parameters cannot be overridden, so the check
    // belongs at the module (this is also what makes the J7 2/4/8/16
    // sweep possible).
    initial begin
        if (MSHR_COUNT < 2 || MSHR_COUNT > 16)
            $error("jet_mshr: MSHR_COUNT must be in 2..16 (J1)");
        if ((SETS & (SETS - 1)) != 0)
            $error("jet_mshr: SETS must be a power of two");
        if ((WAYS & (WAYS - 1)) != 0 || WAYS < 2)
            $error("jet_mshr: WAYS must be a power of two >= 2");
        if (LINE_W <= SET_W)
            $error("jet_mshr: LINE_W must exceed the set-index width");
    end

    // =========================================================================
    // Entry storage (per-field unpacked arrays; the CAM key is `line`).
    // =========================================================================
    logic [MSHR_COUNT-1:0]  r_valid;
    logic [LINE_W-1:0]      r_line       [MSHR_COUNT];
    logic [1:0]             r_cls        [MSHR_COUNT];
    logic                   r_install    [MSHR_COUNT];
    logic [WAY_W-1:0]       r_victim_way [MSHR_COUNT];
    logic [WB_W-1:0]        r_wb_slot    [MSHR_COUNT];
    logic                   r_wb_valid   [MSHR_COUNT];
    logic [SEQ_W-1:0]       r_merge      [MSHR_COUNT * MSHR_COUNT];
    logic [MW:0]            r_merge_count[MSHR_COUNT];
    logic [FILL_BEATS-1:0]  r_beats_rcvd [MSHR_COUNT];
    logic [1:0]             r_pend_eff   [MSHR_COUNT];
    logic [SEQ_W-1:0]       r_seq        [MSHR_COUNT];

    // Per-set victim-claim counters (set oversubscription).
    logic [CLAIM_W-1:0]     r_set_claims [SETS];

    // =========================================================================
    // Alloc: first free entry (lowest index), combinational grant.
    // =========================================================================
    logic           w_any_free;
    logic [MW-1:0]  w_free_sel;

    always_comb begin
        w_any_free = 1'b0;
        w_free_sel = '0;
        for (int e = MSHR_COUNT - 1; e >= 0; e--) begin
            if (!r_valid[e]) begin
                w_any_free = 1'b1;
                w_free_sel = MW'(e);
            end
        end
    end

    assign full_o      = ~w_any_free;
    assign set_full_o  = (r_set_claims[alloc_set_i] == CLAIM_W'(WAYS));
    assign alloc_gnt_o = alloc_i & w_any_free & ~set_full_o;
    assign alloc_idx_o = w_free_sel;

    // =========================================================================
    // CAM probes: lowest-index valid match wins; a granted alloc to the
    // probed line is visible from the alloc cycle (alloc/match same-cycle
    // rule), taking the alloc slot index when no existing entry matches.
    // =========================================================================
    logic [MSHR_COUNT-1:0] w_lkup_hits;
    logic [MSHR_COUNT-1:0] w_sn_hits;

    always_comb begin
        for (int e = 0; e < MSHR_COUNT; e++) begin
            w_lkup_hits[e] = r_valid[e] & (r_line[e] == lkup_line_i);
            w_sn_hits[e]   = r_valid[e] & (r_line[e] == sn_line_i);
        end
    end

    wire w_lkup_alloc_hit = alloc_gnt_o & (alloc_line_i == lkup_line_i);
    wire w_sn_alloc_hit   = alloc_gnt_o & (alloc_line_i == sn_line_i);

    always_comb begin
        lkup_match_o     = 1'b0;
        lkup_match_idx_o = '0;
        for (int e = MSHR_COUNT - 1; e >= 0; e--) begin
            if (w_lkup_hits[e]) begin
                lkup_match_o     = 1'b1;
                lkup_match_idx_o = MW'(e);
            end
        end
        if (!lkup_match_o && w_lkup_alloc_hit) begin
            lkup_match_o     = 1'b1;
            lkup_match_idx_o = w_free_sel;
        end
    end

    assign lkup_match_cls_o = (|w_lkup_hits) ? r_cls[lkup_match_idx_o]
                                             : alloc_cls_i;

    // Registered-entries-only match (no alloc overlay): jet_control's
    // classify drives the alloc from the match outcome, so it must see
    // the pre-alloc match or the two would form a combinational loop
    // (the overlay makes lkup_match_* structurally alloc-dependent).
    assign lkup_reg_match_o = |w_lkup_hits;

    always_comb begin
        lkup_reg_match_idx_o = '0;
        for (int e = MSHR_COUNT - 1; e >= 0; e--) begin
            if (w_lkup_hits[e]) begin
                lkup_reg_match_idx_o = MW'(e);
            end
        end
    end

    assign lkup_reg_match_cls_o = r_cls[lkup_reg_match_idx_o];

    always_comb begin
        sn_match_o     = 1'b0;
        sn_match_idx_o = '0;
        for (int e = MSHR_COUNT - 1; e >= 0; e--) begin
            if (w_sn_hits[e]) begin
                sn_match_o     = 1'b1;
                sn_match_idx_o = MW'(e);
            end
        end
        if (!sn_match_o && w_sn_alloc_hit) begin
            sn_match_o     = 1'b1;
            sn_match_idx_o = w_free_sel;
        end
    end

    // An entry seen through the alloc-first rule has landed no beats yet.
    assign sn_beats_rcvd_o = (|w_sn_hits) ? r_beats_rcvd[sn_match_idx_o] : '0;
    assign sn_install_o    = (|w_sn_hits) ? r_install[sn_match_idx_o]
                                          : (w_sn_alloc_hit & alloc_install_i);

    // =========================================================================
    // Commit read port (combinational).
    // =========================================================================
    always_comb begin
        cpl_line_o        = r_line[cpl_idx_i];
        cpl_install_o     = r_install[cpl_idx_i];
        cpl_pend_eff_o    = r_pend_eff[cpl_idx_i];
        cpl_merge_count_o = r_merge_count[cpl_idx_i];
        cpl_wb_slot_o     = r_wb_slot[cpl_idx_i];
        cpl_wb_valid_o    = r_wb_valid[cpl_idx_i];
        for (int k = 0; k < MSHR_COUNT; k++) begin
            cpl_merge_seqs_o[k*SEQ_W +: SEQ_W] =
                r_merge[32'(cpl_idx_i) * MSHR_COUNT + k];
        end
    end

    // =========================================================================
    // Occupancy gauge (MonBus, J7).
    // =========================================================================
    always_comb begin
        occupancy_o = '0;
        for (int e = 0; e < MSHR_COUNT; e++) begin
            occupancy_o = occupancy_o + (MW+1)'(r_valid[e]);
        end
    end

    // =========================================================================
    // Entry updates. Field ops (merge/beat/sn_eff) and retire target live
    // entries; alloc targets a free one, so retire and alloc never collide
    // on an index. Alloc reinitializes every field (stale merge slots are
    // shadowed by the reset count).
    // =========================================================================
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid <= '0;
            for (int e = 0; e < MSHR_COUNT; e++) begin
                r_line[e]        <= '0;
                r_cls[e]         <= '0;
                r_install[e]     <= 1'b0;
                r_victim_way[e]  <= '0;
                r_wb_slot[e]     <= '0;
                r_wb_valid[e]    <= 1'b0;
                r_merge_count[e] <= '0;
                r_beats_rcvd[e]  <= '0;
                r_pend_eff[e]    <= '0;
                r_seq[e]         <= '0;
            end
            for (int k = 0; k < MSHR_COUNT * MSHR_COUNT; k++) begin
                r_merge[k] <= '0;
            end
        end else begin
            if (merge_i
                    && (r_merge_count[merge_idx_i] < (MW+1)'(MSHR_COUNT))) begin
                r_merge[32'(merge_idx_i) * MSHR_COUNT
                        + 32'(r_merge_count[merge_idx_i])] <= merge_seq_i;
                r_merge_count[merge_idx_i] <= r_merge_count[merge_idx_i] + 1'b1;
            end
            if (beat_i) begin
                r_beats_rcvd[beat_idx_i][beat_num_i] <= 1'b1;
            end
            if (sn_eff_i) begin
                r_pend_eff[sn_eff_idx_i] <= sn_eff_value_i;
            end
            if (retire_i) begin
                r_valid[retire_idx_i] <= 1'b0;
            end
            if (alloc_gnt_o) begin
                r_valid[w_free_sel]        <= 1'b1;
                r_line[w_free_sel]         <= alloc_line_i;
                r_cls[w_free_sel]          <= alloc_cls_i;
                r_install[w_free_sel]      <= alloc_install_i;
                r_victim_way[w_free_sel]   <= alloc_victim_way_i;
                r_wb_slot[w_free_sel]      <= alloc_wb_slot_i;
                r_wb_valid[w_free_sel]     <= alloc_wb_valid_i;
                r_merge[32'(w_free_sel) * MSHR_COUNT] <= alloc_seq_i;
                r_merge_count[w_free_sel]  <= {{MW{1'b0}}, 1'b1};
                r_beats_rcvd[w_free_sel]   <= '0;
                r_pend_eff[w_free_sel]     <= '0;
                r_seq[w_free_sel]          <= alloc_seq_i;
            end
        end
    )

    // =========================================================================
    // Per-set claim counters: alloc grants increment, retires decrement
    // (guarded on the entry being live), and a same-cycle pair to one set
    // nets -- the counter holds.
    // =========================================================================
    wire [SET_W-1:0] w_retire_set = r_line[retire_idx_i][SET_W-1:0];
    wire             w_retire_live = retire_i & r_valid[retire_idx_i];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int s = 0; s < SETS; s++) begin
                r_set_claims[s] <= '0;
            end
        end else begin
            for (int s = 0; s < SETS; s++) begin
                case ({alloc_gnt_o & (alloc_set_i == SET_W'(s)),
                       w_retire_live & (w_retire_set == SET_W'(s))})
                    2'b10:   r_set_claims[s] <= r_set_claims[s] + 1'b1;
                    2'b01:   r_set_claims[s] <= r_set_claims[s] - 1'b1;
                    default: ;  // 00: no event; 11: alloc+retire net to hold
                endcase
            end
        end
    )

    // =========================================================================
    // Simulation-only contract checks (Task 5 integration hardening)
    // =========================================================================
    // pragma translate_off
    // A granted alloc whose line already matches a valid entry is a
    // contract violation (the lookup stage must merge onto it instead).
    logic [MSHR_COUNT-1:0] w_alloc_hits;

    always_comb begin
        for (int e = 0; e < MSHR_COUNT; e++) begin
            w_alloc_hits[e] = r_valid[e] & (r_line[e] == alloc_line_i);
        end
    end

    assert property (@(posedge clk) disable iff (!rst_n)
        (alloc_gnt_o |-> !(|w_alloc_hits)))
        else $error("jet_mshr: granted alloc duplicates a live entry's line");

    // jet_control owns the address decode; the claim bank trusts
    // alloc_set_i, so it must match the line's set field.
    assert property (@(posedge clk) disable iff (!rst_n)
        (alloc_gnt_o |-> (alloc_set_i == alloc_line_i[SET_W-1:0])))
        else $error("jet_mshr: alloc_set_i inconsistent with alloc_line_i");
    // pragma translate_on

endmodule : jet_mshr
