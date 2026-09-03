// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// pumice_rbl_table — RBLA row-locality miss-counter table (Yoon 2012 class).
//
// PUMICE-006 Axis 2, modes 6 (rbl_static) / 7 (rbl_dyn). The scheme counts
// row-buffer MISSES only, not accesses: a row that keeps getting re-activated
// (every ACT is by definition a row-buffer miss for that row) is either
// hot-and-thrashing (close it eagerly -> auto-precharge) or was simply cold.
// Frequency-based schemes conflate hot-friendly with hot-thrashing rows; the
// miss-only counter separates them, because a row served entirely by hits
// after one activate accumulates nothing.
//
// Structure: a per-bank set-associative table of saturating miss counters,
// tag = row address, true-LRU within a set (WAYS_MAX <= 4), runtime-shaped
// inside build caps by PAGE_RBL_CFG.{ways, sets} (log2 encodings, clamped).
// Epoch reset: every reset_interval cycles the COUNTERS clear (tags stay, so
// residency survives the epoch but evidence must re-accumulate).
//
// Decision latch: at ACT time — the only moment a row's locality class is
// consulted — the incremented counter is compared against the threshold and
// the verdict latched per bank: `low_locality_o[bank]` holds for the entire
// time that row is open. The column path therefore reads a flop, never the
// table. The consumer (pumice_page_policy) turns the mask into per-bank
// auto-precharge.
//
// rbl_dyn (dyn_en_i): hill-climb the threshold once per epoch on the measured
// page-hit fraction. Direction memory: keep stepping the way quality improved,
// reverse when it worsened; threshold clamped to [1, 255]. With
// reset_interval == 0 there are no epochs, so no adaptation (and no counter
// clears) — program a nonzero epoch for mode 7.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_rbl_table
    import pumice_pkg::*;
#(
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int WAYS_MAX_LOG2 = 2,   // build cap: 4 ways
    parameter int SETS_MAX_LOG2 = 4,   // build cap: 16 sets
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                   aclk,
    input  logic                   aresetn,

    input  logic                   enable_i,          // mode 6 or 7 active
    input  logic                   dyn_en_i,          // mode 7: hill-climb thresh
    // PAGE_RBL_CFG
    input  logic [7:0]             miss_thresh_i,     // static threshold (mode 6)
    input  logic [1:0]             ways_log2_i,       // clamped to WAYS_MAX_LOG2
    input  logic [3:0]             sets_log2_i,       // clamped to SETS_MAX_LOG2
    input  logic [15:0]            reset_interval_i,  // epoch length, 0 = never

    // issued command stream (valid && ready)
    input  logic                   cmd_valid_i,
    input  dram_op_e               cmd_op_i,
    input  logic [BKW-1:0]         cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]   cmd_row_i,

    output logic [NUM_BANKS-1:0]   low_locality_o     // open row is a thrasher
);

    localparam int WAYS = 1 << WAYS_MAX_LOG2;
    localparam int SETS = 1 << SETS_MAX_LOG2;
    localparam int CTRW = 4;                          // saturating miss counter

    // Runtime shape, clamped into the build caps. Fewer sets = mask index;
    // fewer ways = restrict the replacement scan. Zero means "cap" (the CSR
    // reset value 0 keeps the full table, matching "0 = build default").
    logic [1:0] w_ways_l2;
    logic [3:0] w_sets_l2;
    assign w_ways_l2 = (ways_log2_i == 0 || ways_log2_i > WAYS_MAX_LOG2[1:0])
                       ? WAYS_MAX_LOG2[1:0] : ways_log2_i;
    assign w_sets_l2 = (sets_log2_i == 0 || sets_log2_i > SETS_MAX_LOG2[3:0])
                       ? SETS_MAX_LOG2[3:0] : sets_log2_i;

    logic [SETS_MAX_LOG2-1:0] w_set_mask;
    assign w_set_mask = SETS_MAX_LOG2'((1 << w_sets_l2) - 1);
    logic [WAYS-1:0] w_way_mask;
    assign w_way_mask = WAYS'((1 << (1 << w_ways_l2)) - 1);

    // ---- table state (flops; 4x16 = 64 entries at the caps) ---------------
    logic [SETS-1:0][WAYS-1:0]                 r_valid;
    logic [SETS-1:0][WAYS-1:0][ROW_WIDTH-1:0]  r_tag;
    logic [SETS-1:0][WAYS-1:0][CTRW-1:0]       r_cnt;
    logic [SETS-1:0][WAYS-1:0][1:0]            r_lru;   // age, 0 = MRU

    // Effective threshold (static or the adapting register).
    logic [7:0] r_thresh;
    logic [7:0] w_thresh_eff;
    assign w_thresh_eff = dyn_en_i ? r_thresh : miss_thresh_i;

    // ---- lookup on ACT ------------------------------------------------------
    logic w_is_act;
    assign w_is_act = cmd_valid_i && (cmd_op_i == OP_ACT) && enable_i;

    logic [SETS_MAX_LOG2-1:0] w_idx;
    assign w_idx = cmd_row_i[SETS_MAX_LOG2-1:0] & w_set_mask;

    // Hit way / victim way (LRU among enabled ways).
    logic            w_hit;
    logic [WAYS-1:0] w_hit_way, w_victim_way;
    always_comb begin
        w_hit = 1'b0; w_hit_way = '0;
        for (int wy = 0; wy < WAYS; wy++) begin
            if (w_way_mask[wy] && r_valid[w_idx][wy]
                && (r_tag[w_idx][wy] == cmd_row_i)) begin
                w_hit = 1'b1; w_hit_way = '0; w_hit_way[wy] = 1'b1;
            end
        end
        // victim: first invalid enabled way, else the oldest (max age).
        w_victim_way = '0;
        begin
            automatic int best = -1;
            automatic logic [1:0] best_age = '0;
            for (int wy = WAYS - 1; wy >= 0; wy--) begin
                if (w_way_mask[wy] && !r_valid[w_idx][wy]) best = wy;
            end
            if (best < 0) begin
                for (int wy = 0; wy < WAYS; wy++) begin
                    if (w_way_mask[wy] && r_lru[w_idx][wy] >= best_age) begin
                        best_age = r_lru[w_idx][wy]; best = wy;
                    end
                end
            end
            if (best >= 0) w_victim_way[best] = 1'b1;
        end
    end

    logic [CTRW-1:0] w_hit_cnt, w_cnt_next;
    always_comb begin
        w_hit_cnt = '0;
        for (int wy = 0; wy < WAYS; wy++)
            if (w_hit_way[wy]) w_hit_cnt = r_cnt[w_idx][wy];
        // fresh entry: this ACT is its first miss; hit: saturating increment.
        w_cnt_next = !w_hit       ? CTRW'(1)
                   : (&w_hit_cnt) ? w_hit_cnt
                                  : w_hit_cnt + CTRW'(1);
    end

    // ---- epoch + hill-climb state ------------------------------------------
    logic [15:0] r_epoch_cnt;
    logic        w_epoch_tick;
    assign w_epoch_tick = (reset_interval_i != 0)
                       && (r_epoch_cnt >= reset_interval_i);

    // Page-quality observation for the hill-climb: hits (columns) vs misses
    // (ACTs) this epoch. Compared as hit fraction via cross-multiplication to
    // stay divider-free: quality improved iff
    //   hits_now * total_prev >= hits_prev * total_now.
    logic [15:0] r_ep_hits, r_ep_acts;
    logic [15:0] r_pv_hits, r_pv_total;
    logic        r_dir_up;               // current hill-climb direction

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_valid <= '0; r_tag <= '0; r_cnt <= '0; r_lru <= '0;
            low_locality_o <= '0;
            r_thresh    <= 8'd2;
            r_epoch_cnt <= '0;
            r_ep_hits <= '0; r_ep_acts <= '0;
            r_pv_hits <= '0; r_pv_total <= '0;
            r_dir_up  <= 1'b0;           // first move: tighten (lower thresh)
        end else if (!enable_i) begin
            // Disabled: drop all state so a re-enable starts clean, and the
            // mask releases immediately (mode switch back to open/legacy).
            r_valid <= '0; r_cnt <= '0; r_lru <= '0;
            low_locality_o <= '0;
            r_thresh    <= (miss_thresh_i != 0) ? miss_thresh_i : 8'd2;
            r_epoch_cnt <= '0;
            r_ep_hits <= '0; r_ep_acts <= '0;
            r_pv_hits <= '0; r_pv_total <= '0;
        end else begin
            // ---- table update + verdict latch on ACT ----
            if (w_is_act) begin
                for (int wy = 0; wy < WAYS; wy++) begin
                    if ((w_hit ? w_hit_way[wy] : w_victim_way[wy])) begin
                        r_valid[w_idx][wy] <= 1'b1;
                        r_tag[w_idx][wy]   <= cmd_row_i;
                        r_cnt[w_idx][wy]   <= w_cnt_next;
                        r_lru[w_idx][wy]   <= '0;
                    end else if (w_way_mask[wy] && r_valid[w_idx][wy]
                                 && !(&r_lru[w_idx][wy])) begin
                        r_lru[w_idx][wy] <= r_lru[w_idx][wy] + 2'd1;
                    end
                end
                low_locality_o[cmd_bank_i] <=
                    ({4'h0, w_cnt_next} > w_thresh_eff);
                if (!(&r_ep_acts)) r_ep_acts <= r_ep_acts + 16'd1;
            end
            if (cmd_valid_i && is_column_op(cmd_op_i) && !(&r_ep_hits))
                r_ep_hits <= r_ep_hits + 16'd1;

            // ---- epoch: counter clear + optional threshold hill-climb ----
            if (w_epoch_tick) begin
                r_epoch_cnt <= '0;
                r_cnt <= '0;                       // evidence re-accumulates
                if (dyn_en_i) begin
                    automatic logic [15:0] total_now =
                        r_ep_hits + r_ep_acts;
                    automatic logic worse =
                        ({16'h0, r_ep_hits} * {16'h0, r_pv_total})
                      < ({16'h0, r_pv_hits} * {16'h0, total_now});
                    automatic logic dir = worse ? !r_dir_up : r_dir_up;
                    r_dir_up <= dir;
                    if (dir  && r_thresh != 8'hFF) r_thresh <= r_thresh + 8'd1;
                    if (!dir && r_thresh >  8'd1)  r_thresh <= r_thresh - 8'd1;
                    r_pv_hits  <= r_ep_hits;
                    r_pv_total <= total_now;
                end
                r_ep_hits <= '0; r_ep_acts <= '0;
            end else if (reset_interval_i != 0) begin
                r_epoch_cnt <= r_epoch_cnt + 16'd1;
            end
        end
    end)

endmodule : pumice_rbl_table
