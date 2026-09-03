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

    // Runtime shape, clamped into the build caps (0 = "cap" = build default).
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

    // ---- table state (flops; 4x16 = 64 entries at the caps) ----------------
    logic [SETS-1:0][WAYS-1:0]                 r_valid;
    logic [SETS-1:0][WAYS-1:0][ROW_WIDTH-1:0]  r_tag;
    logic [SETS-1:0][WAYS-1:0][CTRW-1:0]       r_cnt;
    logic [SETS-1:0][WAYS-1:0][1:0]            r_lru;

    // Effective threshold (static or the adapting register).
    logic [7:0] r_thresh;
    logic [7:0] w_thresh_eff;
    assign w_thresh_eff = dyn_en_i ? r_thresh : miss_thresh_i;

    // ---- ACT decode + set index --------------------------------------------
    logic w_is_act;
    assign w_is_act = cmd_valid_i && (cmd_op_i == OP_ACT) && enable_i;
    logic [SETS_MAX_LOG2-1:0] w_idx;
    assign w_idx = cmd_row_i[SETS_MAX_LOG2-1:0] & w_set_mask;

    // ========================================================================
    // PIPELINE (PUMICE-017 depth). The single-cycle read-index -> hit/victim
    // scan -> read-modify-write of the set-associative table was ~69 mux-level
    // (it was 60% of the failing endpoints behind the flat arbiter). Split it:
    //   STAGE 0  latch the ACT context + the dynamic-indexed READ of the set,
    //   STAGE 1  compute hit/victim/counter from those small REGISTERED per-way
    //            arrays and write the table back + latch the verdict.
    // The verdict is consulted only at ACT time and is needed before the NEXT
    // ACT to that bank (>= tRC away), so the +1-cycle decision has ample slack.
    // Two ACTs to the SAME set on consecutive cycles can race (stage-1 write vs
    // the next stage-0 read); that costs only predictor ACCURACY (a lost
    // increment) -- aliasing is already accepted -- never correctness, and the
    // column path always reads the verdict flop.
    // ========================================================================
    logic                            r0_act;
    logic [BKW-1:0]                  r0_bank;
    logic [ROW_WIDTH-1:0]            r0_row;
    logic [SETS_MAX_LOG2-1:0]        r0_idx;
    logic [WAYS-1:0]                 r0_set_valid;
    logic [WAYS-1:0][ROW_WIDTH-1:0]  r0_set_tag;
    logic [WAYS-1:0][CTRW-1:0]       r0_set_cnt;
    logic [WAYS-1:0][1:0]            r0_set_lru;
    logic [WAYS-1:0]                 r0_way_mask;
    logic [7:0]                      r0_thresh;

    // ---- STAGE 1 combinational: hit / victim (LRU) / counter / next set ----
    // All inputs are the REGISTERED per-way snapshot r0_set_* (<= WAYS wide),
    // so every scan below is shallow. The writeback is a SINGLE whole-set store
    // (r_*[r0_idx] <= w1_n*) -- never a per-way dynamic-index write, which sv2v
    // unrolls into a serial chain of full-array demuxes.
    logic [WAYS-1:0] w1_en;              // enabled ways this set
    logic [WAYS-1:0] w1_hit_way, w1_inval;
    logic            w1_hit;
    always_comb begin
        for (int wy = 0; wy < WAYS; wy++) begin
            w1_en[wy]     = r0_way_mask[wy];
            w1_hit_way[wy] = r0_way_mask[wy] && r0_set_valid[wy]
                             && (r0_set_tag[wy] == r0_row);
            w1_inval[wy]  = r0_way_mask[wy] && !r0_set_valid[wy];
        end
        w1_hit = |w1_hit_way;
    end

    // victim one-hot: lowest-index invalid enabled way, else the max-age way.
    // Both selects are computed in PARALLEL (no serial argmax accumulator):
    //  - invalid priority: a way beats another invalid iff its index is lower;
    //  - max-age: a way "wins" iff no enabled way is strictly older and no
    //    lower-index enabled way ties. Each per-way flag is an AND-reduction of
    //    WAYS bounded 2-bit compares -> shallow, independent of the loop order.
    logic [WAYS-1:0] w1_inval_pri, w1_maxwin, w1_victim_way;
    always_comb begin
        for (int wy = 0; wy < WAYS; wy++) begin
            automatic logic inv_lo = w1_inval[wy];
            automatic logic age_hi = w1_en[wy];
            for (int wz = 0; wz < WAYS; wz++) begin
                if (wz < wy && w1_inval[wz])            inv_lo = 1'b0;
                if (w1_en[wz]
                    && (r0_set_lru[wz] > r0_set_lru[wy]
                        || (r0_set_lru[wz] == r0_set_lru[wy] && wz < wy)))
                    age_hi = 1'b0;
            end
            w1_inval_pri[wy] = w1_inval[wy] && inv_lo;
            w1_maxwin[wy]    = age_hi;
        end
        w1_victim_way = (|w1_inval) ? w1_inval_pri : w1_maxwin;
    end

    logic [CTRW-1:0] w1_hit_cnt, w1_cnt_next;
    always_comb begin
        w1_hit_cnt = '0;
        for (int wy = 0; wy < WAYS; wy++)
            if (w1_hit_way[wy]) w1_hit_cnt = r0_set_cnt[wy];
        w1_cnt_next = !w1_hit       ? CTRW'(1)
                    : (&w1_hit_cnt) ? w1_hit_cnt
                                    : w1_hit_cnt + CTRW'(1);
    end

    // whole-set next value (single dynamic-index store per array in stage 1)
    logic [WAYS-1:0]                 w1_nvalid;
    logic [WAYS-1:0][ROW_WIDTH-1:0]  w1_ntag;
    logic [WAYS-1:0][CTRW-1:0]       w1_ncnt;
    logic [WAYS-1:0][1:0]            w1_nlru;
    always_comb begin
        w1_nvalid = r0_set_valid;
        w1_ntag   = r0_set_tag;
        w1_ncnt   = r0_set_cnt;
        w1_nlru   = r0_set_lru;
        for (int wy = 0; wy < WAYS; wy++) begin
            if (w1_hit ? w1_hit_way[wy] : w1_victim_way[wy]) begin
                w1_nvalid[wy] = 1'b1;
                w1_ntag[wy]   = r0_row;
                w1_ncnt[wy]   = w1_cnt_next;
                w1_nlru[wy]   = 2'd0;
            end else if (r0_way_mask[wy] && r0_set_valid[wy]
                         && !(&r0_set_lru[wy])) begin
                w1_nlru[wy] = r0_set_lru[wy] + 2'd1;
            end
        end
    end

    // ---- epoch + hill-climb state (shallow; left single-cycle) -------------
    logic [15:0] r_epoch_cnt;
    logic        w_epoch_tick;
    assign w_epoch_tick = (reset_interval_i != 0)
                       && (r_epoch_cnt >= reset_interval_i);
    logic [15:0] r_ep_hits, r_ep_acts;
    logic [15:0] r_pv_hits, r_pv_total;
    logic        r_dir_up;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_valid <= '0; r_tag <= '0; r_cnt <= '0; r_lru <= '0;
            low_locality_o <= '0;
            r_thresh    <= 8'd2;
            r_epoch_cnt <= '0;
            r_ep_hits <= '0; r_ep_acts <= '0;
            r_pv_hits <= '0; r_pv_total <= '0;
            r_dir_up  <= 1'b0;
            r0_act <= 1'b0; r0_bank <= '0; r0_row <= '0; r0_idx <= '0;
            r0_set_valid <= '0; r0_set_tag <= '0; r0_set_cnt <= '0;
            r0_set_lru <= '0; r0_way_mask <= '0; r0_thresh <= '0;
        end else if (!enable_i) begin
            // Disabled: drop table + release the mask; re-enable starts clean.
            r_valid <= '0; r_cnt <= '0; r_lru <= '0;
            low_locality_o <= '0;
            r_thresh    <= (miss_thresh_i != 0) ? miss_thresh_i : 8'd2;
            r_epoch_cnt <= '0;
            r_ep_hits <= '0; r_ep_acts <= '0;
            r_pv_hits <= '0; r_pv_total <= '0;
            r0_act <= 1'b0;
        end else begin
            // ==== STAGE 0: capture the ACT + read the target set ====
            r0_act       <= w_is_act;
            r0_bank      <= cmd_bank_i;
            r0_row       <= cmd_row_i;
            r0_idx       <= w_idx;
            r0_set_valid <= r_valid[w_idx];
            r0_set_tag   <= r_tag[w_idx];
            r0_set_cnt   <= r_cnt[w_idx];
            r0_set_lru   <= r_lru[w_idx];
            r0_way_mask  <= w_way_mask;
            r0_thresh    <= w_thresh_eff;

            // ==== STAGE 1: single whole-set writeback + verdict ====
            if (r0_act) begin
                r_valid[r0_idx] <= w1_nvalid;
                r_tag[r0_idx]   <= w1_ntag;
                r_cnt[r0_idx]   <= w1_ncnt;
                r_lru[r0_idx]   <= w1_nlru;
                low_locality_o[r0_bank] <= ({4'h0, w1_cnt_next} > r0_thresh);
            end

            // ---- epoch accounting on the incoming stream ----
            if (w_is_act && !(&r_ep_acts)) r_ep_acts <= r_ep_acts + 16'd1;
            if (cmd_valid_i && is_column_op(cmd_op_i) && !(&r_ep_hits))
                r_ep_hits <= r_ep_hits + 16'd1;

            // ---- epoch: counter clear + optional threshold hill-climb ----
            // (the whole-table clear overrides any stage-1 r_cnt writeback this
            //  cycle -- epoch wins, which is the intended priority.)
            if (w_epoch_tick) begin
                r_epoch_cnt <= '0;
                r_cnt <= '0;
                if (dyn_en_i) begin
                    automatic logic [15:0] total_now = r_ep_hits + r_ep_acts;
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
