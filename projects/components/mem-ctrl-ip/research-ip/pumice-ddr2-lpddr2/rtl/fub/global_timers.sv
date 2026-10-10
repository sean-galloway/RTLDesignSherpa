// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: global_timers
// Purpose: Controller-wide constraint trackers that span banks.
//
//          * tFAW — at most 4 ACT commands within a t_faw_i window.
//            Per-rank: each rank has its own 4-deep sliding window so
//            multi-rank silicon enforces the device-local thermal/power
//            limit independently. `tfaw_window_ok_o[r]` is high when
//            rank r has at least one tFAW slot at 0.
//
//          * tRRD — minimum cycles between any two ACTs (per rank).
//            Single countdown timer per rank reloaded on each ACT.
//
//          * tWTR — cycles since last WR (global, shared DQ bus).
//          * tRTW — cycles since last RD (global, shared DQ bus).
//          * tCCD — cycles since last column command (global, shared
//            DQ bus). Limits back-to-back RD/WR pacing across banks.
//
// v2 H — adds per-rank tFAW + tCCD tracking; tWTR / tRTW remain global
// because the DQ bus is shared across all ranks.
//
// Debug outputs (obs_*): expose all counter "non-zero" flags.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module global_timers
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    input  logic [7:0]                 t_faw_i,
    input  logic [7:0]                 t_rrd_i,
    input  logic [7:0]                 t_wtr_global_i,
    input  logic [7:0]                 t_rtw_i,
    input  logic [7:0]                 t_ccd_i,        // CAS-to-CAS

    // ----- events -----
    input  logic                       evt_act_i,
    input  logic [RKW-1:0]             evt_act_rank_i,
    input  logic                       evt_rd_i,
    input  logic                       evt_wr_i,

    // ----- readiness back to scheduler -----
    // Per-rank tFAW + tRRD; global tWTR / tRTW / tCCD.
    output logic [NUM_RANKS-1:0]       tfaw_window_ok_o,
    output logic [NUM_RANKS-1:0]       trrd_window_ok_o,
    output logic                       twtr_global_ok_o,
    output logic                       trtw_window_ok_o,
    output logic                       tccd_window_ok_o,

    // ----- observability -----
    output logic [NUM_RANKS-1:0]       obs_faw_nz_o,
    output logic [NUM_RANKS-1:0]       obs_trrd_nz_o,
    output logic                       obs_twtr_nz_o,
    output logic                       obs_trtw_nz_o,
    output logic                       obs_tccd_nz_o
);

    //=========================================================================
    // Per-rank tFAW: 4-deep sliding window of countdowns.
    // Per-rank tRRD: single countdown.
    // Global tWTR/tRTW/tCCD: single counters shared.
    //
    // ONE NEXT-STATE FUNCTION, TWO FLOPS -- and that is the whole point of the
    // structure below.
    //
    // The readiness outputs and the counters are BOTH registered, and both are
    // descriptions of the same next state. They used to be derived twice: the
    // counter flop sampled the next-state value, while the readiness flop
    // sampled `r_*_cnt == 0`, i.e. the state it was about to REPLACE. The gate
    // therefore stayed open for exactly one cycle after the command that should
    // have closed it:
    //
    //     t=2  evt_rd_i=1            -> reloads tCCD/tRTW on this edge
    //     t=3  tccd_window_ok_o = 1  -> flopped from the PRE-reload counter
    //     t=3  a column issues here  -> tCCD honoured as 1, whatever it was
    //     t=4  the flag finally drops
    //
    // Both consumers had to compensate. pumice_cmd_arbiter stopped using
    // `tccd_ok_i` for gating altogether in favour of a forward counter of its
    // own, and added `!(w_fire_out && r_do_rd)` terms to the turnarounds under a
    // comment headed "ONE-CYCLE BLIND SPOT (board round 2)" -- found on a board
    // ILA capture with a tRTW of 20 honoured as 1. tFAW and tRRD got no such
    // compensation and were simply exposed.
    //
    // Deriving the next state ONCE and feeding both flops from it removes the
    // class, not just the instances: there is no longer a second derivation to
    // fall out of step. Proved in formal/pumice/global_timers, whose
    // environment now assumes only what these outputs publish -- no
    // compensating term -- and still holds every JEDEC window.
    //=========================================================================
    logic [NUM_RANKS-1:0][3:0][7:0] r_faw_slots;
    logic [NUM_RANKS-1:0][7:0]      r_trrd_cnt;
    logic [7:0] r_twtr_cnt;
    logic [7:0] r_trtw_cnt;
    logic [7:0] r_tccd_cnt;

    // Which tFAW slot an ACT would claim: the one with the smallest remaining
    // count. A function of registers only, so it resolves early -- which the
    // readiness timing below depends on.
    logic [NUM_RANKS-1:0][1:0] w_slot_pick;
    always_comb begin
        automatic logic [7:0] slot_min;
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            slot_min       = 8'hFF;
            w_slot_pick[k] = 2'd0;
            for (int unsigned i = 0; i < 4; i++) begin
                if (r_faw_slots[k][i] < slot_min) begin
                    slot_min       = r_faw_slots[k][i];
                    w_slot_pick[k] = 2'(i);
                end
            end
        end
    end

    // Per-rank ACT strobe. Decoding the rank into a select, rather than using
    // it as an index, also means an out-of-range rank cannot address past the
    // arrays.
    logic [NUM_RANKS-1:0] w_act_rank;
    logic                 w_evt_col;
    always_comb begin
        for (int unsigned k = 0; k < NUM_RANKS; k++)
            w_act_rank[k] = evt_act_i && (RKW'(k) == evt_act_rank_i);
    end
    assign w_evt_col = evt_rd_i || evt_wr_i;

    //---- next state, computed once -------------------------------------------
    logic [NUM_RANKS-1:0][3:0][7:0] w_faw_nxt;
    logic [NUM_RANKS-1:0][7:0]      w_trrd_nxt;
    logic [7:0] w_twtr_nxt, w_trtw_nxt, w_tccd_nxt;

    always_comb begin
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            // every slot counts down and saturates at 0 ...
            for (int unsigned i = 0; i < 4; i++)
                w_faw_nxt[k][i] = (r_faw_slots[k][i] > 8'd0)
                                  ? r_faw_slots[k][i] - 8'd1 : 8'd0;
            // ... and an ACT installs t_faw_i into the slot it claims.
            if (w_act_rank[k]) w_faw_nxt[k][w_slot_pick[k]] = t_faw_i;

            w_trrd_nxt[k] = w_act_rank[k] ? t_rrd_i
                          : ((r_trrd_cnt[k] > 8'd0) ? r_trrd_cnt[k] - 8'd1 : 8'd0);
        end
        w_twtr_nxt = evt_wr_i  ? t_wtr_global_i
                   : ((r_twtr_cnt > 8'd0) ? r_twtr_cnt - 8'd1 : 8'd0);
        w_trtw_nxt = evt_rd_i  ? t_rtw_i
                   : ((r_trtw_cnt > 8'd0) ? r_trtw_cnt - 8'd1 : 8'd0);
        w_tccd_nxt = w_evt_col ? t_ccd_i
                   : ((r_tccd_cnt > 8'd0) ? r_tccd_cnt - 8'd1 : 8'd0);
    end

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_faw_slots <= '0;
            r_trrd_cnt  <= '0;
            r_twtr_cnt  <= 8'd0;
            r_trtw_cnt  <= 8'd0;
            r_tccd_cnt  <= 8'd0;
        end else begin
            r_faw_slots <= w_faw_nxt;
            r_trrd_cnt  <= w_trrd_nxt;
            r_twtr_cnt  <= w_twtr_nxt;
            r_trtw_cnt  <= w_trtw_nxt;
            r_tccd_cnt  <= w_tccd_nxt;
        end
    end)

    //---- next-cycle readiness, from that same next state ---------------------
    // TIMING. Each of these is written so the LATE signal -- evt_*, which comes
    // from the arbiter's command output -- drives only a ONE-BIT mux select,
    // with both arms comparisons of registers or of CSR constants that resolve
    // early. Testing `w_*_nxt == 0` directly would instead put the reload mux
    // and an 8-bit zero-compare in series after evt_*, on a path that feeds
    // straight back into the arbiter's own critical cone, on a design whose
    // board WNS is deliberately thin.
    //
    //     next(c) == 0   <=>   event ? (reload == 0) : (c <= 1)
    logic [NUM_RANKS-1:0] w_tfaw_ok_nxt, w_trrd_ok_nxt;
    logic w_twtr_ok_nxt, w_trtw_ok_nxt, w_tccd_ok_nxt;

    always_comb begin
        automatic logic any_free_all;      // some slot frees next cycle
        automatic logic any_free_other;    // ... one the ACT is not reloading
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            any_free_all   = 1'b0;
            any_free_other = 1'b0;
            for (int unsigned i = 0; i < 4; i++) begin
                if (r_faw_slots[k][i] <= 8'd1) begin
                    any_free_all = 1'b1;
                    if (2'(i) != w_slot_pick[k]) any_free_other = 1'b1;
                end
            end
            // On an ACT the claimed slot is about to hold t_faw_i, so it only
            // counts as free if tFAW is programmed to zero (disabled).
            w_tfaw_ok_nxt[k] = w_act_rank[k]
                             ? (any_free_other || (t_faw_i == 8'd0))
                             : any_free_all;
            w_trrd_ok_nxt[k] = w_act_rank[k] ? (t_rrd_i == 8'd0)
                                             : (r_trrd_cnt[k] <= 8'd1);
        end
        w_twtr_ok_nxt = evt_wr_i  ? (t_wtr_global_i == 8'd0) : (r_twtr_cnt <= 8'd1);
        w_trtw_ok_nxt = evt_rd_i  ? (t_rtw_i        == 8'd0) : (r_trtw_cnt <= 8'd1);
        w_tccd_ok_nxt = w_evt_col ? (t_ccd_i        == 8'd0) : (r_tccd_cnt <= 8'd1);
    end

    // CURRENT-state tFAW, for the obs_* debug view only. The gating outputs use
    // w_tfaw_ok_nxt above; these two are now aligned in the same cycle rather
    // than one apart, because the readiness flop no longer lags the state.
    logic [NUM_RANKS-1:0] w_tfaw_ok;
    always_comb begin
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            w_tfaw_ok[k] = 1'b0;
            for (int unsigned i = 0; i < 4; i++) begin
                if (r_faw_slots[k][i] == 8'd0) w_tfaw_ok[k] = 1'b1;
            end
        end
    end

    // Strict-flop outputs.
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            tfaw_window_ok_o <= '1;
            trrd_window_ok_o <= '1;
            twtr_global_ok_o <= 1'b1;
            trtw_window_ok_o <= 1'b1;
            tccd_window_ok_o <= 1'b1;
        end else begin
            // NEXT-state readiness, not current. See the long note at the
            // next-state block: sampling `r_*_cnt == 0` here is what left every
            // gate open for one cycle after the command that should close it.
            tfaw_window_ok_o <= w_tfaw_ok_nxt;
            trrd_window_ok_o <= w_trrd_ok_nxt;
            twtr_global_ok_o <= w_twtr_ok_nxt;
            trtw_window_ok_o <= w_trtw_ok_nxt;
            tccd_window_ok_o <= w_tccd_ok_nxt;
        end
    end)

    // obs_* — combinational.
    always_comb begin
        for (int unsigned k = 0; k < NUM_RANKS; k++) begin
            obs_faw_nz_o [k] = !w_tfaw_ok[k];
            obs_trrd_nz_o[k] = (r_trrd_cnt[k] != 8'd0);
        end
        obs_twtr_nz_o = (r_twtr_cnt != 8'd0);
        obs_trtw_nz_o = (r_trtw_cnt != 8'd0);
        obs_tccd_nz_o = (r_tccd_cnt != 8'd0);
    end

endmodule : global_timers
