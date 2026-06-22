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
    import ddr2_lpddr2_pkg::*;
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
    //=========================================================================
    logic [NUM_RANKS-1:0][3:0][7:0] r_faw_slots;
    logic [NUM_RANKS-1:0][7:0]      r_trrd_cnt;
    logic [7:0] r_twtr_cnt;
    logic [7:0] r_trtw_cnt;
    logic [7:0] r_tccd_cnt;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_faw_slots <= '0;
            r_trrd_cnt  <= '0;
            r_twtr_cnt  <= 8'd0;
            r_trtw_cnt  <= 8'd0;
            r_tccd_cnt  <= 8'd0;
        end else begin
            // Decrement counters (saturate at 0).
            for (int unsigned k = 0; k < NUM_RANKS; k++) begin
                for (int unsigned i = 0; i < 4; i++) begin
                    if (r_faw_slots[k][i] > 8'd0)
                        r_faw_slots[k][i] <= r_faw_slots[k][i] - 8'd1;
                end
                if (r_trrd_cnt[k] > 8'd0) r_trrd_cnt[k] <= r_trrd_cnt[k] - 8'd1;
            end
            if (r_twtr_cnt > 8'd0) r_twtr_cnt <= r_twtr_cnt - 8'd1;
            if (r_trtw_cnt > 8'd0) r_trtw_cnt <= r_trtw_cnt - 8'd1;
            if (r_tccd_cnt > 8'd0) r_tccd_cnt <= r_tccd_cnt - 8'd1;

            // ACT event: install t_faw_i into the slot with the smallest
            // remaining count for the targeted rank; reload that rank's tRRD.
            if (evt_act_i) begin
                automatic int unsigned slot_pick = 0;
                automatic logic [7:0] slot_min = 8'hFF;
                for (int unsigned i = 0; i < 4; i++) begin
                    if (r_faw_slots[evt_act_rank_i][i] < slot_min) begin
                        slot_min  = r_faw_slots[evt_act_rank_i][i];
                        slot_pick = i;
                    end
                end
                r_faw_slots[evt_act_rank_i][slot_pick] <= t_faw_i;
                r_trrd_cnt [evt_act_rank_i]            <= t_rrd_i;
            end
            // WR event: reload tWTR + tCCD.
            if (evt_wr_i) begin
                r_twtr_cnt <= t_wtr_global_i;
                r_tccd_cnt <= t_ccd_i;
            end
            // RD event: reload tRTW + tCCD.
            if (evt_rd_i) begin
                r_trtw_cnt <= t_rtw_i;
                r_tccd_cnt <= t_ccd_i;
            end
        end
    end)

    // Next-cycle window-ok values.
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
            tfaw_window_ok_o <= w_tfaw_ok;
            for (int unsigned k = 0; k < NUM_RANKS; k++) begin
                trrd_window_ok_o[k] <= (r_trrd_cnt[k] == 8'd0);
            end
            twtr_global_ok_o <= (r_twtr_cnt == 8'd0);
            trtw_window_ok_o <= (r_trtw_cnt == 8'd0);
            tccd_window_ok_o <= (r_tccd_cnt == 8'd0);
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
