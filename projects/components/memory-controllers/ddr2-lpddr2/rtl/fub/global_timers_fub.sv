// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: global_timers_fub
// Purpose: Controller-wide constraint trackers that span banks.
//
//          * tFAW — at most 4 ACT commands within a t_faw_i window.
//            Tracked via a 4-deep sliding window of countdown timers:
//            on each ACT, kick out the oldest slot and reload it
//            with t_faw_i. The window is "open" (tfaw_window_ok=1)
//            as long as at least one of the four slots is at 0.
//
//          * tRRD — minimum cycles between any two ACTs.
//            Single countdown timer reloaded on each ACT.
//
//          * tWTR — cycles since last WR (any bank). Limits when
//            the controller can issue RD after a WR.
//          * tRTW — cycles since last RD. Limits when WR after RD.
//            Tracked as single countdowns; output _ok flags.
//
// v1 (TODO):
//   * Per-rank tFAW (multi-rank silicon enforces tFAW per rank).
//   * tCCD (CAS-to-CAS delay) is currently baked into burst-length
//     timing in the scheduler; a real impl would track here.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module global_timers_fub
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

    // ----- events -----
    input  logic                       evt_act_i,
    input  logic [RKW-1:0]             evt_act_rank_i,    // v1: ignored
    input  logic                       evt_rd_i,
    input  logic                       evt_wr_i,

    // ----- readiness back to scheduler -----
    output logic                       tfaw_window_ok_o,
    output logic                       trrd_window_ok_o,
    output logic                       twtr_global_ok_o,
    output logic                       trtw_window_ok_o
);

    //=========================================================================
    // tFAW: 4-deep sliding window of countdowns
    //=========================================================================
    logic [3:0][7:0] r_faw_slots;

    //=========================================================================
    // Single-counter windows
    //=========================================================================
    logic [7:0] r_trrd_cnt;
    logic [7:0] r_twtr_cnt;
    logic [7:0] r_trtw_cnt;

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_faw_slots <= '0;
            r_trrd_cnt  <= 8'd0;
            r_twtr_cnt  <= 8'd0;
            r_trtw_cnt  <= 8'd0;
        end else begin
            // Decrement counters (saturate at 0).
            for (int unsigned i = 0; i < 4; i++) begin
                if (r_faw_slots[i] > 8'd0) r_faw_slots[i] <= r_faw_slots[i] - 8'd1;
            end
            if (r_trrd_cnt > 8'd0) r_trrd_cnt <= r_trrd_cnt - 8'd1;
            if (r_twtr_cnt > 8'd0) r_twtr_cnt <= r_twtr_cnt - 8'd1;
            if (r_trtw_cnt > 8'd0) r_trtw_cnt <= r_trtw_cnt - 8'd1;

            // ACT event: install t_faw_i into the slot with the smallest
            // remaining count (== 0 if window is open); reload tRRD.
            if (evt_act_i) begin
                automatic int unsigned slot_pick = 0;
                automatic logic [7:0] slot_min = 8'hFF;
                for (int unsigned i = 0; i < 4; i++) begin
                    if (r_faw_slots[i] < slot_min) begin
                        slot_min  = r_faw_slots[i];
                        slot_pick = i;
                    end
                end
                r_faw_slots[slot_pick] <= t_faw_i;
                r_trrd_cnt <= t_rrd_i;
            end
            // WR event: reload tWTR (used by next RD).
            if (evt_wr_i) begin
                r_twtr_cnt <= t_wtr_global_i;
            end
            // RD event: reload tRTW (used by next WR).
            if (evt_rd_i) begin
                r_trtw_cnt <= t_rtw_i;
            end
        end
    end)

    // tFAW is OK when at least one of the 4 slots is at 0
    //   (= fewer than 4 ACTs are "live" in the window).
    always_comb begin
        tfaw_window_ok_o = 1'b0;
        for (int unsigned i = 0; i < 4; i++) begin
            if (r_faw_slots[i] == 8'd0) tfaw_window_ok_o = 1'b1;
        end
    end

    assign trrd_window_ok_o = (r_trrd_cnt == 8'd0);
    assign twtr_global_ok_o = (r_twtr_cnt == 8'd0);
    assign trtw_window_ok_o = (r_trtw_cnt == 8'd0);

    wire unused_v1 = |{ evt_act_rank_i };

endmodule : global_timers_fub
