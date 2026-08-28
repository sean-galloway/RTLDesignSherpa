// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_bank_timers
// Purpose: Per-(rank,bank) JEDEC "safe" timing for the command scheduler. Thin
//          aggregator: it stamps ONE `bank_timer` per (rank,bank) and fans the
//          scheduler's command-event strobes (evt_*) to the addressed instance
//          as preset strobes. Each bank_timer is FSM-free (preset/decrement
//          countdown timers + a row-open register); the per-command `safe_*`
//          are combinational off those single-stage timers, so the readiness the
//          arbiter reads reflects the just-issued command one cycle later with no
//          multi-stage lag. (The old design double-registered readiness behind a
//          3-state FSM, which let REF/columns slip into stale bank state.)
//
//          tCCD/tWTR/tRTW/tFAW/tRRD turnaround stays global (pumice_global_timers),
//          ANDed by the arbiter. Auto-precharge (RDA/WRA) is handled inside
//          bank_timer via a single r_ap_pending bit.
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md (scheduler layer)
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_bank_timers
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                       aclk,
    input  logic                       aresetn,

    input  logic [7:0]                 t_rcd_i,
    input  logic [7:0]                 t_rp_i,
    input  logic [7:0]                 t_ras_i,
    input  logic [7:0]                 t_rc_i,
    input  logic [7:0]                 t_wr_i,    // WR cmd -> earliest PRE (incl WL+BL/2)
    input  logic [7:0]                 t_rtp_i,   // RD cmd -> earliest PRE

    // ----- bank-event strobes from the arbiter -----
    input  logic                       evt_act_i,
    input  logic                       evt_rd_i,
    input  logic                       evt_wr_i,
    input  logic                       evt_pre_i,
    input  logic                       evt_ap_i,   // auto-precharge (with RD/WR)
    input  logic [RKW-1:0]             evt_rank_i,
    input  logic [BKW-1:0]             evt_bank_i,
    input  logic [ROW_WIDTH-1:0]       evt_row_i,

    // ----- per-bank readiness to the arbiter (combinational, single-stage) -----
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_o,
    output bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]          bank_state_o,

    // ----- observability -----
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_act_cnt_nz_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_preblk_nz_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_ras_nz_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 obs_ap_pending_o
);

    for (genvar k = 0; k < NUM_RANKS; k++) begin : g_rank
        for (genvar b = 0; b < NUM_BANKS; b++) begin : g_bank
            // route the scheduler's command event to THIS bank only
            logic w_sel;
            assign w_sel = (evt_rank_i == RKW'(k)) && (evt_bank_i == BKW'(b));

            bank_timer #(.ROW_WIDTH(ROW_WIDTH)) u_bt (
                .clk             (aclk),
                .rst_n           (aresetn),
                .t_rcd_i         (t_rcd_i),
                .t_rp_i          (t_rp_i),
                .t_ras_i         (t_ras_i),
                .t_rc_i          (t_rc_i),
                .t_wr_i          (t_wr_i),
                .t_rtp_i         (t_rtp_i),
                .set_act_i       (evt_act_i && w_sel),
                .set_rd_i        (evt_rd_i  && w_sel),
                .set_wr_i        (evt_wr_i  && w_sel),
                .set_pre_i       (evt_pre_i && w_sel),
                .set_ap_i        (evt_ap_i),
                .row_i           (evt_row_i),
                .safe_act_o      (bank_act_ready_o [k][b]),
                .safe_rd_o       (bank_rdwr_ready_o[k][b]),
                .safe_wr_o       (/* == safe_rd */),
                .safe_pre_o      (bank_pre_ready_o [k][b]),
                .row_valid_o     (bank_row_active_o[k][b]),
                .open_row_o      (bank_open_row_o  [k][b]),
                .state_o         (bank_state_o     [k][b]),
                .obs_rcd_nz_o    (obs_act_cnt_nz_o[k][b]),
                .obs_preblk_nz_o (obs_preblk_nz_o [k][b]),
                .obs_ras_nz_o    (obs_ras_nz_o    [k][b]),
                .obs_ap_pending_o(obs_ap_pending_o[k][b])
            );
        end
    end

endmodule : pumice_bank_timers
