// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_bank_timers
// Purpose: Per-(rank,bank) JEDEC "safe" timing for the command scheduler. Thin
//          aggregator: it stamps ONE `mc_bank_timer` per (rank,bank) and fans the
//          scheduler's command-event strobes (evt_*) to the addressed instance
//          as preset strobes. Each mc_bank_timer is FSM-free (preset/decrement
//          countdown timers + a row-open register); the per-command `safe_*`
//          are combinational off those single-stage timers, so the readiness the
//          arbiter reads reflects the just-issued command one cycle later with no
//          multi-stage lag. (The old design double-registered readiness behind a
//          3-state FSM, which let REF/columns slip into stale bank state.)
//
//          tCCD/tWTR/tRTW/tFAW/tRRD turnaround stays global (pumice_global_timers),
//          ANDed by the arbiter. Auto-precharge (RDA/WRA) is handled inside
//          mc_bank_timer via a single r_ap_pending bit.
//
// Documentation: docs/uarch/PUMICE_AXI4_IFC_UARCH.md (scheduler plane)
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_bank_timers
    import mc_common_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int BANK_LA = 0,  // advisory lookahead depth handed to mc_bank_timer
    // Per-bank timer width. The timing CSRs are 8 bits; a narrower timer saturates a
    // value above its range to the maximum it can hold (conservative, never unsafe).
    // DDR2 bank timings at <= 100 MHz fit in 5 bits (tRC 60 ns = 6 cycles).
    parameter int TW      = 8,
    parameter bit BANK_LA_AP = 1'b0, // extrapolate the AP self-close into safe_act_la (mc_bank_timer LA_AP)
    // 1 = each bank's counters load one register after the evt_* strobe
    // (mc_bank_timer SET_LAG): the fire cone drives one flop per bank here
    // and nothing behind it; the readiness outputs stay exact.
    parameter bit EVT_REG    = 1'b0
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
    // advisory lookahead twins (see mc_bank_timer.sv); BANK_LA=0 == the live set
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_la_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_la_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_la_o,

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

    // 8-bit CSR timings -> TW-bit timer loads, saturating (TW < 8 only)
    logic [TW-1:0] w_t_rcd, w_t_rp, w_t_ras, w_t_rc, w_t_wr, w_t_rtp;
    function automatic logic [TW-1:0] sat_tw(input logic [7:0] t);
        if (TW >= 8)        return TW'(t);
        else if (|(t >> TW)) return {TW{1'b1}};
        else                 return TW'(t);
    endfunction
    assign w_t_rcd = sat_tw(t_rcd_i);
    assign w_t_rp  = sat_tw(t_rp_i);
    assign w_t_ras = sat_tw(t_ras_i);
    assign w_t_rc  = sat_tw(t_rc_i);
    assign w_t_wr  = sat_tw(t_wr_i);
    assign w_t_rtp = sat_tw(t_rtp_i);

    for (genvar k = 0; k < NUM_RANKS; k++) begin : g_rank
        for (genvar b = 0; b < NUM_BANKS; b++) begin : g_bank
            // route the scheduler's command event to THIS bank only
            logic w_sel;
            assign w_sel = (evt_rank_i == RKW'(k)) && (evt_bank_i == BKW'(b));

            mc_bank_timer #(.ROW_WIDTH(ROW_WIDTH), .TW(TW), .LA(BANK_LA), .LA_AP(BANK_LA_AP),
                            .SET_LAG(EVT_REG)) u_bt (
                .clk             (aclk),
                .rst_n           (aresetn),
                .t_rcd_i         (w_t_rcd),
                .t_rp_i          (w_t_rp),
                .t_ras_i         (w_t_ras),
                .t_rc_i          (w_t_rc),
                .t_wr_i          (w_t_wr),
                .t_rtp_i         (w_t_rtp),
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
                .safe_act_la_o   (bank_act_ready_la_o [k][b]),
                .safe_rdwr_la_o  (bank_rdwr_ready_la_o[k][b]),
                .safe_pre_la_o   (bank_pre_ready_la_o [k][b]),
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

endmodule : mc_bank_timers
