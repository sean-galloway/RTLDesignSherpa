// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_bank_timers
// Purpose: Per-(rank,bank) JEDEC "safe" timing for the command scheduler. Thin
//
// Documentation:
//   projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried unchanged from scoria_bank_timers per andesite HAS ch02 (INHERITED).
// The only differences from the scoria source are the module name, the
// package import, and this header. Verification evidence transfers with
// scoria's suite (ported, not rewritten).
//
// Author: sean galloway
// Created: 2026-10-04 (carried)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_bank_timers
    import andesite_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int BANK_LA = 0   // advisory lookahead depth handed to scoria_bank_timer
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
    // advisory lookahead twins (see scoria_bank_timer.sv); BANK_LA=0 == the live set
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

    for (genvar k = 0; k < NUM_RANKS; k++) begin : g_rank
        for (genvar b = 0; b < NUM_BANKS; b++) begin : g_bank
            // route the scheduler's command event to THIS bank only
            logic w_sel;
            assign w_sel = (evt_rank_i == RKW'(k)) && (evt_bank_i == BKW'(b));

            andesite_bank_timer #(.ROW_WIDTH(ROW_WIDTH), .LA(BANK_LA)) u_bt (
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

endmodule : andesite_bank_timers
