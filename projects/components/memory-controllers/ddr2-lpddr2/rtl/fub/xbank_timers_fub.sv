// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: xbank_timers_fub
// Purpose: SKELETON — per-(rank,bank) JEDEC timing trackers (tRCD, tRP,
//          tRAS, tRC, tWR, tWTR, tRTP, tRRD-pair). Consumes bank-event
//          strobes from scheduler and exposes per-bank ready vectors.
//
// Status:  Port-list only. Ready vectors permanently asserted.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module xbank_timers_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- live timing constants (loaded by init_sequencer / MR) -----
    input  logic [7:0]                 t_rcd_i,
    input  logic [7:0]                 t_rp_i,
    input  logic [7:0]                 t_ras_i,
    input  logic [7:0]                 t_rc_i,
    input  logic [7:0]                 t_wr_i,
    input  logic [7:0]                 t_wtr_i,
    input  logic [7:0]                 t_rtp_i,

    // ----- bank-event strobes from scheduler -----
    input  logic                       evt_act_i,
    input  logic                       evt_rd_i,
    input  logic                       evt_wr_i,
    input  logic                       evt_pre_i,
    input  logic [RKW-1:0]             evt_rank_i,
    input  logic [BKW-1:0]             evt_bank_i,
    input  logic [ROW_WIDTH-1:0]       evt_row_i,    // for evt_act tracking

    // ----- per-bank readiness back to scheduler -----
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_act_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_rdwr_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_pre_ready_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                  bank_row_active_o,
    output logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]   bank_open_row_o,
    output bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]           bank_state_o
);

    // -- TODO: implementation --
    // Default tie-offs: everything ready, nothing active. Lets the
    // scheduler issue freely until timers are real.
    assign bank_act_ready_o   = '1;
    assign bank_rdwr_ready_o  = '1;
    assign bank_pre_ready_o   = '1;
    assign bank_row_active_o  = '0;
    assign bank_open_row_o    = '0;
    // BANK_IDLE == 3'h0; '0 broadcasts cleanly across the 2D array.
    assign bank_state_o       = '0;

    wire unused = |{ mc_clk, mc_rst_n,
                     t_rcd_i, t_rp_i, t_ras_i, t_rc_i,
                     t_wr_i, t_wtr_i, t_rtp_i,
                     evt_act_i, evt_rd_i, evt_wr_i, evt_pre_i,
                     evt_rank_i, evt_bank_i, evt_row_i };

endmodule : xbank_timers_fub
