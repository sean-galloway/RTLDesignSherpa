// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: global_timers_fub
// Purpose: SKELETON — controller-wide constraint trackers that span banks.
//          tFAW (max 4 ACTs in window), tRRD (ACT-to-ACT spacing),
//          tWTR (write→read turnaround at controller level), tRTW.
//
// Status:  Port-list only. All windows return "open" forever.

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
    input  logic [RKW-1:0]             evt_act_rank_i,
    input  logic                       evt_rd_i,
    input  logic                       evt_wr_i,

    // ----- readiness back to scheduler -----
    output logic                       tfaw_window_ok_o,
    output logic                       trrd_window_ok_o,
    output logic                       twtr_global_ok_o,
    output logic                       trtw_window_ok_o
);

    // -- TODO: implementation --
    assign tfaw_window_ok_o = 1'b1;
    assign trrd_window_ok_o = 1'b1;
    assign twtr_global_ok_o = 1'b1;
    assign trtw_window_ok_o = 1'b1;

    wire unused = |{ mc_clk, mc_rst_n,
                     t_faw_i, t_rrd_i, t_wtr_global_i, t_rtw_i,
                     evt_act_i, evt_act_rank_i, evt_rd_i, evt_wr_i };

endmodule : global_timers_fub
