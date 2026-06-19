// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: scheduler_fub
// Purpose: SKELETON — picks the next memory op from the wr/rd CAM snapshots
//          subject to per-bank/per-rank/global timer readiness and
//          refresh/init/MR injection. Drives the (rank,bank,row) query
//          into the axi_frontend CAMs and emits the chosen op into the
//          cmd-formatter via a simple ready/valid channel.
//
// Status:  Port-list only. Body returns NOP forever.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module scheduler_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH    = 16,
    parameter int RD_CAM_DEPTH    = 16,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int AXI_ID_WIDTH    = 4,

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- CAM query (drive into axi_frontend_macro) -----
    output logic [RKW-1:0]             q_rank_o,
    output logic [BKW-1:0]             q_bank_o,
    output logic [ROW_WIDTH-1:0]       q_row_o,

    // ----- CAM match vectors -----
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_pending_i,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_rowhit_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_pending_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_rowhit_i,

    // ----- per-slot metadata snapshots (col / len for issue) -----
    input  logic [WR_CAM_DEPTH-1:0][COL_WIDTH-1:0]       wr_snap_col_i,
    input  logic [WR_CAM_DEPTH-1:0][BURST_LEN_WIDTH-1:0] wr_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][COL_WIDTH-1:0]       rd_snap_col_i,
    input  logic [RD_CAM_DEPTH-1:0][BURST_LEN_WIDTH-1:0] rd_snap_len_i,

    // ----- mark-issued strobes back to CAMs -----
    output logic                       wr_issued_we_o,
    output logic [WSL-1:0]             wr_issued_slot_o,
    output logic                       rd_issued_we_o,
    output logic [RSL-1:0]             rd_issued_slot_o,

    // ----- timer readiness from xbank_timers / global_timers -----
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0] bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] bank_open_row_i,
    input  logic                       tfaw_window_ok_i,

    // ----- refresh / power injection from refresh_ctrl / powerdown_ctrl -----
    input  logic                       refresh_req_i,
    output logic                       refresh_grant_o,
    input  logic                       pdn_req_i,
    output logic                       pdn_grant_o,

    // ----- init / mode-reg injection -----
    input  logic                       init_busy_i,        // ignore CAMs until clear
    input  logic                       mr_req_i,
    output logic                       mr_grant_o,

    // ----- chosen op into dfi_cmd_formatter -----
    output logic                       cmd_valid_o,
    input  logic                       cmd_ready_i,
    output dram_op_e                   cmd_op_o,
    output logic [RKW-1:0]             cmd_rank_o,
    output logic [BKW-1:0]             cmd_bank_o,
    output logic [ROW_WIDTH-1:0]       cmd_row_o,
    output logic [COL_WIDTH-1:0]       cmd_col_o,
    output logic [BURST_LEN_WIDTH-1:0] cmd_len_o,
    output logic [WSL-1:0]             cmd_wr_slot_o,   // valid when cmd_op_o is WR/WRA
    output logic [RSL-1:0]             cmd_rd_slot_o,   // valid when cmd_op_o is RD/RDA

    // ----- bank-event strobes to xbank_timers -----
    output logic                       evt_act_o,
    output logic                       evt_rd_o,
    output logic                       evt_wr_o,
    output logic                       evt_pre_o,
    output logic [RKW-1:0]             evt_rank_o,
    output logic [BKW-1:0]             evt_bank_o
);

    // -- TODO: implementation --
    // Default tie-offs so the macro elaborates clean.
    assign q_rank_o         = '0;
    assign q_bank_o         = '0;
    assign q_row_o          = '0;
    assign wr_issued_we_o   = 1'b0;
    assign wr_issued_slot_o = '0;
    assign rd_issued_we_o   = 1'b0;
    assign rd_issued_slot_o = '0;
    assign refresh_grant_o  = 1'b0;
    assign pdn_grant_o      = 1'b0;
    assign mr_grant_o       = 1'b0;
    assign cmd_valid_o      = 1'b0;
    assign cmd_op_o         = OP_NOP;
    assign cmd_rank_o       = '0;
    assign cmd_bank_o       = '0;
    assign cmd_row_o        = '0;
    assign cmd_col_o        = '0;
    assign cmd_len_o        = '0;
    assign cmd_wr_slot_o    = '0;
    assign cmd_rd_slot_o    = '0;
    assign evt_act_o        = 1'b0;
    assign evt_rd_o         = 1'b0;
    assign evt_wr_o         = 1'b0;
    assign evt_pre_o        = 1'b0;
    assign evt_rank_o       = '0;
    assign evt_bank_o       = '0;

    wire unused = |{ mc_clk, mc_rst_n,
                     wr_match_pending_i, wr_match_rowhit_i,
                     rd_match_pending_i, rd_match_rowhit_i,
                     wr_snap_col_i, wr_snap_len_i,
                     rd_snap_col_i, rd_snap_len_i,
                     bank_act_ready_i, bank_rdwr_ready_i, bank_pre_ready_i,
                     bank_row_active_i, bank_open_row_i, tfaw_window_ok_i,
                     refresh_req_i, pdn_req_i, init_busy_i, mr_req_i,
                     cmd_ready_i };

endmodule : scheduler_fub
