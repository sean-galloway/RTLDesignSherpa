// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: wr_beat_sequencer_fub
// Purpose: SKELETON — given an issued WR/WRA op, pulls beats from the
//          axi_frontend w_buf (via beat_pull_strb_o/slot_o, reads
//          wbuf_ext_rd_data_i/strb_i) and drives dfi_wrdata /
//          dfi_wrdata_en / dfi_wrdata_mask with CWL alignment.
//          Emits b_complete_strb to the wr CAM when the write retires.
//
// Status:  Port-list only. Drives all DFI write outputs to idle.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module wr_beat_sequencer_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH    = 16,
    parameter int W_BUF_PTR_WIDTH = 7,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DFI_DATA_WIDTH  = 64,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH    = 1,

    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    input  logic [3:0]                 cwl_i,        // from mode_register

    // ----- write-op handshake from scheduler -----
    input  logic                       op_valid_i,
    output logic                       op_ready_o,
    input  logic [WSL-1:0]             op_slot_i,
    input  logic [BLW-1:0]             op_len_i,

    // ----- pull beats out of axi_frontend's w_buf -----
    output logic                       beat_pull_strb_o,
    output logic [WSL-1:0]             beat_pull_slot_o,
    input  logic [WPW-1:0]             beat_pull_ptr_i,
    input  logic [WPW-1:0]             beat_pull_strb_ptr_i,
    input  logic                       beat_pull_last_i,
    input  logic [DFI_DATA_WIDTH-1:0]  wbuf_rd_data_i,
    input  logic [DFI_STRB_WIDTH-1:0]  wbuf_rd_strb_i,

    // ----- DFI write data interface -----
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,

    // ----- b_complete back to wr CAM -----
    output logic                       b_complete_strb_o,
    output logic [WSL-1:0]             b_complete_slot_o
);

    // -- TODO: implementation --
    assign op_ready_o        = 1'b1;
    assign beat_pull_strb_o  = 1'b0;
    assign beat_pull_slot_o  = '0;
    assign dfi_wrdata_o      = '0;
    assign dfi_wrdata_en_o   = '0;
    assign dfi_wrdata_mask_o = '0;
    assign b_complete_strb_o = 1'b0;
    assign b_complete_slot_o = '0;

    wire unused = |{ mc_clk, mc_rst_n, cwl_i,
                     op_valid_i, op_slot_i, op_len_i,
                     beat_pull_ptr_i, beat_pull_strb_ptr_i, beat_pull_last_i,
                     wbuf_rd_data_i, wbuf_rd_strb_i };

endmodule : wr_beat_sequencer_fub
