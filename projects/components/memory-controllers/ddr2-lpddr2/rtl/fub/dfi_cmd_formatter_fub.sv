// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: dfi_cmd_formatter_fub
// Purpose: SKELETON — translates the scheduler's chosen `dram_op_e`
//          plus (rank, bank, row/col) into the DFI v2.1 control bus:
//          {dfi_cas_n, dfi_ras_n, dfi_we_n, dfi_bank, dfi_address,
//          dfi_cs_n, dfi_odt} per JEDEC truth table for DDR2/LPDDR2.
//
// Status:  Port-list only. Idles DFI control signals.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module dfi_cmd_formatter_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DFI_ADDR_WIDTH  = 14,
    parameter int DFI_BANK_WIDTH  = 3,
    parameter int DFI_CTRL_WIDTH  = 1,
    parameter int DFI_CS_WIDTH    = NUM_RANKS,

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,

    input  memtype_e                      memtype_i,

    // ----- chosen op from scheduler -----
    input  logic                          cmd_valid_i,
    output logic                          cmd_ready_o,
    input  dram_op_e                      cmd_op_i,
    input  logic [RKW-1:0]                cmd_rank_i,
    input  logic [BKW-1:0]                cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]          cmd_row_i,
    input  logic [COL_WIDTH-1:0]          cmd_col_i,
    input  logic [BURST_LEN_WIDTH-1:0]    cmd_len_i,

    // ----- DFI control bus -----
    output logic [DFI_ADDR_WIDTH-1:0]     dfi_address_o,
    output logic [DFI_BANK_WIDTH-1:0]     dfi_bank_o,
    output logic [DFI_CTRL_WIDTH-1:0]     dfi_cas_n_o,
    output logic [DFI_CTRL_WIDTH-1:0]     dfi_ras_n_o,
    output logic [DFI_CTRL_WIDTH-1:0]     dfi_we_n_o,
    output logic [DFI_CS_WIDTH-1:0]       dfi_cs_n_o,
    output logic [DFI_CS_WIDTH-1:0]       dfi_odt_o
);

    // -- TODO: implementation --
    assign cmd_ready_o   = 1'b1;
    assign dfi_address_o = '0;
    assign dfi_bank_o    = '0;
    assign dfi_cas_n_o   = '1;   // NOP = all control bits high
    assign dfi_ras_n_o   = '1;
    assign dfi_we_n_o    = '1;
    assign dfi_cs_n_o    = '1;   // deselected
    assign dfi_odt_o     = '0;

    wire unused = |{ mc_clk, mc_rst_n, memtype_i,
                     cmd_valid_i, cmd_op_i,
                     cmd_rank_i, cmd_bank_i, cmd_row_i, cmd_col_i, cmd_len_i };

endmodule : dfi_cmd_formatter_fub
