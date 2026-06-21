// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: dfi_v21_interface_macro
// Purpose: "Translate internal control + data into DFI v2.1 wires."
//          The single layer in the controller core that owns the JEDEC
//          truth tables for DDR2/LPDDR2 commands and the multi-phase
//          pack. Swap THIS macro when moving to DFI v3 / v4 / v5 / v6
//          for newer DRAM generations.
//
// Bundles: dfi_cmd_formatter + dfi_signal_pack.
//
// Multi-phase output widths:
//   For DFI_RATE = N, every DFI control bus output is widened to
//   per-phase × N (DFI_*_WIDTH * DFI_RATE). v1 uses phase 0 for the
//   issued command; phases 1..N-1 emit NOP. The scheduler may later
//   provide multiple commands per cycle.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module dfi_v21_interface_macro
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DFI_RATE        = 2,
    parameter int DFI_ADDR_WIDTH  = 14,
    parameter int DFI_BANK_WIDTH  = 3,
    parameter int DFI_CTRL_WIDTH  = 1,
    parameter int DFI_CS_WIDTH    = NUM_RANKS,
    parameter int DFI_ADDR_BUS_W  = DFI_ADDR_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W  = DFI_BANK_WIDTH * DFI_RATE,
    parameter int DFI_CTRL_BUS_W  = DFI_CTRL_WIDTH * DFI_RATE,
    parameter int DFI_CS_BUS_W    = DFI_CS_WIDTH * DFI_RATE,
    parameter int DFI_DATA_WIDTH  = 64,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH    = 1,

    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH
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
    input  logic [RW-1:0]                 cmd_row_i,
    input  logic [CW-1:0]                 cmd_col_i,
    input  logic [BLW-1:0]                cmd_len_i,

    // ----- pre-pack data from data_path_macro -----
    input  logic [DFI_DATA_WIDTH-1:0]     pre_dfi_wrdata_i,
    input  logic [DFI_EN_WIDTH-1:0]       pre_dfi_wrdata_en_i,
    input  logic [DFI_STRB_WIDTH-1:0]     pre_dfi_wrdata_mask_i,
    input  logic [DFI_EN_WIDTH-1:0]       pre_dfi_rddata_en_i,

    // ----- per-rank CKE from powerdown_ctrl (replicated across phases) -----
    input  logic [DFI_CS_WIDTH-1:0]       pre_dfi_cke_i,

    // ----- DFI v2.1 control bus (multi-phase) -----
    output logic [DFI_ADDR_BUS_W-1:0]     dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]     dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_cke_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_odt_o,

    // ----- DFI Write Data Interface -----
    output logic [DFI_DATA_WIDTH-1:0]     dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]       dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]     dfi_wrdata_mask_o,

    // ----- DFI Read Data Enable -----
    output logic [DFI_EN_WIDTH-1:0]       dfi_rddata_en_o,

    // ----- DFI Status -----
    output logic [DFI_CS_BUS_W-1:0]       dfi_dram_clk_disable_o
);

    //=========================================================================
    // Pre-pack nets from cmd_formatter → signal_pack
    //=========================================================================
    logic [DFI_ADDR_BUS_W-1:0]  pre_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]  pre_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]  pre_dfi_cas_n;
    logic [DFI_CTRL_BUS_W-1:0]  pre_dfi_ras_n;
    logic [DFI_CTRL_BUS_W-1:0]  pre_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]    pre_dfi_cs_n;
    logic [DFI_CS_BUS_W-1:0]    pre_dfi_odt;

    //=========================================================================
    // Replicate per-rank CKE across DFI_RATE phases (CKE is the same
    // value for every phase within a DFI cycle — sub-cycle CKE control
    // is a TODO if a future PHY ever needs it).
    //=========================================================================
    logic [DFI_CS_BUS_W-1:0]    pre_dfi_cke_multi;
    always_comb begin
        for (int unsigned p = 0; p < DFI_RATE; p++) begin
            pre_dfi_cke_multi[p*DFI_CS_WIDTH +: DFI_CS_WIDTH] = pre_dfi_cke_i;
        end
    end

    //=========================================================================
    // FUBs
    //=========================================================================

    dfi_cmd_formatter #(
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (RW),
        .COL_WIDTH       (CW),
        .BURST_LEN_WIDTH (BLW),
        .DFI_RATE        (DFI_RATE),
        .DFI_ADDR_WIDTH  (DFI_ADDR_WIDTH),
        .DFI_BANK_WIDTH  (DFI_BANK_WIDTH),
        .DFI_CTRL_WIDTH  (DFI_CTRL_WIDTH),
        .DFI_CS_WIDTH    (DFI_CS_WIDTH)
    ) u_dfi_cmd_formatter (
        .mc_clk        (mc_clk),
        .mc_rst_n      (mc_rst_n),
        .memtype_i     (memtype_i),
        .cmd_valid_i   (cmd_valid_i),
        .cmd_ready_o   (cmd_ready_o),
        .cmd_op_i      (cmd_op_i),
        .cmd_rank_i    (cmd_rank_i),
        .cmd_bank_i    (cmd_bank_i),
        .cmd_row_i     (cmd_row_i),
        .cmd_col_i     (cmd_col_i),
        .cmd_len_i     (cmd_len_i),
        .dfi_address_o (pre_dfi_address),
        .dfi_bank_o    (pre_dfi_bank),
        .dfi_cas_n_o   (pre_dfi_cas_n),
        .dfi_ras_n_o   (pre_dfi_ras_n),
        .dfi_we_n_o    (pre_dfi_we_n),
        .dfi_cs_n_o    (pre_dfi_cs_n),
        .dfi_odt_o     (pre_dfi_odt)
    );

    dfi_signal_pack #(
        .NUM_RANKS       (NUM_RANKS),
        .DFI_RATE        (DFI_RATE),
        .DFI_ADDR_WIDTH  (DFI_ADDR_WIDTH),
        .DFI_BANK_WIDTH  (DFI_BANK_WIDTH),
        .DFI_CTRL_WIDTH  (DFI_CTRL_WIDTH),
        .DFI_CS_WIDTH    (DFI_CS_WIDTH),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DFI_STRB_WIDTH  (DFI_STRB_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH)
    ) u_dfi_signal_pack (
        .mc_clk                 (mc_clk),
        .mc_rst_n               (mc_rst_n),
        .i_address              (pre_dfi_address),
        .i_bank                 (pre_dfi_bank),
        .i_cas_n                (pre_dfi_cas_n),
        .i_ras_n                (pre_dfi_ras_n),
        .i_we_n                 (pre_dfi_we_n),
        .i_cs_n                 (pre_dfi_cs_n),
        .i_cke                  (pre_dfi_cke_multi),
        .i_odt                  (pre_dfi_odt),
        .i_wrdata               (pre_dfi_wrdata_i),
        .i_wrdata_en            (pre_dfi_wrdata_en_i),
        .i_wrdata_mask          (pre_dfi_wrdata_mask_i),
        .i_rddata_en            (pre_dfi_rddata_en_i),
        .dfi_address_o          (dfi_address_o),
        .dfi_bank_o             (dfi_bank_o),
        .dfi_cas_n_o            (dfi_cas_n_o),
        .dfi_ras_n_o            (dfi_ras_n_o),
        .dfi_we_n_o             (dfi_we_n_o),
        .dfi_cs_n_o             (dfi_cs_n_o),
        .dfi_cke_o              (dfi_cke_o),
        .dfi_odt_o              (dfi_odt_o),
        .dfi_wrdata_o           (dfi_wrdata_o),
        .dfi_wrdata_en_o        (dfi_wrdata_en_o),
        .dfi_wrdata_mask_o      (dfi_wrdata_mask_o),
        .dfi_rddata_en_o        (dfi_rddata_en_o),
        .dfi_dram_clk_disable_o (dfi_dram_clk_disable_o)
    );

endmodule : dfi_v21_interface_macro
