// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: dfi_signal_pack_fub
// Purpose: SKELETON — final mux + register layer on the DFI bus. For
//          rate-2 DFI (one DFI cycle = 2 DRAM beats) it packs phase-0
//          and phase-1 commands/data into the wide DFI signals. Also
//          owns dfi_dram_clk_disable and dfi_reset_n (DDR3 only).
//
// Status:  Port-list only. Pass-through unchanged.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module dfi_signal_pack_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS       = 1,
    parameter int DFI_ADDR_WIDTH  = 14,
    parameter int DFI_BANK_WIDTH  = 3,
    parameter int DFI_CTRL_WIDTH  = 1,
    parameter int DFI_CS_WIDTH    = NUM_RANKS,
    parameter int DFI_DATA_WIDTH  = 64,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_VALID_WIDTH = 1,
    parameter int DFI_EN_WIDTH    = 1
) (
    input  logic                            mc_clk,
    input  logic                            mc_rst_n,

    // ----- pre-pack inputs from cmd_formatter / wr_beat / rd_cl -----
    input  logic [DFI_ADDR_WIDTH-1:0]       i_address,
    input  logic [DFI_BANK_WIDTH-1:0]       i_bank,
    input  logic [DFI_CTRL_WIDTH-1:0]       i_cas_n,
    input  logic [DFI_CTRL_WIDTH-1:0]       i_ras_n,
    input  logic [DFI_CTRL_WIDTH-1:0]       i_we_n,
    input  logic [DFI_CS_WIDTH-1:0]         i_cs_n,
    input  logic [DFI_CS_WIDTH-1:0]         i_cke,
    input  logic [DFI_CS_WIDTH-1:0]         i_odt,

    input  logic [DFI_DATA_WIDTH-1:0]       i_wrdata,
    input  logic [DFI_EN_WIDTH-1:0]         i_wrdata_en,
    input  logic [DFI_STRB_WIDTH-1:0]       i_wrdata_mask,
    input  logic [DFI_EN_WIDTH-1:0]         i_rddata_en,

    // ----- packed DFI bus to PHY -----
    output logic [DFI_ADDR_WIDTH-1:0]       dfi_address_o,
    output logic [DFI_BANK_WIDTH-1:0]       dfi_bank_o,
    output logic [DFI_CTRL_WIDTH-1:0]       dfi_cas_n_o,
    output logic [DFI_CTRL_WIDTH-1:0]       dfi_ras_n_o,
    output logic [DFI_CTRL_WIDTH-1:0]       dfi_we_n_o,
    output logic [DFI_CS_WIDTH-1:0]         dfi_cs_n_o,
    output logic [DFI_CS_WIDTH-1:0]         dfi_cke_o,
    output logic [DFI_CS_WIDTH-1:0]         dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]       dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]         dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]       dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]         dfi_rddata_en_o,
    output logic [DFI_CS_WIDTH-1:0]         dfi_dram_clk_disable_o
);

    // -- TODO: rate-2 packing. For now, pass through unchanged.
    assign dfi_address_o          = i_address;
    assign dfi_bank_o             = i_bank;
    assign dfi_cas_n_o            = i_cas_n;
    assign dfi_ras_n_o            = i_ras_n;
    assign dfi_we_n_o             = i_we_n;
    assign dfi_cs_n_o             = i_cs_n;
    assign dfi_cke_o              = i_cke;
    assign dfi_odt_o              = i_odt;
    assign dfi_wrdata_o           = i_wrdata;
    assign dfi_wrdata_en_o        = i_wrdata_en;
    assign dfi_wrdata_mask_o      = i_wrdata_mask;
    assign dfi_rddata_en_o        = i_rddata_en;
    assign dfi_dram_clk_disable_o = '0;

    wire unused = |{ mc_clk, mc_rst_n };

endmodule : dfi_signal_pack_fub
