// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_dfi_signal_pack
// Purpose: dfi_signal_pack
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_has/
//   ch03_architecture/01_deltas.md (the dormant disposition)
//
// Carried DORMANT from scoria_dfi_signal_pack per andesite HAS Ch 3.1: kept in the tree
// as the starting point for the waking condition named there (a board target
// or the LPDDR4 DSM work), uninstantiated until then. Differences from the
// scoria source: module name, package import, this header.
//
// Author: sean galloway
// Created: 2026-10-04 (carried dormant)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_dfi_signal_pack
    import andesite_pkg::*;
#(
    parameter int NUM_RANKS       = 1,
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
    parameter int DFI_EN_WIDTH    = 1
) (
    input  logic                            mc_clk,
    input  logic                            mc_rst_n,

    // ----- pre-pack inputs from cmd_formatter / data path -----
    input  logic [DFI_ADDR_BUS_W-1:0]       i_address,
    input  logic [DFI_BANK_BUS_W-1:0]       i_bank,
    input  logic [DFI_CTRL_BUS_W-1:0]       i_cas_n,
    input  logic [DFI_CTRL_BUS_W-1:0]       i_ras_n,
    input  logic [DFI_CTRL_BUS_W-1:0]       i_we_n,
    input  logic [DFI_CS_BUS_W-1:0]         i_cs_n,
    input  logic [DFI_CS_BUS_W-1:0]         i_cke,
    input  logic [DFI_CS_BUS_W-1:0]         i_odt,

    input  logic [DFI_DATA_WIDTH-1:0]       i_wrdata,
    input  logic [DFI_EN_WIDTH-1:0]         i_wrdata_en,
    input  logic [DFI_STRB_WIDTH-1:0]       i_wrdata_mask,
    input  logic [DFI_EN_WIDTH-1:0]         i_rddata_en,

    // ----- packed DFI bus to PHY -----
    output logic [DFI_ADDR_BUS_W-1:0]       dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]       dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]       dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]       dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]       dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]         dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]         dfi_cke_o,
    output logic [DFI_CS_BUS_W-1:0]         dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]       dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]         dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]       dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]         dfi_rddata_en_o,
    output logic [DFI_CS_BUS_W-1:0]         dfi_dram_clk_disable_o
);

    //=========================================================================
    // 1-cycle registered pipeline.
    //
    // Reset values are chosen so that during reset / before the scheduler
    // issues anything, the PHY sees a safe NOP:
    //   * cs_n=1 (all-deselected)
    //   * ras_n=cas_n=we_n=1 (NOP)
    //   * cke=0 (DRAM in CKE-low / self-refresh-ish state until init)
    //   * odt=0
    //   * wrdata_en / rddata_en = 0
    //   * wrdata_mask = 1 (don't write any bytes)
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            dfi_address_o          <= '0;
            dfi_bank_o             <= '0;
            dfi_cas_n_o            <= '1;
            dfi_ras_n_o            <= '1;
            dfi_we_n_o             <= '1;
            dfi_cs_n_o             <= '1;
            dfi_cke_o              <= '0;
            dfi_odt_o              <= '0;
            dfi_wrdata_o           <= '0;
            dfi_wrdata_en_o        <= '0;
            dfi_wrdata_mask_o      <= '1;
            dfi_rddata_en_o        <= '0;
            dfi_dram_clk_disable_o <= '0;
        end else begin
            dfi_address_o          <= i_address;
            dfi_bank_o             <= i_bank;
            dfi_cas_n_o            <= i_cas_n;
            dfi_ras_n_o            <= i_ras_n;
            dfi_we_n_o             <= i_we_n;
            dfi_cs_n_o             <= i_cs_n;
            dfi_cke_o              <= i_cke;
            dfi_odt_o              <= i_odt;
            dfi_wrdata_o           <= i_wrdata;
            dfi_wrdata_en_o        <= i_wrdata_en;
            dfi_wrdata_mask_o      <= i_wrdata_mask;
            dfi_rddata_en_o        <= i_rddata_en;
            dfi_dram_clk_disable_o <= '0;   // TODO: power-state machine
        end
    end)

endmodule : andesite_dfi_signal_pack
