// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_cdc_rd
// Purpose: AXI4 read channels (AR, R) carried across a clock-domain
//          boundary: s_axi on s_aclk, m_axi on m_aclk.
//
// Documentation: docs/markdown/rtl-amba/axi4/axi4_cdc.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-11
//
//==============================================================================
// Description:
//   The read half of axi4_cdc_wr: one gaxi_fifo_async for AR (requester ->
//   completer) and one for R (completer -> requester). In order per channel,
//   no protocol state. Both resets asserted together for a clean start; a
//   one-sided reset needs a quiesced bus (see axi4_cdc_wr, handbook
//   design/cdc.md).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   AXI_ID_WIDTH, AXI_ADDR_WIDTH, AXI_DATA_WIDTH, AXI_USER_WIDTH
//   CDC_DEPTH, USE_JOHNSON (0 = Gray, hoisted), N_FLOP_CROSS
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_axi4_cdc.py
//==============================================================================

`timescale 1ns / 1ps

`include "fifo_defs.svh"

module axi4_cdc_rd #(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    parameter int CDC_DEPTH      = 8,
    parameter int USE_JOHNSON    = 0,
    parameter int N_FLOP_CROSS   = 2,
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int ARPW = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW,
    parameter int RPW  = IW + DW + 2 + 1 + UW
) (
    // Requester side
    input  logic            s_aclk,
    input  logic            s_aresetn,
    input  logic [IW-1:0]   s_axi_arid,
    input  logic [AW-1:0]   s_axi_araddr,
    input  logic [7:0]      s_axi_arlen,
    input  logic [2:0]      s_axi_arsize,
    input  logic [1:0]      s_axi_arburst,
    input  logic            s_axi_arlock,
    input  logic [3:0]      s_axi_arcache,
    input  logic [2:0]      s_axi_arprot,
    input  logic [3:0]      s_axi_arqos,
    input  logic [3:0]      s_axi_arregion,
    input  logic [UW-1:0]   s_axi_aruser,
    input  logic            s_axi_arvalid,
    output logic            s_axi_arready,
    output logic [IW-1:0]   s_axi_rid,
    output logic [DW-1:0]   s_axi_rdata,
    output logic [1:0]      s_axi_rresp,
    output logic            s_axi_rlast,
    output logic [UW-1:0]   s_axi_ruser,
    output logic            s_axi_rvalid,
    input  logic            s_axi_rready,

    // Completer side
    input  logic            m_aclk,
    input  logic            m_aresetn,
    output logic [IW-1:0]   m_axi_arid,
    output logic [AW-1:0]   m_axi_araddr,
    output logic [7:0]      m_axi_arlen,
    output logic [2:0]      m_axi_arsize,
    output logic [1:0]      m_axi_arburst,
    output logic            m_axi_arlock,
    output logic [3:0]      m_axi_arcache,
    output logic [2:0]      m_axi_arprot,
    output logic [3:0]      m_axi_arqos,
    output logic [3:0]      m_axi_arregion,
    output logic [UW-1:0]   m_axi_aruser,
    output logic            m_axi_arvalid,
    input  logic            m_axi_arready,
    input  logic [IW-1:0]   m_axi_rid,
    input  logic [DW-1:0]   m_axi_rdata,
    input  logic [1:0]      m_axi_rresp,
    input  logic            m_axi_rlast,
    input  logic [UW-1:0]   m_axi_ruser,
    input  logic            m_axi_rvalid,
    output logic            m_axi_rready
);

    // AR: requester -> completer
    gaxi_fifo_async #(
        .DATA_WIDTH   (ARPW),
        .DEPTH        (CDC_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (N_FLOP_CROSS)
    ) u_ar (
        .axi_wr_aclk    (s_aclk),
        .axi_wr_aresetn (s_aresetn),
        .axi_rd_aclk    (m_aclk),
        .axi_rd_aresetn (m_aresetn),
        .wr_valid       (s_axi_arvalid),
        .wr_ready       (s_axi_arready),
        .wr_data        ({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst,
                          s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos,
                          s_axi_arregion, s_axi_aruser}),
        .rd_ready       (m_axi_arready),
        .rd_valid       (m_axi_arvalid),
        .rd_data        ({m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
                          m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos,
                          m_axi_arregion, m_axi_aruser})
    );

    // R: completer -> requester
    gaxi_fifo_async #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (CDC_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (N_FLOP_CROSS)
    ) u_r (
        .axi_wr_aclk    (m_aclk),
        .axi_wr_aresetn (m_aresetn),
        .axi_rd_aclk    (s_aclk),
        .axi_rd_aresetn (s_aresetn),
        .wr_valid       (m_axi_rvalid),
        .wr_ready       (m_axi_rready),
        .wr_data        ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
        .rd_ready       (s_axi_rready),
        .rd_valid       (s_axi_rvalid),
        .rd_data        ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser})
    );

endmodule : axi4_cdc_rd
