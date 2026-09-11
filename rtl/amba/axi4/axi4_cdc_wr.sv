// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_cdc_wr
// Purpose: AXI4 write channels (AW, W, B) carried across a clock-domain
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
//   Three gaxi_fifo_async instances, one per channel, each crossing in the
//   channel's own direction: AW and W from the s_aclk domain into the m_aclk
//   domain, B back. Every channel keeps its AXI ordering because each FIFO is
//   in order; there is no reordering, no ID logic, and no protocol state --
//   what goes in on one side comes out on the other, later. AW and W cross
//   independently, as AXI allows (a slave may see W before AW).
//
//   The Gray-pointer FIFOs reset each domain's own pointer and its crossed
//   copy of the remote pointer from that domain's reset. That is consistent
//   while BOTH resets are asserted; it is NOT safe under a one-sided reset --
//   the crossed copy re-converges within N_FLOP_CROSS clocks of deassertion
//   against a remote pointer that kept moving, so a write-side-only reset
//   fabricates entries and a read-side-only reset replays them. Quiesce the
//   bus before resetting one side. (Handbook: design/cdc.md.)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   AXI_ID_WIDTH, AXI_ADDR_WIDTH, AXI_DATA_WIDTH, AXI_USER_WIDTH
//   CDC_DEPTH     - entries per channel FIFO (power of 2 under Gray; also the
//                   number of beats that can be in flight across the boundary
//                   per channel)
//   USE_JOHNSON   - 0 (Gray, default) or 1 (Johnson pointers, any depth) --
//                   hoisted per the CDC handbook rule
//   N_FLOP_CROSS  - synchronizer depth
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - axi4_cdc_rd.sv (AR, R)
//   - gaxi_fifo_async.sv (rtl/cdc)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_axi4_cdc.py
//==============================================================================

`timescale 1ns / 1ps

`include "fifo_defs.svh"

module axi4_cdc_wr #(
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
    parameter int SW = AXI_DATA_WIDTH / 8,
    parameter int UW = AXI_USER_WIDTH,
    parameter int AWPW = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW,
    parameter int WPW  = DW + SW + 1 + UW,
    parameter int BPW  = IW + 2 + UW
) (
    // Requester side
    input  logic            s_aclk,
    input  logic            s_aresetn,
    input  logic [IW-1:0]   s_axi_awid,
    input  logic [AW-1:0]   s_axi_awaddr,
    input  logic [7:0]      s_axi_awlen,
    input  logic [2:0]      s_axi_awsize,
    input  logic [1:0]      s_axi_awburst,
    input  logic            s_axi_awlock,
    input  logic [3:0]      s_axi_awcache,
    input  logic [2:0]      s_axi_awprot,
    input  logic [3:0]      s_axi_awqos,
    input  logic [3:0]      s_axi_awregion,
    input  logic [UW-1:0]   s_axi_awuser,
    input  logic            s_axi_awvalid,
    output logic            s_axi_awready,
    input  logic [DW-1:0]   s_axi_wdata,
    input  logic [SW-1:0]   s_axi_wstrb,
    input  logic            s_axi_wlast,
    input  logic [UW-1:0]   s_axi_wuser,
    input  logic            s_axi_wvalid,
    output logic            s_axi_wready,
    output logic [IW-1:0]   s_axi_bid,
    output logic [1:0]      s_axi_bresp,
    output logic [UW-1:0]   s_axi_buser,
    output logic            s_axi_bvalid,
    input  logic            s_axi_bready,

    // Completer side
    input  logic            m_aclk,
    input  logic            m_aresetn,
    output logic [IW-1:0]   m_axi_awid,
    output logic [AW-1:0]   m_axi_awaddr,
    output logic [7:0]      m_axi_awlen,
    output logic [2:0]      m_axi_awsize,
    output logic [1:0]      m_axi_awburst,
    output logic            m_axi_awlock,
    output logic [3:0]      m_axi_awcache,
    output logic [2:0]      m_axi_awprot,
    output logic [3:0]      m_axi_awqos,
    output logic [3:0]      m_axi_awregion,
    output logic [UW-1:0]   m_axi_awuser,
    output logic            m_axi_awvalid,
    input  logic            m_axi_awready,
    output logic [DW-1:0]   m_axi_wdata,
    output logic [SW-1:0]   m_axi_wstrb,
    output logic            m_axi_wlast,
    output logic [UW-1:0]   m_axi_wuser,
    output logic            m_axi_wvalid,
    input  logic            m_axi_wready,
    input  logic [IW-1:0]   m_axi_bid,
    input  logic [1:0]      m_axi_bresp,
    input  logic [UW-1:0]   m_axi_buser,
    input  logic            m_axi_bvalid,
    output logic            m_axi_bready
);

    // AW: requester -> completer
    gaxi_fifo_async #(
        .DATA_WIDTH   (AWPW),
        .DEPTH        (CDC_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (N_FLOP_CROSS)
    ) u_aw (
        .axi_wr_aclk    (s_aclk),
        .axi_wr_aresetn (s_aresetn),
        .axi_rd_aclk    (m_aclk),
        .axi_rd_aresetn (m_aresetn),
        .wr_valid       (s_axi_awvalid),
        .wr_ready       (s_axi_awready),
        .wr_data        ({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst,
                          s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos,
                          s_axi_awregion, s_axi_awuser}),
        .rd_ready       (m_axi_awready),
        .rd_valid       (m_axi_awvalid),
        .rd_data        ({m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
                          m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos,
                          m_axi_awregion, m_axi_awuser})
    );

    // W: requester -> completer
    gaxi_fifo_async #(
        .DATA_WIDTH   (WPW),
        .DEPTH        (CDC_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (N_FLOP_CROSS)
    ) u_w (
        .axi_wr_aclk    (s_aclk),
        .axi_wr_aresetn (s_aresetn),
        .axi_rd_aclk    (m_aclk),
        .axi_rd_aresetn (m_aresetn),
        .wr_valid       (s_axi_wvalid),
        .wr_ready       (s_axi_wready),
        .wr_data        ({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}),
        .rd_ready       (m_axi_wready),
        .rd_valid       (m_axi_wvalid),
        .rd_data        ({m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser})
    );

    // B: completer -> requester
    gaxi_fifo_async #(
        .DATA_WIDTH   (BPW),
        .DEPTH        (CDC_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (N_FLOP_CROSS)
    ) u_b (
        .axi_wr_aclk    (m_aclk),
        .axi_wr_aresetn (m_aresetn),
        .axi_rd_aclk    (s_aclk),
        .axi_rd_aresetn (s_aresetn),
        .wr_valid       (m_axi_bvalid),
        .wr_ready       (m_axi_bready),
        .wr_data        ({m_axi_bid, m_axi_bresp, m_axi_buser}),
        .rd_ready       (s_axi_bready),
        .rd_valid       (s_axi_bvalid),
        .rd_data        ({s_axi_bid, s_axi_bresp, s_axi_buser})
    );

endmodule : axi4_cdc_wr
