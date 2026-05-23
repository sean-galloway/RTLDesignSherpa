// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_dwidth_to_axil4_wr_chain
// Purpose: FUB-level chain wrapping axi4_dwidth_converter_wr (downsize)
//          directly connected to axi4_to_axil4_wr.
//
// Description:
//   Slave side: wide AXI4 (S_AXI_DATA_WIDTH).
//   axi4_dwidth_converter_wr downsizes the W beats to M_AXIL_DATA_WIDTH
//   and rewrites awlen/awsize so the downstream module sees a narrow
//   AXI4 burst of M_AXIL_DATA_WIDTH-wide beats.
//   axi4_to_axil4_wr then decomposes that narrow AXI4 burst into
//   single-beat AXIL4 writes on the master AXIL interface.
//
//   This chain is what real bridges instantiate when a wide master writes
//   to a narrow AXIL4 slave. It is the configuration that surfaces the
//   page-probe class of back-to-back boundary bugs at the bridge level,
//   so we exercise it at the FUB level here.
//
// Parameters:
//   S_AXI_DATA_WIDTH   - Slave wide AXI4 data width (must be > M_AXIL)
//   M_AXIL_DATA_WIDTH  - Master AXIL4 data width (narrow)
//   AXI_ID_WIDTH       - AXI4 ID width (fixed at 8 by convention)
//   AXI_ADDR_WIDTH     - Address width
//
// Author: RTL Design Sherpa
// Created: 2026-05-22

`timescale 1ns / 1ps

module axi4_dwidth_to_axil4_wr_chain #(
    parameter int S_AXI_DATA_WIDTH  = 64,
    parameter int M_AXIL_DATA_WIDTH = 32,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Calculated
    localparam int S_STRB_WIDTH = S_AXI_DATA_WIDTH / 8,
    localparam int M_STRB_WIDTH = M_AXIL_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                          aclk,
    input  logic                          aresetn,

    //==========================================================================
    // Slave AXI4 Write Interface (wide)
    //==========================================================================
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
    input  logic [7:0]                    s_axi_awlen,
    input  logic [2:0]                    s_axi_awsize,
    input  logic [1:0]                    s_axi_awburst,
    input  logic                          s_axi_awlock,
    input  logic [3:0]                    s_axi_awcache,
    input  logic [2:0]                    s_axi_awprot,
    input  logic [3:0]                    s_axi_awqos,
    input  logic [3:0]                    s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_awuser,
    input  logic                          s_axi_awvalid,
    output logic                          s_axi_awready,

    input  logic [S_AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [S_STRB_WIDTH-1:0]       s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_wuser,
    input  logic                          s_axi_wvalid,
    output logic                          s_axi_wready,

    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,

    //==========================================================================
    // Master AXIL4 Write Interface (narrow)
    //==========================================================================
    output logic [AXI_ADDR_WIDTH-1:0]     m_axil_awaddr,
    output logic [2:0]                    m_axil_awprot,
    output logic                          m_axil_awvalid,
    input  logic                          m_axil_awready,

    output logic [M_AXIL_DATA_WIDTH-1:0]  m_axil_wdata,
    output logic [M_STRB_WIDTH-1:0]       m_axil_wstrb,
    output logic                          m_axil_wvalid,
    input  logic                          m_axil_wready,

    input  logic [1:0]                    m_axil_bresp,
    input  logic                          m_axil_bvalid,
    output logic                          m_axil_bready
);

    //==========================================================================
    // Internal narrow AXI4 (between dwidth converter and axil shim)
    //==========================================================================
    logic [AXI_ID_WIDTH-1:0]              int_awid;
    logic [AXI_ADDR_WIDTH-1:0]            int_awaddr;
    logic [7:0]                           int_awlen;
    logic [2:0]                           int_awsize;
    logic [1:0]                           int_awburst;
    logic                                 int_awlock;
    logic [3:0]                           int_awcache;
    logic [2:0]                           int_awprot;
    logic [3:0]                           int_awqos;
    logic [3:0]                           int_awregion;
    logic [AXI_USER_WIDTH-1:0]            int_awuser;
    logic                                 int_awvalid;
    logic                                 int_awready;

    logic [M_AXIL_DATA_WIDTH-1:0]         int_wdata;
    logic [M_STRB_WIDTH-1:0]              int_wstrb;
    logic                                 int_wlast;
    logic [AXI_USER_WIDTH-1:0]            int_wuser;
    logic                                 int_wvalid;
    logic                                 int_wready;

    logic [AXI_ID_WIDTH-1:0]              int_bid;
    logic [1:0]                           int_bresp;
    logic [AXI_USER_WIDTH-1:0]            int_buser;
    logic                                 int_bvalid;
    logic                                 int_bready;

    //==========================================================================
    // Wide AXI4 (slave) → Narrow AXI4 (internal)
    //==========================================================================
    axi4_dwidth_converter_wr #(
        .S_AXI_DATA_WIDTH (S_AXI_DATA_WIDTH),
        .M_AXI_DATA_WIDTH (M_AXIL_DATA_WIDTH),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH)
    ) u_dwidth_wr (
        .aclk             (aclk),
        .aresetn          (aresetn),

        // Slave (wide)
        .s_axi_awid       (s_axi_awid),
        .s_axi_awaddr     (s_axi_awaddr),
        .s_axi_awlen      (s_axi_awlen),
        .s_axi_awsize     (s_axi_awsize),
        .s_axi_awburst    (s_axi_awburst),
        .s_axi_awlock     (s_axi_awlock),
        .s_axi_awcache    (s_axi_awcache),
        .s_axi_awprot     (s_axi_awprot),
        .s_axi_awqos      (s_axi_awqos),
        .s_axi_awregion   (s_axi_awregion),
        .s_axi_awuser     (s_axi_awuser),
        .s_axi_awvalid    (s_axi_awvalid),
        .s_axi_awready    (s_axi_awready),

        .s_axi_wdata      (s_axi_wdata),
        .s_axi_wstrb      (s_axi_wstrb),
        .s_axi_wlast      (s_axi_wlast),
        .s_axi_wuser      (s_axi_wuser),
        .s_axi_wvalid     (s_axi_wvalid),
        .s_axi_wready     (s_axi_wready),

        .s_axi_bid        (s_axi_bid),
        .s_axi_bresp      (s_axi_bresp),
        .s_axi_buser      (s_axi_buser),
        .s_axi_bvalid     (s_axi_bvalid),
        .s_axi_bready     (s_axi_bready),

        // Master (narrow) — feeds internal AXI4 between modules
        .m_axi_awid       (int_awid),
        .m_axi_awaddr     (int_awaddr),
        .m_axi_awlen      (int_awlen),
        .m_axi_awsize     (int_awsize),
        .m_axi_awburst    (int_awburst),
        .m_axi_awlock     (int_awlock),
        .m_axi_awcache    (int_awcache),
        .m_axi_awprot     (int_awprot),
        .m_axi_awqos      (int_awqos),
        .m_axi_awregion   (int_awregion),
        .m_axi_awuser     (int_awuser),
        .m_axi_awvalid    (int_awvalid),
        .m_axi_awready    (int_awready),

        .m_axi_wdata      (int_wdata),
        .m_axi_wstrb      (int_wstrb),
        .m_axi_wlast      (int_wlast),
        .m_axi_wuser      (int_wuser),
        .m_axi_wvalid     (int_wvalid),
        .m_axi_wready     (int_wready),

        .m_axi_bid        (int_bid),
        .m_axi_bresp      (int_bresp),
        .m_axi_buser      (int_buser),
        .m_axi_bvalid     (int_bvalid),
        .m_axi_bready     (int_bready)
    );

    //==========================================================================
    // Narrow AXI4 (internal) → AXIL4 (master)
    //==========================================================================
    axi4_to_axil4_wr #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (M_AXIL_DATA_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH)
    ) u_to_axil_wr (
        .aclk             (aclk),
        .aresetn          (aresetn),

        // Slave AXI4 (narrow) — accepts the dnsize'd burst
        .s_axi_awid       (int_awid),
        .s_axi_awaddr     (int_awaddr),
        .s_axi_awlen      (int_awlen),
        .s_axi_awsize     (int_awsize),
        .s_axi_awburst    (int_awburst),
        .s_axi_awlock     (int_awlock),
        .s_axi_awcache    (int_awcache),
        .s_axi_awprot     (int_awprot),
        .s_axi_awqos      (int_awqos),
        .s_axi_awregion   (int_awregion),
        .s_axi_awuser     (int_awuser),
        .s_axi_awvalid    (int_awvalid),
        .s_axi_awready    (int_awready),

        .s_axi_wdata      (int_wdata),
        .s_axi_wstrb      (int_wstrb),
        .s_axi_wlast      (int_wlast),
        .s_axi_wuser      (int_wuser),
        .s_axi_wvalid     (int_wvalid),
        .s_axi_wready     (int_wready),

        .s_axi_bid        (int_bid),
        .s_axi_bresp      (int_bresp),
        .s_axi_buser      (int_buser),
        .s_axi_bvalid     (int_bvalid),
        .s_axi_bready     (int_bready),

        // Master AXIL4 (narrow) — module output
        .m_axil_awaddr    (m_axil_awaddr),
        .m_axil_awprot    (m_axil_awprot),
        .m_axil_awvalid   (m_axil_awvalid),
        .m_axil_awready   (m_axil_awready),

        .m_axil_wdata     (m_axil_wdata),
        .m_axil_wstrb     (m_axil_wstrb),
        .m_axil_wvalid    (m_axil_wvalid),
        .m_axil_wready    (m_axil_wready),

        .m_axil_bresp     (m_axil_bresp),
        .m_axil_bvalid    (m_axil_bvalid),
        .m_axil_bready    (m_axil_bready)
    );

endmodule : axi4_dwidth_to_axil4_wr_chain
