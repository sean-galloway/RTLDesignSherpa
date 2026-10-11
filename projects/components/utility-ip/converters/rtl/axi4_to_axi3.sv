// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axi3
// Purpose: AXI4 Full to AXI3 Protocol Converter (top wrapper)
//
// Description:
//   Top-level wrapper that combines the standalone read and write AXI4->AXI3
//   converters into a complete bidirectional converter:
//   - axi4_to_axi3_rd: handles AR and R channels with burst chopping and
//     worst-response merging
//   - axi4_to_axi3_wr: handles AW, W, and B channels with burst chopping,
//     WID stamping, and B-response merging
//
//   This module exposes the union of both submodule port lists: a full AXI4
//   slave interface and a full AXI3 master interface.
//
//   Key Features:
//   - Modular design: instantiates standalone read/write converters
//   - Full 5-channel AXI4 slave and AXI3 master port sets
//   - Single source of truth for read/write conversion logic
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4/AXI3 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4/AXI3 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - AXI4 WRAP bursts longer than 16 beats are not supported
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_to_axi3 #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Calculated Parameters
    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Interface (Input - Full Protocol)
    //==========================================================================

    // Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    // Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write Data Channel
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    //==========================================================================
    // Master AXI3 Interface (Output - AXI3 Protocol)
    //==========================================================================

    // Read Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_arid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi3_araddr,
    output logic [3:0]                  m_axi3_arlen,
    output logic [2:0]                  m_axi3_arsize,
    output logic [1:0]                  m_axi3_arburst,
    output logic [1:0]                  m_axi3_arlock,
    output logic [3:0]                  m_axi3_arcache,
    output logic [2:0]                  m_axi3_arprot,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_aruser,
    output logic                        m_axi3_arvalid,
    input  logic                        m_axi3_arready,

    // Read Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi3_rid,
    input  logic [AXI_DATA_WIDTH-1:0]   m_axi3_rdata,
    input  logic [1:0]                  m_axi3_rresp,
    input  logic                        m_axi3_rlast,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi3_ruser,
    input  logic                        m_axi3_rvalid,
    output logic                        m_axi3_rready,

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi3_awaddr,
    output logic [3:0]                  m_axi3_awlen,
    output logic [2:0]                  m_axi3_awsize,
    output logic [1:0]                  m_axi3_awburst,
    output logic [1:0]                  m_axi3_awlock,
    output logic [3:0]                  m_axi3_awcache,
    output logic [2:0]                  m_axi3_awprot,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_awuser,
    output logic                        m_axi3_awvalid,
    input  logic                        m_axi3_awready,

    // Write Data Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_wid,
    output logic [AXI_DATA_WIDTH-1:0]   m_axi3_wdata,
    output logic [STRB_WIDTH-1:0]       m_axi3_wstrb,
    output logic                        m_axi3_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_wuser,
    output logic                        m_axi3_wvalid,
    input  logic                        m_axi3_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi3_bid,
    input  logic [1:0]                  m_axi3_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi3_buser,
    input  logic                        m_axi3_bvalid,
    output logic                        m_axi3_bready
);

    //==========================================================================
    // Read Path: Instantiate axi4_to_axi3_rd
    //==========================================================================

    axi4_to_axi3_rd #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH)
    ) u_rd_converter (
        .aclk           (aclk),
        .aresetn        (aresetn),

        // Slave AXI4 Read Interface
        .s_axi_arid     (s_axi_arid),
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arlen    (s_axi_arlen),
        .s_axi_arsize   (s_axi_arsize),
        .s_axi_arburst  (s_axi_arburst),
        .s_axi_arlock   (s_axi_arlock),
        .s_axi_arcache  (s_axi_arcache),
        .s_axi_arprot   (s_axi_arprot),
        .s_axi_arqos    (s_axi_arqos),
        .s_axi_arregion (s_axi_arregion),
        .s_axi_aruser   (s_axi_aruser),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),
        .s_axi_rid      (s_axi_rid),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rlast    (s_axi_rlast),
        .s_axi_ruser    (s_axi_ruser),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),

        // Master AXI3 Read Interface
        .m_axi3_arid    (m_axi3_arid),
        .m_axi3_araddr  (m_axi3_araddr),
        .m_axi3_arlen   (m_axi3_arlen),
        .m_axi3_arsize  (m_axi3_arsize),
        .m_axi3_arburst (m_axi3_arburst),
        .m_axi3_arlock  (m_axi3_arlock),
        .m_axi3_arcache (m_axi3_arcache),
        .m_axi3_arprot  (m_axi3_arprot),
        .m_axi3_aruser  (m_axi3_aruser),
        .m_axi3_arvalid (m_axi3_arvalid),
        .m_axi3_arready (m_axi3_arready),
        .m_axi3_rid     (m_axi3_rid),
        .m_axi3_rdata   (m_axi3_rdata),
        .m_axi3_rresp   (m_axi3_rresp),
        .m_axi3_rlast   (m_axi3_rlast),
        .m_axi3_ruser   (m_axi3_ruser),
        .m_axi3_rvalid  (m_axi3_rvalid),
        .m_axi3_rready  (m_axi3_rready)
    );

    //==========================================================================
    // Write Path: Instantiate axi4_to_axi3_wr
    //==========================================================================

    axi4_to_axi3_wr #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH)
    ) u_wr_converter (
        .aclk           (aclk),
        .aresetn        (aresetn),

        // Slave AXI4 Write Interface
        .s_axi_awid     (s_axi_awid),
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awlen    (s_axi_awlen),
        .s_axi_awsize   (s_axi_awsize),
        .s_axi_awburst  (s_axi_awburst),
        .s_axi_awlock   (s_axi_awlock),
        .s_axi_awcache  (s_axi_awcache),
        .s_axi_awprot   (s_axi_awprot),
        .s_axi_awqos    (s_axi_awqos),
        .s_axi_awregion (s_axi_awregion),
        .s_axi_awuser   (s_axi_awuser),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),
        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wstrb    (s_axi_wstrb),
        .s_axi_wlast    (s_axi_wlast),
        .s_axi_wuser    (s_axi_wuser),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),
        .s_axi_bid      (s_axi_bid),
        .s_axi_bresp    (s_axi_bresp),
        .s_axi_buser    (s_axi_buser),
        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bready   (s_axi_bready),

        // Master AXI3 Write Interface
        .m_axi3_awid    (m_axi3_awid),
        .m_axi3_awaddr  (m_axi3_awaddr),
        .m_axi3_awlen   (m_axi3_awlen),
        .m_axi3_awsize  (m_axi3_awsize),
        .m_axi3_awburst (m_axi3_awburst),
        .m_axi3_awlock  (m_axi3_awlock),
        .m_axi3_awcache (m_axi3_awcache),
        .m_axi3_awprot  (m_axi3_awprot),
        .m_axi3_awuser  (m_axi3_awuser),
        .m_axi3_awvalid (m_axi3_awvalid),
        .m_axi3_awready (m_axi3_awready),
        .m_axi3_wid     (m_axi3_wid),
        .m_axi3_wdata   (m_axi3_wdata),
        .m_axi3_wstrb   (m_axi3_wstrb),
        .m_axi3_wlast   (m_axi3_wlast),
        .m_axi3_wuser   (m_axi3_wuser),
        .m_axi3_wvalid  (m_axi3_wvalid),
        .m_axi3_wready  (m_axi3_wready),
        .m_axi3_bid     (m_axi3_bid),
        .m_axi3_bresp   (m_axi3_bresp),
        .m_axi3_buser   (m_axi3_buser),
        .m_axi3_bvalid  (m_axi3_bvalid),
        .m_axi3_bready  (m_axi3_bready)
    );

endmodule : axi4_to_axi3
