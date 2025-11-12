// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axil4_to_axi4
// Purpose: AXI4-Lite to AXI4 Full Protocol Converter
//
// Description:
//   Converts AXI4-Lite protocol to AXI4 full by instantiating separate
//   read and write converters:
//   - axil4_to_axi4_rd: Handles AR and R channels
//   - axil4_to_axi4_wr: Handles AW, W, and B channels
//
//   This top-level wrapper provides a complete bidirectional converter
//   while maintaining single source of truth for conversion logic.
//
//   Key Features:
//   - Simple passthrough: All transactions remain single-beat
//   - Protocol upgrade: AXI4-Lite → AXI4 full with safe defaults
//   - Timing closure: Uses gaxi_skid_buffer on all channels
//   - Configurable defaults: ID, USER, REGION, QOS values
//   - Modular design: Instantiates standalone read/write converters
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4 side (0-1024)
//   DEFAULT_ID: Default transaction ID (0-255)
//   DEFAULT_REGION: Default region value (0-15)
//   DEFAULT_QOS: Default QoS value (0-15)
//   SKID_DEPTH_AR/AW: Address channel skid depths (2-8, default 2)
//   SKID_DEPTH_R/B: Response channel skid depths (2-8, default 4)
//   SKID_DEPTH_W: Write data channel skid depth (2-8, default 4)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - All transactions are single-beat (LEN=0)
//   - No burst support on input side (AXI4-Lite restriction)
//
// Author: RTL Design Sherpa
// Created: 2025-11-05
// Modified: 2025-11-10 - Refactored to instantiate separate read/write modules

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil4_to_axi4 #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Default Values for AXI4-only Fields
    parameter int DEFAULT_ID        = 0,
    parameter int DEFAULT_REGION    = 0,
    parameter int DEFAULT_QOS       = 0,

    // Skid Buffer Depths (for timing closure)
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_R      = 4,
    parameter int SKID_DEPTH_B      = 4,

    // Calculated Parameters
    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4-Lite Interface (Input - Simplified Protocol)
    //==========================================================================

    // Read Address Channel
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axil_araddr,
    input  logic [2:0]                  s_axil_arprot,
    input  logic                        s_axil_arvalid,
    output logic                        s_axil_arready,

    // Read Data Channel
    output logic [AXI_DATA_WIDTH-1:0]   s_axil_rdata,
    output logic [1:0]                  s_axil_rresp,
    output logic                        s_axil_rvalid,
    input  logic                        s_axil_rready,

    // Write Address Channel
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axil_awaddr,
    input  logic [2:0]                  s_axil_awprot,
    input  logic                        s_axil_awvalid,
    output logic                        s_axil_awready,

    // Write Data Channel
    input  logic [AXI_DATA_WIDTH-1:0]   s_axil_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axil_wstrb,
    input  logic                        s_axil_wvalid,
    output logic                        s_axil_wready,

    // Write Response Channel
    output logic [1:0]                  s_axil_bresp,
    output logic                        s_axil_bvalid,
    input  logic                        s_axil_bready,

    //==========================================================================
    // Master AXI4 Interface (Output - Full Protocol)
    //==========================================================================

    // Read Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arlock,
    output logic [3:0]                  m_axi_arcache,
    output logic [2:0]                  m_axi_arprot,
    output logic [3:0]                  m_axi_arqos,
    output logic [3:0]                  m_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_aruser,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // Read Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0]   m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // Write Data Channel
    output logic [AXI_DATA_WIDTH-1:0]   m_axi_wdata,
    output logic [STRB_WIDTH-1:0]       m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready
);

    //==========================================================================
    // Read Path: Instantiate axil4_to_axi4_rd
    //==========================================================================

    axil4_to_axi4_rd #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .DEFAULT_ID      (DEFAULT_ID),
        .DEFAULT_REGION  (DEFAULT_REGION),
        .DEFAULT_QOS     (DEFAULT_QOS),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_rd_converter (
        .aclk           (aclk),
        .aresetn        (aresetn),

        // Slave AXI4-Lite Read Interface
        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (s_axil_arvalid),
        .s_axil_arready (s_axil_arready),
        .s_axil_rdata   (s_axil_rdata),
        .s_axil_rresp   (s_axil_rresp),
        .s_axil_rvalid  (s_axil_rvalid),
        .s_axil_rready  (s_axil_rready),

        // Master AXI4 Read Interface
        .m_axi_arid     (m_axi_arid),
        .m_axi_araddr   (m_axi_araddr),
        .m_axi_arlen    (m_axi_arlen),
        .m_axi_arsize   (m_axi_arsize),
        .m_axi_arburst  (m_axi_arburst),
        .m_axi_arlock   (m_axi_arlock),
        .m_axi_arcache  (m_axi_arcache),
        .m_axi_arprot   (m_axi_arprot),
        .m_axi_arqos    (m_axi_arqos),
        .m_axi_arregion (m_axi_arregion),
        .m_axi_aruser   (m_axi_aruser),
        .m_axi_arvalid  (m_axi_arvalid),
        .m_axi_arready  (m_axi_arready),
        .m_axi_rid      (m_axi_rid),
        .m_axi_rdata    (m_axi_rdata),
        .m_axi_rresp    (m_axi_rresp),
        .m_axi_rlast    (m_axi_rlast),
        .m_axi_ruser    (m_axi_ruser),
        .m_axi_rvalid   (m_axi_rvalid),
        .m_axi_rready   (m_axi_rready)
    );

    //==========================================================================
    // Write Path: Instantiate axil4_to_axi4_wr
    //==========================================================================

    axil4_to_axi4_wr #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .DEFAULT_ID      (DEFAULT_ID),
        .DEFAULT_REGION  (DEFAULT_REGION),
        .DEFAULT_QOS     (DEFAULT_QOS),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_wr_converter (
        .aclk           (aclk),
        .aresetn        (aresetn),

        // Slave AXI4-Lite Write Interface
        .s_axil_awaddr  (s_axil_awaddr),
        .s_axil_awprot  (s_axil_awprot),
        .s_axil_awvalid (s_axil_awvalid),
        .s_axil_awready (s_axil_awready),
        .s_axil_wdata   (s_axil_wdata),
        .s_axil_wstrb   (s_axil_wstrb),
        .s_axil_wvalid  (s_axil_wvalid),
        .s_axil_wready  (s_axil_wready),
        .s_axil_bresp   (s_axil_bresp),
        .s_axil_bvalid  (s_axil_bvalid),
        .s_axil_bready  (s_axil_bready),

        // Master AXI4 Write Interface
        .m_axi_awid     (m_axi_awid),
        .m_axi_awaddr   (m_axi_awaddr),
        .m_axi_awlen    (m_axi_awlen),
        .m_axi_awsize   (m_axi_awsize),
        .m_axi_awburst  (m_axi_awburst),
        .m_axi_awlock   (m_axi_awlock),
        .m_axi_awcache  (m_axi_awcache),
        .m_axi_awprot   (m_axi_awprot),
        .m_axi_awqos    (m_axi_awqos),
        .m_axi_awregion (m_axi_awregion),
        .m_axi_awuser   (m_axi_awuser),
        .m_axi_awvalid  (m_axi_awvalid),
        .m_axi_awready  (m_axi_awready),
        .m_axi_wdata    (m_axi_wdata),
        .m_axi_wstrb    (m_axi_wstrb),
        .m_axi_wlast    (m_axi_wlast),
        .m_axi_wuser    (m_axi_wuser),
        .m_axi_wvalid   (m_axi_wvalid),
        .m_axi_wready   (m_axi_wready),
        .m_axi_bid      (m_axi_bid),
        .m_axi_bresp    (m_axi_bresp),
        .m_axi_buser    (m_axi_buser),
        .m_axi_bvalid   (m_axi_bvalid),
        .m_axi_bready   (m_axi_bready)
    );

endmodule : axil4_to_axi4
