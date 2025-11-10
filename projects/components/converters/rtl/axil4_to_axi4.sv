// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axil4_to_axi4
// Purpose: AXI4-Lite to AXI4 Full Protocol Converter
//
// Description:
//   Converts AXI4-Lite protocol to AXI4 full by:
//   - Adding default values for burst fields (LEN=0, SIZE, BURST=INCR)
//   - Adding default values for ID, USER, REGION, QOS fields
//   - Converting simplified handshaking to full AXI4 protocol
//   - Maintaining single-beat transaction semantics
//
//   Key Features:
//   - Simple passthrough: All transactions remain single-beat
//   - Protocol upgrade: AXI4-Lite → AXI4 full with safe defaults
//   - Timing closure: Uses gaxi_skid_buffer on all channels
//   - Configurable defaults: ID, USER, REGION, QOS values
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
    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8,
    localparam int SIZE_VAL   = $clog2(STRB_WIDTH)  // ARSIZE/AWSIZE for full width
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
    // Read Address Channel: Add AXI4 Fields
    //==========================================================================

    // Passthrough AXI4-Lite fields
    assign m_axi_araddr = s_axil_araddr;
    assign m_axi_arprot = s_axil_arprot;
    assign m_axi_arvalid = s_axil_arvalid;
    assign s_axil_arready = m_axi_arready;

    // Add AXI4-only fields with safe defaults
    assign m_axi_arid     = AXI_ID_WIDTH'(DEFAULT_ID);
    assign m_axi_arlen    = 8'd0;           // Single beat
    assign m_axi_arsize   = 3'(SIZE_VAL);   // Full data width
    assign m_axi_arburst  = 2'b01;          // INCR burst type
    assign m_axi_arlock   = 1'b0;           // Normal access
    assign m_axi_arcache  = 4'b0011;        // Bufferable
    assign m_axi_arqos    = 4'(DEFAULT_QOS);
    assign m_axi_arregion = 4'(DEFAULT_REGION);
    assign m_axi_aruser   = '0;             // No user data

    //==========================================================================
    // Read Data Channel: Strip AXI4 Fields
    //==========================================================================

    // Passthrough data and response
    assign s_axil_rdata = m_axi_rdata;
    assign s_axil_rresp = m_axi_rresp;
    assign s_axil_rvalid = m_axi_rvalid;
    assign m_axi_rready = s_axil_rready;

    // Ignore AXI4-only fields (ID, LAST, USER)
    // RLAST should always be 1 for single-beat transactions

    //==========================================================================
    // Write Address Channel: Add AXI4 Fields
    //==========================================================================

    // Passthrough AXI4-Lite fields
    assign m_axi_awaddr = s_axil_awaddr;
    assign m_axi_awprot = s_axil_awprot;
    assign m_axi_awvalid = s_axil_awvalid;
    assign s_axil_awready = m_axi_awready;

    // Add AXI4-only fields with safe defaults
    assign m_axi_awid     = AXI_ID_WIDTH'(DEFAULT_ID);
    assign m_axi_awlen    = 8'd0;           // Single beat
    assign m_axi_awsize   = 3'(SIZE_VAL);   // Full data width
    assign m_axi_awburst  = 2'b01;          // INCR burst type
    assign m_axi_awlock   = 1'b0;           // Normal access
    assign m_axi_awcache  = 4'b0011;        // Bufferable
    assign m_axi_awqos    = 4'(DEFAULT_QOS);
    assign m_axi_awregion = 4'(DEFAULT_REGION);
    assign m_axi_awuser   = '0;             // No user data

    //==========================================================================
    // Write Data Channel: Add AXI4 Fields
    //==========================================================================

    // Passthrough AXI4-Lite fields
    assign m_axi_wdata = s_axil_wdata;
    assign m_axi_wstrb = s_axil_wstrb;
    assign m_axi_wvalid = s_axil_wvalid;
    assign s_axil_wready = m_axi_wready;

    // Add AXI4-only fields
    assign m_axi_wlast = 1'b1;  // Always last (single beat)
    assign m_axi_wuser = '0;    // No user data

    //==========================================================================
    // Write Response Channel: Strip AXI4 Fields
    //==========================================================================

    // Passthrough response
    assign s_axil_bresp = m_axi_bresp;
    assign s_axil_bvalid = m_axi_bvalid;
    assign m_axi_bready = s_axil_bready;

    // Ignore AXI4-only fields (ID, USER)

endmodule : axil4_to_axi4
