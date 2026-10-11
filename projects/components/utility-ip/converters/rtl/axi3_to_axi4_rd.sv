// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi3_to_axi4_rd
// Purpose: AXI3 to AXI4 Protocol Converter (READ-ONLY)
//
// Description:
//   Converts AXI3 protocol to AXI4 for READ path only by:
//   - Zero-extending AXI3 ARLEN (4 bits) to AXI4 ARLEN (8 bits)
//   - Mapping AXI3 2-bit ARLOCK to AXI4 1-bit ARLOCK
//     (normal -> 1'b0, locked -> 1'b0, exclusive -> 1'b1)
//   - Passing through ID, address, size, burst, cache, prot, user
//   - Passing through R channel (rid, rdata, rresp, rlast, ruser)
//
//   No burst chopping is required in this direction because AXI3's 4-bit
//   ARLEN is inherently limited to 16 beats, which fits in a single AXI4
//   transaction.
//
//   Standalone read-only implementation. For write conversion, use
//   axi3_to_axi4_wr.sv.
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI3/AXI4 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI3/AXI4 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - Read-only: No write path support
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi3_to_axi4_rd #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI3 Read Interface (Input - AXI3 Protocol)
    //==========================================================================

    // Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi3_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi3_araddr,
    input  logic [3:0]                  s_axi3_arlen,
    input  logic [2:0]                  s_axi3_arsize,
    input  logic [1:0]                  s_axi3_arburst,
    input  logic [1:0]                  s_axi3_arlock,
    input  logic [3:0]                  s_axi3_arcache,
    input  logic [2:0]                  s_axi3_arprot,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi3_aruser,
    input  logic                        s_axi3_arvalid,
    output logic                        s_axi3_arready,

    // Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi3_rid,
    output logic [AXI_DATA_WIDTH-1:0]   s_axi3_rdata,
    output logic [1:0]                  s_axi3_rresp,
    output logic                        s_axi3_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi3_ruser,
    output logic                        s_axi3_rvalid,
    input  logic                        s_axi3_rready,

    //==========================================================================
    // Master AXI4 Read Interface (Output - Full Protocol)
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
    output logic                        m_axi_rready
);

    //==========================================================================
    // AXI3 to AXI4 Read Address Channel Mapping
    //==========================================================================

    assign m_axi_arid    = s_axi3_arid;
    assign m_axi_araddr  = s_axi3_araddr;
    assign m_axi_arlen   = {4'b0, s_axi3_arlen};
    assign m_axi_arsize  = s_axi3_arsize;
    assign m_axi_arburst = s_axi3_arburst;
    assign m_axi_arlock  = (s_axi3_arlock == 2'b10) ? 1'b1 : 1'b0;
    assign m_axi_arcache = s_axi3_arcache;
    assign m_axi_arprot  = s_axi3_arprot;
    assign m_axi_aruser  = s_axi3_aruser;
    assign m_axi_arvalid = s_axi3_arvalid;
    assign s_axi3_arready = m_axi_arready;

    //==========================================================================
    // AXI4 to AXI3 Read Data Channel Pass-Through
    //==========================================================================

    assign s_axi3_rid    = m_axi_rid;
    assign s_axi3_rdata  = m_axi_rdata;
    assign s_axi3_rresp  = m_axi_rresp;
    assign s_axi3_rlast  = m_axi_rlast;
    assign s_axi3_ruser  = m_axi_ruser;
    assign s_axi3_rvalid = m_axi_rvalid;
    assign m_axi_rready  = s_axi3_rready;

endmodule : axi3_to_axi4_rd
