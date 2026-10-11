// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axi3_rd
// Purpose: AXI4 Full to AXI3 Protocol Converter (READ-ONLY)
//
// Description:
//   Converts AXI4 full protocol to AXI3 for READ path only by:
//   - Passing through read address and data channels with signal width adaptation
//   - Truncating AXI4 ARLEN (8 bits) to AXI3 ARLEN (4 bits)
//   - Dropping AXI4-specific signals (QOS, REGION)
//   - Mapping AXI4 1-bit ARLOCK to AXI3 2-bit ARLOCK
//     (normal -> 2'b00, exclusive -> 2'b10)
//   - Preserving ID, data, response, and user information
//
//   Standalone read-only implementation. For write conversion, use
//   axi4_to_axi3_wr.sv.
//
//   Key Features:
//   - Read-only: AR, R channels only
//   - Pass-through: no burst decomposition (single AXI4 burst maps to single AXI3 burst)
//   - Protocol compliant: Full AXI4 slave, AXI3 master
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4/AXI3 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4/AXI3 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - AXI4 bursts longer than 16 beats (ARLEN > 15) are not supported in v1
//   - Read-only: No write path support
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_to_axi3_rd #(
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
    // Slave AXI4 Read Interface (Input - Full Protocol)
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

    //==========================================================================
    // Master AXI3 Read Interface (Output - AXI3 Protocol)
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
    output logic                        m_axi3_rready
);

    //==========================================================================
    // AXI4 to AXI3 Read Address Channel Mapping
    //==========================================================================

    // Burst length assertion: AXI3 only supports up to 16 beats (ARLEN <= 15).
    // Longer AXI4 bursts require chopping (implemented in Task 3).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // No check during reset
        end else begin
            if (s_axi_arvalid && (s_axi_arlen > 8'd15))
                $error("ASSERT_A3_RD_LEN16: AXI4 read burst length %0d exceeds AXI3 maximum of 16 beats", s_axi_arlen);
        end
    )

    // AR channel pass-through with adaptations
    assign m_axi3_arid    = s_axi_arid;
    assign m_axi3_araddr  = s_axi_araddr;
    assign m_axi3_arlen   = s_axi_arlen[3:0];
    assign m_axi3_arsize  = s_axi_arsize;
    assign m_axi3_arburst = s_axi_arburst;
    // AXI4 lock: 0=normal, 1=exclusive. AXI3 lock: 00=normal, 01=reserved,
    // 10=exclusive, 11=locked. Locked transactions are never generated.
    assign m_axi3_arlock  = s_axi_arlock ? 2'b10 : 2'b00;
    assign m_axi3_arcache = s_axi_arcache;
    assign m_axi3_arprot  = s_axi_arprot;
    // AXI3 has no QOS or REGION; drop them.
    assign m_axi3_aruser  = s_axi_aruser;
    assign m_axi3_arvalid = s_axi_arvalid;
    assign s_axi_arready  = m_axi3_arready;

    //==========================================================================
    // AXI3 to AXI4 Read Data Channel Pass-Through
    //==========================================================================

    assign s_axi_rid   = m_axi3_rid;
    assign s_axi_rdata = m_axi3_rdata;
    assign s_axi_rresp = m_axi3_rresp;
    assign s_axi_rlast = m_axi3_rlast;
    assign s_axi_ruser = m_axi3_ruser;
    assign s_axi_rvalid = m_axi3_rvalid;
    assign m_axi3_rready = s_axi_rready;

endmodule : axi4_to_axi3_rd
