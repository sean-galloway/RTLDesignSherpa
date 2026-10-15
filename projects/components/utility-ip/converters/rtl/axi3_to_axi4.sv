// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi3_to_axi4
// Purpose: AXI3 Full to AXI4 Protocol Converter (top wrapper)
//
// Description:
//   Top-level wrapper that combines the standalone read and write AXI3->AXI4
//   converters into a complete bidirectional converter:
//   - axi3_to_axi4_rd: handles AR and R channels with ARLEN zero-extension and
//     ARLOCK mapping
//   - axi3_to_axi4_wr: handles AW, W, and B channels with AWLEN zero-extension,
//     AWLOCK mapping, and WID stripping under a single-active-write contract
//
//   This module exposes the union of both submodule port lists: a full AXI3
//   slave interface and a full AXI4 master interface.
//
//   Key Features:
//   - Modular design: instantiates standalone read/write converters
//   - Full 5-channel AXI3 slave and AXI4 master port sets
//   - Single source of truth for read/write conversion logic
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI3/AXI4 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI3/AXI4 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - One outstanding write transaction at a time
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi3_to_axi4 #(
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
    // Slave AXI3 Interface (Input - AXI3 Protocol)
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

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi3_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi3_awaddr,
    input  logic [3:0]                  s_axi3_awlen,
    input  logic [2:0]                  s_axi3_awsize,
    input  logic [1:0]                  s_axi3_awburst,
    input  logic [1:0]                  s_axi3_awlock,
    input  logic [3:0]                  s_axi3_awcache,
    input  logic [2:0]                  s_axi3_awprot,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi3_awuser,
    input  logic                        s_axi3_awvalid,
    output logic                        s_axi3_awready,

    // Write Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi3_wid,
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi3_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi3_wstrb,
    input  logic                        s_axi3_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi3_wuser,
    input  logic                        s_axi3_wvalid,
    output logic                        s_axi3_wready,

    // Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi3_bid,
    output logic [1:0]                  s_axi3_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi3_buser,
    output logic                        s_axi3_bvalid,
    input  logic                        s_axi3_bready,

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
    // Boundary reset synchronization. The port aresetn is treated as an
    // asynchronous-assert input of unknown deassert quality: an N=3
    // reset_sync (rtl/cdc, formally proven) produces the internal reset
    // every block below sees.
    logic w_aresetn;
    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1)
    ) u_reset_sync (
        .clk        (aclk),
        .rst_n      (aresetn),
        .sync_rst_n (w_aresetn)
    );


    //==========================================================================
    // Read Path: Instantiate axi3_to_axi4_rd
    //==========================================================================

    // AXI3 has no read-side QOS/REGION; drive AXI4 outputs to zero.
    assign m_axi_arqos    = 4'b0;
    assign m_axi_arregion = 4'b0;

    axi3_to_axi4_rd #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH)
    ) u_rd_converter (
        .aclk           (aclk),
        .aresetn        (w_aresetn),

        // Slave AXI3 Read Interface
        .s_axi3_arid    (s_axi3_arid),
        .s_axi3_araddr  (s_axi3_araddr),
        .s_axi3_arlen   (s_axi3_arlen),
        .s_axi3_arsize  (s_axi3_arsize),
        .s_axi3_arburst (s_axi3_arburst),
        .s_axi3_arlock  (s_axi3_arlock),
        .s_axi3_arcache (s_axi3_arcache),
        .s_axi3_arprot  (s_axi3_arprot),
        .s_axi3_aruser  (s_axi3_aruser),
        .s_axi3_arvalid (s_axi3_arvalid),
        .s_axi3_arready (s_axi3_arready),
        .s_axi3_rid     (s_axi3_rid),
        .s_axi3_rdata   (s_axi3_rdata),
        .s_axi3_rresp   (s_axi3_rresp),
        .s_axi3_rlast   (s_axi3_rlast),
        .s_axi3_ruser   (s_axi3_ruser),
        .s_axi3_rvalid  (s_axi3_rvalid),
        .s_axi3_rready  (s_axi3_rready),

        // Master AXI4 Read Interface
        .m_axi_arid     (m_axi_arid),
        .m_axi_araddr   (m_axi_araddr),
        .m_axi_arlen    (m_axi_arlen),
        .m_axi_arsize   (m_axi_arsize),
        .m_axi_arburst  (m_axi_arburst),
        .m_axi_arlock   (m_axi_arlock),
        .m_axi_arcache  (m_axi_arcache),
        .m_axi_arprot   (m_axi_arprot),
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
    // Write Path: Instantiate axi3_to_axi4_wr
    //==========================================================================

    axi3_to_axi4_wr #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH)
    ) u_wr_converter (
        .aclk           (aclk),
        .aresetn        (w_aresetn),

        // Slave AXI3 Write Interface
        .s_axi3_awid    (s_axi3_awid),
        .s_axi3_awaddr  (s_axi3_awaddr),
        .s_axi3_awlen   (s_axi3_awlen),
        .s_axi3_awsize  (s_axi3_awsize),
        .s_axi3_awburst (s_axi3_awburst),
        .s_axi3_awlock  (s_axi3_awlock),
        .s_axi3_awcache (s_axi3_awcache),
        .s_axi3_awprot  (s_axi3_awprot),
        .s_axi3_awuser  (s_axi3_awuser),
        .s_axi3_awvalid (s_axi3_awvalid),
        .s_axi3_awready (s_axi3_awready),
        .s_axi3_wid     (s_axi3_wid),
        .s_axi3_wdata   (s_axi3_wdata),
        .s_axi3_wstrb   (s_axi3_wstrb),
        .s_axi3_wlast   (s_axi3_wlast),
        .s_axi3_wuser   (s_axi3_wuser),
        .s_axi3_wvalid  (s_axi3_wvalid),
        .s_axi3_wready  (s_axi3_wready),
        .s_axi3_bid     (s_axi3_bid),
        .s_axi3_bresp   (s_axi3_bresp),
        .s_axi3_buser   (s_axi3_buser),
        .s_axi3_bvalid  (s_axi3_bvalid),
        .s_axi3_bready  (s_axi3_bready),

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

endmodule : axi3_to_axi4
