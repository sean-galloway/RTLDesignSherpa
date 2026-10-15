// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi3_loopback
// Purpose: AXI4 -> AXI3 -> AXI4 loopback equivalence chain top wrapper
//
// Description:
//   Integration proof that the converter pair is identity for legal AXI4
//   traffic.  The near side is a full AXI4 slave driven by AXI4MasterRead/Write
//   BFMs; the far side is a full AXI4 master connected to AXI4SlaveRead/Write
//   memory-model responders.  The AXI3 interface between the two converters is
//   wired internally.
//
//   The write side serializes because axi3_to_axi4_wr enforces a single-active-
//   write contract; the read side pipelines.  This is expected and legal.
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4/AXI3 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4/AXI3 side (0-1024)
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi3_loopback #(
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
    // Slave AXI4 Interface (Input - near side)
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
    // Master AXI4 Interface (Output - far side)
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
    // Internal AXI3 loopback signals
    //==========================================================================

    logic [AXI_ID_WIDTH-1:0]     loopback_arid;
    logic [AXI_ADDR_WIDTH-1:0]   loopback_araddr;
    logic [3:0]                  loopback_arlen;
    logic [2:0]                  loopback_arsize;
    logic [1:0]                  loopback_arburst;
    logic [1:0]                  loopback_arlock;
    logic [3:0]                  loopback_arcache;
    logic [2:0]                  loopback_arprot;
    logic [AXI_USER_WIDTH-1:0]   loopback_aruser;
    logic                        loopback_arvalid;
    logic                        loopback_arready;

    logic [AXI_ID_WIDTH-1:0]     loopback_rid;
    logic [AXI_DATA_WIDTH-1:0]   loopback_rdata;
    logic [1:0]                  loopback_rresp;
    logic                        loopback_rlast;
    logic [AXI_USER_WIDTH-1:0]   loopback_ruser;
    logic                        loopback_rvalid;
    logic                        loopback_rready;

    logic [AXI_ID_WIDTH-1:0]     loopback_awid;
    logic [AXI_ADDR_WIDTH-1:0]   loopback_awaddr;
    logic [3:0]                  loopback_awlen;
    logic [2:0]                  loopback_awsize;
    logic [1:0]                  loopback_awburst;
    logic [1:0]                  loopback_awlock;
    logic [3:0]                  loopback_awcache;
    logic [2:0]                  loopback_awprot;
    logic [AXI_USER_WIDTH-1:0]   loopback_awuser;
    logic                        loopback_awvalid;
    logic                        loopback_awready;

    logic [AXI_ID_WIDTH-1:0]     loopback_wid;
    logic [AXI_DATA_WIDTH-1:0]   loopback_wdata;
    logic [STRB_WIDTH-1:0]       loopback_wstrb;
    logic                        loopback_wlast;
    logic [AXI_USER_WIDTH-1:0]   loopback_wuser;
    logic                        loopback_wvalid;
    logic                        loopback_wready;

    logic [AXI_ID_WIDTH-1:0]     loopback_bid;
    logic [1:0]                  loopback_bresp;
    logic [AXI_USER_WIDTH-1:0]   loopback_buser;
    logic                        loopback_bvalid;
    logic                        loopback_bready;

    //==========================================================================
    // AXI4 -> AXI3 near-side converter
    //==========================================================================

    axi4_to_axi3 #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH)
    ) u_axi4_to_axi3 (
        .aclk           (aclk),
        .aresetn        (w_aresetn),

        // Slave AXI4 Interface
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

        // Master AXI3 Interface (looped back to axi3_to_axi4)
        .m_axi3_arid    (loopback_arid),
        .m_axi3_araddr  (loopback_araddr),
        .m_axi3_arlen   (loopback_arlen),
        .m_axi3_arsize  (loopback_arsize),
        .m_axi3_arburst (loopback_arburst),
        .m_axi3_arlock  (loopback_arlock),
        .m_axi3_arcache (loopback_arcache),
        .m_axi3_arprot  (loopback_arprot),
        .m_axi3_aruser  (loopback_aruser),
        .m_axi3_arvalid (loopback_arvalid),
        .m_axi3_arready (loopback_arready),
        .m_axi3_rid     (loopback_rid),
        .m_axi3_rdata   (loopback_rdata),
        .m_axi3_rresp   (loopback_rresp),
        .m_axi3_rlast   (loopback_rlast),
        .m_axi3_ruser   (loopback_ruser),
        .m_axi3_rvalid  (loopback_rvalid),
        .m_axi3_rready  (loopback_rready),
        .m_axi3_awid    (loopback_awid),
        .m_axi3_awaddr  (loopback_awaddr),
        .m_axi3_awlen   (loopback_awlen),
        .m_axi3_awsize  (loopback_awsize),
        .m_axi3_awburst (loopback_awburst),
        .m_axi3_awlock  (loopback_awlock),
        .m_axi3_awcache (loopback_awcache),
        .m_axi3_awprot  (loopback_awprot),
        .m_axi3_awuser  (loopback_awuser),
        .m_axi3_awvalid (loopback_awvalid),
        .m_axi3_awready (loopback_awready),
        .m_axi3_wid     (loopback_wid),
        .m_axi3_wdata   (loopback_wdata),
        .m_axi3_wstrb   (loopback_wstrb),
        .m_axi3_wlast   (loopback_wlast),
        .m_axi3_wuser   (loopback_wuser),
        .m_axi3_wvalid  (loopback_wvalid),
        .m_axi3_wready  (loopback_wready),
        .m_axi3_bid     (loopback_bid),
        .m_axi3_bresp   (loopback_bresp),
        .m_axi3_buser   (loopback_buser),
        .m_axi3_bvalid  (loopback_bvalid),
        .m_axi3_bready  (loopback_bready)
    );

    //==========================================================================
    // AXI3 -> AXI4 far-side converter
    //==========================================================================

    axi3_to_axi4 #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH)
    ) u_axi3_to_axi4 (
        .aclk           (aclk),
        .aresetn        (w_aresetn),

        // Slave AXI3 Interface (looped back from axi4_to_axi3)
        .s_axi3_arid    (loopback_arid),
        .s_axi3_araddr  (loopback_araddr),
        .s_axi3_arlen   (loopback_arlen),
        .s_axi3_arsize  (loopback_arsize),
        .s_axi3_arburst (loopback_arburst),
        .s_axi3_arlock  (loopback_arlock),
        .s_axi3_arcache (loopback_arcache),
        .s_axi3_arprot  (loopback_arprot),
        .s_axi3_aruser  (loopback_aruser),
        .s_axi3_arvalid (loopback_arvalid),
        .s_axi3_arready (loopback_arready),
        .s_axi3_rid     (loopback_rid),
        .s_axi3_rdata   (loopback_rdata),
        .s_axi3_rresp   (loopback_rresp),
        .s_axi3_rlast   (loopback_rlast),
        .s_axi3_ruser   (loopback_ruser),
        .s_axi3_rvalid  (loopback_rvalid),
        .s_axi3_rready  (loopback_rready),
        .s_axi3_awid    (loopback_awid),
        .s_axi3_awaddr  (loopback_awaddr),
        .s_axi3_awlen   (loopback_awlen),
        .s_axi3_awsize  (loopback_awsize),
        .s_axi3_awburst (loopback_awburst),
        .s_axi3_awlock  (loopback_awlock),
        .s_axi3_awcache (loopback_awcache),
        .s_axi3_awprot  (loopback_awprot),
        .s_axi3_awuser  (loopback_awuser),
        .s_axi3_awvalid (loopback_awvalid),
        .s_axi3_awready (loopback_awready),
        .s_axi3_wid     (loopback_wid),
        .s_axi3_wdata   (loopback_wdata),
        .s_axi3_wstrb   (loopback_wstrb),
        .s_axi3_wlast   (loopback_wlast),
        .s_axi3_wuser   (loopback_wuser),
        .s_axi3_wvalid  (loopback_wvalid),
        .s_axi3_wready  (loopback_wready),
        .s_axi3_bid     (loopback_bid),
        .s_axi3_bresp   (loopback_bresp),
        .s_axi3_buser   (loopback_buser),
        .s_axi3_bvalid  (loopback_bvalid),
        .s_axi3_bready  (loopback_bready),

        // Master AXI4 Interface
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
        .m_axi_rready   (m_axi_rready),
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

endmodule : axi3_loopback
