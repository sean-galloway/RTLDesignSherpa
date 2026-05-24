// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_dwidth_to_apb_chain
// Purpose: FUB-level chain wrapping axi4_dwidth_converter_rd (downsize)
//          directly connected to axi4_to_apb_shim (read path only).
//
// Description:
//   Slave side: wide AXI4 (S_AXI_DATA_WIDTH) — read channels only
//   (AR, R). The write channels at the slave port are tied off here.
//
//   axi4_dwidth_converter_rd downsizes the R beats from the shim's
//   APB_DATA_WIDTH up to S_AXI_DATA_WIDTH on the slave-facing side.
//   Equivalently (and more useful for reproducing the bridge bug):
//   the wide master issues a wide-beat AR burst, the rd-converter
//   rewrites arlen/arsize down to APB_DATA_WIDTH-wide narrow beats,
//   and the shim decomposes that narrow AXI4 burst into single-beat
//   APB reads on the master APB interface.
//
//   This chain is what real bridges instantiate when a wide master
//   reads from a narrow APB peripheral. It is the configuration that
//   surfaces the page-probe class of back-to-back boundary bugs at
//   the bridge level (1x5_rd_boundary_probe), so we exercise it here
//   at the FUB level.
//
//   The write channels on the slave-side AXI4 bus are tied off; only
//   the read path is exercised. This mirrors the bridge's APB
//   peripheral adapter for the read-only debug case.
//
// Parameters:
//   S_AXI_DATA_WIDTH - Slave wide AXI4 data width (must be > APB)
//   APB_DATA_WIDTH   - Master APB data width (narrow)
//   AXI_ID_WIDTH     - AXI4 ID width (fixed at 8 by convention)
//   AXI_ADDR_WIDTH   - AXI address width
//   APB_ADDR_WIDTH   - APB address width
//
// Author: RTL Design Sherpa
// Created: 2026-05-22

`timescale 1ns / 1ps

module axi4_dwidth_to_apb_chain #(
    parameter int S_AXI_DATA_WIDTH  = 64,
    parameter int APB_DATA_WIDTH    = 32,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int APB_ADDR_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Calculated
    localparam int S_STRB_WIDTH   = S_AXI_DATA_WIDTH / 8,
    localparam int APB_STRB_WIDTH = APB_DATA_WIDTH / 8
) (
    // Clock and Reset (single clock test config: pclk = aclk, presetn = aresetn)
    input  logic                          aclk,
    input  logic                          aresetn,
    input  logic                          pclk,
    input  logic                          presetn,

    //==========================================================================
    // Slave AXI4 Read Interface (wide)
    //==========================================================================

    // Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
    input  logic [7:0]                    s_axi_arlen,
    input  logic [2:0]                    s_axi_arsize,
    input  logic [1:0]                    s_axi_arburst,
    input  logic                          s_axi_arlock,
    input  logic [3:0]                    s_axi_arcache,
    input  logic [2:0]                    s_axi_arprot,
    input  logic [3:0]                    s_axi_arqos,
    input  logic [3:0]                    s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_aruser,
    input  logic                          s_axi_arvalid,
    output logic                          s_axi_arready,

    // Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [S_AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    //==========================================================================
    // Master APB Interface (narrow)
    //==========================================================================
    output logic                          m_apb_PSEL,
    output logic [APB_ADDR_WIDTH-1:0]     m_apb_PADDR,
    output logic                          m_apb_PENABLE,
    output logic                          m_apb_PWRITE,
    output logic [APB_DATA_WIDTH-1:0]     m_apb_PWDATA,
    output logic [APB_STRB_WIDTH-1:0]     m_apb_PSTRB,
    output logic [2:0]                    m_apb_PPROT,

    input  logic [APB_DATA_WIDTH-1:0]     m_apb_PRDATA,
    input  logic                          m_apb_PREADY,
    input  logic                          m_apb_PSLVERR
);

    //==========================================================================
    // Internal narrow AXI4 (between dwidth converter and APB shim)
    //==========================================================================
    logic [AXI_ID_WIDTH-1:0]              int_arid;
    logic [AXI_ADDR_WIDTH-1:0]            int_araddr;
    logic [7:0]                           int_arlen;
    logic [2:0]                           int_arsize;
    logic [1:0]                           int_arburst;
    logic                                 int_arlock;
    logic [3:0]                           int_arcache;
    logic [2:0]                           int_arprot;
    logic [3:0]                           int_arqos;
    logic [3:0]                           int_arregion;
    logic [AXI_USER_WIDTH-1:0]            int_aruser;
    logic                                 int_arvalid;
    logic                                 int_arready;

    logic [AXI_ID_WIDTH-1:0]              int_rid;
    logic [APB_DATA_WIDTH-1:0]            int_rdata;
    logic [1:0]                           int_rresp;
    logic                                 int_rlast;
    logic [AXI_USER_WIDTH-1:0]            int_ruser;
    logic                                 int_rvalid;
    logic                                 int_rready;

    //==========================================================================
    // Wide AXI4 (slave) → Narrow AXI4 (internal)
    //==========================================================================
    axi4_dwidth_converter_rd #(
        .S_AXI_DATA_WIDTH (S_AXI_DATA_WIDTH),
        .M_AXI_DATA_WIDTH (APB_DATA_WIDTH),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH)
    ) u_dwidth_rd (
        .aclk             (aclk),
        .aresetn          (aresetn),

        // Slave (wide) — module input
        .s_axi_arid       (s_axi_arid),
        .s_axi_araddr     (s_axi_araddr),
        .s_axi_arlen      (s_axi_arlen),
        .s_axi_arsize     (s_axi_arsize),
        .s_axi_arburst    (s_axi_arburst),
        .s_axi_arlock     (s_axi_arlock),
        .s_axi_arcache    (s_axi_arcache),
        .s_axi_arprot     (s_axi_arprot),
        .s_axi_arqos      (s_axi_arqos),
        .s_axi_arregion   (s_axi_arregion),
        .s_axi_aruser     (s_axi_aruser),
        .s_axi_arvalid    (s_axi_arvalid),
        .s_axi_arready    (s_axi_arready),

        .s_axi_rid        (s_axi_rid),
        .s_axi_rdata      (s_axi_rdata),
        .s_axi_rresp      (s_axi_rresp),
        .s_axi_rlast      (s_axi_rlast),
        .s_axi_ruser      (s_axi_ruser),
        .s_axi_rvalid     (s_axi_rvalid),
        .s_axi_rready     (s_axi_rready),

        // Master (narrow) — feeds internal AXI4 between modules
        .m_axi_arid       (int_arid),
        .m_axi_araddr     (int_araddr),
        .m_axi_arlen      (int_arlen),
        .m_axi_arsize     (int_arsize),
        .m_axi_arburst    (int_arburst),
        .m_axi_arlock     (int_arlock),
        .m_axi_arcache    (int_arcache),
        .m_axi_arprot     (int_arprot),
        .m_axi_arqos      (int_arqos),
        .m_axi_arregion   (int_arregion),
        .m_axi_aruser     (int_aruser),
        .m_axi_arvalid    (int_arvalid),
        .m_axi_arready    (int_arready),

        .m_axi_rid        (int_rid),
        .m_axi_rdata      (int_rdata),
        .m_axi_rresp      (int_rresp),
        .m_axi_rlast      (int_rlast),
        .m_axi_ruser      (int_ruser),
        .m_axi_rvalid     (int_rvalid),
        .m_axi_rready     (int_rready)
    );

    //==========================================================================
    // Narrow AXI4 (internal) → APB (master)
    //
    // Read-only configuration: tie off write channels at the shim's
    // slave port. We must drive bready / wvalid / awvalid as inactive
    // and accept the unused B and W outputs.
    //==========================================================================

    // Unused write-side outputs from the shim
    logic                       sink_awready;
    logic                       sink_wready;
    logic [AXI_ID_WIDTH-1:0]    sink_bid;
    logic [1:0]                 sink_bresp;
    logic [AXI_USER_WIDTH-1:0]  sink_buser;
    logic                       sink_bvalid;

    axi4_to_apb_shim #(
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH   (APB_DATA_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH),
        .APB_ADDR_WIDTH   (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH   (APB_DATA_WIDTH)
    ) u_axi2apb (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .pclk             (pclk),
        .presetn          (presetn),

        // Write channels — tie off (read-only chain)
        .s_axi_awid       ('0),
        .s_axi_awaddr     ('0),
        .s_axi_awlen      ('0),
        .s_axi_awsize     ('0),
        .s_axi_awburst    ('0),
        .s_axi_awlock     (1'b0),
        .s_axi_awcache    ('0),
        .s_axi_awprot     ('0),
        .s_axi_awqos      ('0),
        .s_axi_awregion   ('0),
        .s_axi_awuser     ('0),
        .s_axi_awvalid    (1'b0),
        .s_axi_awready    (sink_awready),

        .s_axi_wdata      ('0),
        .s_axi_wstrb      ('0),
        .s_axi_wlast      (1'b0),
        .s_axi_wuser      ('0),
        .s_axi_wvalid     (1'b0),
        .s_axi_wready     (sink_wready),

        .s_axi_bid        (sink_bid),
        .s_axi_bresp      (sink_bresp),
        .s_axi_buser      (sink_buser),
        .s_axi_bvalid     (sink_bvalid),
        .s_axi_bready     (1'b1),

        // Read channels — wired through from dwidth converter
        .s_axi_arid       (int_arid),
        .s_axi_araddr     (int_araddr),
        .s_axi_arlen      (int_arlen),
        .s_axi_arsize     (int_arsize),
        .s_axi_arburst    (int_arburst),
        .s_axi_arlock     (int_arlock),
        .s_axi_arcache    (int_arcache),
        .s_axi_arprot     (int_arprot),
        .s_axi_arqos      (int_arqos),
        .s_axi_arregion   (int_arregion),
        .s_axi_aruser     (int_aruser),
        .s_axi_arvalid    (int_arvalid),
        .s_axi_arready    (int_arready),

        .s_axi_rid        (int_rid),
        .s_axi_rdata      (int_rdata),
        .s_axi_rresp      (int_rresp),
        .s_axi_rlast      (int_rlast),
        .s_axi_ruser      (int_ruser),
        .s_axi_rvalid     (int_rvalid),
        .s_axi_rready     (int_rready),

        // APB master interface — module output
        .m_apb_PSEL       (m_apb_PSEL),
        .m_apb_PADDR      (m_apb_PADDR),
        .m_apb_PENABLE    (m_apb_PENABLE),
        .m_apb_PWRITE     (m_apb_PWRITE),
        .m_apb_PWDATA     (m_apb_PWDATA),
        .m_apb_PSTRB      (m_apb_PSTRB),
        .m_apb_PPROT      (m_apb_PPROT),
        .m_apb_PRDATA     (m_apb_PRDATA),
        .m_apb_PREADY     (m_apb_PREADY),
        .m_apb_PSLVERR    (m_apb_PSLVERR)
    );

    // Silence linter about unused write-side sink wires
    /* verilator lint_off UNUSED */
    wire _unused = &{1'b0, sink_awready, sink_wready, sink_bid, sink_bresp,
                     sink_buser, sink_bvalid};
    /* verilator lint_on UNUSED */

endmodule : axi4_dwidth_to_apb_chain
