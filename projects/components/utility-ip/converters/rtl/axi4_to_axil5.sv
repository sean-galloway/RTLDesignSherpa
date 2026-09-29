// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
`timescale 1ns / 1ps
//
// axi4_to_axil5: AXI4 slave -> AXI5-Lite master, read and write.
//
// Pairs axi4_to_axil5_rd and axi4_to_axil5_wr, exactly as axi4_to_axil4
// pairs its two halves. There is no logic here beyond the two
// instantiations: every conversion decision lives in the halves, and every
// AXI5-Lite sideband decision (what is forwarded, tied, or terminated) is
// documented in their headers rather than restated here.
//
// The AXI4 slave surface is the FULL AXI4 interface, not a subset. A master
// upstream of this converter may be feeding a fabric whose other branches
// reach AXI4 slaves, so nothing is dropped from the boundary on the grounds
// that this particular downstream path cannot use it.
//
// Author: sean galloway
// Created: 2026-09-05

module axi4_to_axil5 #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // AXI5-Lite optional signal groups. Default OFF: with every group
    // disabled this converter presents the same behaviour as axi4_to_axil4
    // with the sideband ports tied off, which is what an integrator
    // migrating an AXI4-Lite slave to an AXI5-Lite port starts from.
    // Only LOCK and USER get an ENABLE_ knob, because only they have an AXI4
    // source to gate. TRACE / LOOP / MPAM / MECID / NSAID / POISON are tied
    // to zero unconditionally -- an ENABLE_ for those would be a parameter
    // that cannot change the design's behaviour, which is worse than no
    // parameter: a reader sets it and believes something happened. The
    // widths stay, because they set the port shape.
    parameter bit ENABLE_LOCK       = 1'b0,
    parameter bit ENABLE_USER       = 1'b0,

    parameter int USER_WIDTH        = 1,
    parameter int LOOP_WIDTH        = 1,
    parameter int MPAM_WIDTH        = 11,
    parameter int MECID_WIDTH       = 16,
    parameter int NSAID_WIDTH       = 4,

    localparam int STRB_WIDTH   = AXI_DATA_WIDTH / 8,
    localparam int POISON_WIDTH = (AXI_DATA_WIDTH / 64) > 0
                                    ? (AXI_DATA_WIDTH / 64) : 1
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Interface (input, full protocol)
    //==========================================================================
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

    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

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

    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    //==========================================================================
    // Master AXI5-Lite Interface (output)
    //==========================================================================
    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_araddr,
    output logic [2:0]                  m_axil_arprot,
    output logic                        m_axil_arvalid,
    input  logic                        m_axil_arready,

    input  logic [AXI_DATA_WIDTH-1:0]   m_axil_rdata,
    input  logic [1:0]                  m_axil_rresp,
    input  logic                        m_axil_rvalid,
    output logic                        m_axil_rready,

    output logic [AXI_ADDR_WIDTH-1:0]   m_axil_awaddr,
    output logic [2:0]                  m_axil_awprot,
    output logic                        m_axil_awvalid,
    input  logic                        m_axil_awready,

    output logic [AXI_DATA_WIDTH-1:0]   m_axil_wdata,
    output logic [STRB_WIDTH-1:0]       m_axil_wstrb,
    output logic                        m_axil_wvalid,
    input  logic                        m_axil_wready,

    input  logic [1:0]                  m_axil_bresp,
    input  logic                        m_axil_bvalid,
    output logic                        m_axil_bready,

    // ---- AXI5-Lite sideband, read --------------------------------------
    output logic                        m_axil_arlock,
    output logic [USER_WIDTH-1:0]       m_axil_aruser,
    output logic [LOOP_WIDTH-1:0]       m_axil_arloop,
    output logic [MPAM_WIDTH-1:0]       m_axil_armpam,
    output logic [MECID_WIDTH-1:0]      m_axil_armecid,
    output logic [NSAID_WIDTH-1:0]      m_axil_arnsaid,
    output logic                        m_axil_artrace,

    input  logic [USER_WIDTH-1:0]       m_axil_ruser,
    input  logic [LOOP_WIDTH-1:0]       m_axil_rloop,
    input  logic                        m_axil_rtrace,
    input  logic [POISON_WIDTH-1:0]     m_axil_rpoison,

    // ---- AXI5-Lite sideband, write -------------------------------------
    output logic                        m_axil_awlock,
    output logic [USER_WIDTH-1:0]       m_axil_awuser,
    output logic [LOOP_WIDTH-1:0]       m_axil_awloop,
    output logic [MPAM_WIDTH-1:0]       m_axil_awmpam,
    output logic [MECID_WIDTH-1:0]      m_axil_awmecid,
    output logic [NSAID_WIDTH-1:0]      m_axil_awnsaid,
    output logic                        m_axil_awtrace,

    output logic [USER_WIDTH-1:0]       m_axil_wuser,
    output logic [POISON_WIDTH-1:0]     m_axil_wpoison,

    input  logic [USER_WIDTH-1:0]       m_axil_buser,
    input  logic [LOOP_WIDTH-1:0]       m_axil_bloop,
    input  logic                        m_axil_btrace
);

    axi4_to_axil5_rd #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .ENABLE_LOCK    (ENABLE_LOCK),
        .ENABLE_USER    (ENABLE_USER),
        .USER_WIDTH     (USER_WIDTH),
        .LOOP_WIDTH     (LOOP_WIDTH),
        .MPAM_WIDTH     (MPAM_WIDTH),
        .MECID_WIDTH    (MECID_WIDTH),
        .NSAID_WIDTH    (NSAID_WIDTH)
    ) u_rd_converter (
        .aclk           (aclk),
        .aresetn        (aresetn),

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

        .m_axil_araddr  (m_axil_araddr),
        .m_axil_arprot  (m_axil_arprot),
        .m_axil_arvalid (m_axil_arvalid),
        .m_axil_arready (m_axil_arready),
        .m_axil_rdata   (m_axil_rdata),
        .m_axil_rresp   (m_axil_rresp),
        .m_axil_rvalid  (m_axil_rvalid),
        .m_axil_rready  (m_axil_rready),

        .m_axil_arlock  (m_axil_arlock),
        .m_axil_aruser  (m_axil_aruser),
        .m_axil_arloop  (m_axil_arloop),
        .m_axil_armpam  (m_axil_armpam),
        .m_axil_armecid (m_axil_armecid),
        .m_axil_arnsaid (m_axil_arnsaid),
        .m_axil_artrace (m_axil_artrace),
        .m_axil_ruser   (m_axil_ruser),
        .m_axil_rloop   (m_axil_rloop),
        .m_axil_rtrace  (m_axil_rtrace),
        .m_axil_rpoison (m_axil_rpoison)
    );

    axi4_to_axil5_wr #(
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .ENABLE_LOCK    (ENABLE_LOCK),
        .ENABLE_USER    (ENABLE_USER),
        .USER_WIDTH     (USER_WIDTH),
        .LOOP_WIDTH     (LOOP_WIDTH),
        .MPAM_WIDTH     (MPAM_WIDTH),
        .MECID_WIDTH    (MECID_WIDTH),
        .NSAID_WIDTH    (NSAID_WIDTH)
    ) u_wr_converter (
        .aclk           (aclk),
        .aresetn        (aresetn),

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

        .m_axil_awaddr  (m_axil_awaddr),
        .m_axil_awprot  (m_axil_awprot),
        .m_axil_awvalid (m_axil_awvalid),
        .m_axil_awready (m_axil_awready),
        .m_axil_wdata   (m_axil_wdata),
        .m_axil_wstrb   (m_axil_wstrb),
        .m_axil_wvalid  (m_axil_wvalid),
        .m_axil_wready  (m_axil_wready),
        .m_axil_bresp   (m_axil_bresp),
        .m_axil_bvalid  (m_axil_bvalid),
        .m_axil_bready  (m_axil_bready),

        .m_axil_awlock  (m_axil_awlock),
        .m_axil_awuser  (m_axil_awuser),
        .m_axil_awloop  (m_axil_awloop),
        .m_axil_awmpam  (m_axil_awmpam),
        .m_axil_awmecid (m_axil_awmecid),
        .m_axil_awnsaid (m_axil_awnsaid),
        .m_axil_awtrace (m_axil_awtrace),
        .m_axil_wuser   (m_axil_wuser),
        .m_axil_wpoison (m_axil_wpoison),
        .m_axil_buser   (m_axil_buser),
        .m_axil_bloop   (m_axil_bloop),
        .m_axil_btrace  (m_axil_btrace)
    );

endmodule : axi4_to_axil5
