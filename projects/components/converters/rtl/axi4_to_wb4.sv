// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
`timescale 1ns / 1ps
//
// axi4_to_wb4: full AXI4 slave in, Wishbone B4 master out.
//
// Composition, no new protocol logic:
//
//   axi4_to_axil4_wr + axi4_to_axil4_rd   burst decomposition, response
//                                          folding, one AXI4-Lite beat per
//                                          AXI4 beat
//   axil4_to_wb4                           the five AXI4-Lite channels to
//                                          one Wishbone command stream and
//                                          back (in-order termination)
//
// Every AXI4 beat becomes one Wishbone transfer (WE from the channel, SEL
// from WSTRB, ADR the beat's address). Termination maps ACK -> OKAY,
// ERR -> SLVERR, RTY -> RTY_RESP (SLVERR by default: AXI has no retry, so
// unless a wb4_retry sits in front of the completer the requester sees an
// error). Same address and data width on both sides; the bridge puts its
// width converters in front when they differ.
//
// The bridge generator instantiates this for a slave port declared
// protocol = "wb4"; it is the Wishbone counterpart of axi4_to_apb4_shim.
// CLASSIC selects B4 standard mode on the Wishbone side (match the peer).

module axi4_to_wb4 #(
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 2,
    parameter int SKID_DEPTH_B      = 2,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 2,
    parameter int CMD_DEPTH         = 4,
    parameter int RSP_DEPTH         = 4,
    parameter int SIDE_DEPTH        = 8,
    parameter int CLASSIC           = 0,
    parameter logic [1:0] RTY_RESP  = 2'b10,
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_DATA_WIDTH / 8
) (
    input  logic                aclk,
    input  logic                aresetn,

    // AXI4 slave (from the fabric)
    input  logic [IW-1:0]       s_axi_awid,
    input  logic [AW-1:0]       s_axi_awaddr,
    input  logic [7:0]          s_axi_awlen,
    input  logic [2:0]          s_axi_awsize,
    input  logic [1:0]          s_axi_awburst,
    input  logic                s_axi_awlock,
    input  logic [3:0]          s_axi_awcache,
    input  logic [2:0]          s_axi_awprot,
    input  logic [3:0]          s_axi_awqos,
    input  logic [3:0]          s_axi_awregion,
    input  logic [UW-1:0]       s_axi_awuser,
    input  logic                s_axi_awvalid,
    output logic                s_axi_awready,
    input  logic [DW-1:0]       s_axi_wdata,
    input  logic [SW-1:0]       s_axi_wstrb,
    input  logic                s_axi_wlast,
    input  logic [UW-1:0]       s_axi_wuser,
    input  logic                s_axi_wvalid,
    output logic                s_axi_wready,
    output logic [IW-1:0]       s_axi_bid,
    output logic [1:0]          s_axi_bresp,
    output logic [UW-1:0]       s_axi_buser,
    output logic                s_axi_bvalid,
    input  logic                s_axi_bready,
    input  logic [IW-1:0]       s_axi_arid,
    input  logic [AW-1:0]       s_axi_araddr,
    input  logic [7:0]          s_axi_arlen,
    input  logic [2:0]          s_axi_arsize,
    input  logic [1:0]          s_axi_arburst,
    input  logic                s_axi_arlock,
    input  logic [3:0]          s_axi_arcache,
    input  logic [2:0]          s_axi_arprot,
    input  logic [3:0]          s_axi_arqos,
    input  logic [3:0]          s_axi_arregion,
    input  logic [UW-1:0]       s_axi_aruser,
    input  logic                s_axi_arvalid,
    output logic                s_axi_arready,
    output logic [IW-1:0]       s_axi_rid,
    output logic [DW-1:0]       s_axi_rdata,
    output logic [1:0]          s_axi_rresp,
    output logic                s_axi_rlast,
    output logic [UW-1:0]       s_axi_ruser,
    output logic                s_axi_rvalid,
    input  logic                s_axi_rready,

    // Wishbone B4 master (to the external completer)
    output logic                m_wb_CYC,
    output logic                m_wb_STB,
    output logic                m_wb_WE,
    output logic [AW-1:0]       m_wb_ADR,
    output logic [DW-1:0]       m_wb_DAT_W,
    output logic [SW-1:0]       m_wb_SEL,
    output logic [wb4_pkg::WB4_CTI_WIDTH-1:0] m_wb_CTI,
    output logic [wb4_pkg::WB4_BTE_WIDTH-1:0] m_wb_BTE,
    input  logic                m_wb_STALL,
    input  logic                m_wb_ACK,
    input  logic                m_wb_ERR,
    input  logic                m_wb_RTY,
    input  logic [DW-1:0]       m_wb_DAT_R
);

    // AXI4-Lite between the decomposers and the Wishbone converter
    logic [AW-1:0]   w_axil_awaddr;
    logic [2:0]      w_axil_awprot;
    logic            w_axil_awvalid;
    logic            w_axil_awready;
    logic [DW-1:0]   w_axil_wdata;
    logic [SW-1:0]   w_axil_wstrb;
    logic            w_axil_wvalid;
    logic            w_axil_wready;
    logic [1:0]      w_axil_bresp;
    logic            w_axil_bvalid;
    logic            w_axil_bready;
    logic [AW-1:0]   w_axil_araddr;
    logic [2:0]      w_axil_arprot;
    logic            w_axil_arvalid;
    logic            w_axil_arready;
    logic [DW-1:0]   w_axil_rdata;
    logic [1:0]      w_axil_rresp;
    logic            w_axil_rvalid;
    logic            w_axil_rready;

    axi4_to_axil4_wr #(
        .AXI_ID_WIDTH   (IW),
        .AXI_ADDR_WIDTH (AW),
        .AXI_DATA_WIDTH (DW),
        .AXI_USER_WIDTH (UW)
    ) u_wr (
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
        .m_axil_awaddr  (w_axil_awaddr),
        .m_axil_awprot  (w_axil_awprot),
        .m_axil_awvalid (w_axil_awvalid),
        .m_axil_awready (w_axil_awready),
        .m_axil_wdata   (w_axil_wdata),
        .m_axil_wstrb   (w_axil_wstrb),
        .m_axil_wvalid  (w_axil_wvalid),
        .m_axil_wready  (w_axil_wready),
        .m_axil_bresp   (w_axil_bresp),
        .m_axil_bvalid  (w_axil_bvalid),
        .m_axil_bready  (w_axil_bready)
    );

    axi4_to_axil4_rd #(
        .AXI_ID_WIDTH   (IW),
        .AXI_ADDR_WIDTH (AW),
        .AXI_DATA_WIDTH (DW),
        .AXI_USER_WIDTH (UW)
    ) u_rd (
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
        .m_axil_araddr  (w_axil_araddr),
        .m_axil_arprot  (w_axil_arprot),
        .m_axil_arvalid (w_axil_arvalid),
        .m_axil_arready (w_axil_arready),
        .m_axil_rdata   (w_axil_rdata),
        .m_axil_rresp   (w_axil_rresp),
        .m_axil_rvalid  (w_axil_rvalid),
        .m_axil_rready  (w_axil_rready)
    );

    axil4_to_wb4 #(
        .ADDR_WIDTH     (AW),
        .DATA_WIDTH     (DW),
        .SKID_DEPTH_AW  (SKID_DEPTH_AW),
        .SKID_DEPTH_W   (SKID_DEPTH_W),
        .SKID_DEPTH_B   (SKID_DEPTH_B),
        .SKID_DEPTH_AR  (SKID_DEPTH_AR),
        .SKID_DEPTH_R   (SKID_DEPTH_R),
        .CMD_DEPTH      (CMD_DEPTH),
        .RSP_DEPTH      (RSP_DEPTH),
        .SIDE_DEPTH     (SIDE_DEPTH),
        .CLASSIC        (CLASSIC),
        .RTY_RESP       (RTY_RESP)
    ) u_wb (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .s_axil_awaddr  (w_axil_awaddr),
        .s_axil_awprot  (w_axil_awprot),
        .s_axil_awvalid (w_axil_awvalid),
        .s_axil_awready (w_axil_awready),
        .s_axil_wdata   (w_axil_wdata),
        .s_axil_wstrb   (w_axil_wstrb),
        .s_axil_wvalid  (w_axil_wvalid),
        .s_axil_wready  (w_axil_wready),
        .s_axil_bresp   (w_axil_bresp),
        .s_axil_bvalid  (w_axil_bvalid),
        .s_axil_bready  (w_axil_bready),
        .s_axil_araddr  (w_axil_araddr),
        .s_axil_arprot  (w_axil_arprot),
        .s_axil_arvalid (w_axil_arvalid),
        .s_axil_arready (w_axil_arready),
        .s_axil_rdata   (w_axil_rdata),
        .s_axil_rresp   (w_axil_rresp),
        .s_axil_rvalid  (w_axil_rvalid),
        .s_axil_rready  (w_axil_rready),
        .m_wb_CYC       (m_wb_CYC),
        .m_wb_STB       (m_wb_STB),
        .m_wb_WE        (m_wb_WE),
        .m_wb_ADR       (m_wb_ADR),
        .m_wb_DAT_W     (m_wb_DAT_W),
        .m_wb_SEL       (m_wb_SEL),
        .m_wb_CTI       (m_wb_CTI),
        .m_wb_BTE       (m_wb_BTE),
        .m_wb_STALL     (m_wb_STALL),
        .m_wb_ACK       (m_wb_ACK),
        .m_wb_ERR       (m_wb_ERR),
        .m_wb_RTY       (m_wb_RTY),
        .m_wb_DAT_R     (m_wb_DAT_R),
        /* verilator lint_off PINCONNECTEMPTY */
        .busy           ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi4_to_wb4
