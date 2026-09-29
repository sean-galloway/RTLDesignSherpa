// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
`timescale 1ns / 1ps
//
// wb4_to_axi4: Wishbone B4 slave in, AXI4 requester out.
//
// wb4_to_axil4 does the work -- wb4_slave, the in-order response merge of
// wb4_to_axil4_core, the axil4 masters -- and this wrapper promotes its
// AXI4-Lite face to full AXI4 the way an AXI4-Lite requester is promoted
// anywhere in the fabric: every transfer is one beat (AxLEN = 0, AxSIZE the
// full width, INCR, WLAST = 1), the ID is a constant (DEFAULT_ID), the
// attributes it cannot express are zero, and the response's ID and LAST are
// dropped. SEL rides WSTRB unchanged; Wishbone carries no protection bits,
// so AxPROT is AXIL_PROT.
//
// ERR to the requester when the AXI response is SLVERR or DECERR (the core
// maps resp[1]); Wishbone has no way to say which. RTY is never generated:
// AXI has no retry to translate.
//
// The bridge generator puts this in front of a master port declared
// protocol = "wb4" and feeds the ordinary AXI4 timing wrapper with its
// m_axi face -- the Wishbone counterpart of apb4_to_axi4.

module wb4_to_axi4
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int AXI_ID_WIDTH    = 1,
    parameter int AXI_USER_WIDTH  = 1,
    parameter logic [AXI_ID_WIDTH-1:0] DEFAULT_ID = '0,
    parameter logic [3:0] DEFAULT_CACHE = 4'b0000,
    parameter int CMD_DEPTH       = 2,
    parameter int RSP_DEPTH       = 2,
    parameter int MAX_OUTSTANDING = 16,
    parameter int CLASSIC         = 0,
    parameter int OUTSTANDING     = 1,
    parameter int SKID_DEPTH_AW   = 2,
    parameter int SKID_DEPTH_W    = 2,
    parameter int SKID_DEPTH_B    = 2,
    parameter int SKID_DEPTH_AR   = 2,
    parameter int SKID_DEPTH_R    = 2,
    parameter logic [2:0] AXIL_PROT = 3'b000,
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW / 8,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int UW  = AXI_USER_WIDTH,
    parameter int CTW = WB4_CTI_WIDTH,
    parameter int BTW = WB4_BTE_WIDTH
) (
    input  logic              aclk,
    input  logic              aresetn,

    // Wishbone B4 slave (the external requester drives these)
    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [AW-1:0]     s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [SW-1:0]     s_wb_SEL,
    input  logic [CTW-1:0]    s_wb_CTI,
    input  logic [BTW-1:0]    s_wb_BTE,
    output logic              s_wb_STALL,
    output logic              s_wb_ACK,
    output logic              s_wb_ERR,
    output logic              s_wb_RTY,
    output logic [DW-1:0]     s_wb_DAT_R,

    // AXI4 requester
    output logic [IW-1:0]     m_axi_awid,
    output logic [AW-1:0]     m_axi_awaddr,
    output logic [7:0]        m_axi_awlen,
    output logic [2:0]        m_axi_awsize,
    output logic [1:0]        m_axi_awburst,
    output logic              m_axi_awlock,
    output logic [3:0]        m_axi_awcache,
    output logic [2:0]        m_axi_awprot,
    output logic [3:0]        m_axi_awqos,
    output logic [3:0]        m_axi_awregion,
    output logic [UW-1:0]     m_axi_awuser,
    output logic              m_axi_awvalid,
    input  logic              m_axi_awready,
    output logic [DW-1:0]     m_axi_wdata,
    output logic [SW-1:0]     m_axi_wstrb,
    output logic              m_axi_wlast,
    output logic [UW-1:0]     m_axi_wuser,
    output logic              m_axi_wvalid,
    input  logic              m_axi_wready,
    input  logic [IW-1:0]     m_axi_bid,
    input  logic [1:0]        m_axi_bresp,
    input  logic [UW-1:0]     m_axi_buser,
    input  logic              m_axi_bvalid,
    output logic              m_axi_bready,
    output logic [IW-1:0]     m_axi_arid,
    output logic [AW-1:0]     m_axi_araddr,
    output logic [7:0]        m_axi_arlen,
    output logic [2:0]        m_axi_arsize,
    output logic [1:0]        m_axi_arburst,
    output logic              m_axi_arlock,
    output logic [3:0]        m_axi_arcache,
    output logic [2:0]        m_axi_arprot,
    output logic [3:0]        m_axi_arqos,
    output logic [3:0]        m_axi_arregion,
    output logic [UW-1:0]     m_axi_aruser,
    output logic              m_axi_arvalid,
    input  logic              m_axi_arready,
    input  logic [IW-1:0]     m_axi_rid,
    input  logic [DW-1:0]     m_axi_rdata,
    input  logic [1:0]        m_axi_rresp,
    input  logic              m_axi_rlast,
    input  logic [UW-1:0]     m_axi_ruser,
    input  logic              m_axi_rvalid,
    output logic              m_axi_rready
);

    localparam logic [2:0] AXSIZE = 3'($clog2(SW));

    // The single-beat AXI4 fields an AXI4-Lite requester cannot express.
    assign m_axi_awid     = DEFAULT_ID;
    assign m_axi_awlen    = 8'd0;
    assign m_axi_awsize   = AXSIZE;
    assign m_axi_awburst  = 2'b01;
    assign m_axi_awlock   = 1'b0;
    assign m_axi_awcache  = DEFAULT_CACHE;
    assign m_axi_awqos    = 4'd0;
    assign m_axi_awregion = 4'd0;
    assign m_axi_awuser   = '0;
    assign m_axi_wlast    = 1'b1;
    assign m_axi_wuser    = '0;
    assign m_axi_arid     = DEFAULT_ID;
    assign m_axi_arlen    = 8'd0;
    assign m_axi_arsize   = AXSIZE;
    assign m_axi_arburst  = 2'b01;
    assign m_axi_arlock   = 1'b0;
    assign m_axi_arcache  = DEFAULT_CACHE;
    assign m_axi_arqos    = 4'd0;
    assign m_axi_arregion = 4'd0;
    assign m_axi_aruser   = '0;

    // Response ID, USER and LAST have no Wishbone meaning: every read is
    // one beat, and with one ID in use the response can only be ours.
    wire unused_resp = &{1'b0, m_axi_bid, m_axi_buser, m_axi_rid, m_axi_ruser, m_axi_rlast};

    wb4_to_axil4 #(
        .ADDR_WIDTH      (AW),
        .DATA_WIDTH      (DW),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .MAX_OUTSTANDING (MAX_OUTSTANDING),
        .CLASSIC         (CLASSIC),
        .OUTSTANDING     (OUTSTANDING),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R),
        .AXIL_PROT       (AXIL_PROT)
    ) u_core (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .s_wb_CYC        (s_wb_CYC),
        .s_wb_STB        (s_wb_STB),
        .s_wb_WE         (s_wb_WE),
        .s_wb_ADR        (s_wb_ADR),
        .s_wb_DAT_W      (s_wb_DAT_W),
        .s_wb_SEL        (s_wb_SEL),
        .s_wb_CTI        (s_wb_CTI),
        .s_wb_BTE        (s_wb_BTE),
        .s_wb_STALL      (s_wb_STALL),
        .s_wb_ACK        (s_wb_ACK),
        .s_wb_ERR        (s_wb_ERR),
        .s_wb_RTY        (s_wb_RTY),
        .s_wb_DAT_R      (s_wb_DAT_R),
        .m_axil_awaddr   (m_axi_awaddr),
        .m_axil_awprot   (m_axi_awprot),
        .m_axil_awvalid  (m_axi_awvalid),
        .m_axil_awready  (m_axi_awready),
        .m_axil_wdata    (m_axi_wdata),
        .m_axil_wstrb    (m_axi_wstrb),
        .m_axil_wvalid   (m_axi_wvalid),
        .m_axil_wready   (m_axi_wready),
        .m_axil_bresp    (m_axi_bresp),
        .m_axil_bvalid   (m_axi_bvalid),
        .m_axil_bready   (m_axi_bready),
        .m_axil_araddr   (m_axi_araddr),
        .m_axil_arprot   (m_axi_arprot),
        .m_axil_arvalid  (m_axi_arvalid),
        .m_axil_arready  (m_axi_arready),
        .m_axil_rdata    (m_axi_rdata),
        .m_axil_rresp    (m_axi_rresp),
        .m_axil_rvalid   (m_axi_rvalid),
        .m_axil_rready   (m_axi_rready),
        /* verilator lint_off PINCONNECTEMPTY */
        .busy            ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : wb4_to_axi4
