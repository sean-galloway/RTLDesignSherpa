// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
`timescale 1ns / 1ps
//
// apb4_to_axi4: APB4 completer in, AXI4 requester out.
//
// The mirror of axi4_to_apb4_shim. An APB4 requester (a small CPU, a debug
// port, a register sequencer) drives this module's s_apb_* completer
// surface and every transfer comes out as one single-beat AXI4 transaction
// on m_axi_*. Two proven pieces, no new protocol logic:
//
//   apb4_slave          PSEL/PENABLE/PREADY handshake, skid-buffered
//                       cmd/rsp pair, orphan-response guard
//   apb_cmdrsp_to_axi4  one command -> one AXI4 write or read -> one rsp
//
// APB4 has no USER signals, so the AXI USER fields are driven to zero and
// the returned ones are dropped here. The bridge generator instantiates
// this for a master port with protocol = "apb".

module apb4_to_axi4 #(
    parameter int APB_ADDR_WIDTH  = 32,
    parameter int APB_DATA_WIDTH  = 32,
    parameter int AXI_ID_WIDTH    = 1,
    parameter int AXI_USER_WIDTH  = 1,
    parameter logic [AXI_ID_WIDTH-1:0] DEFAULT_ID = '0,
    // Skid depth inside apb4_slave (cmd and rsp).
    parameter int DEPTH           = 2,
    parameter int AW = APB_ADDR_WIDTH,
    parameter int DW = APB_DATA_WIDTH,
    parameter int SW = APB_DATA_WIDTH / 8,
    parameter int IW = AXI_ID_WIDTH,
    parameter int UW = AXI_USER_WIDTH
) (
    input  logic            aclk,
    input  logic            aresetn,

    // APB4 completer (external requester drives these)
    input  logic            s_apb_PSEL,
    input  logic            s_apb_PENABLE,
    output logic            s_apb_PREADY,
    input  logic [AW-1:0]   s_apb_PADDR,
    input  logic            s_apb_PWRITE,
    input  logic [DW-1:0]   s_apb_PWDATA,
    input  logic [SW-1:0]   s_apb_PSTRB,
    input  logic [2:0]      s_apb_PPROT,
    output logic [DW-1:0]   s_apb_PRDATA,
    output logic            s_apb_PSLVERR,

    // AXI4 requester
    output logic [IW-1:0]   m_axi_awid,
    output logic [AW-1:0]   m_axi_awaddr,
    output logic [7:0]      m_axi_awlen,
    output logic [2:0]      m_axi_awsize,
    output logic [1:0]      m_axi_awburst,
    output logic            m_axi_awlock,
    output logic [3:0]      m_axi_awcache,
    output logic [2:0]      m_axi_awprot,
    output logic [3:0]      m_axi_awqos,
    output logic [3:0]      m_axi_awregion,
    output logic [UW-1:0]   m_axi_awuser,
    output logic            m_axi_awvalid,
    input  logic            m_axi_awready,

    output logic [DW-1:0]   m_axi_wdata,
    output logic [SW-1:0]   m_axi_wstrb,
    output logic            m_axi_wlast,
    output logic [UW-1:0]   m_axi_wuser,
    output logic            m_axi_wvalid,
    input  logic            m_axi_wready,

    input  logic [IW-1:0]   m_axi_bid,
    input  logic [1:0]      m_axi_bresp,
    input  logic [UW-1:0]   m_axi_buser,
    input  logic            m_axi_bvalid,
    output logic            m_axi_bready,

    output logic [IW-1:0]   m_axi_arid,
    output logic [AW-1:0]   m_axi_araddr,
    output logic [7:0]      m_axi_arlen,
    output logic [2:0]      m_axi_arsize,
    output logic [1:0]      m_axi_arburst,
    output logic            m_axi_arlock,
    output logic [3:0]      m_axi_arcache,
    output logic [2:0]      m_axi_arprot,
    output logic [3:0]      m_axi_arqos,
    output logic [3:0]      m_axi_arregion,
    output logic [UW-1:0]   m_axi_aruser,
    output logic            m_axi_arvalid,
    input  logic            m_axi_arready,

    input  logic [IW-1:0]   m_axi_rid,
    input  logic [DW-1:0]   m_axi_rdata,
    input  logic [1:0]      m_axi_rresp,
    input  logic            m_axi_rlast,
    input  logic [UW-1:0]   m_axi_ruser,
    input  logic            m_axi_rvalid,
    output logic            m_axi_rready
);

    logic            w_cmd_valid;
    logic            w_cmd_ready;
    logic            w_cmd_pwrite;
    logic [AW-1:0]   w_cmd_paddr;
    logic [DW-1:0]   w_cmd_pwdata;
    logic [SW-1:0]   w_cmd_pstrb;
    logic [2:0]      w_cmd_pprot;
    logic            w_rsp_valid;
    logic            w_rsp_ready;
    logic [DW-1:0]   w_rsp_prdata;
    logic            w_rsp_pslverr;

    apb4_slave #(
        .ADDR_WIDTH (AW),
        .DATA_WIDTH (DW),
        .STRB_WIDTH (SW),
        .PROT_WIDTH (3),
        .DEPTH      (DEPTH)
    ) u_apb4_slave (
        .pclk          (aclk),
        .presetn       (aresetn),
        .s_apb_PSEL    (s_apb_PSEL),
        .s_apb_PENABLE (s_apb_PENABLE),
        .s_apb_PREADY  (s_apb_PREADY),
        .s_apb_PADDR   (s_apb_PADDR),
        .s_apb_PWRITE  (s_apb_PWRITE),
        .s_apb_PWDATA  (s_apb_PWDATA),
        .s_apb_PSTRB   (s_apb_PSTRB),
        .s_apb_PPROT   (s_apb_PPROT),
        .s_apb_PRDATA  (s_apb_PRDATA),
        .s_apb_PSLVERR (s_apb_PSLVERR),
        .cmd_valid     (w_cmd_valid),
        .cmd_ready     (w_cmd_ready),
        .cmd_pwrite    (w_cmd_pwrite),
        .cmd_paddr     (w_cmd_paddr),
        .cmd_pwdata    (w_cmd_pwdata),
        .cmd_pstrb     (w_cmd_pstrb),
        .cmd_pprot     (w_cmd_pprot),
        .rsp_valid     (w_rsp_valid),
        .rsp_ready     (w_rsp_ready),
        .rsp_prdata    (w_rsp_prdata),
        .rsp_pslverr   (w_rsp_pslverr)
    );

    apb_cmdrsp_to_axi4 #(
        .AXI_ID_WIDTH   (IW),
        .AXI_ADDR_WIDTH (AW),
        .AXI_DATA_WIDTH (DW),
        .AXI_USER_WIDTH (UW),
        .DEFAULT_ID     (DEFAULT_ID)
    ) u_requester (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .cmd_valid      (w_cmd_valid),
        .cmd_ready      (w_cmd_ready),
        .cmd_pwrite     (w_cmd_pwrite),
        .cmd_paddr      (w_cmd_paddr),
        .cmd_pwdata     (w_cmd_pwdata),
        .cmd_pstrb      (w_cmd_pstrb),
        .cmd_pprot      (w_cmd_pprot),
        .cmd_auser      ('0),
        .cmd_wuser      ('0),
        .rsp_valid      (w_rsp_valid),
        .rsp_ready      (w_rsp_ready),
        .rsp_prdata     (w_rsp_prdata),
        .rsp_pslverr    (w_rsp_pslverr),
        /* verilator lint_off PINCONNECTEMPTY */
        .rsp_ruser      (),
        .rsp_buser      (),
        /* verilator lint_on PINCONNECTEMPTY */
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
        .m_axi_bready   (m_axi_bready),
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

endmodule : apb4_to_axi4
