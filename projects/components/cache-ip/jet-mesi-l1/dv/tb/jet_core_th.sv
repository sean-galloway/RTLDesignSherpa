// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_core_th
// Purpose:
//   Test harness for the jet_top full-core bring-up (Task 8).  Pure
//   structural wrapper: the DUT boundary IS jet_top's external shape
//   (CPU GAXI slave, monlite-wrapped AXI4 m_axi_* masters, ACE snoop
//   responder, MonBus, D-8 coherence sideband, status).  The cocotb TB
//   (dv/tbclasses/jet_core_tb.py) closes the memory side with the house
//   AXI4 slave responders, the CPU side with the GAXI BFM pair, and the
//   ACE port with the house snoop master; its event-stream scoreboard
//   taps jet_top's internals with read-only hierarchical references (the
//   amber_core / pair-rig sanctioned pattern).
//
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-29

`timescale 1ns / 1ps

//==============================================================================
// Module: jet_core_th
//==============================================================================

module jet_core_th
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int WAYS           = AMBER_WAYS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int REPL_POLICY    = int'(AMBER_REPL_LRU),
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int MSHR_COUNT     = jet_pkg::MSHR_COUNT,
    parameter int VICTIM_DEPTH   = jet_pkg::VICTIM_DEPTH,
    localparam int STRB_W        = BUS_WIDTH / 8,
    localparam int IW            = AXI_ID_WIDTH,
    localparam int UW            = AXI_USER_WIDTH,
    localparam int CPU_REQ_W     = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W     = BUS_WIDTH
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // CPU GAXI slave
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // AXI4 read master
    output logic [IW-1:0]               m_axi_arid,
    output logic [ADDR_WIDTH-1:0]       m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arlock,
    output logic [3:0]                  m_axi_arcache,
    output logic [2:0]                  m_axi_arprot,
    output logic [3:0]                  m_axi_arqos,
    output logic [3:0]                  m_axi_arregion,
    output logic [UW-1:0]               m_axi_aruser,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [BUS_WIDTH-1:0]        m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [UW-1:0]               m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    // AXI4 write master
    output logic [IW-1:0]               m_axi_awid,
    output logic [ADDR_WIDTH-1:0]       m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [UW-1:0]               m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,
    output logic [BUS_WIDTH-1:0]        m_axi_wdata,
    output logic [STRB_W-1:0]           m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [UW-1:0]               m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,
    input  logic [IW-1:0]               m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [UW-1:0]               m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    // ACE snoop responder
    input  logic [ADDR_WIDTH-1:0]       m_axi_acaddr,
    input  logic [3:0]                  m_axi_acsnoop,
    input  logic [2:0]                  m_axi_acprot,
    input  logic                        m_axi_acvalid,
    output logic                        m_axi_acready,
    output logic [AMBER_CRRESP_WIDTH-1:0] m_axi_crresp,
    output logic                        m_axi_crvalid,
    input  logic                        m_axi_crready,
    output logic [BUS_WIDTH-1:0]        m_axi_cddata,
    output logic                        m_axi_cdlast,
    output logic                        m_axi_cdvalid,
    input  logic                        m_axi_cdready,

    // D-8 coherence sideband + MonBus + status
    output logic                        coh_req_valid,
    output logic [ADDR_WIDTH-1:0]       coh_req_addr,
    output logic [2:0]                  coh_req_type,
    input  logic [63:0]                 i_mon_time,
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp,
    output logic                        init_busy,
    output logic [3:0]                  ctrl_state,
    output logic                        busy
);

    jet_top #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (1'b1),
        .MSHR_COUNT     (MSHR_COUNT),
        .VICTIM_DEPTH   (VICTIM_DEPTH)
    ) u_top (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .cpu_req_wr_valid(cpu_req_wr_valid),
        .cpu_req_wr_ready(cpu_req_wr_ready),
        .cpu_req_wr_data (cpu_req_wr_data),
        .cpu_rsp_rd_valid(cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready(cpu_rsp_rd_ready),
        .cpu_rsp_rd_data (cpu_rsp_rd_data),
        .m_axi_arid      (m_axi_arid),
        .m_axi_araddr    (m_axi_araddr),
        .m_axi_arlen     (m_axi_arlen),
        .m_axi_arsize    (m_axi_arsize),
        .m_axi_arburst   (m_axi_arburst),
        .m_axi_arlock    (m_axi_arlock),
        .m_axi_arcache   (m_axi_arcache),
        .m_axi_arprot    (m_axi_arprot),
        .m_axi_arqos     (m_axi_arqos),
        .m_axi_arregion  (m_axi_arregion),
        .m_axi_aruser    (m_axi_aruser),
        .m_axi_arvalid   (m_axi_arvalid),
        .m_axi_arready   (m_axi_arready),
        .m_axi_rid       (m_axi_rid),
        .m_axi_rdata     (m_axi_rdata),
        .m_axi_rresp     (m_axi_rresp),
        .m_axi_rlast     (m_axi_rlast),
        .m_axi_ruser     (m_axi_ruser),
        .m_axi_rvalid    (m_axi_rvalid),
        .m_axi_rready    (m_axi_rready),
        .m_axi_awid      (m_axi_awid),
        .m_axi_awaddr    (m_axi_awaddr),
        .m_axi_awlen     (m_axi_awlen),
        .m_axi_awsize    (m_axi_awsize),
        .m_axi_awburst   (m_axi_awburst),
        .m_axi_awlock    (m_axi_awlock),
        .m_axi_awcache   (m_axi_awcache),
        .m_axi_awprot    (m_axi_awprot),
        .m_axi_awqos     (m_axi_awqos),
        .m_axi_awregion  (m_axi_awregion),
        .m_axi_awuser    (m_axi_awuser),
        .m_axi_awvalid   (m_axi_awvalid),
        .m_axi_awready   (m_axi_awready),
        .m_axi_wdata     (m_axi_wdata),
        .m_axi_wstrb     (m_axi_wstrb),
        .m_axi_wlast     (m_axi_wlast),
        .m_axi_wuser     (m_axi_wuser),
        .m_axi_wvalid    (m_axi_wvalid),
        .m_axi_wready    (m_axi_wready),
        .m_axi_bid       (m_axi_bid),
        .m_axi_bresp     (m_axi_bresp),
        .m_axi_buser     (m_axi_buser),
        .m_axi_bvalid    (m_axi_bvalid),
        .m_axi_bready    (m_axi_bready),
        .m_axi_acaddr    (m_axi_acaddr),
        .m_axi_acsnoop   (m_axi_acsnoop),
        .m_axi_acprot    (m_axi_acprot),
        .m_axi_acvalid   (m_axi_acvalid),
        .m_axi_acready   (m_axi_acready),
        .m_axi_crresp    (m_axi_crresp),
        .m_axi_crvalid   (m_axi_crvalid),
        .m_axi_crready   (m_axi_crready),
        .m_axi_cddata    (m_axi_cddata),
        .m_axi_cdlast    (m_axi_cdlast),
        .m_axi_cdvalid   (m_axi_cdvalid),
        .m_axi_cdready   (m_axi_cdready),
        .coh_req_valid   (coh_req_valid),
        .coh_req_addr    (coh_req_addr),
        .coh_req_type    (coh_req_type),
        .i_mon_time      (i_mon_time),
        .mon_valid       (mon_valid),
        .mon_ready       (mon_ready),
        .mon_packet      (mon_packet),
        .mon_timestamp   (mon_timestamp),
        .init_busy       (init_busy),
        .ctrl_state      (ctrl_state),
        .busy            (busy)
    );

endmodule : jet_core_th
