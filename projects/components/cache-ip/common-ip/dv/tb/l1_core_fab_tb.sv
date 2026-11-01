// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_core_fab_tb
// Purpose:
//   Testbench wrapper for the restructured l1_core (cache-ip plane
//   restructure, Task 1): composes the aggregate l1_core (u_core) with
//   the ACE snoop responder (u_snoop) so that test_l1_core's stimulus
//   and hierarchical taps survive unchanged. The wrapper's top-level
//   ports are IDENTICAL to the pre-restructure l1_core, including the
//   ACE snoop responder pins; internally the snoop responder is wired
//   to l1_core's new fabric seam bundle.
//
//   This is a test-side harness (approved `_tb` suffix): pure wiring,
//   no new control logic.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/01_architecture.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

//==============================================================================
// Module: l1_core_fab_tb
//==============================================================================
// Description:
//   Preserves the l1_core external contract for the existing DV suite by
//   re-instantiating the snoop responder that moved out of the core in
//   Task 1. The fabric seam (ctrl_snoop_*, ctrl_crresp, ctrl_cd*) is
//   internal to this wrapper; the outside world sees the same ACE snoop
//   port as before.
//
//------------------------------------------------------------------------------
// Parameters: same geometry contract as l1_core.
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset domain (clk / rst_n).
//   - This wrapper deliberately does NOT re-export hierarchical taps:
//     the testbench reaches through `u_core` for control/repl/tag and
//     through `u_snoop` for the snoop responder.
//
//==============================================================================

module l1_core_fab_tb
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
    parameter bit USE_MONITOR    = 1'b1,
    parameter bit PF_GUARD       = 1'b0,
    localparam int STRB_W        = BUS_WIDTH / 8,
    localparam int IW            = AXI_ID_WIDTH,
    localparam int UW            = AXI_USER_WIDTH,
    localparam int CPU_REQ_W     = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W     = BUS_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // CPU GAXI slave (MAS ch03/01; packed {addr, we, be, wdata} /
    // {rdata})
    // ------------------------------------------------------------------
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // fub_axi read master side (l1_fill -> axi4_master_rd in the rig top)
    // ------------------------------------------------------------------
    output logic [IW-1:0]               fub_axi_arid,
    output logic [ADDR_WIDTH-1:0]       fub_axi_araddr,
    output logic [7:0]                  fub_axi_arlen,
    output logic [2:0]                  fub_axi_arsize,
    output logic [1:0]                  fub_axi_arburst,
    output logic                        fub_axi_arlock,
    output logic [3:0]                  fub_axi_arcache,
    output logic [2:0]                  fub_axi_arprot,
    output logic [3:0]                  fub_axi_arqos,
    output logic [3:0]                  fub_axi_arregion,
    output logic [UW-1:0]               fub_axi_aruser,
    output logic                        fub_axi_arvalid,
    input  logic                        fub_axi_arready,
    input  logic [IW-1:0]               fub_axi_rid,
    input  logic [BUS_WIDTH-1:0]        fub_axi_rdata,
    input  logic [3:0]                  fub_axi_rresp,
    input  logic                        fub_axi_rlast,
    input  logic [UW-1:0]               fub_axi_ruser,
    input  logic                        fub_axi_rvalid,
    output logic                        fub_axi_rready,

    // ------------------------------------------------------------------
    // fub_axi write master side (l1_drain -> axi4_master_wr)
    // ------------------------------------------------------------------
    output logic [IW-1:0]               fub_axi_awid,
    output logic [ADDR_WIDTH-1:0]       fub_axi_awaddr,
    output logic [7:0]                  fub_axi_awlen,
    output logic [2:0]                  fub_axi_awsize,
    output logic [1:0]                  fub_axi_awburst,
    output logic                        fub_axi_awlock,
    output logic [3:0]                  fub_axi_awcache,
    output logic [2:0]                  fub_axi_awprot,
    output logic [3:0]                  fub_axi_awqos,
    output logic [3:0]                  fub_axi_awregion,
    output logic [UW-1:0]               fub_axi_awuser,
    output logic                        fub_axi_awvalid,
    input  logic                        fub_axi_awready,
    output logic [BUS_WIDTH-1:0]        fub_axi_wdata,
    output logic [STRB_W-1:0]           fub_axi_wstrb,
    output logic                        fub_axi_wlast,
    output logic [UW-1:0]               fub_axi_wuser,
    output logic                        fub_axi_wvalid,
    input  logic                        fub_axi_wready,
    input  logic [IW-1:0]               fub_axi_bid,
    input  logic [1:0]                  fub_axi_bresp,
    input  logic [UW-1:0]               fub_axi_buser,
    input  logic                        fub_axi_bvalid,
    output logic                        fub_axi_bready,

    // ------------------------------------------------------------------
    // ACE snoop responder (MAS ch03/03) -- same surface as pre-restructure
    // ------------------------------------------------------------------
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

    // ------------------------------------------------------------------
    // Pair-rig coherence sideband (DECISION D-8; amber_ace_req_t type)
    // ------------------------------------------------------------------
    output logic                        coh_req_valid,
    output logic [ADDR_WIDTH-1:0]       coh_req_addr,
    output logic [2:0]                  coh_req_type,

    // ------------------------------------------------------------------
    // MonBus observation (*_monlite only, PRD D8; MAS ch03/05)
    // ------------------------------------------------------------------
    input  logic [63:0]                 mon_time,
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp,
    output logic [7:0]                  mon_dropped,

    // ------------------------------------------------------------------
    // Status / observability
    // ------------------------------------------------------------------
    output logic                        init_busy,
    output logic [3:0]                  ctrl_state
);

    // ------------------------------------------------------------------
    // Fabric seam between l1_core and the snoop responder
    // ------------------------------------------------------------------
    logic                     w_ctrl_snoop_req;
    logic                     w_ctrl_snoop_ready;
    logic                     w_ctrl_snoop_safe;
    logic [2:0]               w_ctrl_snoop_type;
    logic [ADDR_WIDTH-1:0]    w_ctrl_snoop_addr;
    logic [AMBER_CRRESP_WIDTH-1:0] w_ctrl_crresp;
    logic [BUS_WIDTH-1:0]     w_ctrl_cddata;
    logic                     w_ctrl_cdlast;
    logic                     w_ctrl_cdvalid;
    logic                     w_ctrl_cdready;

    // ------------------------------------------------------------------
    // The aggregate core (CPU plane + coherence core plane)
    // ------------------------------------------------------------------
    l1_core #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR),
        .PF_GUARD       (PF_GUARD)
    ) u_core (
        .clk               (clk),
        .rst_n             (rst_n),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
        .fub_axi_arid      (fub_axi_arid),
        .fub_axi_araddr    (fub_axi_araddr),
        .fub_axi_arlen     (fub_axi_arlen),
        .fub_axi_arsize    (fub_axi_arsize),
        .fub_axi_arburst   (fub_axi_arburst),
        .fub_axi_arlock    (fub_axi_arlock),
        .fub_axi_arcache   (fub_axi_arcache),
        .fub_axi_arprot    (fub_axi_arprot),
        .fub_axi_arqos     (fub_axi_arqos),
        .fub_axi_arregion  (fub_axi_arregion),
        .fub_axi_aruser    (fub_axi_aruser),
        .fub_axi_arvalid   (fub_axi_arvalid),
        .fub_axi_arready   (fub_axi_arready),
        .fub_axi_rid       (fub_axi_rid),
        .fub_axi_rdata     (fub_axi_rdata),
        .fub_axi_rresp     (fub_axi_rresp),
        .fub_axi_rlast     (fub_axi_rlast),
        .fub_axi_ruser     (fub_axi_ruser),
        .fub_axi_rvalid    (fub_axi_rvalid),
        .fub_axi_rready    (fub_axi_rready),
        .fub_axi_awid      (fub_axi_awid),
        .fub_axi_awaddr    (fub_axi_awaddr),
        .fub_axi_awlen     (fub_axi_awlen),
        .fub_axi_awsize    (fub_axi_awsize),
        .fub_axi_awburst   (fub_axi_awburst),
        .fub_axi_awlock    (fub_axi_awlock),
        .fub_axi_awcache   (fub_axi_awcache),
        .fub_axi_awprot    (fub_axi_awprot),
        .fub_axi_awqos     (fub_axi_awqos),
        .fub_axi_awregion  (fub_axi_awregion),
        .fub_axi_awuser    (fub_axi_awuser),
        .fub_axi_awvalid   (fub_axi_awvalid),
        .fub_axi_awready   (fub_axi_awready),
        .fub_axi_wdata     (fub_axi_wdata),
        .fub_axi_wstrb     (fub_axi_wstrb),
        .fub_axi_wlast     (fub_axi_wlast),
        .fub_axi_wuser     (fub_axi_wuser),
        .fub_axi_wvalid    (fub_axi_wvalid),
        .fub_axi_wready    (fub_axi_wready),
        .fub_axi_bid       (fub_axi_bid),
        .fub_axi_bresp     (fub_axi_bresp),
        .fub_axi_buser     (fub_axi_buser),
        .fub_axi_bvalid    (fub_axi_bvalid),
        .fub_axi_bready    (fub_axi_bready),
        .ctrl_snoop_req    (w_ctrl_snoop_req),
        .ctrl_snoop_ready  (w_ctrl_snoop_ready),
        .ctrl_snoop_safe   (w_ctrl_snoop_safe),
        .ctrl_snoop_type   (w_ctrl_snoop_type),
        .ctrl_snoop_addr   (w_ctrl_snoop_addr),
        .ctrl_crresp       (w_ctrl_crresp),
        .ctrl_cddata       (w_ctrl_cddata),
        .ctrl_cdlast       (w_ctrl_cdlast),
        .ctrl_cdvalid      (w_ctrl_cdvalid),
        .ctrl_cdready      (w_ctrl_cdready),
        .coh_req_valid     (coh_req_valid),
        .coh_req_addr      (coh_req_addr),
        .coh_req_type      (coh_req_type),
        .mon_time          (mon_time),
        .mon_valid         (mon_valid),
        .mon_ready         (mon_ready),
        .mon_packet        (mon_packet),
        .mon_timestamp     (mon_timestamp),
        .mon_dropped       (mon_dropped),
        .init_busy         (init_busy),
        .ctrl_state        (ctrl_state)
    );

    // ------------------------------------------------------------------
    // ACE snoop responder (moved out of the core in Task 1)
    // ------------------------------------------------------------------
    l1_snoop_resp #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (BUS_WIDTH),
        .LINE_BYTES (LINE_BYTES)
    ) u_snoop (
        .aclk           (clk),
        .aresetn        (rst_n),
        .m_axi_acaddr   (m_axi_acaddr),
        .m_axi_acsnoop  (m_axi_acsnoop),
        .m_axi_acprot   (m_axi_acprot),
        .m_axi_acvalid  (m_axi_acvalid),
        .m_axi_acready  (m_axi_acready),
        .m_axi_crresp   (m_axi_crresp),
        .m_axi_crvalid  (m_axi_crvalid),
        .m_axi_crready  (m_axi_crready),
        .m_axi_cddata   (m_axi_cddata),
        .m_axi_cdlast   (m_axi_cdlast),
        .m_axi_cdvalid  (m_axi_cdvalid),
        .m_axi_cdready  (m_axi_cdready),
        .ctrl_snoop_req    (w_ctrl_snoop_req),
        .ctrl_snoop_addr   (w_ctrl_snoop_addr),
        .ctrl_snoop_type   (w_ctrl_snoop_type),
        .ctrl_snoop_ready  (w_ctrl_snoop_ready),
        .ctrl_snoop_safe   (w_ctrl_snoop_safe),
        .ctrl_crresp       (w_ctrl_crresp),
        .ctrl_cddata       (w_ctrl_cddata),
        .ctrl_cdlast       (w_ctrl_cdlast),
        .ctrl_cdvalid      (w_ctrl_cdvalid),
        .ctrl_cdready      (w_ctrl_cdready)
    );

endmodule : l1_core_fab_tb
