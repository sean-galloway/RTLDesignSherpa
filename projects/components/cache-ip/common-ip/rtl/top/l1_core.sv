// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_core
// Purpose:
//   Aggregate CPU plane + coherence-core plane for the cache-ip shared
//   MESI L1 (cache-ip plane restructure, Task 1): the shipping structural
//   integrator is now `l1_cpu_plane` + `l1_coh_core`, with `l1_core`
//   preserved as the familiar aggregate so existing core DV/formal
//   targets keep a stable boundary. The ACE snoop responder has moved to
//   the fabric plane; `l1_core` now exposes the core-facing fabric seam
//   bundle (ctrl_snoop_*, ctrl_crresp, ctrl_cd*).
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/01_architecture.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08
// Updated: 2026-11-01

`timescale 1ns / 1ps

//==============================================================================
// Module: l1_core
//==============================================================================
// Description:
//   Hierarchy (MAS ch01 hierarchy, plane restructure):
//
//     l1_core
//     |-- u_cpu   l1_cpu_plane    GAXI slave <-> CPU seam
//     `-- u_coh   l1_coh_core     coherence FSM, arrays, engines, observer
//
//   The external shape is MAS ch01/02 minus the top-level masters and
//   minus the ACE snoop responder (which now lives in the fabric plane):
//   CPU GAXI slave, the raw fub_axi_* rd/wr master sides the engines
//   drive, the core-facing fabric seam, MonBus observation, the pair-rig
//   coherence sideband coh_req_* and status.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per l1_pkg defaults (HAS Table 5.0)
//     Type: int
//   REPL_POLICY:
//     Description: replacement policy; amber_repl_t encodings
//     Type: int
//   AXI_ID_WIDTH / AXI_USER_WIDTH:
//     Description: fub_axi id/user field widths, matching the engines
//     Type: int
//   USE_MONITOR:
//     Description: 0 ties the MonBus observer outputs off (house idiom)
//     Type: bit
//   PF_GUARD:
//     Description: set when this core sits behind a coherence fabric that can
//                  hold fill ARs unaccepted.
//     Type: bit
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset domain (clk / rst_n).
//   - The fub_axi_* ports are the raw engine-side master pins.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_top / amber_ace_top (Task 3), l1_core_fab_tb
//   - Instantiated: l1_cpu_plane, l1_coh_core
//   - Package: l1_pkg
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/common-ip/dv/tests/test_l1_core.py
//   Plan: dv/testplans/l1_core_testplan.yaml
//   Run: pytest projects/components/cache-ip/common-ip/dv/tests/test_l1_core.py -v
//   Note: the test runner targets the l1_core_fab_tb wrapper so the ACE
//         snoop stimulus survives the plane restructure unchanged.
//
//==============================================================================

module l1_core
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
    // Fabric (snoop) seam: the core-facing contract the fabric plane
    // implements (ACE today, CHI tomorrow). Direction is from the core
    // boundary toward the coherence core plane.
    // ------------------------------------------------------------------
    input  logic                        ctrl_snoop_req,
    output logic                        ctrl_snoop_ready,
    output logic                        ctrl_snoop_safe,
    input  logic [2:0]                  ctrl_snoop_type,
    input  logic [ADDR_WIDTH-1:0]       ctrl_snoop_addr,
    output logic [AMBER_CRRESP_WIDTH-1:0] ctrl_crresp,
    output logic [BUS_WIDTH-1:0]        ctrl_cddata,
    output logic                        ctrl_cdlast,
    output logic                        ctrl_cdvalid,
    input  logic                        ctrl_cdready,

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
    // CPU seam between the planes
    // ------------------------------------------------------------------
    logic                     fe_req_valid;
    logic [ADDR_WIDTH-1:0]    fe_req_addr;
    logic                     fe_req_we;
    logic [STRB_W-1:0]        fe_req_be;
    logic [BUS_WIDTH-1:0]     fe_req_wdata;
    logic                     ctrl_req_ready;
    logic                     ctrl_rsp_valid;
    logic [BUS_WIDTH-1:0]     ctrl_rsp_data;

    // ------------------------------------------------------------------
    // Fabric (snoop) seam between the planes. The l1_core boundary
    // direction is from the fabric plane toward the core; the coherence
    // core plane's direction is the opposite (it drives the request to
    // control and samples the handshakes back). Use internal wires so
    // both port declarations can be correct without direction conflicts.
    // ------------------------------------------------------------------
    logic                     core_snoop_req;
    logic                     core_snoop_ready;
    logic                     core_snoop_safe;
    logic [2:0]               core_snoop_type;
    logic [ADDR_WIDTH-1:0]    core_snoop_addr;
    logic [AMBER_CRRESP_WIDTH-1:0] core_crresp;
    logic [BUS_WIDTH-1:0]     core_cddata;
    logic                     core_cdlast;
    logic                     core_cdvalid;
    logic                     core_cdready;

    assign core_snoop_req    = ctrl_snoop_req;
    assign ctrl_snoop_ready  = core_snoop_ready;
    assign ctrl_snoop_safe   = core_snoop_safe;
    assign core_snoop_type   = ctrl_snoop_type;
    assign core_snoop_addr   = ctrl_snoop_addr;
    assign ctrl_crresp       = core_crresp;
    assign ctrl_cddata       = core_cddata;
    assign ctrl_cdlast       = core_cdlast;
    assign ctrl_cdvalid      = core_cdvalid;
    assign core_cdready      = ctrl_cdready;

    // ------------------------------------------------------------------
    // CPU plane
    // ------------------------------------------------------------------
    l1_cpu_plane #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_cpu (
        .clk               (clk),
        .rst_n             (rst_n),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
        .fe_req_valid      (fe_req_valid),
        .fe_req_addr       (fe_req_addr),
        .fe_req_we         (fe_req_we),
        .fe_req_be         (fe_req_be),
        .fe_req_wdata      (fe_req_wdata),
        .ctrl_req_ready    (ctrl_req_ready),
        .ctrl_rsp_valid    (ctrl_rsp_valid),
        .ctrl_rsp_data     (ctrl_rsp_data)
    );

    // ------------------------------------------------------------------
    // Coherence core plane
    // ------------------------------------------------------------------
    l1_coh_core #(
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
    ) u_coh (
        .clk               (clk),
        .rst_n             (rst_n),
        .fe_req_valid      (fe_req_valid),
        .fe_req_addr       (fe_req_addr),
        .fe_req_we         (fe_req_we),
        .fe_req_be         (fe_req_be),
        .fe_req_wdata      (fe_req_wdata),
        .ctrl_req_ready    (ctrl_req_ready),
        .ctrl_rsp_valid    (ctrl_rsp_valid),
        .ctrl_rsp_data     (ctrl_rsp_data),
        .ctrl_snoop_req    (core_snoop_req),
        .ctrl_snoop_ready  (core_snoop_ready),
        .ctrl_snoop_safe   (core_snoop_safe),
        .ctrl_snoop_type   (core_snoop_type),
        .ctrl_snoop_addr   (core_snoop_addr),
        .ctrl_crresp       (core_crresp),
        .ctrl_cddata       (core_cddata),
        .ctrl_cdlast       (core_cdlast),
        .ctrl_cdvalid      (core_cdvalid),
        .ctrl_cdready      (core_cdready),
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

endmodule : l1_core
