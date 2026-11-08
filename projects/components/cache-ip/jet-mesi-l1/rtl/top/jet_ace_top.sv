// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_ace_top
// Purpose:
//   The jet onyx-rig top (MAS ch01 hierarchy, Task 9): jet_top's twin
//   for the ACE rig, recomposed onto the cache-ip planes (Task 4) --
//   jet_cpu_plane (GAXI frontend + D-6 request skid + J4 response
//   sequencer) + jet_coh_core (the jet control closure + the UNCHANGED
//   common-ip slice + the integration glue) + l1_ace_plane (the ACE
//   snoop responder, the shared l1_ace_issue Table 2.8.1 mapping block,
//   and the house axi4ace_master_rd/wr_monlite transports, DECISION D3),
//   plus the D-7 monbus_arbiter and the boundary reset_sync.  The
//   m_axi_* memory side is the monlite-wrapped (measured) ACE path with
//   ARSNOOP/AWSNOOP on the address payloads, the shareability-domain and
//   barrier fields, the 4-bit ACE RRESP (PassDirty live: an RNSD fill
//   with PassDirty installs M, per l1_control's #106 rule), and the
//   auto-pulsed RACK/WACK handshakes.
//
//   There is NO coh_req coherence sideband to the top level in this rig
//   (the fabric is not here): the coherence core's D-8 launch stream
//   feeds the fabric plane's l1_ace_issue event inputs on-chip instead.
//   jet v1 never emits EVICT/MAKE_UNIQUE (clean victims drop silently;
//   upgrades are CleanUnique), so l1_ace_issue's AW-only generator is
//   present but unexercised.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch01_overview/02_port_list.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-30
// Updated: 2026-11-01

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_ace_top
//==============================================================================
// Description:
//   External shape: jet_top's MAS ch01/02 contract on the ACE master
//   side -- aclk/aresetn, CPU GAXI slave, ACE m_axi_* rd/wr masters
//   (ARSNOOP/AWSNOOP, ARDOMAIN/AWDOMAIN, ARBAR/AWBAR, 4-bit RRESP,
//   RACK/WACK), ACE snoop responder, single MonBus, the rig-level
//   mon_time source, init_busy/ctrl_state status, and the jet `busy`
//   roll-up.  No coh_req sideband pins (see the header).
//
//   All integration glue lives in the planes (jet_coh_core carries the
//   fill-launch adapter, the data-array W-port mux, the coh_req
//   drain-collision replay, and the mon_state pseudo-state encoder;
//   jet_cpu_plane carries the D-6 request/response skid adaptation --
//   see the plane headers).  This top is pure wiring plus the sim-only
//   launch/issue-stream assertions (which tap the coherence core's
//   adapter registers read-only).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH / REPL_POLICY /
//   AXI_ID_WIDTH / AXI_USER_WIDTH / USE_MONITOR:
//     as jet_top (geometry per l1_pkg defaults)
//   MSHR_COUNT / VICTIM_DEPTH:
//     J1 / J5 geometry (jet_pkg defaults)
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset: the port aresetn is async-assert,
//     synchronized internally (reset_sync, N=3) -- integrators may
//     deassert it asynchronously (same pattern as jet_top).
//   - The monitor cfg inputs are tied to observation-only defaults
//     inside the fabric plane's transports; cam_clear tied off.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: the onyx rig (Task 9 deliverable; DV coverage via
//     the pair-rig twin jet_top + the jet_ace_top.f elaboration)
//   - Instantiated: jet_cpu_plane, jet_coh_core, l1_ace_plane,
//     monbus_arbiter, reset_sync
//   - Package: jet_pkg, l1_pkg, ocelus_common_pkg
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_pair_rig.py
//     (the coherent behavior, via the plain-AXI4 twin; this top's
//     elaboration is pinned by the filelist lint)
//   Plan: dv/testplans/jet_pair_rig_testplan.yaml
//
//==============================================================================

module jet_ace_top
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
    parameter bit USE_MONITOR    = 1'b1,
    parameter int MSHR_COUNT     = jet_pkg::MSHR_COUNT,
    parameter int VICTIM_DEPTH   = jet_pkg::VICTIM_DEPTH,
    localparam int STRB_W      = BUS_WIDTH / 8,
    localparam int RSP_DEPTH   = MSHR_COUNT + 2,
    localparam int SEQ_W       = $clog2(RSP_DEPTH),
    localparam int IW          = AXI_ID_WIDTH,
    localparam int UW          = AXI_USER_WIDTH,
    localparam int CPU_REQ_W   = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W   = BUS_WIDTH
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // CPU GAXI slave (MAS ch03/01)
    // ------------------------------------------------------------------
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // ACE memory masters via the monlite-wrapped transports (DECISION
    // D3; MAS ch03/03 signal names + ARSNOOP/AWSNOOP, ARDOMAIN/AWDOMAIN,
    // ARBAR/AWBAR, the 4-bit ACE RRESP, RACK/WACK)
    // ------------------------------------------------------------------
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
    output logic [3:0]                  m_axi_arsnoop,
    output logic [1:0]                  m_axi_ardomain,
    output logic [1:0]                  m_axi_arbar,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [BUS_WIDTH-1:0]        m_axi_rdata,
    input  logic [3:0]                  m_axi_rresp,   // [3]=IsShared [2]=PassDirty
    input  logic                        m_axi_rlast,
    input  logic [UW-1:0]               m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,
    output logic                        m_axi_rack,

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
    output logic [2:0]                  m_axi_awsnoop,
    output logic [1:0]                  m_axi_awdomain,
    output logic [1:0]                  m_axi_awbar,
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
    output logic                        m_axi_wack,

    // ------------------------------------------------------------------
    // ACE snoop responder (MAS ch03/03)
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
    // Rig-level timestamp source + merged MonBus (D-7)
    // ------------------------------------------------------------------
    input  logic [63:0]                 i_mon_time,
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp,

    // ------------------------------------------------------------------
    // Status / observability
    // ------------------------------------------------------------------
    output logic                        init_busy,
    output logic [3:0]                  ctrl_state,
    output logic                        busy
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the core blocks)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("jet_ace_top: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("jet_ace_top: LINE_BYTES must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("jet_ace_top: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("jet_ace_top: WAYS must be >= 2");
    end

    // ------------------------------------------------------------------
    // Boundary reset synchronization (async-assert port, synchronous
    // release inside; the jet_top pattern)
    // ------------------------------------------------------------------
    logic w_aresetn;
    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1),
        // replicable output stage: the pinned chain MSB must not be the one
        // flop driving every CLR pin of the core (FPGA review 2026-11-07)
        .REPLICATED_OUT(1'b1)
    ) u_reset_sync (
        .clk        (aclk),
        .rst_n      (aresetn),
        .sync_rst_n (w_aresetn)
    );

    // ------------------------------------------------------------------
    // CPU seam between the CPU plane and the coherence core plane: the
    // D-6 skid's held lookup request, the CTRL_ERROR dead-stop, and the
    // J4 response sequencer's tag/cpl partner pins
    // ------------------------------------------------------------------
    logic                     lkup_valid;
    logic [ADDR_WIDTH-1:0]    lkup_addr;
    logic                     lkup_we;
    logic [STRB_W-1:0]        lkup_be;
    logic [BUS_WIDTH-1:0]     lkup_wdata;
    logic                     lkup_ready;
    logic                     ctrl_error;
    logic                     ctrl_tag_req;
    logic                     rsp_tag_gnt;
    logic [SEQ_W-1:0]         rsp_tag;
    logic                     ctrl_cpl_valid;
    logic [SEQ_W-1:0]         ctrl_cpl_tag;
    logic [BUS_WIDTH-1:0]     ctrl_cpl_data;

    // ------------------------------------------------------------------
    // Fabric (snoop) seam between the coherence core plane and the ACE
    // fabric plane, and the fabric plane's AC-pending throttle back to
    // the core (jet_control's J6 throttle)
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
    logic                     sn_want;

    // ------------------------------------------------------------------
    // Engine (fub_axi) seam between the coherence core plane and the ACE
    // fabric plane. The plane closes l1_ace_issue and the ACE transports.
    // ------------------------------------------------------------------
    logic [IW-1:0]        fub_arid, fub_rid;
    logic [ADDR_WIDTH-1:0] fub_araddr;
    logic [7:0]           fub_arlen;
    logic [2:0]           fub_arsize;
    logic [1:0]           fub_arburst;
    logic                 fub_arlock;
    logic [3:0]           fub_arcache;
    logic [2:0]           fub_arprot;
    logic [3:0]           fub_arqos;
    logic [3:0]           fub_arregion;
    logic [UW-1:0]        fub_aruser;
    logic                 fub_arvalid, fub_arready;
    logic [BUS_WIDTH-1:0] fub_rdata;
    logic [3:0]           fub_rresp;
    logic                 fub_rlast;
    logic [UW-1:0]        fub_ruser;
    logic                 fub_rvalid, fub_rready;

    logic [IW-1:0]        fub_awid, fub_bid;
    logic [ADDR_WIDTH-1:0] fub_awaddr;
    logic [7:0]           fub_awlen;
    logic [2:0]           fub_awsize;
    logic [1:0]           fub_awburst;
    logic                 fub_awlock;
    logic [3:0]           fub_awcache;
    logic [2:0]           fub_awprot;
    logic [3:0]           fub_awqos;
    logic [3:0]           fub_awregion;
    logic [UW-1:0]        fub_awuser;
    logic                 fub_awvalid, fub_awready;
    logic [BUS_WIDTH-1:0] fub_wdata;
    logic [STRB_W-1:0]    fub_wstrb;
    logic                 fub_wlast;
    logic [UW-1:0]        fub_wuser;
    logic                 fub_wvalid, fub_wready;
    logic [1:0]           fub_bresp;
    logic [UW-1:0]        fub_buser;
    logic                 fub_bvalid, fub_bready;

    // ------------------------------------------------------------------
    // D-8 coherence launch stream, consumed on-chip by the ACE fabric
    // plane's l1_ace_issue (there is no fabric in this rig)
    // ------------------------------------------------------------------
    logic                 coh_req_valid;
    logic [ADDR_WIDTH-1:0] coh_req_addr;
    logic [2:0]           coh_req_type;

    // ------------------------------------------------------------------
    // MonBus streams: core observer + J7 observer + fabric-plane merged
    // rd/wr transport observers
    // ------------------------------------------------------------------
    logic        core_mon_valid;
    logic        core_mon_ready;
    logic [127:0] core_mon_packet;
    logic [63:0] core_mon_timestamp;
    logic [7:0]  core_mon_dropped_unused;

    logic        j7_mon_valid;
    logic        j7_mon_ready;
    logic [127:0] j7_mon_packet;
    logic [63:0]  j7_mon_timestamp;

    logic        fab_mon_valid;
    logic        fab_mon_ready;
    logic [127:0] fab_mon_packet;
    logic [63:0] fab_mon_timestamp;

    // ------------------------------------------------------------------
    // CPU plane
    // ------------------------------------------------------------------
    jet_cpu_plane #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH),
        .MSHR_COUNT (MSHR_COUNT)
    ) u_cpu (
        .aclk              (aclk),
        .aresetn           (w_aresetn),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
        .lkup_valid        (lkup_valid),
        .lkup_addr         (lkup_addr),
        .lkup_we           (lkup_we),
        .lkup_be           (lkup_be),
        .lkup_wdata        (lkup_wdata),
        .lkup_ready        (lkup_ready),
        .ctrl_error        (ctrl_error),
        .ctrl_tag_req      (ctrl_tag_req),
        .rsp_tag_gnt       (rsp_tag_gnt),
        .rsp_tag           (rsp_tag),
        .ctrl_cpl_valid    (ctrl_cpl_valid),
        .ctrl_cpl_tag      (ctrl_cpl_tag),
        .ctrl_cpl_data     (ctrl_cpl_data)
    );

    // ------------------------------------------------------------------
    // Coherence core plane
    // ------------------------------------------------------------------
    jet_coh_core #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR),
        .MSHR_COUNT     (MSHR_COUNT),
        .VICTIM_DEPTH   (VICTIM_DEPTH)
    ) u_coh (
        .aclk              (aclk),
        .aresetn           (w_aresetn),
        .lkup_valid        (lkup_valid),
        .lkup_addr         (lkup_addr),
        .lkup_we           (lkup_we),
        .lkup_be           (lkup_be),
        .lkup_wdata        (lkup_wdata),
        .lkup_ready        (lkup_ready),
        .ctrl_error        (ctrl_error),
        .ctrl_tag_req      (ctrl_tag_req),
        .rsp_tag_gnt       (rsp_tag_gnt),
        .rsp_tag           (rsp_tag),
        .ctrl_cpl_valid    (ctrl_cpl_valid),
        .ctrl_cpl_tag      (ctrl_cpl_tag),
        .ctrl_cpl_data     (ctrl_cpl_data),
        .ctrl_snoop_req    (core_snoop_req),
        .sn_want_i         (sn_want),
        .ctrl_snoop_type   (core_snoop_type),
        .ctrl_snoop_addr   (core_snoop_addr),
        .ctrl_snoop_ready  (core_snoop_ready),
        .ctrl_snoop_safe   (core_snoop_safe),
        .ctrl_crresp       (core_crresp),
        .ctrl_cddata       (core_cddata),
        .ctrl_cdlast       (core_cdlast),
        .ctrl_cdvalid      (core_cdvalid),
        .ctrl_cdready      (core_cdready),
        .fub_axi_arid      (fub_arid),
        .fub_axi_araddr    (fub_araddr),
        .fub_axi_arlen     (fub_arlen),
        .fub_axi_arsize    (fub_arsize),
        .fub_axi_arburst   (fub_arburst),
        .fub_axi_arlock    (fub_arlock),
        .fub_axi_arcache   (fub_arcache),
        .fub_axi_arprot    (fub_arprot),
        .fub_axi_arqos     (fub_arqos),
        .fub_axi_arregion  (fub_arregion),
        .fub_axi_aruser    (fub_aruser),
        .fub_axi_arvalid   (fub_arvalid),
        .fub_axi_arready   (fub_arready),
        .fub_axi_rid       (fub_rid),
        .fub_axi_rdata     (fub_rdata),
        .fub_axi_rresp     (fub_rresp),
        .fub_axi_rlast     (fub_rlast),
        .fub_axi_ruser     (fub_ruser),
        .fub_axi_rvalid    (fub_rvalid),
        .fub_axi_rready    (fub_rready),
        .fub_axi_awid      (fub_awid),
        .fub_axi_awaddr    (fub_awaddr),
        .fub_axi_awlen     (fub_awlen),
        .fub_axi_awsize    (fub_awsize),
        .fub_axi_awburst   (fub_awburst),
        .fub_axi_awlock    (fub_awlock),
        .fub_axi_awcache   (fub_awcache),
        .fub_axi_awprot    (fub_awprot),
        .fub_axi_awqos     (fub_awqos),
        .fub_axi_awregion  (fub_awregion),
        .fub_axi_awuser    (fub_awuser),
        .fub_axi_awvalid   (fub_awvalid),
        .fub_axi_awready   (fub_awready),
        .fub_axi_wdata     (fub_wdata),
        .fub_axi_wstrb     (fub_wstrb),
        .fub_axi_wlast     (fub_wlast),
        .fub_axi_wuser     (fub_wuser),
        .fub_axi_wvalid    (fub_wvalid),
        .fub_axi_wready    (fub_wready),
        .fub_axi_bid       (fub_bid),
        .fub_axi_bresp     (fub_bresp),
        .fub_axi_buser     (fub_buser),
        .fub_axi_bvalid    (fub_bvalid),
        .fub_axi_bready    (fub_bready),
        .fill_ar_done      (m_axi_arvalid & m_axi_arready),
        .coh_req_valid     (coh_req_valid),
        .coh_req_addr      (coh_req_addr),
        .coh_req_type      (coh_req_type),
        .mon_time          (i_mon_time),
        .mon_valid         (core_mon_valid),
        .mon_ready         (core_mon_ready),
        .mon_packet        (core_mon_packet),
        .mon_timestamp     (core_mon_timestamp),
        .mon_dropped       (core_mon_dropped_unused),
        .j7_mon_valid      (j7_mon_valid),
        .j7_mon_ready      (j7_mon_ready),
        .j7_mon_packet     (j7_mon_packet),
        .j7_mon_timestamp  (j7_mon_timestamp),
        .init_busy         (init_busy),
        .ctrl_state        (ctrl_state),
        .busy              (busy)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_core_mon;
    assign unused_core_mon = &{1'b0, core_mon_dropped_unused};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // ACE fabric plane: closes l1_snoop_resp, l1_ace_issue, and the ACE
    // rd/wr monlite transports; consumes the D-8 launch stream on-chip
    // ------------------------------------------------------------------
    l1_ace_plane #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR),
        // jet's historical MonBus agent id for the transport observers
        // (amber keeps the 16'h00A0 default)
        .AGENT_ID       (16'h00A1)
    ) u_fab (
        .aclk              (aclk),
        .aresetn           (w_aresetn),
        .m_axi_arid        (m_axi_arid),
        .m_axi_araddr      (m_axi_araddr),
        .m_axi_arlen       (m_axi_arlen),
        .m_axi_arsize      (m_axi_arsize),
        .m_axi_arburst     (m_axi_arburst),
        .m_axi_arlock      (m_axi_arlock),
        .m_axi_arcache     (m_axi_arcache),
        .m_axi_arprot      (m_axi_arprot),
        .m_axi_arqos       (m_axi_arqos),
        .m_axi_arregion    (m_axi_arregion),
        .m_axi_aruser      (m_axi_aruser),
        .m_axi_arsnoop     (m_axi_arsnoop),
        .m_axi_ardomain    (m_axi_ardomain),
        .m_axi_arbar       (m_axi_arbar),
        .m_axi_arvalid     (m_axi_arvalid),
        .m_axi_arready     (m_axi_arready),
        .m_axi_rid         (m_axi_rid),
        .m_axi_rdata       (m_axi_rdata),
        .m_axi_rresp       (m_axi_rresp),
        .m_axi_rlast       (m_axi_rlast),
        .m_axi_ruser       (m_axi_ruser),
        .m_axi_rvalid      (m_axi_rvalid),
        .m_axi_rready      (m_axi_rready),
        .m_axi_rack        (m_axi_rack),
        .m_axi_awid        (m_axi_awid),
        .m_axi_awaddr      (m_axi_awaddr),
        .m_axi_awlen       (m_axi_awlen),
        .m_axi_awsize      (m_axi_awsize),
        .m_axi_awburst     (m_axi_awburst),
        .m_axi_awlock      (m_axi_awlock),
        .m_axi_awcache     (m_axi_awcache),
        .m_axi_awprot      (m_axi_awprot),
        .m_axi_awqos       (m_axi_awqos),
        .m_axi_awregion    (m_axi_awregion),
        .m_axi_awuser      (m_axi_awuser),
        .m_axi_awsnoop     (m_axi_awsnoop),
        .m_axi_awdomain    (m_axi_awdomain),
        .m_axi_awbar       (m_axi_awbar),
        .m_axi_awvalid     (m_axi_awvalid),
        .m_axi_awready     (m_axi_awready),
        .m_axi_wdata       (m_axi_wdata),
        .m_axi_wstrb       (m_axi_wstrb),
        .m_axi_wlast       (m_axi_wlast),
        .m_axi_wuser       (m_axi_wuser),
        .m_axi_wvalid      (m_axi_wvalid),
        .m_axi_wready      (m_axi_wready),
        .m_axi_bid         (m_axi_bid),
        .m_axi_bresp       (m_axi_bresp),
        .m_axi_buser       (m_axi_buser),
        .m_axi_bvalid      (m_axi_bvalid),
        .m_axi_bready      (m_axi_bready),
        .m_axi_wack        (m_axi_wack),
        .m_axi_acaddr      (m_axi_acaddr),
        .m_axi_acsnoop     (m_axi_acsnoop),
        .m_axi_acprot      (m_axi_acprot),
        .m_axi_acvalid     (m_axi_acvalid),
        .m_axi_acready     (m_axi_acready),
        .m_axi_crresp      (m_axi_crresp),
        .m_axi_crvalid     (m_axi_crvalid),
        .m_axi_crready     (m_axi_crready),
        .m_axi_cddata      (m_axi_cddata),
        .m_axi_cdlast      (m_axi_cdlast),
        .m_axi_cdvalid     (m_axi_cdvalid),
        .m_axi_cdready     (m_axi_cdready),
        .fub_axi_arid      (fub_arid),
        .fub_axi_araddr    (fub_araddr),
        .fub_axi_arlen     (fub_arlen),
        .fub_axi_arsize    (fub_arsize),
        .fub_axi_arburst   (fub_arburst),
        .fub_axi_arlock    (fub_arlock),
        .fub_axi_arcache   (fub_arcache),
        .fub_axi_arprot    (fub_arprot),
        .fub_axi_arqos     (fub_arqos),
        .fub_axi_arregion  (fub_arregion),
        .fub_axi_aruser    (fub_aruser),
        .fub_axi_arvalid   (fub_arvalid),
        .fub_axi_arready   (fub_arready),
        .fub_axi_rid       (fub_rid),
        .fub_axi_rdata     (fub_rdata),
        .fub_axi_rresp     (fub_rresp),
        .fub_axi_rlast     (fub_rlast),
        .fub_axi_ruser     (fub_ruser),
        .fub_axi_rvalid    (fub_rvalid),
        .fub_axi_rready    (fub_rready),
        .fub_axi_awid      (fub_awid),
        .fub_axi_awaddr    (fub_awaddr),
        .fub_axi_awlen     (fub_awlen),
        .fub_axi_awsize    (fub_awsize),
        .fub_axi_awburst   (fub_awburst),
        .fub_axi_awlock    (fub_awlock),
        .fub_axi_awcache   (fub_awcache),
        .fub_axi_awprot    (fub_awprot),
        .fub_axi_awqos     (fub_awqos),
        .fub_axi_awregion  (fub_awregion),
        .fub_axi_awuser    (fub_awuser),
        .fub_axi_awvalid   (fub_awvalid),
        .fub_axi_awready   (fub_awready),
        .fub_axi_wdata     (fub_wdata),
        .fub_axi_wstrb     (fub_wstrb),
        .fub_axi_wlast     (fub_wlast),
        .fub_axi_wuser     (fub_wuser),
        .fub_axi_wvalid    (fub_wvalid),
        .fub_axi_wready    (fub_wready),
        .fub_axi_bid       (fub_bid),
        .fub_axi_bresp     (fub_bresp),
        .fub_axi_buser     (fub_buser),
        .fub_axi_bvalid    (fub_bvalid),
        .fub_axi_bready    (fub_bready),
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
        .coh_req_valid     (coh_req_valid),
        .coh_req_addr      (coh_req_addr),
        .coh_req_type      (coh_req_type),
        .sn_want_o         (sn_want),
        .i_mon_time        (i_mon_time),
        .mon_valid         (fab_mon_valid),
        .mon_ready         (fab_mon_ready),
        .mon_packet        (fab_mon_packet),
        .mon_timestamp     (fab_mon_timestamp)
    );

    // ------------------------------------------------------------------
    // D-7 MonBus arbiter: {l1_monlite, fabric-plane observers, J7
    // jet_monlite} -> the one MonBus port pair. The fabric plane
    // internally merges the rd/wr transport observers before exporting
    // them here.
    // ------------------------------------------------------------------
    logic                    arb_vld [3];
    logic                    arb_rdy [3];
    ocelus_common_pkg::monitor_packet_t   arb_pkt [3];
    ocelus_common_pkg::monbus_timestamp_t arb_ts  [3];

    assign arb_vld[0] = core_mon_valid;
    assign arb_vld[1] = fab_mon_valid;
    assign arb_vld[2] = j7_mon_valid;
    assign core_mon_ready = arb_rdy[0];
    assign fab_mon_ready  = arb_rdy[1];
    assign j7_mon_ready   = arb_rdy[2];
    assign arb_pkt[0] = core_mon_packet;
    assign arb_pkt[1] = fab_mon_packet;
    assign arb_pkt[2] = j7_mon_packet;
    assign arb_ts[0]  = core_mon_timestamp;
    assign arb_ts[1]  = fab_mon_timestamp;
    assign arb_ts[2]  = j7_mon_timestamp;

    monbus_arbiter #(
        .CLIENTS            (3),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_monbus_arbiter (
        .axi_aclk            (aclk),
        .axi_aresetn         (w_aresetn),
        .block_arb           (1'b0),
        .monbus_valid_in     (arb_vld),
        .monbus_ready_in     (arb_rdy),
        .monbus_packet_in    (arb_pkt),
        .monbus_timestamp_in (arb_ts),
        .monbus_valid        (mon_valid),
        .monbus_ready        (mon_ready),
        .monbus_packet       (mon_packet),
        .monbus_timestamp    (mon_timestamp),
        .grant_valid         (),
        .grant               (),
        .grant_id            (),
        .last_grant          ()
    );

    // ------------------------------------------------------------------
    // Simulation-only integration checks (the launch-adapter nets live in
    // the coherence core plane; tapped read-only, the sanctioned l1_core
    // pattern)
    // ------------------------------------------------------------------
    // pragma translate_off
    // The launch adapter never lets a fill's beats race the victim
    // capture (MAS ch02/01 fill-engine contract): no accept while a
    // capture streams, and never on the cycle a dirty-victim capture
    // opens (cap_busy_o rises one cycle later).
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (u_coh.w_fill_accept |-> !u_coh.ctrl_cap_busy))
        else $error("jet_ace_top: fill launch accepted during a victim capture");

    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (u_coh.w_fill_accept |-> !(u_coh.ctrl_mshr_alloc
                                   & u_coh.ctrl_mshr_alloc_wb_valid)))
        else $error("jet_ace_top: fill launch accepted on a dirty-victim alloc cycle");

    // The engine is idle exactly when the adapter is not busy.
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (u_coh.w_fill_accept |-> !u_coh.r_eng_busy))
        else $error("jet_ace_top: fill launch accepted while the engine is busy");

    // A held launch is always the pending record's (no same-cycle alloc).
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        ((u_coh.w_fill_accept & (u_coh.ctrl_fill_cls != JET_CLS_CU)
          & ~(u_coh.ctrl_mshr_alloc & u_coh.mshr_alloc_gnt))
         |-> u_coh.r_pend_valid))
        else $error("jet_ace_top: held fill launch with no pending alloc record");

    // The on-chip launch stream feeding the fabric plane's l1_ace_issue
    // never drops a fill launch: every accept presents a read-channel
    // class (RNSD/RU/CU).  The stream is registered at the jet_coh_core
    // boundary (ISSUE-001), so the pulse lands the cycle AFTER the accept.
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (u_coh.w_fill_accept |=> (coh_req_valid
                            && (coh_req_type != 3'(AMBER_ACE_WRITE_BACK)))))
        else $error("jet_ace_top: fill launch dropped from the issue stream");
    // pragma translate_on

endmodule : jet_ace_top
