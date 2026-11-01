// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_ace_top
// Purpose:
//   The onyx-rig cache top (MAS ch01 hierarchy, Task 12): l1_cpu_plane +
//   l1_coh_core + l1_ace_plane, plus the D-7 monbus_arbiter and boundary
//   reset_sync. The ACE fabric plane closes the ACE snoop responder, the
//   shared l1_ace_issue event-to-transaction map, and the house
//   axi4ace_master_rd/wr_monlite transports (D3 measured paths, ACE snoop
//   fields + auto-pulsed RACK/WACK). The D-8 coherence launch stream is
//   consumed on-chip by l1_ace_issue; no coh_req sideband reaches the top
//   level.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/02_port_list.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-09
// Updated: 2026-11-01

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_ace_top
//==============================================================================
// Description:
//   amber_top's twin for the ACE rig: identical CPU GAXI slave / ACE snoop
//   responder / single MonBus surface and identical errata additions
//   (i_mon_time, init_busy, ctrl_state), with three deltas:
//
//   * the memory-side transports are the axi4ace_master_rd/wr_monlite
//     wrappers (snoop fields + auto-pulsed RACK/WACK), not the plain
//     axi4_master_rd/wr_monlite pair;
//   * l1_ace_issue sits inside the fabric plane between the core's fub_axi_*
//     engine pins and the transports: it stamps ARSNOOP on the fill engine's
//     AR, stamps AWSNOOP=WriteBack on the drain engine's AW, originates the
//     AW-only CleanUnique/MakeUnique/Evict transactions the engines never
//     generate, and swallows the AW-only B responses off the drain engine's
//     B channel (the AWONLY_ID BID mux);
//   * there is NO coh_req coherence sideband to the top level (the fabric
//     is not in this rig): the core's coh_req pulses feed ace_issue's
//     event inputs instead -- the same launch stream, consumed on-chip.
//
//   MonBus merge (D-7): client 0 = l1_monlite (the cache-event observer
//   inside the coherence core), client 1 = the fabric plane's merged
//   rd/wr_monlite observer. UNIT_IDs 8'h01/02/03 distinguish the streams.
//
//------------------------------------------------------------------------------
// Parameters: geometry per l1_pkg (HAS Table 5.0); REPL_POLICY per
//   amber_repl_t; USE_MONITOR ties all three observers off (house idiom,
//   present-vs-absent equivalence).
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (aclk / aresetn), MAS ch01/03.
//     Port aresetn is async-assert, synchronized internally (reset_sync,
//     N=3) -- see amber_top for the full contract.
//   - The monitor cfg inputs are tied to observation-only defaults
//     (monitor enabled, no error/timeout/completion/threshold actions, no
//     address windows); cam_clear tied off.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: the Task 12 ACE rig (dv/tests/test_amber_ace_top.py)
//   - Instantiated: l1_cpu_plane, l1_coh_core, l1_ace_plane;
//     axi4ace_master_rd/wr_monlite + l1_ace_issue (inside the fabric plane);
//     monbus_arbiter
//   - Package: l1_pkg; ocelus_common_pkg
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_ace_top.py
//   Plan: dv/testplans/amber_ace_top_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_ace_top.py -v
//
//==============================================================================

module amber_ace_top
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
    localparam int STRB_W       = BUS_WIDTH / 8,
    localparam int IW           = AXI_ID_WIDTH,
    localparam int UW           = AXI_USER_WIDTH,
    localparam int CPU_REQ_W    = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W    = BUS_WIDTH
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // CPU GAXI slave (MAS ch01/02)
    // ------------------------------------------------------------------
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // ACE memory masters via the monlite-wrapped transports (DECISION
    // D3; MAS ch01/02 signal names + ARSNOOP/AWSNOOP, ARDOMAIN/AWDOMAIN,
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
    // ACE snoop responder (MAS ch01/02)
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
    // Rig-level timestamp source (MAS ch04/05; errata'd into ch01/02)
    // ------------------------------------------------------------------
    input  logic [63:0]                 i_mon_time,

    // ------------------------------------------------------------------
    // MonBus (D-7 merged observation output pair; MAS ch01/02)
    // ------------------------------------------------------------------
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp,

    // ------------------------------------------------------------------
    // Status / observability
    // ------------------------------------------------------------------
    output logic                        init_busy,
    output logic [3:0]                  ctrl_state
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the core)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_ace_top: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_ace_top: LINE_BYTES must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_ace_top: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("amber_ace_top: WAYS must be >= 2");
    end

    // ------------------------------------------------------------------
    // Boundary reset synchronization -- same contract as amber_top: the
    // port aresetn is async-assert of unknown deassert quality, and the
    // N=3 house reset_sync produces the internal reset every block below
    // sees. Integrators may deassert it asynchronously.
    // ------------------------------------------------------------------
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

    // ------------------------------------------------------------------
    // CPU seam between the CPU plane and the coherence core plane
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
    // Fabric (snoop) seam between the coherence core plane and the ACE
    // fabric plane. Direction is from the fabric plane toward the core;
    // the coherence core plane drives the request to control and samples
    // the handshakes back.
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
    // plane's l1_ace_issue.
    // ------------------------------------------------------------------
    logic                 coh_req_valid;
    logic [ADDR_WIDTH-1:0] coh_req_addr;
    logic [2:0]           coh_req_type;

    // ------------------------------------------------------------------
    // MonBus streams: core observer + fabric-plane merged observer.
    // ------------------------------------------------------------------
    logic        core_mon_valid;
    logic        core_mon_ready;
    logic [127:0] core_mon_packet;
    logic [63:0] core_mon_timestamp;
    logic [7:0]  core_mon_dropped_unused;

    logic        fab_mon_valid;
    logic        fab_mon_ready;
    logic [127:0] fab_mon_packet;
    logic [63:0] fab_mon_timestamp;

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
        .clk               (aclk),
        .rst_n             (w_aresetn),
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
        .USE_MONITOR    (USE_MONITOR)
        // PF_GUARD stays 0 here: the ACE rig's TB interconnect never
        // blocks fill ARs on snoop responses, and its directed snoop
        // scenarios encode the classic bypass answer. Enable the guard
        // when a real ACE fabric integration appears (BUG-002).
    ) u_coh (
        .clk               (aclk),
        .rst_n             (w_aresetn),
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
        .coh_req_valid     (coh_req_valid),
        .coh_req_addr      (coh_req_addr),
        .coh_req_type      (coh_req_type),
        .mon_time          (i_mon_time),
        .mon_valid         (core_mon_valid),
        .mon_ready         (core_mon_ready),
        .mon_packet        (core_mon_packet),
        .mon_timestamp     (core_mon_timestamp),
        .mon_dropped       (core_mon_dropped_unused),
        .init_busy         (init_busy),
        .ctrl_state        (ctrl_state)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_core_mon;
    assign unused_core_mon = &{1'b0, core_mon_dropped_unused};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // ACE fabric plane: closes l1_snoop_resp, l1_ace_issue, and the ACE
    // rd/wr monlite transports; consumes the D-8 launch stream on-chip.
    // ------------------------------------------------------------------
    logic fab_sn_want_unused;

    l1_ace_plane #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR)
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
        .sn_want_o         (fab_sn_want_unused),
        .i_mon_time        (i_mon_time),
        .mon_valid         (fab_mon_valid),
        .mon_ready         (fab_mon_ready),
        .mon_packet        (fab_mon_packet),
        .mon_timestamp     (fab_mon_timestamp)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_fab_sn_want;
    assign unused_fab_sn_want = fab_sn_want_unused;
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // D-7 MonBus arbiter: {l1_monlite, fabric-plane observer} -> the one
    // MonBus port pair. The fabric plane internally merges the rd/wr
    // transport observers before exporting them here.
    // ------------------------------------------------------------------
    logic                    arb_vld [2];
    logic                    arb_rdy [2];
    ocelus_common_pkg::monitor_packet_t   arb_pkt [2];
    ocelus_common_pkg::monbus_timestamp_t arb_ts  [2];

    assign arb_vld[0] = core_mon_valid;
    assign arb_vld[1] = fab_mon_valid;
    assign core_mon_ready = arb_rdy[0];
    assign fab_mon_ready  = arb_rdy[1];
    assign arb_pkt[0] = core_mon_packet;
    assign arb_pkt[1] = fab_mon_packet;
    assign arb_ts[0]  = core_mon_timestamp;
    assign arb_ts[1]  = fab_mon_timestamp;

    monbus_arbiter #(
        .CLIENTS            (2),
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

endmodule : amber_ace_top
