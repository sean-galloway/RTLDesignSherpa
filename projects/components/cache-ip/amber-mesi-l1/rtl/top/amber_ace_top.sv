// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_ace_top
// Purpose:
//   The onyx-rig cache top (MAS ch01 hierarchy, Task 12): amber_core wrapped
//   with the house ACE transports it deliberately does not contain
//   (DECISION D3) -- axi4ace_master_rd_monlite / axi4ace_master_wr_monlite,
//   so the m_axi_* memory side is the monlite-wrapped (measured) ACE path
//   with ARSNOOP/AWSNOOP on the address payloads and the auto-pulsed
//   RACK/WACK handshakes -- plus the amber_ace_issue Table 2.8.1 mapping
//   block between the core's engines and those transports. A house
//   monbus_arbiter (DECISION D-7) merges the three observer streams
//   {amber_monlite, rd_monlite, wr_monlite} onto the one MonBus port pair.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/02_port_list.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-09

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
//   * amber_ace_issue sits between the core's fub_axi_* engine pins and
//     the transports: it stamps ARSNOOP on the fill engine's AR, stamps
//     AWSNOOP=WriteBack on the drain engine's AW, originates the AW-only
//     CleanUnique/MakeUnique/Evict transactions the engines never
//     generate, and swallows the AW-only B responses off the drain
//     engine's B channel (the AWONLY_ID BID mux);
//   * there is NO coh_req coherence sideband to the top level (the fabric
//     is not in this rig): the core's coh_req pulses feed ace_issue's
//     event inputs instead -- the same launch stream, consumed on-chip.
//
//   MonBus merge (D-7): client 0 = amber_monlite (the cache-event observer
//   inside the core), client 1 = rd_monlite (AR/R observation), client 2 =
//   wr_monlite (AW/W/B observation). UNIT_IDs 8'h01/02/03 distinguish the
//   streams in the merged packets.
//
//------------------------------------------------------------------------------
// Parameters: geometry per amber_pkg (HAS Table 5.0); REPL_POLICY per
//   amber_repl_t; USE_MONITOR ties all three observers off (house idiom,
//   present-vs-absent equivalence).
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (aclk / aresetn), MAS ch01/03.
//   - The monitor cfg inputs are tied to observation-only defaults
//     (monitor enabled, no error/timeout/completion/threshold actions, no
//     address windows); cam_clear tied off.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: the Task 12 ACE rig (dv/tests/test_amber_ace_top.py)
//   - Instantiated: amber_core; amber_ace_issue;
//     axi4ace_master_rd/wr_monlite; monbus_arbiter
//   - Package: amber_pkg; monitor_common_pkg
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_ace_top.py
//   Plan: dv/testplans/amber_ace_top_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_ace_top.py -v
//
//==============================================================================

module amber_ace_top
    import amber_pkg::*;
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
    localparam int CPU_RSP_W    = BUS_WIDTH,
    localparam int FILL_BEATS   = LINE_BYTES / STRB_W
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
    // D3; MAS ch01/02 signal names + ARSNOOP/AWSNOOP/RACK/WACK)
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
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [BUS_WIDTH-1:0]        m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
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
    // The core: everything cache-side. The fub_axi_* pins are the raw
    // engine-side pins; ace_issue sits between them and the ACE
    // transports (AR/AW/B); R and W bypass it (no snoop field, no
    // muxing). The coh_req launch stream feeds ace_issue's events --
    // the fabric is not in this rig, so the sideband stops at chip
    // level, not at a top-level port.
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
    logic [1:0]           fub_rresp;
    logic                 fub_rlast;
    logic [UW-1:0]        fub_ruser;
    logic                 fub_rvalid, fub_rready;

    logic [IW-1:0]        fub_awid;
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

    // B channel: wrapper-side net (the ace transports drive it, ace_issue
    // consumes it) and core-side net (ace_issue drives it, the core's
    // drain engine consumes it) -- ace_issue's BID mux bridges them
    logic [IW-1:0]        fub_bid;
    logic [1:0]           fub_bresp;
    logic [UW-1:0]        fub_buser;
    logic                 fub_bvalid, fub_bready;
    logic [IW-1:0]        core_bid;
    logic [1:0]           core_bresp;
    logic [UW-1:0]        core_buser;
    logic                 core_bvalid, core_bready;

    // the launch stream (D-8 sideband), consumed on-chip by ace_issue
    logic                 coh_req_valid;
    logic [ADDR_WIDTH-1:0] coh_req_addr;
    logic [2:0]           coh_req_type;

    // ace_issue wrapper-side AR/AW pins
    logic [IW-1:0]        iss_arid;
    logic [ADDR_WIDTH-1:0] iss_araddr;
    logic [7:0]           iss_arlen;
    logic [2:0]           iss_arsize;
    logic [1:0]           iss_arburst;
    logic                 iss_arlock;
    logic [3:0]           iss_arcache;
    logic [2:0]           iss_arprot;
    logic [3:0]           iss_arqos;
    logic [3:0]           iss_arregion;
    logic [UW-1:0]        iss_aruser;
    logic [3:0]           iss_arsnoop;
    logic                 iss_arvalid, iss_arready;
    logic [IW-1:0]        iss_awid;
    logic [ADDR_WIDTH-1:0] iss_awaddr;
    logic [7:0]           iss_awlen;
    logic [2:0]           iss_awsize;
    logic [1:0]           iss_awburst;
    logic                 iss_awlock;
    logic [3:0]           iss_awcache;
    logic [2:0]           iss_awprot;
    logic [3:0]           iss_awqos;
    logic [3:0]           iss_awregion;
    logic [UW-1:0]        iss_awuser;
    logic [2:0]           iss_awsnoop;
    logic                 iss_awvalid, iss_awready;

    logic        core_mon_valid;
    logic        core_mon_ready;
    logic [127:0] core_mon_packet;
    logic [63:0] core_mon_timestamp;
    logic [7:0]  core_mon_dropped_unused;

    amber_core #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR)
    ) u_core (
        .clk               (aclk),
        .rst_n             (aresetn),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
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
        .fub_axi_bid       (core_bid),
        .fub_axi_bresp     (core_bresp),
        .fub_axi_buser     (core_buser),
        .fub_axi_bvalid    (core_bvalid),
        .fub_axi_bready    (core_bready),
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
    // amber_ace_issue: the Table 2.8.1 map between the engines and the
    // ACE transports. The coh_req launch stream is its event input:
    // READ_SHARED / READ_UNIQUE latch the AR snoop class; CLEAN_UNIQUE
    // (the upgrade) / MAKE_UNIQUE / EVICT originate the AW-only
    // transactions; WRITE_BACK rides the drain engine's AW. Write-side
    // event wiring is class-gated so the WriteBack launch (which the
    // drain engine itself carries) never double-fires the generator.
    // ------------------------------------------------------------------
    amber_ace_issue #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_ace_issue (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .ace_rd_req    (coh_req_valid
                        && (coh_req_type == 3'(AMBER_ACE_READ_SHARED)
                            || coh_req_type == 3'(AMBER_ACE_READ_UNIQUE))),
        .ace_rd_type   (coh_req_type),
        .ace_rd_addr   (coh_req_addr),
        .ace_rd_len    (8'(FILL_BEATS - 1)),
        .ace_wr_req    (coh_req_valid
                        && (coh_req_type == 3'(AMBER_ACE_CLEAN_UNIQUE)
                            || coh_req_type == 3'(AMBER_ACE_MAKE_UNIQUE)
                            || coh_req_type == 3'(AMBER_ACE_EVICT))),
        .ace_wr_type   (coh_req_type),
        .ace_wr_addr   (coh_req_addr),
        .ace_wr_len    (8'(FILL_BEATS - 1)),
        .eng_arid      (fub_arid),
        .eng_araddr    (fub_araddr),
        .eng_arlen     (fub_arlen),
        .eng_arsize    (fub_arsize),
        .eng_arburst   (fub_arburst),
        .eng_arlock    (fub_arlock),
        .eng_arcache   (fub_arcache),
        .eng_arprot    (fub_arprot),
        .eng_arqos     (fub_arqos),
        .eng_arregion  (fub_arregion),
        .eng_aruser    (fub_aruser),
        .eng_arvalid   (fub_arvalid),
        .eng_arready   (fub_arready),
        .eng_awid      (fub_awid),
        .eng_awaddr    (fub_awaddr),
        .eng_awlen     (fub_awlen),
        .eng_awsize    (fub_awsize),
        .eng_awburst   (fub_awburst),
        .eng_awlock    (fub_awlock),
        .eng_awcache   (fub_awcache),
        .eng_awprot    (fub_awprot),
        .eng_awqos     (fub_awqos),
        .eng_awregion  (fub_awregion),
        .eng_awuser    (fub_awuser),
        .eng_awvalid   (fub_awvalid),
        .eng_awready   (fub_awready),
        .eng_bid       (core_bid),
        .eng_bresp     (core_bresp),
        .eng_buser     (core_buser),
        .eng_bvalid    (core_bvalid),
        .eng_bready    (core_bready),
        .fub_arid      (iss_arid),
        .fub_araddr    (iss_araddr),
        .fub_arlen     (iss_arlen),
        .fub_arsize    (iss_arsize),
        .fub_arburst   (iss_arburst),
        .fub_arlock    (iss_arlock),
        .fub_arcache   (iss_arcache),
        .fub_arprot    (iss_arprot),
        .fub_arqos     (iss_arqos),
        .fub_arregion  (iss_arregion),
        .fub_aruser    (iss_aruser),
        .fub_arsnoop   (iss_arsnoop),
        .fub_arvalid   (iss_arvalid),
        .fub_arready   (iss_arready),
        .fub_awid      (iss_awid),
        .fub_awaddr    (iss_awaddr),
        .fub_awlen     (iss_awlen),
        .fub_awsize    (iss_awsize),
        .fub_awburst   (iss_awburst),
        .fub_awlock    (iss_awlock),
        .fub_awcache   (iss_awcache),
        .fub_awprot    (iss_awprot),
        .fub_awqos     (iss_awqos),
        .fub_awregion  (iss_awregion),
        .fub_awuser    (iss_awuser),
        .fub_awsnoop   (iss_awsnoop),
        .fub_awvalid   (iss_awvalid),
        .fub_awready   (iss_awready),
        .fub_bid       (fub_bid),
        .fub_bresp     (fub_bresp),
        .fub_buser     (fub_buser),
        .fub_bvalid    (fub_bvalid),
        .fub_bready    (fub_bready)
    );

    // ------------------------------------------------------------------
    // Read transport: ace_issue AR -> m_axi AR, observed
    // ------------------------------------------------------------------
    logic        rd_mon_valid;
    logic        rd_mon_ready;
    logic [127:0] rd_mon_packet;
    logic [63:0] rd_mon_timestamp;

    axi4ace_master_rd_monlite #(
        .USE_MONITOR      (USE_MONITOR),
        .UNIT_ID          (8'h02),
        .AGENT_ID         (16'h00A0),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (ADDR_WIDTH),
        .AXI_DATA_WIDTH   (BUS_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH)
    ) u_rd_monlite (
        .aclk                    (aclk),
        .aresetn                 (aresetn),
        .fub_axi_arid            (iss_arid),
        .fub_axi_araddr          (iss_araddr),
        .fub_axi_arlen           (iss_arlen),
        .fub_axi_arsize          (iss_arsize),
        .fub_axi_arburst         (iss_arburst),
        .fub_axi_arlock          (iss_arlock),
        .fub_axi_arcache         (iss_arcache),
        .fub_axi_arprot          (iss_arprot),
        .fub_axi_arqos           (iss_arqos),
        .fub_axi_arregion        (iss_arregion),
        .fub_axi_aruser          (iss_aruser),
        .fub_axi_arsnoop         (iss_arsnoop),
        .fub_axi_arvalid         (iss_arvalid),
        .fub_axi_arready         (iss_arready),
        .fub_axi_rid             (fub_rid),
        .fub_axi_rdata           (fub_rdata),
        .fub_axi_rresp           (fub_rresp),
        .fub_axi_rlast           (fub_rlast),
        .fub_axi_ruser           (fub_ruser),
        .fub_axi_rvalid          (fub_rvalid),
        .fub_axi_rready          (fub_rready),
        .m_axi_arid              (m_axi_arid),
        .m_axi_araddr            (m_axi_araddr),
        .m_axi_arlen             (m_axi_arlen),
        .m_axi_arsize            (m_axi_arsize),
        .m_axi_arburst           (m_axi_arburst),
        .m_axi_arlock            (m_axi_arlock),
        .m_axi_arcache           (m_axi_arcache),
        .m_axi_arprot            (m_axi_arprot),
        .m_axi_arqos             (m_axi_arqos),
        .m_axi_arregion          (m_axi_arregion),
        .m_axi_aruser            (m_axi_aruser),
        .m_axi_arsnoop           (m_axi_arsnoop),
        .m_axi_arvalid           (m_axi_arvalid),
        .m_axi_arready           (m_axi_arready),
        .m_axi_rid               (m_axi_rid),
        .m_axi_rdata             (m_axi_rdata),
        .m_axi_rresp             (m_axi_rresp),
        .m_axi_rlast             (m_axi_rlast),
        .m_axi_ruser             (m_axi_ruser),
        .m_axi_rvalid            (m_axi_rvalid),
        .m_axi_rready            (m_axi_rready),
        .m_axi_rack              (m_axi_rack),
        .busy                    (),
        .cam_clear               (1'b0),
        .cfg_monitor_enable      (1'b1),
        .cfg_error_enable        (1'b0),
        .cfg_timeout_enable      (1'b0),
        .cfg_compl_enable        (1'b0),
        .cfg_threshold_enable    (1'b0),
        .cfg_timeout_cycles      (16'h0000),
        .cfg_freq_sel            (4'h0),
        .cfg_axi_pkt_mask        (16'h0000),
        .cfg_latency_threshold   (32'h0000_0000),
        .cfg_addr_check_enable   (1'b0),
        .cfg_addr_match_enable   (1'b0),
        .cfg_addr_range_enable   ('0),
        .cfg_addr_range_low      ('0),
        .cfg_addr_range_high     ('0),
        .i_mon_time              (i_mon_time),
        .monbus_valid            (rd_mon_valid),
        .monbus_ready            (rd_mon_ready),
        .monbus_packet           (rd_mon_packet),
        .monbus_timestamp        (rd_mon_timestamp),
        .active_transactions     (),
        .error_count             (),
        .transaction_count       (),
        .dropped_count           (),
        .refused_count           ()
    );

    // ------------------------------------------------------------------
    // Write transport: ace_issue AW -> m_axi AW (W and B bypass ace_issue
    // on the data path; B's valid/ready routing already passes through
    // it), observed
    // ------------------------------------------------------------------
    logic        wr_mon_valid;
    logic        wr_mon_ready;
    logic [127:0] wr_mon_packet;
    logic [63:0] wr_mon_timestamp;

    axi4ace_master_wr_monlite #(
        .USE_MONITOR      (USE_MONITOR),
        .UNIT_ID          (8'h03),
        .AGENT_ID         (16'h00A0),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (ADDR_WIDTH),
        .AXI_DATA_WIDTH   (BUS_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH)
    ) u_wr_monlite (
        .aclk                    (aclk),
        .aresetn                 (aresetn),
        .fub_axi_awid            (iss_awid),
        .fub_axi_awaddr          (iss_awaddr),
        .fub_axi_awlen           (iss_awlen),
        .fub_axi_awsize          (iss_awsize),
        .fub_axi_awburst         (iss_awburst),
        .fub_axi_awlock          (iss_awlock),
        .fub_axi_awcache         (iss_awcache),
        .fub_axi_awprot          (iss_awprot),
        .fub_axi_awqos           (iss_awqos),
        .fub_axi_awregion        (iss_awregion),
        .fub_axi_awuser          (iss_awuser),
        .fub_axi_awsnoop         (iss_awsnoop),
        .fub_axi_awvalid         (iss_awvalid),
        .fub_axi_awready         (iss_awready),
        .fub_axi_wdata           (fub_wdata),
        .fub_axi_wstrb           (fub_wstrb),
        .fub_axi_wlast           (fub_wlast),
        .fub_axi_wuser           (fub_wuser),
        .fub_axi_wvalid          (fub_wvalid),
        .fub_axi_wready          (fub_wready),
        .fub_axi_bid             (fub_bid),
        .fub_axi_bresp           (fub_bresp),
        .fub_axi_buser           (fub_buser),
        .fub_axi_bvalid          (fub_bvalid),
        .fub_axi_bready          (fub_bready),
        .m_axi_awid              (m_axi_awid),
        .m_axi_awaddr            (m_axi_awaddr),
        .m_axi_awlen             (m_axi_awlen),
        .m_axi_awsize            (m_axi_awsize),
        .m_axi_awburst           (m_axi_awburst),
        .m_axi_awlock            (m_axi_awlock),
        .m_axi_awcache           (m_axi_awcache),
        .m_axi_awprot            (m_axi_awprot),
        .m_axi_awqos             (m_axi_awqos),
        .m_axi_awregion          (m_axi_awregion),
        .m_axi_awuser            (m_axi_awuser),
        .m_axi_awsnoop           (m_axi_awsnoop),
        .m_axi_awvalid           (m_axi_awvalid),
        .m_axi_awready           (m_axi_awready),
        .m_axi_wdata             (m_axi_wdata),
        .m_axi_wstrb             (m_axi_wstrb),
        .m_axi_wlast             (m_axi_wlast),
        .m_axi_wuser             (m_axi_wuser),
        .m_axi_wvalid            (m_axi_wvalid),
        .m_axi_wready            (m_axi_wready),
        .m_axi_bid               (m_axi_bid),
        .m_axi_bresp             (m_axi_bresp),
        .m_axi_buser             (m_axi_buser),
        .m_axi_bvalid            (m_axi_bvalid),
        .m_axi_bready            (m_axi_bready),
        .m_axi_wack              (m_axi_wack),
        .busy                    (),
        .cam_clear               (1'b0),
        .cfg_monitor_enable      (1'b1),
        .cfg_error_enable        (1'b0),
        .cfg_timeout_enable      (1'b0),
        .cfg_compl_enable        (1'b0),
        .cfg_threshold_enable    (1'b0),
        .cfg_timeout_cycles      (16'h0000),
        .cfg_freq_sel            (4'h0),
        .cfg_axi_pkt_mask        (16'h0000),
        .cfg_latency_threshold   (32'h0000_0000),
        .cfg_addr_check_enable   (1'b0),
        .cfg_addr_match_enable   (1'b0),
        .cfg_addr_range_enable   ('0),
        .cfg_addr_range_low      ('0),
        .cfg_addr_range_high     ('0),
        .i_mon_time              (i_mon_time),
        .monbus_valid            (wr_mon_valid),
        .monbus_ready            (wr_mon_ready),
        .monbus_packet           (wr_mon_packet),
        .monbus_timestamp        (wr_mon_timestamp),
        .active_transactions     (),
        .error_count             (),
        .transaction_count       (),
        .dropped_count           (),
        .refused_count           ()
    );

    // ------------------------------------------------------------------
    // D-7 MonBus arbiter: {amber_monlite, rd_monlite, wr_monlite} -> the
    // one MonBus port pair
    // ------------------------------------------------------------------
    logic                    arb_vld [3];
    logic                    arb_rdy [3];
    monitor_common_pkg::monitor_packet_t   arb_pkt [3];
    monitor_common_pkg::monbus_timestamp_t arb_ts  [3];

    assign arb_vld[0] = core_mon_valid;
    assign arb_vld[1] = rd_mon_valid;
    assign arb_vld[2] = wr_mon_valid;
    assign core_mon_ready = arb_rdy[0];
    assign rd_mon_ready   = arb_rdy[1];
    assign wr_mon_ready   = arb_rdy[2];
    assign arb_pkt[0] = core_mon_packet;
    assign arb_pkt[1] = rd_mon_packet;
    assign arb_pkt[2] = wr_mon_packet;
    assign arb_ts[0]  = core_mon_timestamp;
    assign arb_ts[1]  = rd_mon_timestamp;
    assign arb_ts[2]  = wr_mon_timestamp;

    monbus_arbiter #(
        .CLIENTS            (3),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_monbus_arbiter (
        .axi_aclk            (aclk),
        .axi_aresetn         (aresetn),
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
