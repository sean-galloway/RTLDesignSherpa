// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_ace_plane
// Purpose:
//   ACE fabric plane for the cache-ip shared MESI L1 (cache-ip plane
//   restructure, Task 2): the protocol-generation boundary that sits between
//   the coherence core plane and the onyx-rig ACE fabric. Closes the ACE snoop
//   responder (l1_snoop_resp), the shared l1_ace_issue event-to-transaction
//   map, and the house axi4ace_master_rd/wr_monlite transports. The core-facing
//   fabric seam matches the bundle l1_core exposes; the D-8 coherence launch
//   events are consumed on-chip by l1_ace_issue.
//
// Documentation: projects/components/cache-ip/common-ip/docs/l1_fabric_contract.md
// Subsystem: cache-ip (common)
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: l1_ace_plane
//==============================================================================
// Description:
//   The onyx-rig fabric plane: l1_snoop_resp speaks ACE on the snoop pins and
//   presents the core-facing snoop seam to the coherence core plane;
//   l1_ace_issue maps the D-8 launch events into ACE ARSNOOP/AWSNOOP fields
//   and swallows AW-only B responses; the axi4ace_master_rd/wr_monlite
//   transports expose the measured ACE memory-side interface with auto-pulsed
//   RACK/WACK. A registered AC-pending counter (sn_want_o) samples external AC
//   handshakes and the snoop grant for the jet coherence core's J6 throttle.
//
//   The MonBus observation streams from the two transports are exported to the
//   top, which merges them with the core's l1_monlite stream on the D-7
//   monbus_arbiter.
//
//------------------------------------------------------------------------------
// Parameters: geometry per l1_pkg (HAS Table 5.0); AXI_ID_WIDTH / AXI_USER_WIDTH
//   match the fub_axi engine pins; USE_MONITOR ties the transport observers off.
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (aclk / aresetn).
//   - The port aresetn is treated as async-assert of unknown deassert quality;
//     the plane is reset-synchronized by its top (amber_ace_top / jet_ace_top),
//     so this module consumes the synchronized reset.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_ace_top, jet_ace_top (Task 3/4)
//   - Instantiates: l1_snoop_resp, l1_ace_issue,
//                   axi4ace_master_rd_monlite, axi4ace_master_wr_monlite
//   - Package: l1_pkg
//
//==============================================================================

module l1_ace_plane
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int WAYS           = AMBER_WAYS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter bit USE_MONITOR    = 1'b1,
    // MonBus agent id stamped by the two transport observers: amber's
    // 16'h00A0 by default; the jet tops pass 16'h00A1 (their historical
    // stream id, jet_ace_top.sv pre-restructure).
    parameter logic [15:0] AGENT_ID = 16'h00A0,
    localparam int STRB_W        = BUS_WIDTH / 8,
    localparam int IW            = AXI_ID_WIDTH,
    localparam int UW            = AXI_USER_WIDTH,
    localparam int FILL_BEATS    = LINE_BYTES / STRB_W
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // ACE memory masters via the monlite-wrapped transports (onyx rig)
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
    input  logic [3:0]                  m_axi_rresp,
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
    // ACE snoop responder
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
    // fub_axi read master side (from l1_fill in the coherence core plane)
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               fub_axi_arid,
    input  logic [ADDR_WIDTH-1:0]       fub_axi_araddr,
    input  logic [7:0]                  fub_axi_arlen,
    input  logic [2:0]                  fub_axi_arsize,
    input  logic [1:0]                  fub_axi_arburst,
    input  logic                        fub_axi_arlock,
    input  logic [3:0]                  fub_axi_arcache,
    input  logic [2:0]                  fub_axi_arprot,
    input  logic [3:0]                  fub_axi_arqos,
    input  logic [3:0]                  fub_axi_arregion,
    input  logic [UW-1:0]               fub_axi_aruser,
    input  logic                        fub_axi_arvalid,
    output logic                        fub_axi_arready,
    output logic [IW-1:0]               fub_axi_rid,
    output logic [BUS_WIDTH-1:0]        fub_axi_rdata,
    output logic [3:0]                  fub_axi_rresp,
    output logic                        fub_axi_rlast,
    output logic [UW-1:0]               fub_axi_ruser,
    output logic                        fub_axi_rvalid,
    input  logic                        fub_axi_rready,

    // ------------------------------------------------------------------
    // fub_axi write master side (from l1_drain in the coherence core plane)
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               fub_axi_awid,
    input  logic [ADDR_WIDTH-1:0]       fub_axi_awaddr,
    input  logic [7:0]                  fub_axi_awlen,
    input  logic [2:0]                  fub_axi_awsize,
    input  logic [1:0]                  fub_axi_awburst,
    input  logic                        fub_axi_awlock,
    input  logic [3:0]                  fub_axi_awcache,
    input  logic [2:0]                  fub_axi_awprot,
    input  logic [3:0]                  fub_axi_awqos,
    input  logic [3:0]                  fub_axi_awregion,
    input  logic [UW-1:0]               fub_axi_awuser,
    input  logic                        fub_axi_awvalid,
    output logic                        fub_axi_awready,
    input  logic [BUS_WIDTH-1:0]        fub_axi_wdata,
    input  logic [STRB_W-1:0]           fub_axi_wstrb,
    input  logic                        fub_axi_wlast,
    input  logic [UW-1:0]               fub_axi_wuser,
    input  logic                        fub_axi_wvalid,
    output logic                        fub_axi_wready,
    output logic [IW-1:0]               fub_axi_bid,
    output logic [1:0]                  fub_axi_bresp,
    output logic [UW-1:0]               fub_axi_buser,
    output logic                        fub_axi_bvalid,
    input  logic                        fub_axi_bready,

    // ------------------------------------------------------------------
    // Fabric (snoop) seam to the coherence core plane
    // ------------------------------------------------------------------
    output logic                        ctrl_snoop_req,
    input  logic                        ctrl_snoop_ready,
    input  logic                        ctrl_snoop_safe,
    output logic [2:0]                  ctrl_snoop_type,
    output logic [ADDR_WIDTH-1:0]       ctrl_snoop_addr,
    input  logic [AMBER_CRRESP_WIDTH-1:0] ctrl_crresp,
    input  logic [BUS_WIDTH-1:0]        ctrl_cddata,
    input  logic                        ctrl_cdlast,
    input  logic                        ctrl_cdvalid,
    output logic                        ctrl_cdready,

    // ------------------------------------------------------------------
    // Pair-rig coherence sideband from the coherence core plane (consumed
    // on-chip by l1_ace_issue; not exported to the top level)
    // ------------------------------------------------------------------
    input  logic                        coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       coh_req_addr,
    input  logic [2:0]                  coh_req_type,

    // ------------------------------------------------------------------
    // AC-pending throttle (jet J6; sampled from the external AC handshake)
    // ------------------------------------------------------------------
    output logic                        sn_want_o,

    // ------------------------------------------------------------------
    // Rig-level timestamp source for the transport observers
    // ------------------------------------------------------------------
    input  logic [63:0]                 i_mon_time,

    // ------------------------------------------------------------------
    // MonBus observation from the rd/wr transports (top merges with core)
    // ------------------------------------------------------------------
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp
);

    // ------------------------------------------------------------------
    // ACE shareability domain and barrier fields (IHI 0022H D2.1.1-2,
    // D3.1.1-2). Every transaction issued is coherent and the onyx rig has
    // a single shareability domain, so both address channels carry Outer
    // Shareable; amber/jet issue no barrier transactions, so AxBAR is 0b00.
    // These constants move here from amber_ace_top.sv:546-547.
    // ------------------------------------------------------------------
    localparam logic [1:0] ACE_DOMAIN = 2'b10;   // Outer Shareable
    localparam logic [1:0] ACE_BAR    = 2'b00;   // normal access, respecting barriers

    // ------------------------------------------------------------------
    // ACE snoop responder
    // ------------------------------------------------------------------
    l1_snoop_resp #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (BUS_WIDTH),
        .LINE_BYTES (LINE_BYTES)
    ) u_snoop (
        .aclk           (aclk),
        .aresetn        (aresetn),
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
        .ctrl_snoop_req    (ctrl_snoop_req),
        .ctrl_snoop_addr   (ctrl_snoop_addr),
        .ctrl_snoop_type   (ctrl_snoop_type),
        .ctrl_snoop_ready  (ctrl_snoop_ready),
        .ctrl_snoop_safe   (ctrl_snoop_safe),
        .ctrl_crresp       (ctrl_crresp),
        .ctrl_cddata       (ctrl_cddata),
        .ctrl_cdlast       (ctrl_cdlast),
        .ctrl_cdvalid      (ctrl_cdvalid),
        .ctrl_cdready      (ctrl_cdready)
    );

    // ------------------------------------------------------------------
    // AC-pending counter (jet_top.sv:1144-1159). +1 on external AC
    // handshake, -1 on the snoop grant cycle (u_snoop.ctrl_snoop_req).
    // Registered only to avoid a combinational loop through the fabric.
    // ------------------------------------------------------------------
    logic [1:0] r_sn_pend_cnt;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_sn_pend_cnt <= '0;
        end else begin
            case ({(m_axi_acvalid & m_axi_acready), ctrl_snoop_req})
                2'b10:   r_sn_pend_cnt <= r_sn_pend_cnt + 2'd1;
                2'b01:   r_sn_pend_cnt <= (r_sn_pend_cnt != '0)
                                          ? r_sn_pend_cnt - 2'd1 : '0;
                default: ;  // 00: none; 11: one arrives as one is granted
            endcase
        end
    )

    assign sn_want_o = (r_sn_pend_cnt != '0);

    // ------------------------------------------------------------------
    // l1_ace_issue wrapper-side AR/AW pins (between ace_issue and the
    // ACE transports)
    // ------------------------------------------------------------------
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

    // ------------------------------------------------------------------
    // B channel: wrapper-side net (the ACE transports drive it, ace_issue
    // consumes it) and core-side net (ace_issue drives it, the core's
    // drain engine consumes it) -- ace_issue's BID mux bridges them.
    // ------------------------------------------------------------------
    logic [IW-1:0]        fub_bid;
    logic [1:0]           fub_bresp;
    logic [UW-1:0]        fub_buser;
    logic                 fub_bvalid, fub_bready;

    // ------------------------------------------------------------------
    // l1_ace_issue: the Table 2.8.1 map between the engines and the ACE
    // transports. The coh_req launch stream is its event input.
    // ------------------------------------------------------------------
    l1_ace_issue #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_ace_issue (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .ace_rd_req    (coh_req_valid
                        && (coh_req_type == 3'(AMBER_ACE_READ_NOT_SHARED_DIRTY)
                            || coh_req_type == 3'(AMBER_ACE_READ_UNIQUE)
                            || coh_req_type == 3'(AMBER_ACE_CLEAN_UNIQUE)
                            || coh_req_type == 3'(AMBER_ACE_MAKE_UNIQUE))),
        .ace_rd_type   (coh_req_type),
        .ace_rd_addr   (coh_req_addr),
        .ace_rd_len    (8'(FILL_BEATS - 1)),
        .ace_wr_req    (coh_req_valid
                        && (coh_req_type == 3'(AMBER_ACE_EVICT))),
        .ace_wr_type   (coh_req_type),
        .ace_wr_addr   (coh_req_addr),
        .ace_wr_len    (8'(FILL_BEATS - 1)),
        .eng_arid      (fub_axi_arid),
        .eng_araddr    (fub_axi_araddr),
        .eng_arlen     (fub_axi_arlen),
        .eng_arsize    (fub_axi_arsize),
        .eng_arburst   (fub_axi_arburst),
        .eng_arlock    (fub_axi_arlock),
        .eng_arcache   (fub_axi_arcache),
        .eng_arprot    (fub_axi_arprot),
        .eng_arqos     (fub_axi_arqos),
        .eng_arregion  (fub_axi_arregion),
        .eng_aruser    (fub_axi_aruser),
        .eng_arvalid   (fub_axi_arvalid),
        .eng_arready   (fub_axi_arready),
        .eng_awid      (fub_axi_awid),
        .eng_awaddr    (fub_axi_awaddr),
        .eng_awlen     (fub_axi_awlen),
        .eng_awsize    (fub_axi_awsize),
        .eng_awburst   (fub_axi_awburst),
        .eng_awlock    (fub_axi_awlock),
        .eng_awcache   (fub_axi_awcache),
        .eng_awprot    (fub_axi_awprot),
        .eng_awqos     (fub_axi_awqos),
        .eng_awregion  (fub_axi_awregion),
        .eng_awuser    (fub_axi_awuser),
        .eng_awvalid   (fub_axi_awvalid),
        .eng_awready   (fub_axi_awready),
        .eng_bid       (fub_axi_bid),
        .eng_bresp     (fub_axi_bresp),
        .eng_buser     (fub_axi_buser),
        .eng_bvalid    (fub_axi_bvalid),
        .eng_bready    (fub_axi_bready),
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
        .AGENT_ID         (AGENT_ID),
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
        .fub_axi_ardomain        (ACE_DOMAIN),
        .fub_axi_arbar           (ACE_BAR),
        .fub_axi_arvalid         (iss_arvalid),
        .fub_axi_arready         (iss_arready),
        .fub_axi_rid             (fub_axi_rid),
        .fub_axi_rdata           (fub_axi_rdata),
        .fub_axi_rresp           (fub_axi_rresp),
        .fub_axi_rlast           (fub_axi_rlast),
        .fub_axi_ruser           (fub_axi_ruser),
        .fub_axi_rvalid          (fub_axi_rvalid),
        .fub_axi_rready          (fub_axi_rready),
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
        .m_axi_ardomain          (m_axi_ardomain),
        .m_axi_arbar             (m_axi_arbar),
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
    // on the data path; B's valid/ready routing passes through it)
    // ------------------------------------------------------------------
    logic        wr_mon_valid;
    logic        wr_mon_ready;
    logic [127:0] wr_mon_packet;
    logic [63:0] wr_mon_timestamp;

    axi4ace_master_wr_monlite #(
        .USE_MONITOR      (USE_MONITOR),
        .UNIT_ID          (8'h03),
        .AGENT_ID         (AGENT_ID),
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
        .fub_axi_awdomain        (ACE_DOMAIN),
        .fub_axi_awbar           (ACE_BAR),
        .fub_axi_awvalid         (iss_awvalid),
        .fub_axi_awready         (iss_awready),
        .fub_axi_wdata           (fub_axi_wdata),
        .fub_axi_wstrb           (fub_axi_wstrb),
        .fub_axi_wlast           (fub_axi_wlast),
        .fub_axi_wuser           (fub_axi_wuser),
        .fub_axi_wvalid          (fub_axi_wvalid),
        .fub_axi_wready          (fub_axi_wready),
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
        .m_axi_awdomain          (m_axi_awdomain),
        .m_axi_awbar             (m_axi_awbar),
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
    // MonBus merge of the two transport observers. The top-level plane
    // consumer merges this with the core's l1_monlite stream.
    // ------------------------------------------------------------------
    logic                    arb_vld [2];
    logic                    arb_rdy [2];
    ocelus_common_pkg::monitor_packet_t   arb_pkt [2];
    ocelus_common_pkg::monbus_timestamp_t arb_ts  [2];

    assign arb_vld[0] = rd_mon_valid;
    assign arb_vld[1] = wr_mon_valid;
    assign rd_mon_ready = arb_rdy[0];
    assign wr_mon_ready = arb_rdy[1];
    assign arb_pkt[0] = rd_mon_packet;
    assign arb_pkt[1] = wr_mon_packet;
    assign arb_ts[0]  = rd_mon_timestamp;
    assign arb_ts[1]  = wr_mon_timestamp;

    monbus_arbiter #(
        .CLIENTS            (2),
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

endmodule : l1_ace_plane
