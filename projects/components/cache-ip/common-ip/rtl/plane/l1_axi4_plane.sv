// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_axi4_plane
// Purpose:
//   AXI4 fabric plane for the cache-ip shared MESI L1 (cache-ip plane
//   restructure, Task 2): the protocol-generation boundary that sits between
//   the coherence core plane and the pair-rig fabric. Closes the ACE snoop
//   responder (l1_snoop_resp), the house AXI4 read/write monlite transports,
//   and re-exports the D-8 coherence sideband launch events. The core-facing
//   fabric seam matches the bundle l1_core exposes.
//
// Documentation: projects/components/cache-ip/common-ip/docs/l1_fabric_contract.md
// Subsystem: cache-ip (common)
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: l1_axi4_plane
//==============================================================================
// Description:
//   The pair-rig fabric plane: l1_snoop_resp speaks ACE on the snoop pins and
//   presents the core-facing snoop seam to the coherence core plane; the
//   axi4_master_rd/wr_monlite transports convert the raw fub_axi_* engine
//   pins into the measured m_axi_* memory-side AXI4 interface. The D-8
//   coh_req_* launch events pass straight through to the top-level pair-rig
//   sideband. A registered AC-pending counter (sn_want_o) samples external AC
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
//     the plane is reset-synchronized by its top (amber_top / jet_top), so this
//     module consumes the synchronized reset.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_top, jet_top (Task 3/4)
//   - Instantiates: l1_snoop_resp, axi4_master_rd_monlite, axi4_master_wr_monlite
//   - Package: l1_pkg
//
//==============================================================================

module l1_axi4_plane
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
    localparam int STRB_W        = BUS_WIDTH / 8,
    localparam int IW            = AXI_ID_WIDTH,
    localparam int UW            = AXI_USER_WIDTH
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // AXI4 memory masters via the monlite-wrapped transports (pair rig)
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
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [BUS_WIDTH-1:0]        m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [UW-1:0]               m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

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

    // ------------------------------------------------------------------
    // ACE snoop responder (the pair rig still exposes ACE snoop pins)
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
    input  logic [2:0]                  fuby_axi_awsize,
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
    // Pair-rig coherence sideband from the coherence core plane
    // ------------------------------------------------------------------
    input  logic                        core_coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       core_coh_req_addr,
    input  logic [2:0]                  core_coh_req_type,

    // ------------------------------------------------------------------
    // Pair-rig coherence sideband exported to the fabric
    // ------------------------------------------------------------------
    output logic                        coh_req_valid,
    output logic [ADDR_WIDTH-1:0]       coh_req_addr,
    output logic [2:0]                  coh_req_type,

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
    // Coherence sideband pass-through (axi4 plane: exported to the fabric)
    // ------------------------------------------------------------------
    assign coh_req_valid = core_coh_req_valid;
    assign coh_req_addr  = core_coh_req_addr;
    assign coh_req_type  = core_coh_req_type;

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
    // Internal 2-bit RRESP from the read transport; the core seam carries
    // a 4-bit fub_axi_rresp per l1_core's port contract.
    // ------------------------------------------------------------------
    logic [1:0] fub_rresp_raw;
    assign fub_axi_rresp = {2'b0, fub_rresp_raw};

    // ------------------------------------------------------------------
    // Read transport: fub_axi (the fill engine) -> m_axi AR/R, observed
    // ------------------------------------------------------------------
    logic        rd_mon_valid;
    logic        rd_mon_ready;
    logic [127:0] rd_mon_packet;
    logic [63:0] rd_mon_timestamp;

    axi4_master_rd_monlite #(
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
        .fub_axi_arid            (fub_axi_arid),
        .fub_axi_araddr          (fub_axi_araddr),
        .fub_axi_arlen           (fub_axi_arlen),
        .fub_axi_arsize          (fub_axi_arsize),
        .fub_axi_arburst         (fub_axi_arburst),
        .fub_axi_arlock          (fub_axi_arlock),
        .fub_axi_arcache         (fub_axi_arcache),
        .fub_axi_arprot          (fub_axi_arprot),
        .fub_axi_arqos           (fub_axi_arqos),
        .fub_axi_arregion        (fub_axi_arregion),
        .fub_axi_aruser          (fub_axi_aruser),
        .fub_axi_arvalid         (fub_axi_arvalid),
        .fub_axi_arready         (fub_axi_arready),
        .fub_axi_rid             (fub_axi_rid),
        .fub_axi_rdata           (fub_axi_rdata),
        .fub_axi_rresp           (fub_rresp_raw),
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
        .m_axi_arvalid           (m_axi_arvalid),
        .m_axi_arready           (m_axi_arready),
        .m_axi_rid               (m_axi_rid),
        .m_axi_rdata             (m_axi_rdata),
        .m_axi_rresp             (m_axi_rresp),
        .m_axi_rlast             (m_axi_rlast),
        .m_axi_ruser             (m_axi_ruser),
        .m_axi_rvalid            (m_axi_rvalid),
        .m_axi_rready            (m_axi_rready),
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
    // Write transport: fub_axi (the drain engine) -> m_axi AW/W/B, observed
    // ------------------------------------------------------------------
    logic        wr_mon_valid;
    logic        wr_mon_ready;
    logic [127:0] wr_mon_packet;
    logic [63:0] wr_mon_timestamp;

    axi4_master_wr_monlite #(
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
        .fub_axi_awid            (fub_axi_awid),
        .fub_axi_awaddr          (fub_axi_awaddr),
        .fub_axi_awlen           (fub_axi_awlen),
        .fub_axi_awsize          (fub_axi_awsize),
        .fub_axi_awburst         (fub_axi_awburst),
        .fub_axi_awlock          (fub_axi_awlock),
        .fub_axi_awcache         (fub_axi_awcache),
        .fub_axi_awprot          (fub_axi_awprot),
        .fub_axi_awqos           (fub_axi_awqos),
        .fub_axi_awregion        (fub_axi_awregion),
        .fub_axi_awuser          (fub_axi_awuser),
        .fub_axi_awvalid         (fub_axi_awvalid),
        .fub_axi_awready         (fub_axi_awready),
        .fub_axi_wdata           (fub_axi_wdata),
        .fub_axi_wstrb           (fub_axi_wstrb),
        .fub_axi_wlast           (fub_axi_wlast),
        .fub_axi_wuser           (fub_axi_wuser),
        .fub_axi_wvalid          (fub_axi_wvalid),
        .fub_axi_wready          (fub_axi_wready),
        .fub_axi_bid             (fub_axi_bid),
        .fub_axi_bresp           (fub_axi_bresp),
        .fub_axi_buser           (fub_axi_buser),
        .fub_axi_bvalid          (fub_axi_bvalid),
        .fub_axi_bready          (fub_axi_bready),
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

endmodule : l1_axi4_plane
