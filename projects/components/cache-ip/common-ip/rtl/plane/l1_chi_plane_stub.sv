// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_chi_plane_stub
// Purpose:
//   CHI fabric plane stub for the cache-ip shared MESI L1 (cache-ip plane
//   restructure, Task 5): an elaboration-only proof that the core-facing
//   fabric seam is complete and named consistently enough for a future CHI
//   plane to drop in beside the AXI4 and ACE planes.  The core side carries
//   the full seam (snoop in/out, fub_axi fill/drain engine, coh_req launch
//   events, sn_want throttle, MonBus observer); the memory side carries a
//   CHI channel pin skeleton (RXREQ/RXSNP/TXREQ/TXRSP/TXDAT/RXDAT groups)
//   tied off.  No protocol logic is implemented.
//
// Documentation: projects/components/cache-ip/common-ip/docs/l1_fabric_contract.md
// Subsystem: cache-ip (common)
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

//==============================================================================
// Module: l1_chi_plane_stub
//==============================================================================
// Description:
//   Elaboration-only placeholder.  A real CHI plane would replace the
//   ACE-derived snoop seam with CHI snoop semantics (RXSNP/RXRSP/RXDAT) and
//   map the coherence-core launch events into CHI REQ/RSP/DAT channels.  This
//   stub proves that the core-facing port list is syntactically compatible
//   with the l1_axi4_plane / l1_ace_plane seam and that the module can be
//   linted/elaborated standalone.
//
//   The MonBus observation stream is tied off; a real implementation would
//   observe the CHI transport layers and export a merged stream to the top,
//   exactly as the AXI4/ACE planes merge their rd/wr transport observers.
//
//------------------------------------------------------------------------------
// Parameters: geometry per l1_pkg (HAS Table 5.0); AXI_ID_WIDTH / AXI_USER_WIDTH
//   match the fub_axi engine pins; USE_MONITOR is reserved for a future CHI
//   transport observer; AGENT_ID selects the per-IP MonBus stream id.
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (aclk / aresetn).
//   - No sequential logic; the stub is purely combinational tie-offs.
//   - CHI channel widths are illustrative placeholders.  A real CHI plane
//     would take width parameters or import a CHI package.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - l1_axi4_plane, l1_ace_plane — the seam this stub mirrors
//   - Package: l1_pkg
//
//==============================================================================

module l1_chi_plane_stub
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
    // MonBus agent id reserved for a future CHI transport observer:
    // amber's historical id is 16'h00A0, jet's is 16'h00A1.
    parameter logic [15:0] AGENT_ID = 16'h00A0,
    localparam int STRB_W        = BUS_WIDTH / 8,
    localparam int IW            = AXI_ID_WIDTH,
    localparam int UW            = AXI_USER_WIDTH,
    // CHI channel flit widths — placeholders; a real package would own these.
    localparam int CHI_REQ_W     = 80,
    localparam int CHI_RSP_W     = 48,
    localparam int CHI_DAT_W     = BUS_WIDTH + 16,
    localparam int CHI_SNP_W     = 56
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // CHI memory-side channel skeleton (RN-facing the interconnect)
    // ------------------------------------------------------------------
    // RXREQ: request messages from the interconnect (includes DVM)
    input  logic [CHI_REQ_W-1:0]        chi_rxreq_flit,
    input  logic                        chi_rxreq_valid,
    output logic                        chi_rxreq_ready,

    // RXSNP: snoop requests from the interconnect
    input  logic [CHI_SNP_W-1:0]        chi_rxsnp_flit,
    input  logic                        chi_rxsnp_valid,
    output logic                        chi_rxsnp_ready,

    // TXREQ: coherent requests to the interconnect
    output logic [CHI_REQ_W-1:0]        chi_txreq_flit,
    output logic                        chi_txreq_valid,
    input  logic                        chi_txreq_ready,

    // TXRSP: responses to the interconnect
    output logic [CHI_RSP_W-1:0]        chi_txrsp_flit,
    output logic                        chi_txrsp_valid,
    input  logic                        chi_txrsp_ready,

    // TXDAT: write data / snoop response data to the interconnect
    output logic [CHI_DAT_W-1:0]        chi_txdat_flit,
    output logic                        chi_txdat_valid,
    input  logic                        chi_txdat_ready,

    // RXDAT: read data / snoop data from the interconnect
    input  logic [CHI_DAT_W-1:0]        chi_rxdat_flit,
    input  logic                        chi_rxdat_valid,
    output logic                        chi_rxdat_ready,

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
    // AC-pending throttle (reserved for future CHI snoop back-pressure map)
    // ------------------------------------------------------------------
    output logic                        sn_want_o,

    // ------------------------------------------------------------------
    // Rig-level timestamp source for a future transport observer
    // ------------------------------------------------------------------
    input  logic [63:0]                 i_mon_time,

    // ------------------------------------------------------------------
    // MonBus observation (reserved; tied off in this stub)
    // ------------------------------------------------------------------
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp
);

    // Elaboration-time geometry checks (same contract as the core blocks)
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("l1_chi_plane_stub: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("l1_chi_plane_stub: LINE_BYTES must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("l1_chi_plane_stub: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("l1_chi_plane_stub: WAYS must be >= 2");
    end

    // ------------------------------------------------------------------
    // Core-facing seam outputs — tied off.  A real CHI plane would drive
    // these from CHI RXREQ/RXSNP/RXDAT/RXRSP decoding and the fill/drain
    // engines would be replaced by CHI transport/state machines.
    // ------------------------------------------------------------------
    assign fub_axi_arready = 1'b0;
    assign fub_axi_rid     = '0;
    assign fub_axi_rdata   = '0;
    assign fub_axi_rresp   = '0;
    assign fub_axi_rlast   = 1'b0;
    assign fub_axi_ruser   = '0;
    assign fub_axi_rvalid  = 1'b0;

    assign fub_axi_awready = 1'b0;
    assign fub_axi_wready  = 1'b0;
    assign fub_axi_bid     = '0;
    assign fub_axi_bresp   = '0;
    assign fub_axi_buser   = '0;
    assign fub_axi_bvalid  = 1'b0;

    assign ctrl_snoop_req  = 1'b0;
    assign ctrl_snoop_type = '0;
    assign ctrl_snoop_addr = '0;
    assign ctrl_cdready    = 1'b0;

    assign coh_req_valid   = 1'b0;
    assign coh_req_addr    = '0;
    assign coh_req_type    = '0;

    assign sn_want_o       = 1'b0;

    assign mon_valid       = 1'b0;
    assign mon_packet      = '0;
    assign mon_timestamp   = '0;

    // ------------------------------------------------------------------
    // CHI memory-side outputs — tied off.
    // ------------------------------------------------------------------
    assign chi_txreq_flit  = '0;
    assign chi_txreq_valid = 1'b0;
    assign chi_txrsp_flit  = '0;
    assign chi_txrsp_valid = 1'b0;
    assign chi_txdat_flit  = '0;
    assign chi_txdat_valid = 1'b0;
    assign chi_rxreq_ready = 1'b0;
    assign chi_rxsnp_ready = 1'b0;
    assign chi_rxdat_ready = 1'b0;

    // ------------------------------------------------------------------
    // Inputs that are intentionally not used in an elaboration-only stub.
    // ------------------------------------------------------------------
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused;
    assign unused = &{1'b0,
                      aclk, aresetn,
                      chi_rxreq_flit, chi_rxreq_valid,
                      chi_rxsnp_flit, chi_rxsnp_valid,
                      chi_txreq_ready, chi_txrsp_ready, chi_txdat_ready,
                      chi_rxdat_flit, chi_rxdat_valid,
                      fub_axi_arid, fub_axi_araddr, fub_axi_arlen,
                      fub_axi_arsize, fub_axi_arburst, fub_axi_arlock,
                      fub_axi_arcache, fub_axi_arprot, fub_axi_arqos,
                      fub_axi_arregion, fub_axi_aruser, fub_axi_arvalid,
                      fub_axi_rready,
                      fub_axi_awid, fub_axi_awaddr, fub_axi_awlen,
                      fub_axi_awsize, fub_axi_awburst, fub_axi_awlock,
                      fub_axi_awcache, fub_axi_awprot, fub_axi_awqos,
                      fub_axi_awregion, fub_axi_awuser, fub_axi_awvalid,
                      fub_axi_wdata, fub_axi_wstrb, fub_axi_wlast,
                      fub_axi_wuser, fub_axi_wvalid, fub_axi_bready,
                      ctrl_snoop_ready, ctrl_snoop_safe,
                      ctrl_crresp, ctrl_cddata, ctrl_cdlast, ctrl_cdvalid,
                      core_coh_req_valid, core_coh_req_addr, core_coh_req_type,
                      i_mon_time, mon_ready,
                      USE_MONITOR, AGENT_ID, SETS, WAYS, LINE_BYTES};
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : l1_chi_plane_stub
