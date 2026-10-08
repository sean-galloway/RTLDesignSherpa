// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_fill_drain_th
// Purpose:
//   Test harness for the amber_fill / amber_drain unit bring-up (Task 6).
//   Closes each engine with its house AXI4 master wrapper -- amber_fill ->
//   axi4_master_rd, amber_drain -> axi4_master_wr -- and exposes the
//   wrappers' m_axi memory sides at the top so the cocotb TB can attach the
//   house AXI4 slave responders (create_axi4_slave_rd/wr) with a shared
//   memory model. Pure wiring; no registers, no logic.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch03_interfaces/02_fabric_axi4.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_fill_drain_th
//==============================================================================
// Description:
//   amber_core (a later task) is the shipping integrator; this harness puts
//   each sequencing engine in front of its real transport wrapper so the
//   unit tests score the fub_axi_* contract the engines actually drive
//   (DECISION D3): the wrapper skids (AR/R on the read side, AW/W/B on the
//   write side) are in the loop, and the AXI-visible protocol is checked at
//   the m_axi pins while the MAS ch03/02 waveform is checked at the
//   wrapper's fub pins (hierarchically tapped by the TB).
//
//   The drain-side victim payload pins model amber_control's staged payload
//   outputs (ctrl_victim_addr_in / ctrl_victim_data_in), which hold stable
//   for the whole drain window by construction; the TB drives them like the
//   control FSM would.
//
//------------------------------------------------------------------------------
// Parameters: same geometry contract as the other amber blocks.
//------------------------------------------------------------------------------
//
// Notes:
//   - No resets or registers here: this is pure wiring.
//   - The wrapper user/lock/cache/prot/qos/region/id fub inputs are tied by
//     the engines themselves (zero); the wrappers pass them through.
//
//==============================================================================

module amber_fill_drain_th
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    localparam int STRB_W           = BUS_WIDTH / 8,
    localparam int FILL_BEATS       = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH = $clog2(FILL_BEATS),
    localparam int LINE_WIDTH       = LINE_BYTES * 8
)(
    input  logic clk,
    input  logic rst_n,

    // amber_control-facing fill handshake (the landed binding port group)
    input  logic                        fill_start,
    input  logic [ADDR_WIDTH-1:0]       fill_addr,
    input  logic [2:0]                  fill_req_class,
    output logic                        fill_done,
    output logic                        fill_beat_valid,
    output logic [BUS_WIDTH-1:0]        fill_beat_data,
    output logic [BEAT_INDEX_WIDTH-1:0] fill_beat_idx,
    output logic                        fill_last,

    // amber_control-facing drain handshake + staged victim payload
    input  logic                    drain_start,
    input  logic [ADDR_WIDTH-1:0]   victim_addr,
    input  logic [LINE_WIDTH-1:0]   victim_data,
    output logic                    drain_done,

    // m_axi memory side (responder BFM attaches here; AR/R are the read
    // wrapper's, AW/W/B the write wrapper's)
    output logic [7:0]                  m_axi_arid,
    output logic [ADDR_WIDTH-1:0]       m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arlock,
    output logic [3:0]                  m_axi_arcache,
    output logic [2:0]                  m_axi_arprot,
    output logic [3:0]                  m_axi_arqos,
    output logic [3:0]                  m_axi_arregion,
    output logic [0:0]                  m_axi_aruser,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,
    input  logic [7:0]                  m_axi_rid,
    input  logic [BUS_WIDTH-1:0]        m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [0:0]                  m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    output logic [7:0]                  m_axi_awid,
    output logic [ADDR_WIDTH-1:0]       m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [0:0]                  m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,
    output logic [BUS_WIDTH-1:0]        m_axi_wdata,
    output logic [STRB_W-1:0]           m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [0:0]                  m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,
    input  logic [7:0]                  m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [0:0]                  m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready
);

    // ------------------------------------------------------------------
    // Geometry contract (same elaboration checks as the other blocks)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_fill_drain_th: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_fill_drain_th: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("amber_fill_drain_th: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if (WAYS < 2)
            $error("amber_fill_drain_th: WAYS must be >= 2");
    end

    // ------------------------------------------------------------------
    // Fill path: amber_fill -> axi4_master_rd
    // ------------------------------------------------------------------
    logic [7:0]          fill_arid;
    logic [ADDR_WIDTH-1:0] fill_araddr;
    logic [7:0]          fill_arlen;
    logic [2:0]          fill_arsize;
    logic [1:0]          fill_arburst;
    logic                fill_arlock;
    logic [3:0]          fill_arcache;
    logic [2:0]          fill_arprot;
    logic [3:0]          fill_arqos;
    logic [3:0]          fill_arregion;
    logic [0:0]          fill_aruser;
    logic                fill_arvalid;
    logic                fill_arready;
    logic [7:0]          fill_rid;
    logic [BUS_WIDTH-1:0] fill_rdata;
    logic [1:0]          fill_rresp;
    logic                fill_rlast;
    logic [0:0]          fill_ruser;
    logic                fill_rvalid;
    logic                fill_rready;

    amber_fill #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_fill (
        .clk               (clk),
        .rst_n             (rst_n),
        .fill_start        (fill_start),
        .fill_addr         (fill_addr),
        .fill_req_class    (fill_req_class),
        .fill_done         (fill_done),
        .fill_beat_valid   (fill_beat_valid),
        .fill_beat_data    (fill_beat_data),
        .fill_beat_idx     (fill_beat_idx),
        .fill_last         (fill_last),
        .fub_axi_arid      (fill_arid),
        .fub_axi_araddr    (fill_araddr),
        .fub_axi_arlen     (fill_arlen),
        .fub_axi_arsize    (fill_arsize),
        .fub_axi_arburst   (fill_arburst),
        .fub_axi_arlock    (fill_arlock),
        .fub_axi_arcache   (fill_arcache),
        .fub_axi_arprot    (fill_arprot),
        .fub_axi_arqos     (fill_arqos),
        .fub_axi_arregion  (fill_arregion),
        .fub_axi_aruser    (fill_aruser),
        .fub_axi_arvalid   (fill_arvalid),
        .fub_axi_arready   (fill_arready),
        .fub_axi_rid       (fill_rid),
        .fub_axi_rdata     (fill_rdata),
        .fub_axi_rresp     (fill_rresp),
        .fub_axi_rlast     (fill_rlast),
        .fub_axi_ruser     (fill_ruser),
        .fub_axi_rvalid    (fill_rvalid),
        .fub_axi_rready    (fill_rready)
    );

    axi4_master_rd #(
        .AXI_ID_WIDTH   (8),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (BUS_WIDTH),
        .AXI_USER_WIDTH (1)
    ) u_axi_rd (
        .aclk              (clk),
        .aresetn           (rst_n),
        .fub_axi_arid      (fill_arid),
        .fub_axi_araddr    (fill_araddr),
        .fub_axi_arlen     (fill_arlen),
        .fub_axi_arsize    (fill_arsize),
        .fub_axi_arburst   (fill_arburst),
        .fub_axi_arlock    (fill_arlock),
        .fub_axi_arcache   (fill_arcache),
        .fub_axi_arprot    (fill_arprot),
        .fub_axi_arqos     (fill_arqos),
        .fub_axi_arregion  (fill_arregion),
        .fub_axi_aruser    (fill_aruser),
        .fub_axi_arvalid   (fill_arvalid),
        .fub_axi_arready   (fill_arready),
        .fub_axi_rid       (fill_rid),
        .fub_axi_rdata     (fill_rdata),
        .fub_axi_rresp     (fill_rresp),
        .fub_axi_rlast     (fill_rlast),
        .fub_axi_ruser     (fill_ruser),
        .fub_axi_rvalid    (fill_rvalid),
        .fub_axi_rready    (fill_rready),
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
        .m_axi_arvalid     (m_axi_arvalid),
        .m_axi_arready     (m_axi_arready),
        .m_axi_rid         (m_axi_rid),
        .m_axi_rdata       (m_axi_rdata),
        .m_axi_rresp       (m_axi_rresp),
        .m_axi_rlast       (m_axi_rlast),
        .m_axi_ruser       (m_axi_ruser),
        .m_axi_rvalid      (m_axi_rvalid),
        .m_axi_rready      (m_axi_rready),
        .busy              ()
    );

    // ------------------------------------------------------------------
    // Drain path: amber_drain -> axi4_master_wr
    // ------------------------------------------------------------------
    logic [7:0]            drain_awid;
    logic [ADDR_WIDTH-1:0] drain_awaddr;
    logic [7:0]            drain_awlen;
    logic [2:0]            drain_awsize;
    logic [1:0]            drain_awburst;
    logic                  drain_awlock;
    logic [3:0]            drain_awcache;
    logic [2:0]            drain_awprot;
    logic [3:0]            drain_awqos;
    logic [3:0]            drain_awregion;
    logic [0:0]            drain_awuser;
    logic                  drain_awvalid;
    logic                  drain_awready;
    logic [BUS_WIDTH-1:0]  drain_wdata;
    logic [STRB_W-1:0]     drain_wstrb;
    logic                  drain_wlast;
    logic [0:0]            drain_wuser;
    logic                  drain_wvalid;
    logic                  drain_wready;
    logic [7:0]            drain_bid;
    logic [1:0]            drain_bresp;
    logic [0:0]            drain_buser;
    logic                  drain_bvalid;
    logic                  drain_bready;

    amber_drain #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_drain (
        .clk              (clk),
        .rst_n            (rst_n),
        .drain_start      (drain_start),
        .victim_addr      (victim_addr),
        .victim_data      (victim_data),
        .drain_done       (drain_done),
        .fub_axi_awid     (drain_awid),
        .fub_axi_awaddr   (drain_awaddr),
        .fub_axi_awlen    (drain_awlen),
        .fub_axi_awsize   (drain_awsize),
        .fub_axi_awburst  (drain_awburst),
        .fub_axi_awlock   (drain_awlock),
        .fub_axi_awcache  (drain_awcache),
        .fub_axi_awprot   (drain_awprot),
        .fub_axi_awqos    (drain_awqos),
        .fub_axi_awregion (drain_awregion),
        .fub_axi_awuser   (drain_awuser),
        .fub_axi_awvalid  (drain_awvalid),
        .fub_axi_awready  (drain_awready),
        .fub_axi_wdata    (drain_wdata),
        .fub_axi_wstrb    (drain_wstrb),
        .fub_axi_wlast    (drain_wlast),
        .fub_axi_wuser    (drain_wuser),
        .fub_axi_wvalid   (drain_wvalid),
        .fub_axi_wready   (drain_wready),
        .fub_axi_bid      (drain_bid),
        .fub_axi_bresp    (drain_bresp),
        .fub_axi_buser    (drain_buser),
        .fub_axi_bvalid   (drain_bvalid),
        .fub_axi_bready   (drain_bready)
    );

    axi4_master_wr #(
        .AXI_ID_WIDTH   (8),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (BUS_WIDTH),
        .AXI_USER_WIDTH (1)
    ) u_axi_wr (
        .aclk              (clk),
        .aresetn           (rst_n),
        .fub_axi_awid      (drain_awid),
        .fub_axi_awaddr    (drain_awaddr),
        .fub_axi_awlen     (drain_awlen),
        .fub_axi_awsize    (drain_awsize),
        .fub_axi_awburst   (drain_awburst),
        .fub_axi_awlock    (drain_awlock),
        .fub_axi_awcache   (drain_awcache),
        .fub_axi_awprot    (drain_awprot),
        .fub_axi_awqos     (drain_awqos),
        .fub_axi_awregion  (drain_awregion),
        .fub_axi_awuser    (drain_awuser),
        .fub_axi_awvalid   (drain_awvalid),
        .fub_axi_awready   (drain_awready),
        .fub_axi_wdata     (drain_wdata),
        .fub_axi_wstrb     (drain_wstrb),
        .fub_axi_wlast     (drain_wlast),
        .fub_axi_wuser     (drain_wuser),
        .fub_axi_wvalid    (drain_wvalid),
        .fub_axi_wready    (drain_wready),
        .fub_axi_bid       (drain_bid),
        .fub_axi_bresp     (drain_bresp),
        .fub_axi_buser     (drain_buser),
        .fub_axi_bvalid    (drain_bvalid),
        .fub_axi_bready    (drain_bready),
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
        .busy              ()
    );

endmodule : amber_fill_drain_th
