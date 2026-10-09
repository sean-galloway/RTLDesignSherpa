// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_pair_rig_tb
// Purpose:
//   The Task 11 pair-rig harness (THE gated deliverable): TWO amber_top
//   caches + the amber_pair_fabric snoopy manager + ONE house
//   sdpram_slave_axi4_axi4 shared memory, wired for coherent end-to-end
//   operation. Pure wiring: the only logic is the rig-level mon_time
//   free-running counter (MAS ch04/05 rig-level sourcing; a free-running
//   counter is the documented choice -- the observer timestamp, not a
//   coherence input). The TB drives both CPU GAXI ports and observes
//   through hierarchical taps (the sanctioned read-only pattern); the
//   fabric's safe-peer wait consumes each cache's ctrl_state status.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/01_architecture.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-09

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_pair_rig_tb
//==============================================================================
// Description:
//
//        cpu0 GAXI        cpu1 GAXI
//           |                 |
//     u_amber0 (amber_top) u_amber1 (amber_top)
//       m_axi_*  \       /  m_axi_*        ACE responder pins
//                 \     /                  (snooped by the fabric)
//            u_fabric (amber_pair_fabric)
//                    |  m_axi_* (single AXI4 master pair)
//               u_mem (sdpram_slave_axi4_axi4) -- the D11 ruling's
//                    genuine sdpram_core consumer
//
//   Each amber_top carries its own D-7 monbus_arbiter; the two merged
//   MonBus output pairs (mon0_*, mon1_*) are observation-only top ports.
//   The D-8 coherence sidebands feed the fabric; the fabric drives the ACE
//   AC channel of the peer. The shared memory's AXIL surfaces are left
//   unconnected (the AXI4 surfaces are the rig's); the config clear port
//   is tied off (the TB backdoor-writes initial content through the
//   sdpram_core r_mem, the same quiescent-phase discipline as the landed
//   suites' hierarchical taps).
//
//------------------------------------------------------------------------------
// Parameters: geometry per amber_pkg (both caches + fabric + memory share
//   it); MEM_DEPTH sizes the sdpram to the TB working set.
//------------------------------------------------------------------------------
//
// Notes:
//   - Clock/reset naming follows the house TH idiom (clk / rst_n); the
//     amber_top aclk/aresetn ports are joined to them here.
//   - Everything here is wiring + the mon_time counter; all other
//     registers belong to the DUTs.
//
//==============================================================================

module amber_pair_rig_tb
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
    parameter int MEM_DEPTH      = 16384,
    localparam int STRB_W       = BUS_WIDTH / 8,
    localparam int IW           = AXI_ID_WIDTH,
    localparam int UW           = AXI_USER_WIDTH,
    localparam int CPU_REQ_W    = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W    = BUS_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // CPU GAXI slave ports, one per cache (TB GAXI BFM pairs attach here)
    // ------------------------------------------------------------------
    input  logic                        cpu0_req_wr_valid,
    output logic                        cpu0_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu0_req_wr_data,
    output logic                        cpu0_rsp_rd_valid,
    input  logic                        cpu0_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu0_rsp_rd_data,

    input  logic                        cpu1_req_wr_valid,
    output logic                        cpu1_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu1_req_wr_data,
    output logic                        cpu1_rsp_rd_valid,
    input  logic                        cpu1_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu1_rsp_rd_data,

    // ------------------------------------------------------------------
    // One MonBus observation output per cache (D-7 merged stream)
    // ------------------------------------------------------------------
    output logic                        mon0_valid,
    input  logic                        mon0_ready,
    output logic [127:0]                mon0_packet,
    output logic [63:0]                 mon0_timestamp,

    output logic                        mon1_valid,
    input  logic                        mon1_ready,
    output logic [127:0]                mon1_packet,
    output logic [63:0]                 mon1_timestamp
);

    // ------------------------------------------------------------------
    // Rig-level mon_time: free-running counter (documented choice). It is
    // an observer timestamp only; coherence never samples it.
    // ------------------------------------------------------------------
    logic [63:0] mon_time_q;

    always_ff @(posedge clk) begin
        mon_time_q <= mon_time_q + 1'b1;
    end

    // ------------------------------------------------------------------
    // amber_top 0 / 1 <-> fabric interconnections
    // ------------------------------------------------------------------
    logic [IW-1:0]        m0_arid, m1_arid;
    logic [ADDR_WIDTH-1:0] m0_araddr, m1_araddr;
    logic [7:0]           m0_arlen, m1_arlen;
    logic [2:0]           m0_arsize, m1_arsize;
    logic [1:0]           m0_arburst, m1_arburst;
    logic                     m0_arlock, m1_arlock;
    logic [3:0]               m0_arcache, m1_arcache;
    logic [2:0]               m0_arprot, m1_arprot;
    logic [3:0]               m0_arqos, m1_arqos;
    logic [3:0]               m0_arregion, m1_arregion;
    logic [UW-1:0]            m0_aruser, m1_aruser;
    logic                     m0_arvalid, m1_arvalid;
    logic                     m0_arready, m1_arready;
    logic [IW-1:0]            m0_rid, m1_rid;
    logic [BUS_WIDTH-1:0]     m0_rdata, m1_rdata;
    logic [1:0]               m0_rresp, m1_rresp;
    logic                     m0_rlast, m1_rlast;
    logic [UW-1:0]            m0_ruser, m1_ruser;
    logic                     m0_rvalid, m1_rvalid;
    logic                     m0_rready, m1_rready;

    logic [IW-1:0]        m0_awid, m1_awid;
    logic [ADDR_WIDTH-1:0] m0_awaddr, m1_awaddr;
    logic [7:0]           m0_awlen, m1_awlen;
    logic [2:0]           m0_awsize, m1_awsize;
    logic [1:0]           m0_awburst, m1_awburst;
    logic                     m0_awlock, m1_awlock;
    logic [3:0]               m0_awcache, m1_awcache;
    logic [2:0]               m0_awprot, m1_awprot;
    logic [3:0]               m0_awqos, m1_awqos;
    logic [3:0]               m0_awregion, m1_awregion;
    logic [UW-1:0]            m0_awuser, m1_awuser;
    logic                     m0_awvalid, m1_awvalid;
    logic                     m0_awready, m1_awready;
    logic [BUS_WIDTH-1:0]     m0_wdata, m1_wdata;
    logic [STRB_W-1:0]        m0_wstrb, m1_wstrb;
    logic                     m0_wlast, m1_wlast;
    logic [UW-1:0]            m0_wuser, m1_wuser;
    logic                     m0_wvalid, m1_wvalid;
    logic                     m0_wready, m1_wready;
    logic [IW-1:0]            m0_bid, m1_bid;
    logic [1:0]               m0_bresp, m1_bresp;
    logic [UW-1:0]            m0_buser, m1_buser;
    logic                     m0_bvalid, m1_bvalid;
    logic                     m0_bready, m1_bready;

    // ACE snoop responder pins (fabric drives AC; the caches respond)
    logic [ADDR_WIDTH-1:0]    s0_acaddr, s1_acaddr;
    logic [3:0]               s0_acsnoop, s1_acsnoop;
    logic [2:0]               s0_acprot, s1_acprot;
    logic                     s0_acvalid, s1_acvalid;
    logic                     s0_acready, s1_acready;
    logic [AMBER_CRRESP_WIDTH-1:0] s0_crresp, s1_crresp;
    logic                     s0_crvalid, s1_crvalid;
    logic                     s0_crready, s1_crready;
    logic [BUS_WIDTH-1:0]     s0_cddata, s1_cddata;
    logic                     s0_cdlast, s1_cdlast;
    logic                     s0_cdvalid, s1_cdvalid;
    logic                     s0_cdready, s1_cdready;

    // D-8 coherence sidebands
    logic                     coh0_valid, coh1_valid;
    logic [ADDR_WIDTH-1:0]    coh0_addr, coh1_addr;
    logic [2:0]               coh0_type, coh1_type;

    // status
    logic                     init_busy0, init_busy1;
    logic [3:0]               ctrl_state0, ctrl_state1;

    // ------------------------------------------------------------------
    // The two caches
    // ------------------------------------------------------------------
    amber_top #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR)
    ) u_amber0 (
        .aclk            (clk),
        .aresetn         (rst_n),
        .cpu_req_wr_valid(cpu0_req_wr_valid),
        .cpu_req_wr_ready(cpu0_req_wr_ready),
        .cpu_req_wr_data (cpu0_req_wr_data),
        .cpu_rsp_rd_valid(cpu0_rsp_rd_valid),
        .cpu_rsp_rd_ready(cpu0_rsp_rd_ready),
        .cpu_rsp_rd_data (cpu0_rsp_rd_data),
        .m_axi_arid      (m0_arid),
        .m_axi_araddr    (m0_araddr),
        .m_axi_arlen     (m0_arlen),
        .m_axi_arsize    (m0_arsize),
        .m_axi_arburst   (m0_arburst),
        .m_axi_arlock    (m0_arlock),
        .m_axi_arcache   (m0_arcache),
        .m_axi_arprot    (m0_arprot),
        .m_axi_arqos     (m0_arqos),
        .m_axi_arregion  (m0_arregion),
        .m_axi_aruser    (m0_aruser),
        .m_axi_arvalid   (m0_arvalid),
        .m_axi_arready   (m0_arready),
        .m_axi_rid       (m0_rid),
        .m_axi_rdata     (m0_rdata),
        .m_axi_rresp     (m0_rresp),
        .m_axi_rlast     (m0_rlast),
        .m_axi_ruser     (m0_ruser),
        .m_axi_rvalid    (m0_rvalid),
        .m_axi_rready    (m0_rready),
        .m_axi_awid      (m0_awid),
        .m_axi_awaddr    (m0_awaddr),
        .m_axi_awlen     (m0_awlen),
        .m_axi_awsize    (m0_awsize),
        .m_axi_awburst   (m0_awburst),
        .m_axi_awlock    (m0_awlock),
        .m_axi_awcache   (m0_awcache),
        .m_axi_awprot    (m0_awprot),
        .m_axi_awqos     (m0_awqos),
        .m_axi_awregion  (m0_awregion),
        .m_axi_awuser    (m0_awuser),
        .m_axi_awvalid   (m0_awvalid),
        .m_axi_awready   (m0_awready),
        .m_axi_wdata     (m0_wdata),
        .m_axi_wstrb     (m0_wstrb),
        .m_axi_wlast     (m0_wlast),
        .m_axi_wuser     (m0_wuser),
        .m_axi_wvalid    (m0_wvalid),
        .m_axi_wready    (m0_wready),
        .m_axi_bid       (m0_bid),
        .m_axi_bresp     (m0_bresp),
        .m_axi_buser     (m0_buser),
        .m_axi_bvalid    (m0_bvalid),
        .m_axi_bready    (m0_bready),
        .m_axi_acaddr    (s0_acaddr),
        .m_axi_acsnoop   (s0_acsnoop),
        .m_axi_acprot    (s0_acprot),
        .m_axi_acvalid   (s0_acvalid),
        .m_axi_acready   (s0_acready),
        .m_axi_crresp    (s0_crresp),
        .m_axi_crvalid   (s0_crvalid),
        .m_axi_crready   (s0_crready),
        .m_axi_cddata    (s0_cddata),
        .m_axi_cdlast    (s0_cdlast),
        .m_axi_cdvalid   (s0_cdvalid),
        .m_axi_cdready   (s0_cdready),
        .coh_req_valid   (coh0_valid),
        .coh_req_addr    (coh0_addr),
        .coh_req_type    (coh0_type),
        .i_mon_time      (mon_time_q),
        .mon_valid       (mon0_valid),
        .mon_ready       (mon0_ready),
        .mon_packet      (mon0_packet),
        .mon_timestamp   (mon0_timestamp),
        .init_busy       (init_busy0),
        .ctrl_state      (ctrl_state0)
    );

    amber_top #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .REPL_POLICY    (REPL_POLICY),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .USE_MONITOR    (USE_MONITOR)
    ) u_amber1 (
        .aclk            (clk),
        .aresetn         (rst_n),
        .cpu_req_wr_valid(cpu1_req_wr_valid),
        .cpu_req_wr_ready(cpu1_req_wr_ready),
        .cpu_req_wr_data (cpu1_req_wr_data),
        .cpu_rsp_rd_valid(cpu1_rsp_rd_valid),
        .cpu_rsp_rd_ready(cpu1_rsp_rd_ready),
        .cpu_rsp_rd_data (cpu1_rsp_rd_data),
        .m_axi_arid      (m1_arid),
        .m_axi_araddr    (m1_araddr),
        .m_axi_arlen     (m1_arlen),
        .m_axi_arsize    (m1_arsize),
        .m_axi_arburst   (m1_arburst),
        .m_axi_arlock    (m1_arlock),
        .m_axi_arcache   (m1_arcache),
        .m_axi_arprot    (m1_arprot),
        .m_axi_arqos     (m1_arqos),
        .m_axi_arregion  (m1_arregion),
        .m_axi_aruser    (m1_aruser),
        .m_axi_arvalid   (m1_arvalid),
        .m_axi_arready   (m1_arready),
        .m_axi_rid       (m1_rid),
        .m_axi_rdata     (m1_rdata),
        .m_axi_rresp     (m1_rresp),
        .m_axi_rlast     (m1_rlast),
        .m_axi_ruser     (m1_ruser),
        .m_axi_rvalid    (m1_rvalid),
        .m_axi_rready    (m1_rready),
        .m_axi_awid      (m1_awid),
        .m_axi_awaddr    (m1_awaddr),
        .m_axi_awlen     (m1_awlen),
        .m_axi_awsize    (m1_awsize),
        .m_axi_awburst   (m1_awburst),
        .m_axi_awlock    (m1_awlock),
        .m_axi_awcache   (m1_awcache),
        .m_axi_awprot    (m1_awprot),
        .m_axi_awqos     (m1_awqos),
        .m_axi_awregion  (m1_awregion),
        .m_axi_awuser    (m1_awuser),
        .m_axi_awvalid   (m1_awvalid),
        .m_axi_awready   (m1_awready),
        .m_axi_wdata     (m1_wdata),
        .m_axi_wstrb     (m1_wstrb),
        .m_axi_wlast     (m1_wlast),
        .m_axi_wuser     (m1_wuser),
        .m_axi_wvalid    (m1_wvalid),
        .m_axi_wready    (m1_wready),
        .m_axi_bid       (m1_bid),
        .m_axi_bresp     (m1_bresp),
        .m_axi_buser     (m1_buser),
        .m_axi_bvalid    (m1_bvalid),
        .m_axi_bready    (m1_bready),
        .m_axi_acaddr    (s1_acaddr),
        .m_axi_acsnoop   (s1_acsnoop),
        .m_axi_acprot    (s1_acprot),
        .m_axi_acvalid   (s1_acvalid),
        .m_axi_acready   (s1_acready),
        .m_axi_crresp    (s1_crresp),
        .m_axi_crvalid   (s1_crvalid),
        .m_axi_crready   (s1_crready),
        .m_axi_cddata    (s1_cddata),
        .m_axi_cdlast    (s1_cdlast),
        .m_axi_cdvalid   (s1_cdvalid),
        .m_axi_cdready   (s1_cdready),
        .coh_req_valid   (coh1_valid),
        .coh_req_addr    (coh1_addr),
        .coh_req_type    (coh1_type),
        .i_mon_time      (mon_time_q),
        .mon_valid       (mon1_valid),
        .mon_ready       (mon1_ready),
        .mon_packet      (mon1_packet),
        .mon_timestamp   (mon1_timestamp),
        .init_busy       (init_busy1),
        .ctrl_state      (ctrl_state1)
    );

    // ------------------------------------------------------------------
    // The pair fabric
    // ------------------------------------------------------------------
    logic [IW-1:0]        mem_arid;
    logic [ADDR_WIDTH-1:0] mem_araddr;
    logic [7:0]           mem_arlen;
    logic [2:0]           mem_arsize;
    logic [1:0]           mem_arburst;
    logic                     mem_arlock;
    logic [3:0]               mem_arcache;
    logic [2:0]               mem_arprot;
    logic [3:0]               mem_arqos;
    logic [3:0]               mem_arregion;
    logic [UW-1:0]            mem_aruser;
    logic                     mem_arvalid, mem_arready;
    logic [IW-1:0]            mem_rid;
    logic [BUS_WIDTH-1:0]     mem_rdata;
    logic [1:0]               mem_rresp;
    logic                     mem_rlast;
    logic [UW-1:0]            mem_ruser;
    logic                     mem_rvalid, mem_rready;
    logic [IW-1:0]        mem_awid;
    logic [ADDR_WIDTH-1:0] mem_awaddr;
    logic [7:0]           mem_awlen;
    logic [2:0]           mem_awsize;
    logic [1:0]           mem_awburst;
    logic                     mem_awlock;
    logic [3:0]               mem_awcache;
    logic [2:0]               mem_awprot;
    logic [3:0]               mem_awqos;
    logic [3:0]               mem_awregion;
    logic [UW-1:0]            mem_awuser;
    logic                     mem_awvalid, mem_awready;
    logic [BUS_WIDTH-1:0]     mem_wdata;
    logic [STRB_W-1:0]        mem_wstrb;
    logic                     mem_wlast;
    logic [UW-1:0]            mem_wuser;
    logic                     mem_wvalid, mem_wready;
    logic [IW-1:0]            mem_bid;
    logic [1:0]               mem_bresp;
    logic [UW-1:0]            mem_buser;
    logic                     mem_bvalid, mem_bready;

    amber_pair_fabric #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .WAYS           (WAYS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_fabric (
        .clk               (clk),
        .rst_n             (rst_n),
        .c0_arid           (m0_arid),
        .c0_araddr         (m0_araddr),
        .c0_arlen          (m0_arlen),
        .c0_arsize         (m0_arsize),
        .c0_arburst        (m0_arburst),
        .c0_arlock         (m0_arlock),
        .c0_arcache        (m0_arcache),
        .c0_arprot         (m0_arprot),
        .c0_arqos          (m0_arqos),
        .c0_arregion       (m0_arregion),
        .c0_aruser         (m0_aruser),
        .c0_arvalid        (m0_arvalid),
        .c0_arready        (m0_arready),
        .c0_rid            (m0_rid),
        .c0_rdata          (m0_rdata),
        .c0_rresp          (m0_rresp),
        .c0_rlast          (m0_rlast),
        .c0_ruser          (m0_ruser),
        .c0_rvalid         (m0_rvalid),
        .c0_rready         (m0_rready),
        .c0_awid           (m0_awid),
        .c0_awaddr         (m0_awaddr),
        .c0_awlen          (m0_awlen),
        .c0_awsize         (m0_awsize),
        .c0_awburst        (m0_awburst),
        .c0_awlock         (m0_awlock),
        .c0_awcache        (m0_awcache),
        .c0_awprot         (m0_awprot),
        .c0_awqos          (m0_awqos),
        .c0_awregion       (m0_awregion),
        .c0_awuser         (m0_awuser),
        .c0_awvalid        (m0_awvalid),
        .c0_awready        (m0_awready),
        .c0_wdata          (m0_wdata),
        .c0_wstrb          (m0_wstrb),
        .c0_wlast          (m0_wlast),
        .c0_wuser          (m0_wuser),
        .c0_wvalid         (m0_wvalid),
        .c0_wready         (m0_wready),
        .c0_bid            (m0_bid),
        .c0_bresp          (m0_bresp),
        .c0_buser          (m0_buser),
        .c0_bvalid         (m0_bvalid),
        .c0_bready         (m0_bready),
        .c1_arid           (m1_arid),
        .c1_araddr         (m1_araddr),
        .c1_arlen          (m1_arlen),
        .c1_arsize         (m1_arsize),
        .c1_arburst        (m1_arburst),
        .c1_arlock         (m1_arlock),
        .c1_arcache        (m1_arcache),
        .c1_arprot         (m1_arprot),
        .c1_arqos          (m1_arqos),
        .c1_arregion       (m1_arregion),
        .c1_aruser         (m1_aruser),
        .c1_arvalid        (m1_arvalid),
        .c1_arready        (m1_arready),
        .c1_rid            (m1_rid),
        .c1_rdata          (m1_rdata),
        .c1_rresp          (m1_rresp),
        .c1_rlast          (m1_rlast),
        .c1_ruser          (m1_ruser),
        .c1_rvalid         (m1_rvalid),
        .c1_rready         (m1_rready),
        .c1_awid           (m1_awid),
        .c1_awaddr         (m1_awaddr),
        .c1_awlen          (m1_awlen),
        .c1_awsize         (m1_awsize),
        .c1_awburst        (m1_awburst),
        .c1_awlock         (m1_awlock),
        .c1_awcache        (m1_awcache),
        .c1_awprot         (m1_awprot),
        .c1_awqos          (m1_awqos),
        .c1_awregion       (m1_awregion),
        .c1_awuser         (m1_awuser),
        .c1_awvalid        (m1_awvalid),
        .c1_awready        (m1_awready),
        .c1_wdata          (m1_wdata),
        .c1_wstrb          (m1_wstrb),
        .c1_wlast          (m1_wlast),
        .c1_wuser          (m1_wuser),
        .c1_wvalid         (m1_wvalid),
        .c1_wready         (m1_wready),
        .c1_bid            (m1_bid),
        .c1_bresp          (m1_bresp),
        .c1_buser          (m1_buser),
        .c1_bvalid         (m1_bvalid),
        .c1_bready         (m1_bready),
        .s0_acaddr         (s0_acaddr),
        .s0_acsnoop        (s0_acsnoop),
        .s0_acprot         (s0_acprot),
        .s0_acvalid        (s0_acvalid),
        .s0_acready        (s0_acready),
        .s0_crresp         (s0_crresp),
        .s0_crvalid        (s0_crvalid),
        .s0_crready        (s0_crready),
        .s0_cddata         (s0_cddata),
        .s0_cdlast         (s0_cdlast),
        .s0_cdvalid        (s0_cdvalid),
        .s0_cdready        (s0_cdready),
        .s1_acaddr         (s1_acaddr),
        .s1_acsnoop        (s1_acsnoop),
        .s1_acprot         (s1_acprot),
        .s1_acvalid        (s1_acvalid),
        .s1_acready        (s1_acready),
        .s1_crresp         (s1_crresp),
        .s1_crvalid        (s1_crvalid),
        .s1_crready        (s1_crready),
        .s1_cddata         (s1_cddata),
        .s1_cdlast         (s1_cdlast),
        .s1_cdvalid        (s1_cdvalid),
        .s1_cdready        (s1_cdready),
        .c0_coh_req_valid  (coh0_valid),
        .c0_coh_req_addr   (coh0_addr),
        .c0_coh_req_type   (coh0_type),
        .c1_coh_req_valid  (coh1_valid),
        .c1_coh_req_addr   (coh1_addr),
        .c1_coh_req_type   (coh1_type),
        .peer0_state       (ctrl_state0),
        .peer1_state       (ctrl_state1),
        .mem_arid          (mem_arid),
        .mem_araddr        (mem_araddr),
        .mem_arlen         (mem_arlen),
        .mem_arsize        (mem_arsize),
        .mem_arburst       (mem_arburst),
        .mem_arlock        (mem_arlock),
        .mem_arcache       (mem_arcache),
        .mem_arprot        (mem_arprot),
        .mem_arqos         (mem_arqos),
        .mem_arregion      (mem_arregion),
        .mem_aruser        (mem_aruser),
        .mem_arvalid       (mem_arvalid),
        .mem_arready       (mem_arready),
        .mem_rid           (mem_rid),
        .mem_rdata         (mem_rdata),
        .mem_rresp         (mem_rresp),
        .mem_rlast         (mem_rlast),
        .mem_ruser         (mem_ruser),
        .mem_rvalid        (mem_rvalid),
        .mem_rready        (mem_rready),
        .mem_awid          (mem_awid),
        .mem_awaddr        (mem_awaddr),
        .mem_awlen         (mem_awlen),
        .mem_awsize        (mem_awsize),
        .mem_awburst       (mem_awburst),
        .mem_awlock        (mem_awlock),
        .mem_awcache       (mem_awcache),
        .mem_awprot        (mem_awprot),
        .mem_awqos         (mem_awqos),
        .mem_awregion      (mem_awregion),
        .mem_awuser        (mem_awuser),
        .mem_awvalid       (mem_awvalid),
        .mem_awready       (mem_awready),
        .mem_wdata         (mem_wdata),
        .mem_wstrb         (mem_wstrb),
        .mem_wlast         (mem_wlast),
        .mem_wuser         (mem_wuser),
        .mem_wvalid        (mem_wvalid),
        .mem_wready        (mem_wready),
        .mem_bid           (mem_bid),
        .mem_bresp         (mem_bresp),
        .mem_buser         (mem_buser),
        .mem_bvalid        (mem_bvalid),
        .mem_bready        (mem_bready),
        .dbg_state         (),
        .dbg_grant_dir     (),
        .dbg_pend_vld      (),
        .dbg_buf_vld       (),
        .dbg_abs_pend      (),
        .dbg_kill          (),
        .dbg_acsnoop       (),
        .dbg_grant_addr    ()
    );

    // ------------------------------------------------------------------
    // The shared memory (D11 ruling's genuine sdpram_core consumer)
    // ------------------------------------------------------------------
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH  (AXI_ID_WIDTH),
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (BUS_WIDTH),
        .USER_WIDTH    (AXI_USER_WIDTH),
        .MEM_DEPTH     (MEM_DEPTH)
    ) u_mem (
        .aclk             (clk),
        .aresetn          (rst_n),
        .s_axi_awid       (mem_awid),
        .s_axi_awaddr     (mem_awaddr),
        .s_axi_awlen      (mem_awlen),
        .s_axi_awsize     (mem_awsize),
        .s_axi_awburst    (mem_awburst),
        .s_axi_awlock     (mem_awlock),
        .s_axi_awcache    (mem_awcache),
        .s_axi_awprot     (mem_awprot),
        .s_axi_awqos      (mem_awqos),
        .s_axi_awregion   (mem_awregion),
        .s_axi_awuser     (mem_awuser),
        .s_axi_awvalid    (mem_awvalid),
        .s_axi_awready    (mem_awready),
        .s_axi_wdata      (mem_wdata),
        .s_axi_wstrb      (mem_wstrb),
        .s_axi_wlast      (mem_wlast),
        .s_axi_wuser      (mem_wuser),
        .s_axi_wvalid     (mem_wvalid),
        .s_axi_wready     (mem_wready),
        .s_axi_bid        (mem_bid),
        .s_axi_bresp      (mem_bresp),
        .s_axi_buser      (mem_buser),
        .s_axi_bvalid     (mem_bvalid),
        .s_axi_bready     (mem_bready),
        .s_axi_arid       (mem_arid),
        .s_axi_araddr     (mem_araddr),
        .s_axi_arlen      (mem_arlen),
        .s_axi_arsize     (mem_arsize),
        .s_axi_arburst    (mem_arburst),
        .s_axi_arlock     (mem_arlock),
        .s_axi_arcache    (mem_arcache),
        .s_axi_arprot     (mem_arprot),
        .s_axi_arqos      (mem_arqos),
        .s_axi_arregion   (mem_arregion),
        .s_axi_aruser     (mem_aruser),
        .s_axi_arvalid    (mem_arvalid),
        .s_axi_arready    (mem_arready),
        .s_axi_rid        (mem_rid),
        .s_axi_rdata      (mem_rdata),
        .s_axi_rresp      (mem_rresp),
        .s_axi_rlast      (mem_rlast),
        .s_axi_ruser      (mem_ruser),
        .s_axi_rvalid     (mem_rvalid),
        .s_axi_rready     (mem_rready),
        .i_cfg_start_clear(1'b0),
        .o_cfg_done_clear (),
        .o_dbg_vr         (),
        .o_dbg_fub_vr     (),
        .o_dbg_bram_wr    (),
        .o_dbg_bram_rd    (),
        .o_dbg_busy_wr    (),
        .o_dbg_busy_rd    ()
    );

endmodule : amber_pair_rig_tb
