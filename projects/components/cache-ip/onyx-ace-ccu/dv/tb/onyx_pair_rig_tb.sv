// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_pair_rig_tb
// Purpose:
//   onyx TASK-001 step 2: the jet-prime pair rig with onyx_ccu (N_PORTS=2)
//   in jet_prime_pair_fabric's place -- the same two caches, memory and
//   TB (JetPairRigTB reads u_fabric's taps unchanged), so every pair-rig
//   cell is the proof that onyx replaces the fabric.  Derived from
//   jet_prime_pair_rig_tb (whose own notes follow).
//
// Original purpose (jet_prime_pair_rig_tb):
//   The jet pair-rig harness (Task 9): TWO jet_prime_top caches + the
//   jet_prime_pair_fabric snoopy manager + ONE house sdpram_slave_axi4_axi4
//   shared memory, wired for coherent end-to-end operation -- the
//   amber_pair_rig_tb structure with two jets (the spec's
//   "amber_pair_fabric hosts two jets" deliverable, jet-named).  Pure
//   wiring plus the rig-level mon_time free-running counter (observer
//   timestamp only; coherence never samples it).  The TB drives both CPU
//   GAXI ports and observes through hierarchical taps (the sanctioned
//   read-only pattern).  Step 3 (2026-11-16): the fabric is the pipelined
//   jet_prime_pair_fabric -- it consumes each cache's retire sideband
//   (coh_done_*) instead of the ctrl_state / lkup_live observability
//   outputs, and both caches run the fill engine at full depth.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch01_overview/01_architecture.md
// Subsystem: jet-prime (forked from jet at 2be919254, 2026-11-12 -- jet-prime TASK-001)
//
// Author: sean galloway
// Created: 2026-11-21 (from jet_prime_pair_rig_tb)

`timescale 1ns / 1ps

//==============================================================================
// Module: onyx_pair_rig_tb
//==============================================================================
// Description:
//
//        cpu0 GAXI        cpu1 GAXI
//           |                 |
//      u_jet0 (jet_prime_top)  u_jet1 (jet_prime_top)
//       m_axi_*  \       /  m_axi_*        ACE responder pins
//                 \     /                  (snooped by the fabric)
//             u_fabric (jet_prime_pair_fabric)
//                    |  m_axi_* (single AXI4 master pair)
//               u_mem (sdpram_slave_axi4_axi4)
//
//   Each jet_prime_top carries its own D-7 monbus_arbiter; the two merged
//   MonBus output pairs (mon0_*, mon1_*) are observation-only top ports.
//   The D-8 coherence and retire sidebands feed the fabric; the fabric
//   drives the ACE AC channel of the peer.  The shared memory's AXIL surfaces are left
//   unconnected; the config clear port is tied off (the TB backdoor-writes
//   initial content through the sdpram_core r_mem, the same
//   quiescent-phase discipline as the landed suites).
//
//------------------------------------------------------------------------------
// Parameters: geometry per l1_pkg (both caches + fabric + memory share
//   it); MSHR_COUNT / VICTIM_DEPTH per jet_prime_pkg (J1/J5); MEM_DEPTH sizes
//   the sdpram to the TB working set.
//------------------------------------------------------------------------------
//
// Notes:
//   - Clock/reset naming follows the house TH idiom (clk / rst_n); the
//     jet_prime_top aclk/aresetn ports are joined to them here (jet_prime_top
//     synchronizes the boundary internally; both caches share it).
//   - Everything here is wiring + the mon_time counter; all other
//     registers belong to the DUTs.
//
//==============================================================================

module onyx_pair_rig_tb
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
    parameter int MSHR_COUNT     = jet_prime_pkg::MSHR_COUNT,
    parameter int VICTIM_DEPTH   = jet_prime_pkg::VICTIM_DEPTH,
    // every entry and the upgrade in flight (step 2's engine depth; the
    // pipelined fabric of step 3 carries it)
    parameter int FILL_INFLIGHT  = MSHR_COUNT + 1,
    // the fabric's transaction table: both caches' entries and upgrades
    parameter int FAB_SLOTS      = 2 * (MSHR_COUNT + 1),
    parameter int SNOOP_INFLIGHT = 2,
    // onyx D6 / D5 modes (see onyx_ccu)
    parameter bit DEFER_AR       = 1'b0,
    parameter bit SERIAL_MODE    = 1'b0,
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
    output logic [63:0]                 mon1_timestamp,
    // onyx's observer (D9): the TB counts its packets per event code
    // against its own fabric model (grants, memory reads, absorptions)
    output logic                        mon2_valid,
    input  logic                        mon2_ready,
    output logic [127:0]                mon2_packet,
    output logic [63:0]                 mon2_timestamp,
    output logic [7:0]                  mon2_dropped,
    // onyx's exact event counters (never cleared or frozen here)
    output logic [31:0]                 cnt_txn,
    output logic [31:0]                 cnt_supplied,
    output logic [31:0]                 cnt_mem_read,
    output logic [31:0]                 cnt_read_wasted,
    output logic [31:0]                 cnt_absorb,
    output logic [31:0]                 cnt_wb
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
    // jet_prime_top 0 / 1 <-> fabric interconnections
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

    // D-8 coherence sidebands + the retire sidebands (step 3)
    logic                     coh0_valid, coh1_valid;
    logic [ADDR_WIDTH-1:0]    coh0_addr, coh1_addr;
    logic [2:0]               coh0_type, coh1_type;
    logic                     done0_valid, done1_valid;
    logic [IW-1:0]            done0_id, done1_id;

    // status (observability nets the TB taps through the cache instances)
    /* verilator lint_off UNUSEDSIGNAL */
    logic                     init_busy0, init_busy1;
    logic [3:0]               ctrl_state0, ctrl_state1;
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // The two caches
    // ------------------------------------------------------------------
    jet_prime_top #(
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
        .VICTIM_DEPTH   (VICTIM_DEPTH),
        .FILL_INFLIGHT  (FILL_INFLIGHT)
    ) u_jet0 (
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
        .coh_done_valid  (done0_valid),
        .coh_done_id     (done0_id),
        .i_mon_time      (mon_time_q),
        .mon_valid       (mon0_valid),
        .mon_ready       (mon0_ready),
        .mon_packet      (mon0_packet),
        .mon_timestamp   (mon0_timestamp),
        .init_busy       (init_busy0),
        .ctrl_state      (ctrl_state0),
        .busy            ()
    );

    jet_prime_top #(
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
        .VICTIM_DEPTH   (VICTIM_DEPTH),
        .FILL_INFLIGHT  (FILL_INFLIGHT)
    ) u_jet1 (
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
        .coh_done_valid  (done1_valid),
        .coh_done_id     (done1_id),
        .i_mon_time      (mon_time_q),
        .mon_valid       (mon1_valid),
        .mon_ready       (mon1_ready),
        .mon_packet      (mon1_packet),
        .mon_timestamp   (mon1_timestamp),
        .init_busy       (init_busy1),
        .ctrl_state      (ctrl_state1),
        .busy            ()
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

    // ------------------------------------------------------------------
    // onyx in the pair fabric's place (onyx TASK-001 step 2): the two
    // caches' flat memory sides, sidebands and snoop ports packed into
    // onyx_ccu's per-port arrays; instance name and debug taps kept so
    // the jet-prime pair-rig TB reads onyx unchanged
    // ------------------------------------------------------------------
    logic [IW-1:0]            c_arid    [2];
    logic [ADDR_WIDTH-1:0]    c_araddr  [2];
    logic [7:0]               c_arlen   [2];
    logic [2:0]               c_arsize  [2];
    logic [1:0]               c_arburst [2];
    logic [3:0]               c_arcache [2];
    logic [2:0]               c_arprot  [2];
    logic [3:0]               c_arqos   [2];
    logic [3:0]               c_arregion[2];
    logic [UW-1:0]            c_aruser  [2];
    logic [IW-1:0]            c_rid     [2];
    logic [BUS_WIDTH-1:0]     c_rdata   [2];
    logic [1:0]               c_rresp   [2];
    logic [UW-1:0]            c_ruser   [2];
    logic [IW-1:0]            c_awid    [2];
    logic [ADDR_WIDTH-1:0]    c_awaddr  [2];
    logic [7:0]               c_awlen   [2];
    logic [2:0]               c_awsize  [2];
    logic [1:0]               c_awburst [2];
    logic [3:0]               c_awcache [2];
    logic [2:0]               c_awprot  [2];
    logic [3:0]               c_awqos   [2];
    logic [3:0]               c_awregion[2];
    logic [UW-1:0]            c_awuser  [2];
    logic [BUS_WIDTH-1:0]     c_wdata   [2];
    logic [STRB_W-1:0]        c_wstrb   [2];
    logic [UW-1:0]            c_wuser   [2];
    logic [IW-1:0]            c_bid     [2];
    logic [1:0]               c_bresp   [2];
    logic [UW-1:0]            c_buser   [2];
    logic [ADDR_WIDTH-1:0]    s_acaddr  [2];
    logic [3:0]               s_acsnoop [2];
    logic [2:0]               s_acprot  [2];
    logic [AMBER_CRRESP_WIDTH-1:0] s_crresp [2];
    logic [BUS_WIDTH-1:0]     s_cddata  [2];
    logic [ADDR_WIDTH-1:0]    c_coh_addr[2];
    logic [2:0]               c_coh_type[2];
    logic [IW-1:0]            c_done_id [2];
    logic [1:0]               c_arready_v, c_rlast_v, c_rvalid_v, c_awready_v, c_wready_v, c_bvalid_v;
    logic [1:0]               s_acvalid_v, s_crready_v, s_cdready_v;
    logic                     oc_grant_dir;
    logic [$clog2(FAB_SLOTS)-1:0] oc_grant_slot;
    logic [$clog2(FAB_SLOTS)-1:0] oc_evt_gather_slot [2];
    logic                     oc_evt_grant, oc_evt_mem_ar, oc_evt_absorb, oc_evt_wb;
    logic [1:0]               oc_evt_gather, oc_evt_gather_dt, oc_evt_gather_pd, oc_evt_read_wasted;
    logic [2:0]               oc_evt_grant_cls;
    logic [1:0]               oc_evt_ac, oc_evt_lock_wait;

    assign c_arid[0] = m0_arid;         assign c_arid[1] = m1_arid;
    assign c_araddr[0] = m0_araddr;     assign c_araddr[1] = m1_araddr;
    assign c_arlen[0] = m0_arlen;       assign c_arlen[1] = m1_arlen;
    assign c_arsize[0] = m0_arsize;     assign c_arsize[1] = m1_arsize;
    assign c_arburst[0] = m0_arburst;   assign c_arburst[1] = m1_arburst;
    assign c_arcache[0] = m0_arcache;   assign c_arcache[1] = m1_arcache;
    assign c_arprot[0] = m0_arprot;     assign c_arprot[1] = m1_arprot;
    assign c_arqos[0] = m0_arqos;       assign c_arqos[1] = m1_arqos;
    assign c_arregion[0] = m0_arregion; assign c_arregion[1] = m1_arregion;
    assign c_aruser[0] = m0_aruser;     assign c_aruser[1] = m1_aruser;
    assign {m1_arready, m0_arready} = c_arready_v;
    assign m0_rid = c_rid[0];           assign m1_rid = c_rid[1];
    assign m0_rdata = c_rdata[0];       assign m1_rdata = c_rdata[1];
    assign m0_rresp = c_rresp[0];       assign m1_rresp = c_rresp[1];
    assign m0_ruser = c_ruser[0];       assign m1_ruser = c_ruser[1];
    assign {m1_rlast, m0_rlast} = c_rlast_v;
    assign {m1_rvalid, m0_rvalid} = c_rvalid_v;
    assign c_awid[0] = m0_awid;         assign c_awid[1] = m1_awid;
    assign c_awaddr[0] = m0_awaddr;     assign c_awaddr[1] = m1_awaddr;
    assign c_awlen[0] = m0_awlen;       assign c_awlen[1] = m1_awlen;
    assign c_awsize[0] = m0_awsize;     assign c_awsize[1] = m1_awsize;
    assign c_awburst[0] = m0_awburst;   assign c_awburst[1] = m1_awburst;
    assign c_awcache[0] = m0_awcache;   assign c_awcache[1] = m1_awcache;
    assign c_awprot[0] = m0_awprot;     assign c_awprot[1] = m1_awprot;
    assign c_awqos[0] = m0_awqos;       assign c_awqos[1] = m1_awqos;
    assign c_awregion[0] = m0_awregion; assign c_awregion[1] = m1_awregion;
    assign c_awuser[0] = m0_awuser;     assign c_awuser[1] = m1_awuser;
    assign {m1_awready, m0_awready} = c_awready_v;
    assign c_wdata[0] = m0_wdata;       assign c_wdata[1] = m1_wdata;
    assign c_wstrb[0] = m0_wstrb;       assign c_wstrb[1] = m1_wstrb;
    assign c_wuser[0] = m0_wuser;       assign c_wuser[1] = m1_wuser;
    assign {m1_wready, m0_wready} = c_wready_v;
    assign m0_bid = c_bid[0];           assign m1_bid = c_bid[1];
    assign m0_bresp = c_bresp[0];       assign m1_bresp = c_bresp[1];
    assign m0_buser = c_buser[0];       assign m1_buser = c_buser[1];
    assign {m1_bvalid, m0_bvalid} = c_bvalid_v;
    assign s0_acaddr = s_acaddr[0];     assign s1_acaddr = s_acaddr[1];
    assign s0_acsnoop = s_acsnoop[0];   assign s1_acsnoop = s_acsnoop[1];
    assign s0_acprot = s_acprot[0];     assign s1_acprot = s_acprot[1];
    assign {s1_acvalid, s0_acvalid} = s_acvalid_v;
    assign s_crresp[0] = s0_crresp;     assign s_crresp[1] = s1_crresp;
    assign {s1_crready, s0_crready} = s_crready_v;
    assign s_cddata[0] = s0_cddata;     assign s_cddata[1] = s1_cddata;
    assign {s1_cdready, s0_cdready} = s_cdready_v;
    assign c_coh_addr[0] = coh0_addr;   assign c_coh_addr[1] = coh1_addr;
    assign c_coh_type[0] = coh0_type;   assign c_coh_type[1] = coh1_type;
    assign c_done_id[0] = done0_id;     assign c_done_id[1] = done1_id;

    onyx_ccu #(
        .N_PORTS        (2),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .SLOTS          (FAB_SLOTS),
        .SNOOP_INFLIGHT (SNOOP_INFLIGHT),
        .DEFER_AR       (DEFER_AR),
        .SERIAL_MODE    (SERIAL_MODE)
    ) u_fabric (
        .clk              (clk),
        .rst_n            (rst_n),
        .c_arid           (c_arid),
        .c_araddr         (c_araddr),
        .c_arlen          (c_arlen),
        .c_arsize         (c_arsize),
        .c_arburst        (c_arburst),
        .c_arlock         ({m1_arlock, m0_arlock}),
        .c_arcache        (c_arcache),
        .c_arprot         (c_arprot),
        .c_arqos          (c_arqos),
        .c_arregion       (c_arregion),
        .c_aruser         (c_aruser),
        .c_arvalid        ({m1_arvalid, m0_arvalid}),
        .c_arready        (c_arready_v),
        .c_rid            (c_rid),
        .c_rdata          (c_rdata),
        .c_rresp          (c_rresp),
        .c_rlast          (c_rlast_v),
        .c_ruser          (c_ruser),
        .c_rvalid         (c_rvalid_v),
        .c_rready         ({m1_rready, m0_rready}),
        .c_awid           (c_awid),
        .c_awaddr         (c_awaddr),
        .c_awlen          (c_awlen),
        .c_awsize         (c_awsize),
        .c_awburst        (c_awburst),
        .c_awlock         ({m1_awlock, m0_awlock}),
        .c_awcache        (c_awcache),
        .c_awprot         (c_awprot),
        .c_awqos          (c_awqos),
        .c_awregion       (c_awregion),
        .c_awuser         (c_awuser),
        .c_awvalid        ({m1_awvalid, m0_awvalid}),
        .c_awready        (c_awready_v),
        .c_wdata          (c_wdata),
        .c_wstrb          (c_wstrb),
        .c_wlast          ({m1_wlast, m0_wlast}),
        .c_wuser          (c_wuser),
        .c_wvalid         ({m1_wvalid, m0_wvalid}),
        .c_wready         (c_wready_v),
        .c_bid            (c_bid),
        .c_bresp          (c_bresp),
        .c_buser          (c_buser),
        .c_bvalid         (c_bvalid_v),
        .c_bready         ({m1_bready, m0_bready}),
        .s_acaddr         (s_acaddr),
        .s_acsnoop        (s_acsnoop),
        .s_acprot         (s_acprot),
        .s_acvalid        (s_acvalid_v),
        .s_acready        ({s1_acready, s0_acready}),
        .s_crresp         (s_crresp),
        .s_crvalid        ({s1_crvalid, s0_crvalid}),
        .s_crready        (s_crready_v),
        .s_cddata         (s_cddata),
        .s_cdlast         ({s1_cdlast, s0_cdlast}),
        .s_cdvalid        ({s1_cdvalid, s0_cdvalid}),
        .s_cdready        (s_cdready_v),
        .c_coh_req_valid  ({coh1_valid, coh0_valid}),
        .c_coh_req_addr   (c_coh_addr),
        .c_coh_req_type   (c_coh_type),
        .c_coh_done_valid ({done1_valid, done0_valid}),
        .c_coh_done_id    (c_done_id),
        .mem_arid         (mem_arid),
        .mem_araddr       (mem_araddr),
        .mem_arlen        (mem_arlen),
        .mem_arsize       (mem_arsize),
        .mem_arburst      (mem_arburst),
        .mem_arlock       (mem_arlock),
        .mem_arcache      (mem_arcache),
        .mem_arprot       (mem_arprot),
        .mem_arqos        (mem_arqos),
        .mem_arregion     (mem_arregion),
        .mem_aruser       (mem_aruser),
        .mem_arvalid      (mem_arvalid),
        .mem_arready      (mem_arready),
        .mem_rid          (mem_rid),
        .mem_rdata        (mem_rdata),
        .mem_rresp        (mem_rresp),
        .mem_rlast        (mem_rlast),
        .mem_ruser        (mem_ruser),
        .mem_rvalid       (mem_rvalid),
        .mem_rready       (mem_rready),
        .mem_awid         (mem_awid),
        .mem_awaddr       (mem_awaddr),
        .mem_awlen        (mem_awlen),
        .mem_awsize       (mem_awsize),
        .mem_awburst      (mem_awburst),
        .mem_awlock       (mem_awlock),
        .mem_awcache      (mem_awcache),
        .mem_awprot       (mem_awprot),
        .mem_awqos        (mem_awqos),
        .mem_awregion     (mem_awregion),
        .mem_awuser       (mem_awuser),
        .mem_awvalid      (mem_awvalid),
        .mem_awready      (mem_awready),
        .mem_wdata        (mem_wdata),
        .mem_wstrb        (mem_wstrb),
        .mem_wlast        (mem_wlast),
        .mem_wuser        (mem_wuser),
        .mem_wvalid       (mem_wvalid),
        .mem_wready       (mem_wready),
        .mem_bid          (mem_bid),
        .mem_bresp        (mem_bresp),
        .mem_buser        (mem_buser),
        .mem_bvalid       (mem_bvalid),
        .mem_bready       (mem_bready),
        .dbg_busy         (),
        .dbg_slot_vld     (),
        .dbg_pend_vld     (),
        .dbg_abs_pend     (),
        .dbg_grant        (),
        .dbg_grant_dir    (oc_grant_dir),
        .dbg_grant_addr   (),
        .dbg_grant_slot   (oc_grant_slot),
        .evt_grant        (oc_evt_grant),
        .evt_grant_cls    (oc_evt_grant_cls),
        .evt_ac           (oc_evt_ac),
        .evt_gather       (oc_evt_gather),
        .evt_gather_slot  (oc_evt_gather_slot),
        .evt_gather_dt    (oc_evt_gather_dt),
        .evt_gather_pd    (oc_evt_gather_pd),
        .evt_mem_ar       (oc_evt_mem_ar),
        .evt_read_wasted  (oc_evt_read_wasted),
        .evt_absorb       (oc_evt_absorb),
        .evt_wb           (oc_evt_wb),
        .evt_lock_wait    (oc_evt_lock_wait)
    );

    // onyx's D9 observer beside the unit (onyx_top composes the two; the
    // pair-rig TB reads u_fabric's internals, so the unit stays u_fabric)
    onyx_monlite #(
        .N_PORTS     (2),
        .SLOTS       (FAB_SLOTS),
        .USE_MONITOR (USE_MONITOR),
        .OUT_DEPTH   (16)
    ) u_onyx_mon (
        .clk               (clk),
        .rst_n             (rst_n),
        .evt_grant_i       (oc_evt_grant),
        .evt_grant_port_i  (oc_grant_dir),
        .evt_grant_slot_i  (oc_grant_slot),
        .evt_grant_cls_i   (oc_evt_grant_cls),
        .evt_ac_i          (oc_evt_ac),
        .evt_gather_i      (oc_evt_gather),
        .evt_gather_slot_i (oc_evt_gather_slot),
        .evt_gather_dt_i   (oc_evt_gather_dt),
        .evt_gather_pd_i   (oc_evt_gather_pd),
        .evt_mem_ar_i      (oc_evt_mem_ar),
        .evt_mem_ar_slot_i (mem_arid[$clog2(FAB_SLOTS)-1:0]),
        .evt_read_wasted_i (oc_evt_read_wasted),
        .evt_absorb_i      (oc_evt_absorb),
        .evt_absorb_slot_i ('0),
        .evt_wb_i          (oc_evt_wb),
        .evt_wb_port_i     ('0),
        .evt_lock_wait_i   (oc_evt_lock_wait),
        .i_mon_time        (mon_time_q),
        .monbus_valid      (mon2_valid),
        .monbus_ready      (mon2_ready),
        .monbus_packet     (mon2_packet),
        .monbus_timestamp  (mon2_timestamp),
        .dropped_count     (mon2_dropped)
    );
    onyx_counters #(.N_PORTS(2)) u_onyx_cnt (
        .clk(clk), .rst_n(rst_n), .clear_i(1'b0), .freeze_i(1'b0),
        .evt_grant_i(oc_evt_grant), .evt_gather_i(oc_evt_gather), .evt_gather_dt_i(oc_evt_gather_dt),
        .evt_mem_ar_i(oc_evt_mem_ar), .evt_read_wasted_i(oc_evt_read_wasted),
        .evt_absorb_i(oc_evt_absorb), .evt_wb_i(oc_evt_wb),
        .cnt_txn_o(cnt_txn), .cnt_supplied_o(cnt_supplied), .cnt_mem_read_o(cnt_mem_read),
        .cnt_read_wasted_o(cnt_read_wasted), .cnt_absorb_o(cnt_absorb), .cnt_wb_o(cnt_wb)
    );

    // ------------------------------------------------------------------
    // The shared memory (the D11 ruling's genuine sdpram_core consumer)
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

endmodule : onyx_pair_rig_tb
