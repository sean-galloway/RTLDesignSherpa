// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_core_rig_tb
// Purpose: the core-alone rig (onyx TASK-001 step 5): onyx_ccu by itself,
//   every neighbour a cocotb BFM -- N_PORTS BFM caches (an AXI4 master
//   pair for the memory side, an ACE snoop slave for AC/CR/CD, the D-8
//   request and retire sidebands driven by the TB's cache model) and an
//   AXI4 slave memory.  Pure wiring.
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/docs/onyx_has/onyx_has_index.md
// Subsystem: onyx (cache-ip)
//
// Author: sean galloway
// Created: 2026-11-26
//==============================================================================
// Description:
//   onyx_ccu's cache side is unpacked arrays over N_PORTS; the BFMs bind
//   flat names, so the rig declares four port sets c0_* .. c3_* (the
//   largest N_PORTS, D11) and connects the first N_PORTS.  A set beyond
//   N_PORTS is left unconnected (its outputs read 0, the TB binds no BFM
//   to it).  The memory side is mem_*.  The ACE-Lite IO port is tied idle:
//   the IO's paths are the pair rig's and the reference rig's (onyx
//   TASK-001 D1); this rig is about the caches against the core.
//
// Parameters:
//   N_PORTS        -- live cache ports, 2..4
//   ADDR_WIDTH, LINE_BYTES, BUS_WIDTH, AXI_ID_WIDTH -- onyx_ccu geometry
//   SLOTS, SNOOP_INFLIGHT, DEFER_AR, SERIAL_MODE -- onyx_ccu modes
//
// Test:
//   Location: projects/components/cache-ip/onyx-ace-ccu/dv/tests/test_onyx_core_rig.py
//   Run: cd projects/components/cache-ip/onyx-ace-ccu/dv/tests && make clean-all && make run-all-gate-parallel
//==============================================================================
`timescale 1ns / 1ps

// One cache port set: the cache's AXI4 master (memory side), its ACE snoop
// responder (AC in, CR/CD out) and the D-8 request / retire sidebands.
`define ONYX_RIG_CACHE_PORTS(P)                                          \
    input  logic [AXI_ID_WIDTH-1:0]     P``_arid,                        \
    input  logic [ADDR_WIDTH-1:0]       P``_araddr,                      \
    input  logic [7:0]                  P``_arlen,                       \
    input  logic [2:0]                  P``_arsize,                      \
    input  logic [1:0]                  P``_arburst,                     \
    input  logic                        P``_arlock,                      \
    input  logic [3:0]                  P``_arcache,                     \
    input  logic [2:0]                  P``_arprot,                      \
    input  logic [3:0]                  P``_arqos,                       \
    input  logic [3:0]                  P``_arregion,                    \
    input  logic [0:0]                  P``_aruser,                      \
    input  logic                        P``_arvalid,                     \
    output logic                        P``_arready,                     \
    output logic [AXI_ID_WIDTH-1:0]     P``_rid,                         \
    output logic [BUS_WIDTH-1:0]        P``_rdata,                       \
    output logic [1:0]                  P``_rresp,                       \
    output logic                        P``_rlast,                       \
    output logic [0:0]                  P``_ruser,                       \
    output logic                        P``_rvalid,                      \
    input  logic                        P``_rready,                      \
    input  logic [AXI_ID_WIDTH-1:0]     P``_awid,                        \
    input  logic [ADDR_WIDTH-1:0]       P``_awaddr,                      \
    input  logic [7:0]                  P``_awlen,                       \
    input  logic [2:0]                  P``_awsize,                      \
    input  logic [1:0]                  P``_awburst,                     \
    input  logic                        P``_awlock,                      \
    input  logic [3:0]                  P``_awcache,                     \
    input  logic [2:0]                  P``_awprot,                      \
    input  logic [3:0]                  P``_awqos,                       \
    input  logic [3:0]                  P``_awregion,                    \
    input  logic [0:0]                  P``_awuser,                      \
    input  logic                        P``_awvalid,                     \
    output logic                        P``_awready,                     \
    input  logic [BUS_WIDTH-1:0]        P``_wdata,                       \
    input  logic [BUS_WIDTH/8-1:0]      P``_wstrb,                       \
    input  logic                        P``_wlast,                       \
    input  logic [0:0]                  P``_wuser,                       \
    input  logic                        P``_wvalid,                      \
    output logic                        P``_wready,                      \
    output logic [AXI_ID_WIDTH-1:0]     P``_bid,                         \
    output logic [1:0]                  P``_bresp,                       \
    output logic [0:0]                  P``_buser,                       \
    output logic                        P``_bvalid,                      \
    input  logic                        P``_bready,                      \
    output logic [ADDR_WIDTH-1:0]       P``_acaddr,                      \
    output logic [3:0]                  P``_acsnoop,                     \
    output logic [2:0]                  P``_acprot,                      \
    output logic                        P``_acvalid,                     \
    input  logic                        P``_acready,                     \
    input  logic [4:0]                  P``_crresp,                      \
    input  logic                        P``_crvalid,                     \
    output logic                        P``_crready,                     \
    input  logic [BUS_WIDTH-1:0]        P``_cddata,                      \
    input  logic                        P``_cdlast,                      \
    input  logic                        P``_cdvalid,                     \
    output logic                        P``_cdready,                     \
    input  logic                        P``_coh_req_valid,               \
    input  logic [ADDR_WIDTH-1:0]       P``_coh_req_addr,                \
    input  logic [2:0]                  P``_coh_req_type,                \
    input  logic                        P``_coh_done_valid,              \
    input  logic [AXI_ID_WIDTH-1:0]     P``_coh_done_id,

// Port set P onto array index I of the core (I < N_PORTS), or its outputs
// tied off (I >= N_PORTS).
`define ONYX_RIG_CACHE_BIND(P, I)                                        \
    if (I < N_PORTS) begin : g_bind_``P                                   \
        assign a_arid[I] = P``_arid;       assign a_araddr[I] = P``_araddr; \
        assign a_arlen[I] = P``_arlen;     assign a_arsize[I] = P``_arsize; \
        assign a_arburst[I] = P``_arburst; assign a_arlock[I] = P``_arlock; \
        assign a_arcache[I] = P``_arcache; assign a_arprot[I] = P``_arprot; \
        assign a_arqos[I] = P``_arqos;     assign a_arregion[I] = P``_arregion; \
        assign a_aruser[I] = P``_aruser;   assign a_arvalid[I] = P``_arvalid; \
        assign P``_arready = a_arready[I];                                \
        assign P``_rid = a_rid[I];         assign P``_rdata = a_rdata[I];  \
        assign P``_rresp = a_rresp[I];     assign P``_rlast = a_rlast[I];  \
        assign P``_ruser = a_ruser[I];     assign P``_rvalid = a_rvalid[I]; \
        assign a_rready[I] = P``_rready;                                  \
        assign a_awid[I] = P``_awid;       assign a_awaddr[I] = P``_awaddr; \
        assign a_awlen[I] = P``_awlen;     assign a_awsize[I] = P``_awsize; \
        assign a_awburst[I] = P``_awburst; assign a_awlock[I] = P``_awlock; \
        assign a_awcache[I] = P``_awcache; assign a_awprot[I] = P``_awprot; \
        assign a_awqos[I] = P``_awqos;     assign a_awregion[I] = P``_awregion; \
        assign a_awuser[I] = P``_awuser;   assign a_awvalid[I] = P``_awvalid; \
        assign P``_awready = a_awready[I];                                \
        assign a_wdata[I] = P``_wdata;     assign a_wstrb[I] = P``_wstrb;  \
        assign a_wlast[I] = P``_wlast;     assign a_wuser[I] = P``_wuser;  \
        assign a_wvalid[I] = P``_wvalid;   assign P``_wready = a_wready[I]; \
        assign P``_bid = a_bid[I];         assign P``_bresp = a_bresp[I];  \
        assign P``_buser = a_buser[I];     assign P``_bvalid = a_bvalid[I]; \
        assign a_bready[I] = P``_bready;                                  \
        assign P``_acaddr = a_acaddr[I];   assign P``_acsnoop = a_acsnoop[I]; \
        assign P``_acprot = a_acprot[I];   assign P``_acvalid = a_acvalid[I]; \
        assign a_acready[I] = P``_acready;                                \
        assign a_crresp[I] = P``_crresp;   assign a_crvalid[I] = P``_crvalid; \
        assign P``_crready = a_crready[I];                                \
        assign a_cddata[I] = P``_cddata;   assign a_cdlast[I] = P``_cdlast; \
        assign a_cdvalid[I] = P``_cdvalid; assign P``_cdready = a_cdready[I]; \
        assign a_coh_req_valid[I] = P``_coh_req_valid;                    \
        assign a_coh_req_addr[I]  = P``_coh_req_addr;                     \
        assign a_coh_req_type[I]  = P``_coh_req_type;                     \
        assign a_coh_done_valid[I] = P``_coh_done_valid;                  \
        assign a_coh_done_id[I]    = P``_coh_done_id;                     \
    end else begin : g_tie_``P                                            \
        assign P``_arready = 1'b0;  assign P``_rid = '0;   assign P``_rdata = '0; \
        assign P``_rresp = '0;      assign P``_rlast = 1'b0; assign P``_ruser = '0; \
        assign P``_rvalid = 1'b0;   assign P``_awready = 1'b0; assign P``_wready = 1'b0; \
        assign P``_bid = '0;        assign P``_bresp = '0; assign P``_buser = '0; \
        assign P``_bvalid = 1'b0;   assign P``_acaddr = '0; assign P``_acsnoop = '0; \
        assign P``_acprot = '0;     assign P``_acvalid = 1'b0; assign P``_crready = 1'b0; \
        assign P``_cdready = 1'b0;                                        \
    end

module onyx_core_rig_tb #(
    parameter int N_PORTS        = 2,
    parameter int ADDR_WIDTH     = 32,
    parameter int LINE_BYTES     = 64,
    parameter int BUS_WIDTH      = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int SLOTS          = 18,
    parameter int SNOOP_INFLIGHT = 2,
    parameter bit DEFER_AR       = 1'b0,
    parameter bit SERIAL_MODE    = 1'b0
) (
    input  logic                        clk,
    input  logic                        rst_n,

    `ONYX_RIG_CACHE_PORTS(c0)
    `ONYX_RIG_CACHE_PORTS(c1)
    `ONYX_RIG_CACHE_PORTS(c2)
    `ONYX_RIG_CACHE_PORTS(c3)

    // memory side (the TB's AXI4 slave)
    output logic [AXI_ID_WIDTH-1:0]     mem_arid,
    output logic [ADDR_WIDTH-1:0]       mem_araddr,
    output logic [7:0]                  mem_arlen,
    output logic [2:0]                  mem_arsize,
    output logic [1:0]                  mem_arburst,
    output logic                        mem_arlock,
    output logic [3:0]                  mem_arcache,
    output logic [2:0]                  mem_arprot,
    output logic [3:0]                  mem_arqos,
    output logic [3:0]                  mem_arregion,
    output logic [0:0]                  mem_aruser,
    output logic                        mem_arvalid,
    input  logic                        mem_arready,
    input  logic [AXI_ID_WIDTH-1:0]     mem_rid,
    input  logic [BUS_WIDTH-1:0]        mem_rdata,
    input  logic [1:0]                  mem_rresp,
    input  logic                        mem_rlast,
    input  logic [0:0]                  mem_ruser,
    input  logic                        mem_rvalid,
    output logic                        mem_rready,
    output logic [AXI_ID_WIDTH-1:0]     mem_awid,
    output logic [ADDR_WIDTH-1:0]       mem_awaddr,
    output logic [7:0]                  mem_awlen,
    output logic [2:0]                  mem_awsize,
    output logic [1:0]                  mem_awburst,
    output logic                        mem_awlock,
    output logic [3:0]                  mem_awcache,
    output logic [2:0]                  mem_awprot,
    output logic [3:0]                  mem_awqos,
    output logic [3:0]                  mem_awregion,
    output logic [0:0]                  mem_awuser,
    output logic                        mem_awvalid,
    input  logic                        mem_awready,
    output logic [BUS_WIDTH-1:0]        mem_wdata,
    output logic [BUS_WIDTH/8-1:0]      mem_wstrb,
    output logic                        mem_wlast,
    output logic [0:0]                  mem_wuser,
    output logic                        mem_wvalid,
    input  logic                        mem_wready,
    input  logic [AXI_ID_WIDTH-1:0]     mem_bid,
    input  logic [1:0]                  mem_bresp,
    input  logic [0:0]                  mem_buser,
    input  logic                        mem_bvalid,
    output logic                        mem_bready,

    // grant tap (the TB counts grants per port and class)
    output logic                        dbg_grant,
    output logic [2:0]                  dbg_grant_dir,
    output logic [ADDR_WIDTH-1:0]       dbg_grant_addr,
    output logic [3:0]                  dbg_busy_slots
);

    localparam int STRB_W = BUS_WIDTH / 8;
    localparam int RQ_W   = $clog2(N_PORTS + 1);

    // the core's per-port arrays
    logic [AXI_ID_WIDTH-1:0] a_arid [N_PORTS];
    logic [ADDR_WIDTH-1:0]   a_araddr [N_PORTS];
    logic [7:0]              a_arlen [N_PORTS];
    logic [2:0]              a_arsize [N_PORTS];
    logic [1:0]              a_arburst [N_PORTS];
    logic [N_PORTS-1:0]      a_arlock;
    logic [3:0]              a_arcache [N_PORTS];
    logic [2:0]              a_arprot [N_PORTS];
    logic [3:0]              a_arqos [N_PORTS];
    logic [3:0]              a_arregion [N_PORTS];
    logic [0:0]              a_aruser [N_PORTS];
    logic [N_PORTS-1:0]      a_arvalid, a_arready;
    logic [AXI_ID_WIDTH-1:0] a_rid [N_PORTS];
    logic [BUS_WIDTH-1:0]    a_rdata [N_PORTS];
    logic [1:0]              a_rresp [N_PORTS];
    logic [N_PORTS-1:0]      a_rlast;
    logic [0:0]              a_ruser [N_PORTS];
    logic [N_PORTS-1:0]      a_rvalid, a_rready;
    logic [AXI_ID_WIDTH-1:0] a_awid [N_PORTS];
    logic [ADDR_WIDTH-1:0]   a_awaddr [N_PORTS];
    logic [7:0]              a_awlen [N_PORTS];
    logic [2:0]              a_awsize [N_PORTS];
    logic [1:0]              a_awburst [N_PORTS];
    logic [N_PORTS-1:0]      a_awlock;
    logic [3:0]              a_awcache [N_PORTS];
    logic [2:0]              a_awprot [N_PORTS];
    logic [3:0]              a_awqos [N_PORTS];
    logic [3:0]              a_awregion [N_PORTS];
    logic [0:0]              a_awuser [N_PORTS];
    logic [N_PORTS-1:0]      a_awvalid, a_awready;
    logic [BUS_WIDTH-1:0]    a_wdata [N_PORTS];
    logic [STRB_W-1:0]       a_wstrb [N_PORTS];
    logic [N_PORTS-1:0]      a_wlast;
    logic [0:0]              a_wuser [N_PORTS];
    logic [N_PORTS-1:0]      a_wvalid, a_wready;
    logic [AXI_ID_WIDTH-1:0] a_bid [N_PORTS];
    logic [1:0]              a_bresp [N_PORTS];
    logic [0:0]              a_buser [N_PORTS];
    logic [N_PORTS-1:0]      a_bvalid, a_bready;
    logic [ADDR_WIDTH-1:0]   a_acaddr [N_PORTS];
    logic [3:0]              a_acsnoop [N_PORTS];
    logic [2:0]              a_acprot [N_PORTS];
    logic [N_PORTS-1:0]      a_acvalid, a_acready;
    logic [4:0]              a_crresp [N_PORTS];
    logic [N_PORTS-1:0]      a_crvalid, a_crready;
    logic [BUS_WIDTH-1:0]    a_cddata [N_PORTS];
    logic [N_PORTS-1:0]      a_cdlast, a_cdvalid, a_cdready;
    logic [N_PORTS-1:0]      a_coh_req_valid;
    logic [ADDR_WIDTH-1:0]   a_coh_req_addr [N_PORTS];
    logic [2:0]              a_coh_req_type [N_PORTS];
    logic [N_PORTS-1:0]      a_coh_done_valid;
    logic [AXI_ID_WIDTH-1:0] a_coh_done_id [N_PORTS];

    generate
        `ONYX_RIG_CACHE_BIND(c0, 0)
        `ONYX_RIG_CACHE_BIND(c1, 1)
        `ONYX_RIG_CACHE_BIND(c2, 2)
        `ONYX_RIG_CACHE_BIND(c3, 3)
    endgenerate

    logic [SLOTS-1:0] w_slot_vld;
    logic [RQ_W-1:0]  w_grant_dir;
    /* verilator lint_off UNUSEDSIGNAL */
    logic             w_unused_io_r, w_unused_io_b;
    logic [AXI_ID_WIDTH-1:0] w_io_rid, w_io_bid;
    logic [BUS_WIDTH-1:0]    w_io_rdata;
    logic [1:0]       w_io_rresp, w_io_bresp;
    logic [0:0]       w_io_ruser, w_io_buser;
    logic             w_io_arready, w_io_awready, w_io_wready, w_io_rlast;
    /* verilator lint_on UNUSEDSIGNAL */

    onyx_ccu #(
        .N_PORTS        (N_PORTS),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (1),
        .SLOTS          (SLOTS),
        .SNOOP_INFLIGHT (SNOOP_INFLIGHT),
        .DEFER_AR       (DEFER_AR),
        .SERIAL_MODE    (SERIAL_MODE)
    ) u_ccu (
        .clk (clk), .rst_n (rst_n),
        .c_arid (a_arid), .c_araddr (a_araddr), .c_arlen (a_arlen), .c_arsize (a_arsize),
        .c_arburst (a_arburst), .c_arlock (a_arlock), .c_arcache (a_arcache),
        .c_arprot (a_arprot), .c_arqos (a_arqos), .c_arregion (a_arregion),
        .c_aruser (a_aruser), .c_arvalid (a_arvalid), .c_arready (a_arready),
        .c_rid (a_rid), .c_rdata (a_rdata), .c_rresp (a_rresp), .c_rlast (a_rlast),
        .c_ruser (a_ruser), .c_rvalid (a_rvalid), .c_rready (a_rready),
        .c_awid (a_awid), .c_awaddr (a_awaddr), .c_awlen (a_awlen), .c_awsize (a_awsize),
        .c_awburst (a_awburst), .c_awlock (a_awlock), .c_awcache (a_awcache),
        .c_awprot (a_awprot), .c_awqos (a_awqos), .c_awregion (a_awregion),
        .c_awuser (a_awuser), .c_awvalid (a_awvalid), .c_awready (a_awready),
        .c_wdata (a_wdata), .c_wstrb (a_wstrb), .c_wlast (a_wlast), .c_wuser (a_wuser),
        .c_wvalid (a_wvalid), .c_wready (a_wready),
        .c_bid (a_bid), .c_bresp (a_bresp), .c_buser (a_buser), .c_bvalid (a_bvalid),
        .c_bready (a_bready),
        .s_acaddr (a_acaddr), .s_acsnoop (a_acsnoop), .s_acprot (a_acprot),
        .s_acvalid (a_acvalid), .s_acready (a_acready),
        .s_crresp (a_crresp), .s_crvalid (a_crvalid), .s_crready (a_crready),
        .s_cddata (a_cddata), .s_cdlast (a_cdlast), .s_cdvalid (a_cdvalid),
        .s_cdready (a_cdready),
        .c_coh_req_valid (a_coh_req_valid), .c_coh_req_addr (a_coh_req_addr),
        .c_coh_req_type (a_coh_req_type),
        .c_coh_done_valid (a_coh_done_valid), .c_coh_done_id (a_coh_done_id),
        // the IO port, idle
        .io_arid ('0), .io_araddr ('0), .io_arlen ('0), .io_arsize ('0), .io_arburst ('0),
        .io_arlock (1'b0), .io_arcache ('0), .io_arprot ('0), .io_arqos ('0),
        .io_arregion ('0), .io_aruser ('0), .io_arsnoop ('0), .io_ardomain ('0),
        .io_arbar ('0), .io_arvalid (1'b0), .io_arready (w_io_arready),
        .io_rid (w_io_rid), .io_rdata (w_io_rdata), .io_rresp (w_io_rresp),
        .io_rlast (w_io_rlast), .io_ruser (w_io_ruser), .io_rvalid (w_unused_io_r),
        .io_rready (1'b1),
        .io_awid ('0), .io_awaddr ('0), .io_awlen ('0), .io_awsize ('0), .io_awburst ('0),
        .io_awlock (1'b0), .io_awcache ('0), .io_awprot ('0), .io_awqos ('0),
        .io_awregion ('0), .io_awuser ('0), .io_awsnoop ('0), .io_awdomain ('0),
        .io_awbar ('0), .io_awvalid (1'b0), .io_awready (w_io_awready),
        .io_wdata ('0), .io_wstrb ('0), .io_wlast (1'b0), .io_wuser ('0),
        .io_wvalid (1'b0), .io_wready (w_io_wready),
        .io_bid (w_io_bid), .io_bresp (w_io_bresp), .io_buser (w_io_buser),
        .io_bvalid (w_unused_io_b), .io_bready (1'b1),
        // memory
        .mem_arid (mem_arid), .mem_araddr (mem_araddr), .mem_arlen (mem_arlen),
        .mem_arsize (mem_arsize), .mem_arburst (mem_arburst), .mem_arlock (mem_arlock),
        .mem_arcache (mem_arcache), .mem_arprot (mem_arprot), .mem_arqos (mem_arqos),
        .mem_arregion (mem_arregion), .mem_aruser (mem_aruser), .mem_arvalid (mem_arvalid),
        .mem_arready (mem_arready),
        .mem_rid (mem_rid), .mem_rdata (mem_rdata), .mem_rresp (mem_rresp),
        .mem_rlast (mem_rlast), .mem_ruser (mem_ruser), .mem_rvalid (mem_rvalid),
        .mem_rready (mem_rready),
        .mem_awid (mem_awid), .mem_awaddr (mem_awaddr), .mem_awlen (mem_awlen),
        .mem_awsize (mem_awsize), .mem_awburst (mem_awburst), .mem_awlock (mem_awlock),
        .mem_awcache (mem_awcache), .mem_awprot (mem_awprot), .mem_awqos (mem_awqos),
        .mem_awregion (mem_awregion), .mem_awuser (mem_awuser), .mem_awvalid (mem_awvalid),
        .mem_awready (mem_awready),
        .mem_wdata (mem_wdata), .mem_wstrb (mem_wstrb), .mem_wlast (mem_wlast),
        .mem_wuser (mem_wuser), .mem_wvalid (mem_wvalid), .mem_wready (mem_wready),
        .mem_bid (mem_bid), .mem_bresp (mem_bresp), .mem_buser (mem_buser),
        .mem_bvalid (mem_bvalid), .mem_bready (mem_bready),
        // taps
        .dbg_busy (), .dbg_slot_vld (w_slot_vld), .dbg_pend_vld (), .dbg_abs_pend (),
        .dbg_grant (dbg_grant), .dbg_grant_dir (w_grant_dir), .dbg_grant_addr (dbg_grant_addr),
        .dbg_grant_slot (),
        .evt_grant (), .evt_grant_cls (), .evt_ac (), .evt_gather (), .evt_gather_slot (),
        .evt_gather_dt (), .evt_gather_pd (), .evt_mem_ar (), .evt_read_wasted (),
        .evt_absorb (), .evt_absorb_slot (), .evt_wb (), .evt_wb_io (), .evt_lock_wait (),
        .evt_lock_wait_addr ()
    );

    assign dbg_grant_dir = 3'(w_grant_dir);

    // live slots, saturated at 15 (the TB samples occupancy)
    always_comb begin
        dbg_busy_slots = '0;
        for (int s = 0; s < SLOTS; s++)
            if (w_slot_vld[s] && (dbg_busy_slots != 4'hF)) dbg_busy_slots = dbg_busy_slots + 4'd1;
    end

endmodule : onyx_core_rig_tb

`undef ONYX_RIG_CACHE_PORTS
`undef ONYX_RIG_CACHE_BIND
