// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_top
// Purpose:
//   onyx_ccu with its D9 observer: the coherency unit plus onyx_monlite on
//   its event taps, one MonBus output.  Every onyx_ccu port passes through
//   (the per-port arrays, the memory master, the debug taps); the event
//   taps stay inside.  USE_MONITOR=0 ties the observer off (the same
//   present-vs-absent pin the caches carry).  Beside the observer,
//   onyx_counters holds exact counts of the events the D6 measurement is
//   made of, cleared and frozen with the rig's tally.
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/docs/onyx_has/onyx_has_index.md
// Subsystem: onyx (cache-ip)
//
// Author: sean galloway
// Created: 2026-11-21
`timescale 1ns / 1ps

module onyx_top
    import l1_pkg::*;
    import ocelus_common_pkg::*;
#(
    parameter int N_PORTS        = 2,
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int SLOTS          = 18,
    parameter int SNOOP_INFLIGHT = 1,
    parameter bit DEFER_AR       = 1'b0,
    parameter bit SERIAL_MODE    = 1'b0,
    parameter bit USE_MONITOR    = 1'b1,
    parameter int MON_OUT_DEPTH  = 16,
    localparam int STRB_W = BUS_WIDTH / 8,
    localparam int IW     = AXI_ID_WIDTH,
    localparam int UW     = AXI_USER_WIDTH,
    localparam int SLOT_W = (SLOTS > 1) ? $clog2(SLOTS) : 1,
    localparam int PORT_W = (N_PORTS > 1) ? $clog2(N_PORTS) : 1,
    localparam int N_REQ  = N_PORTS + 1,           // the caches and the IO port (D1)
    localparam int RQ_W   = $clog2(N_REQ)
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // Cache side: plain-AXI4 slave per port (the cache's memory side)
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               c_arid     [N_PORTS],
    input  logic [ADDR_WIDTH-1:0]       c_araddr   [N_PORTS],
    input  logic [7:0]                  c_arlen    [N_PORTS],
    input  logic [2:0]                  c_arsize   [N_PORTS],
    input  logic [1:0]                  c_arburst  [N_PORTS],
    input  logic [N_PORTS-1:0]          c_arlock,
    input  logic [3:0]                  c_arcache  [N_PORTS],
    input  logic [2:0]                  c_arprot   [N_PORTS],
    input  logic [3:0]                  c_arqos    [N_PORTS],
    input  logic [3:0]                  c_arregion [N_PORTS],
    input  logic [UW-1:0]               c_aruser   [N_PORTS],
    input  logic [N_PORTS-1:0]          c_arvalid,
    output logic [N_PORTS-1:0]          c_arready,
    output logic [IW-1:0]               c_rid      [N_PORTS],
    output logic [BUS_WIDTH-1:0]        c_rdata    [N_PORTS],
    output logic [1:0]                  c_rresp    [N_PORTS],
    output logic [N_PORTS-1:0]          c_rlast,
    output logic [UW-1:0]               c_ruser    [N_PORTS],
    output logic [N_PORTS-1:0]          c_rvalid,
    input  logic [N_PORTS-1:0]          c_rready,

    input  logic [IW-1:0]               c_awid     [N_PORTS],
    input  logic [ADDR_WIDTH-1:0]       c_awaddr   [N_PORTS],
    input  logic [7:0]                  c_awlen    [N_PORTS],
    input  logic [2:0]                  c_awsize   [N_PORTS],
    input  logic [1:0]                  c_awburst  [N_PORTS],
    input  logic [N_PORTS-1:0]          c_awlock,
    input  logic [3:0]                  c_awcache  [N_PORTS],
    input  logic [2:0]                  c_awprot   [N_PORTS],
    input  logic [3:0]                  c_awqos    [N_PORTS],
    input  logic [3:0]                  c_awregion [N_PORTS],
    input  logic [UW-1:0]               c_awuser   [N_PORTS],
    input  logic [N_PORTS-1:0]          c_awvalid,
    output logic [N_PORTS-1:0]          c_awready,
    input  logic [BUS_WIDTH-1:0]        c_wdata    [N_PORTS],
    input  logic [STRB_W-1:0]           c_wstrb    [N_PORTS],
    input  logic [N_PORTS-1:0]          c_wlast,
    input  logic [UW-1:0]               c_wuser    [N_PORTS],
    input  logic [N_PORTS-1:0]          c_wvalid,
    output logic [N_PORTS-1:0]          c_wready,
    output logic [IW-1:0]               c_bid      [N_PORTS],
    output logic [1:0]                  c_bresp    [N_PORTS],
    output logic [UW-1:0]               c_buser    [N_PORTS],
    output logic [N_PORTS-1:0]          c_bvalid,
    input  logic [N_PORTS-1:0]          c_bready,

    // ------------------------------------------------------------------
    // Snoop side per port: onyx drives AC into the cache's responder;
    // CR/CD return (the ACE-shaped D7 port)
    // ------------------------------------------------------------------
    output logic [ADDR_WIDTH-1:0]       s_acaddr   [N_PORTS],
    output logic [3:0]                  s_acsnoop  [N_PORTS],
    output logic [2:0]                  s_acprot   [N_PORTS],
    output logic [N_PORTS-1:0]          s_acvalid,
    input  logic [N_PORTS-1:0]          s_acready,
    input  logic [AMBER_CRRESP_WIDTH-1:0] s_crresp [N_PORTS],
    input  logic [N_PORTS-1:0]          s_crvalid,
    output logic [N_PORTS-1:0]          s_crready,
    input  logic [BUS_WIDTH-1:0]        s_cddata   [N_PORTS],
    input  logic [N_PORTS-1:0]          s_cdlast,
    input  logic [N_PORTS-1:0]          s_cdvalid,
    output logic [N_PORTS-1:0]          s_cdready,

    // ------------------------------------------------------------------
    // D-8 coherence sideband (one pulse per fill / upgrade / WB) and the
    // retire sideband per port
    // ------------------------------------------------------------------
    input  logic [N_PORTS-1:0]          c_coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       c_coh_req_addr [N_PORTS],
    input  logic [2:0]                  c_coh_req_type [N_PORTS],
    input  logic [N_PORTS-1:0]          c_coh_done_valid,
    input  logic [IW-1:0]               c_coh_done_id  [N_PORTS],

    // ------------------------------------------------------------------
    // ACE-Lite IO port (D1): one non-caching master, requester N_PORTS
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               io_arid,
    input  logic [ADDR_WIDTH-1:0]       io_araddr,
    input  logic [7:0]                  io_arlen,
    input  logic [2:0]                  io_arsize,
    input  logic [1:0]                  io_arburst,
    input  logic                        io_arlock,
    input  logic [3:0]                  io_arcache,
    input  logic [2:0]                  io_arprot,
    input  logic [3:0]                  io_arqos,
    input  logic [3:0]                  io_arregion,
    input  logic [UW-1:0]               io_aruser,
    input  logic [3:0]                  io_arsnoop,
    input  logic [1:0]                  io_ardomain,
    input  logic [1:0]                  io_arbar,
    input  logic                        io_arvalid,
    output logic                        io_arready,
    output logic [IW-1:0]               io_rid,
    output logic [BUS_WIDTH-1:0]        io_rdata,
    output logic [1:0]                  io_rresp,
    output logic                        io_rlast,
    output logic [UW-1:0]               io_ruser,
    output logic                        io_rvalid,
    input  logic                        io_rready,
    input  logic [IW-1:0]               io_awid,
    input  logic [ADDR_WIDTH-1:0]       io_awaddr,
    input  logic [7:0]                  io_awlen,
    input  logic [2:0]                  io_awsize,
    input  logic [1:0]                  io_awburst,
    input  logic                        io_awlock,
    input  logic [3:0]                  io_awcache,
    input  logic [2:0]                  io_awprot,
    input  logic [3:0]                  io_awqos,
    input  logic [3:0]                  io_awregion,
    input  logic [UW-1:0]               io_awuser,
    input  logic [2:0]                  io_awsnoop,
    input  logic [1:0]                  io_awdomain,
    input  logic [1:0]                  io_awbar,
    input  logic                        io_awvalid,
    output logic                        io_awready,
    input  logic [BUS_WIDTH-1:0]        io_wdata,
    input  logic [STRB_W-1:0]           io_wstrb,
    input  logic                        io_wlast,
    input  logic [UW-1:0]               io_wuser,
    input  logic                        io_wvalid,
    output logic                        io_wready,
    output logic [IW-1:0]               io_bid,
    output logic [1:0]                  io_bresp,
    output logic [UW-1:0]               io_buser,
    output logic                        io_bvalid,
    input  logic                        io_bready,

    // ------------------------------------------------------------------
    // Memory-side AXI4 master
    // ------------------------------------------------------------------
    output logic [IW-1:0]               mem_arid,
    output logic [ADDR_WIDTH-1:0]       mem_araddr,
    output logic [7:0]                  mem_arlen,
    output logic [2:0]                  mem_arsize,
    output logic [1:0]                  mem_arburst,
    output logic                        mem_arlock,
    output logic [3:0]                  mem_arcache,
    output logic [2:0]                  mem_arprot,
    output logic [3:0]                  mem_arqos,
    output logic [3:0]                  mem_arregion,
    output logic [UW-1:0]               mem_aruser,
    output logic                        mem_arvalid,
    input  logic                        mem_arready,
    input  logic [IW-1:0]               mem_rid,
    input  logic [BUS_WIDTH-1:0]        mem_rdata,
    input  logic [1:0]                  mem_rresp,
    input  logic                        mem_rlast,
    input  logic [UW-1:0]               mem_ruser,
    input  logic                        mem_rvalid,
    output logic                        mem_rready,

    output logic [IW-1:0]               mem_awid,
    output logic [ADDR_WIDTH-1:0]       mem_awaddr,
    output logic [7:0]                  mem_awlen,
    output logic [2:0]                  mem_awsize,
    output logic [1:0]                  mem_awburst,
    output logic                        mem_awlock,
    output logic [3:0]                  mem_awcache,
    output logic [2:0]                  mem_awprot,
    output logic [3:0]                  mem_awqos,
    output logic [3:0]                  mem_awregion,
    output logic [UW-1:0]               mem_awuser,
    output logic                        mem_awvalid,
    input  logic                        mem_awready,
    output logic [BUS_WIDTH-1:0]        mem_wdata,
    output logic [STRB_W-1:0]           mem_wstrb,
    output logic                        mem_wlast,
    output logic [UW-1:0]               mem_wuser,
    output logic                        mem_wvalid,
    input  logic                        mem_wready,
    input  logic [IW-1:0]               mem_bid,
    input  logic [1:0]                  mem_bresp,
    input  logic [UW-1:0]               mem_buser,
    input  logic                        mem_bvalid,
    output logic                        mem_bready,

    // ------------------------------------------------------------------
    // Debug / observability taps (unused in the datapath; the pair-rig
    // TB's names)
    // ------------------------------------------------------------------
    output logic                        dbg_busy,
    output logic [SLOTS-1:0]            dbg_slot_vld,
    output logic [N_PORTS-1:0]          dbg_pend_vld,
    output logic                        dbg_abs_pend,
    output logic                        dbg_grant,
    output logic [RQ_W-1:0]             dbg_grant_dir,      // the requester: a cache port, or N_PORTS for the IO port
    output logic [ADDR_WIDTH-1:0]       dbg_grant_addr,
    output logic [SLOT_W-1:0]           dbg_grant_slot,

    // ------------------------------------------------------------------
    // MonBus (D9) and the rig's timestamp source
    // ------------------------------------------------------------------
    input  monbus_timestamp_t           i_mon_time,
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output monitor_packet_t             mon_packet,
    output monbus_timestamp_t           mon_timestamp,
    output logic [7:0]                  mon_dropped,
    // the observer's masks, the ocelus layers (enables 1 = on; masks bit
    // set = drop; see onyx_monlite)
    input  logic                        mon_cfg_enable,
    input  logic                        mon_cfg_perf_enable,
    input  logic                        mon_cfg_error_enable,
    input  logic [15:0]                 mon_cfg_pkt_mask,
    input  logic [15:0]                 mon_cfg_perf_mask,
    input  logic [15:0]                 mon_cfg_error_mask,
    input  logic [N_REQ-1:0]            mon_cfg_port_mask,  // per requester; bit N_PORTS is the IO port
    // the content filter: an inclusive address window on the transaction
    input  logic                        mon_cfg_addr_win_enable,
    input  logic [ADDR_WIDTH-1:0]       mon_cfg_addr_win_low,
    input  logic [ADDR_WIDTH-1:0]       mon_cfg_addr_win_high,

    // exact event counters (onyx_counters): cleared and frozen with the
    // rig's tally so one host protocol snapshots both
    input  logic                        cnt_clear,
    input  logic                        cnt_freeze,
    output logic [31:0]                 cnt_txn,
    output logic [31:0]                 cnt_supplied,
    output logic [31:0]                 cnt_mem_read,
    output logic [31:0]                 cnt_read_wasted,
    output logic [31:0]                 cnt_absorb,
    output logic [31:0]                 cnt_wb
);

    logic                evt_grant;
    logic [2:0]          evt_grant_cls;
    logic [N_PORTS-1:0]  evt_ac;
    logic [N_PORTS-1:0]  evt_gather, evt_gather_dt, evt_gather_pd, evt_read_wasted;
    logic [SLOT_W-1:0]   evt_gather_slot [N_PORTS];
    logic                evt_mem_ar, evt_absorb, evt_wb, evt_wb_io;
    logic [SLOT_W-1:0]   evt_absorb_slot;
    logic [N_REQ-1:0]    evt_lock_wait;
    logic [ADDR_WIDTH-1:0] evt_lock_wait_addr [N_REQ];

    onyx_ccu #(
        .N_PORTS(N_PORTS), .ADDR_WIDTH(ADDR_WIDTH), .LINE_BYTES(LINE_BYTES),
        .BUS_WIDTH(BUS_WIDTH), .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .SLOTS(SLOTS), .SNOOP_INFLIGHT(SNOOP_INFLIGHT), .DEFER_AR(DEFER_AR), .SERIAL_MODE(SERIAL_MODE)
    ) u_ccu (
        .clk(clk), .rst_n(rst_n),
        .c_arid(c_arid), .c_araddr(c_araddr), .c_arlen(c_arlen), .c_arsize(c_arsize), .c_arburst(c_arburst),
        .c_arlock(c_arlock), .c_arcache(c_arcache), .c_arprot(c_arprot), .c_arqos(c_arqos),
        .c_arregion(c_arregion), .c_aruser(c_aruser), .c_arvalid(c_arvalid), .c_arready(c_arready),
        .c_rid(c_rid), .c_rdata(c_rdata), .c_rresp(c_rresp), .c_rlast(c_rlast), .c_ruser(c_ruser),
        .c_rvalid(c_rvalid), .c_rready(c_rready),
        .c_awid(c_awid), .c_awaddr(c_awaddr), .c_awlen(c_awlen), .c_awsize(c_awsize), .c_awburst(c_awburst),
        .c_awlock(c_awlock), .c_awcache(c_awcache), .c_awprot(c_awprot), .c_awqos(c_awqos),
        .c_awregion(c_awregion), .c_awuser(c_awuser), .c_awvalid(c_awvalid), .c_awready(c_awready),
        .c_wdata(c_wdata), .c_wstrb(c_wstrb), .c_wlast(c_wlast), .c_wuser(c_wuser), .c_wvalid(c_wvalid),
        .c_wready(c_wready), .c_bid(c_bid), .c_bresp(c_bresp), .c_buser(c_buser), .c_bvalid(c_bvalid),
        .c_bready(c_bready),
        .s_acaddr(s_acaddr), .s_acsnoop(s_acsnoop), .s_acprot(s_acprot), .s_acvalid(s_acvalid),
        .s_acready(s_acready), .s_crresp(s_crresp), .s_crvalid(s_crvalid), .s_crready(s_crready),
        .s_cddata(s_cddata), .s_cdlast(s_cdlast), .s_cdvalid(s_cdvalid), .s_cdready(s_cdready),
        .c_coh_req_valid(c_coh_req_valid), .c_coh_req_addr(c_coh_req_addr), .c_coh_req_type(c_coh_req_type),
        .c_coh_done_valid(c_coh_done_valid), .c_coh_done_id(c_coh_done_id),
        .io_arid(io_arid), .io_araddr(io_araddr), .io_arlen(io_arlen), .io_arsize(io_arsize),
        .io_arburst(io_arburst), .io_arlock(io_arlock), .io_arcache(io_arcache), .io_arprot(io_arprot),
        .io_arqos(io_arqos), .io_arregion(io_arregion), .io_aruser(io_aruser), .io_arsnoop(io_arsnoop),
        .io_ardomain(io_ardomain), .io_arbar(io_arbar), .io_arvalid(io_arvalid), .io_arready(io_arready),
        .io_rid(io_rid), .io_rdata(io_rdata), .io_rresp(io_rresp), .io_rlast(io_rlast), .io_ruser(io_ruser),
        .io_rvalid(io_rvalid), .io_rready(io_rready),
        .io_awid(io_awid), .io_awaddr(io_awaddr), .io_awlen(io_awlen), .io_awsize(io_awsize),
        .io_awburst(io_awburst), .io_awlock(io_awlock), .io_awcache(io_awcache), .io_awprot(io_awprot),
        .io_awqos(io_awqos), .io_awregion(io_awregion), .io_awuser(io_awuser), .io_awsnoop(io_awsnoop),
        .io_awdomain(io_awdomain), .io_awbar(io_awbar), .io_awvalid(io_awvalid), .io_awready(io_awready),
        .io_wdata(io_wdata), .io_wstrb(io_wstrb), .io_wlast(io_wlast), .io_wuser(io_wuser),
        .io_wvalid(io_wvalid), .io_wready(io_wready), .io_bid(io_bid), .io_bresp(io_bresp),
        .io_buser(io_buser), .io_bvalid(io_bvalid), .io_bready(io_bready),
        .mem_arid(mem_arid), .mem_araddr(mem_araddr), .mem_arlen(mem_arlen), .mem_arsize(mem_arsize),
        .mem_arburst(mem_arburst), .mem_arlock(mem_arlock), .mem_arcache(mem_arcache), .mem_arprot(mem_arprot),
        .mem_arqos(mem_arqos), .mem_arregion(mem_arregion), .mem_aruser(mem_aruser), .mem_arvalid(mem_arvalid),
        .mem_arready(mem_arready), .mem_rid(mem_rid), .mem_rdata(mem_rdata), .mem_rresp(mem_rresp),
        .mem_rlast(mem_rlast), .mem_ruser(mem_ruser), .mem_rvalid(mem_rvalid), .mem_rready(mem_rready),
        .mem_awid(mem_awid), .mem_awaddr(mem_awaddr), .mem_awlen(mem_awlen), .mem_awsize(mem_awsize),
        .mem_awburst(mem_awburst), .mem_awlock(mem_awlock), .mem_awcache(mem_awcache), .mem_awprot(mem_awprot),
        .mem_awqos(mem_awqos), .mem_awregion(mem_awregion), .mem_awuser(mem_awuser), .mem_awvalid(mem_awvalid),
        .mem_awready(mem_awready), .mem_wdata(mem_wdata), .mem_wstrb(mem_wstrb), .mem_wlast(mem_wlast),
        .mem_wuser(mem_wuser), .mem_wvalid(mem_wvalid), .mem_wready(mem_wready), .mem_bid(mem_bid),
        .mem_bresp(mem_bresp), .mem_buser(mem_buser), .mem_bvalid(mem_bvalid), .mem_bready(mem_bready),
        .dbg_busy(dbg_busy), .dbg_slot_vld(dbg_slot_vld), .dbg_pend_vld(dbg_pend_vld),
        .dbg_abs_pend(dbg_abs_pend), .dbg_grant(dbg_grant), .dbg_grant_dir(dbg_grant_dir),
        .dbg_grant_addr(dbg_grant_addr), .dbg_grant_slot(dbg_grant_slot),
        .evt_grant(evt_grant), .evt_grant_cls(evt_grant_cls), .evt_ac(evt_ac),
        .evt_gather(evt_gather), .evt_gather_slot(evt_gather_slot), .evt_gather_dt(evt_gather_dt),
        .evt_gather_pd(evt_gather_pd), .evt_mem_ar(evt_mem_ar), .evt_read_wasted(evt_read_wasted),
        .evt_absorb(evt_absorb), .evt_absorb_slot(evt_absorb_slot), .evt_wb(evt_wb), .evt_wb_io(evt_wb_io),
        .evt_lock_wait(evt_lock_wait), .evt_lock_wait_addr(evt_lock_wait_addr)
    );

    // a cache write-back's port rides in the AW's low ID bits only by
    // convention of the caches' IDs, which the observer does not assume:
    // v1 records a cache's write-back without a port (0) and the IO's
    // write as requester N_PORTS; the window matches the write on its AW
    // address and the absorption on its slot
    onyx_monlite #(
        .N_PORTS(N_PORTS), .SLOTS(SLOTS), .ADDR_WIDTH(ADDR_WIDTH), .USE_MONITOR(USE_MONITOR), .OUT_DEPTH(MON_OUT_DEPTH)
    ) u_mon (
        .clk(clk), .rst_n(rst_n),
        .evt_grant_i(evt_grant), .evt_grant_port_i(dbg_grant_dir), .evt_grant_slot_i(dbg_grant_slot),
        .evt_grant_addr_i(dbg_grant_addr),
        .evt_grant_cls_i(evt_grant_cls), .evt_ac_i(evt_ac),
        .evt_gather_i(evt_gather), .evt_gather_slot_i(evt_gather_slot),
        .evt_gather_dt_i(evt_gather_dt), .evt_gather_pd_i(evt_gather_pd),
        .evt_mem_ar_i(evt_mem_ar), .evt_mem_ar_slot_i(mem_arid[SLOT_W-1:0]),
        .evt_read_wasted_i(evt_read_wasted),
        .evt_absorb_i(evt_absorb), .evt_absorb_slot_i(evt_absorb_slot),
        .evt_wb_i(evt_wb), .evt_wb_port_i(evt_wb_io ? RQ_W'(N_PORTS) : '0), .evt_wb_addr_i(mem_awaddr),
        .evt_lock_wait_i(evt_lock_wait), .evt_lock_wait_addr_i(evt_lock_wait_addr),
        .cfg_mon_enable(mon_cfg_enable), .cfg_perf_enable(mon_cfg_perf_enable),
        .cfg_error_enable(mon_cfg_error_enable), .cfg_pkt_mask(mon_cfg_pkt_mask),
        .cfg_perf_mask(mon_cfg_perf_mask), .cfg_error_mask(mon_cfg_error_mask),
        .cfg_port_mask(mon_cfg_port_mask),
        .cfg_addr_win_enable(mon_cfg_addr_win_enable), .cfg_addr_win_low(mon_cfg_addr_win_low),
        .cfg_addr_win_high(mon_cfg_addr_win_high),
        .i_mon_time(i_mon_time),
        .monbus_valid(mon_valid), .monbus_ready(mon_ready),
        .monbus_packet(mon_packet), .monbus_timestamp(mon_timestamp),
        .dropped_count(mon_dropped)
    );

    onyx_counters #(.N_PORTS(N_PORTS)) u_cnt (
        .clk(clk), .rst_n(rst_n), .clear_i(cnt_clear), .freeze_i(cnt_freeze),
        .evt_grant_i(evt_grant), .evt_gather_i(evt_gather), .evt_gather_dt_i(evt_gather_dt),
        .evt_mem_ar_i(evt_mem_ar), .evt_read_wasted_i(evt_read_wasted),
        .evt_absorb_i(evt_absorb), .evt_wb_i(evt_wb),
        .cnt_txn_o(cnt_txn), .cnt_supplied_o(cnt_supplied), .cnt_mem_read_o(cnt_mem_read),
        .cnt_read_wasted_o(cnt_read_wasted), .cnt_absorb_o(cnt_absorb), .cnt_wb_o(cnt_wb)
    );

endmodule : onyx_top
