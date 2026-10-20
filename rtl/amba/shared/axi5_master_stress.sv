// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_stress
// Purpose: AXI5 bus-stress master: axi_stress_mst_rd / axi_stress_mst_wr on
//          the axi5_master_rd / axi5_master_wr channel modules.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// The AXI5 shell of the stress master. Same cores and status as
// axi4_master_stress, plus the AXI5 fields this build carries:
//   AxNSAID, AxTRACE, AxMPAM, AxMECID   (EN_NSAID / EN_TRACE / EN_MPAM /
//            EN_MECID) the fields of f_sb(start address), packed at the
//            axi_stress_pkg SB_M_* positions; the slave recomputes them.
//   BTRACE, RTRACE   (EN_TRACE) checked against the request's TRACE on a
//            window with sb set (responses echo), else against 0.
//   WPOISON, RPOISON (EN_POISON) f_poison(beat address, the window's rate).
// No AxREGION (AXI5 removed it). Not driven yet, held at 0: AWATOP, AxIDUNQ,
// AxTAGOP / WTAG / WTAGUPDATE, ARCHUNKEN, AWAKEUP; their response fields are
// ignored. Every AXI5 pin is on the port whatever the build; a pin of a
// disabled feature is tied off by the channel module.
// A port built for one direction (EN_RD / EN_WR = 0) elaborates no logic for
// the other; its outputs are tied idle and its status reads done, no errors.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi5_master_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD     = 1'b1,
    parameter bit EN_WR     = 1'b1,
    parameter bit EN_NSAID  = 1'b0,
    parameter bit EN_TRACE  = 1'b0,
    parameter bit EN_MPAM   = 1'b0,
    parameter bit EN_MECID  = 1'b0,
    parameter bit EN_POISON = 1'b0,
    parameter int DEPTH   = 16,
    parameter int NWIN    = 8,
    parameter int IW      = 8,
    parameter int DW      = 64,
    parameter int UW      = 1,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 4,
    parameter int SKID_DEPTH_B  = 2,
    parameter int NUM_TAGS = (DW / 128) > 0 ? (DW / 128) : 1,
    parameter int TW       = 4 * NUM_TAGS
) (
    input  logic              aclk,
    input  logic              aresetn,

    input  logic              go,
    input  logic              stop,
    input  stress_mdir_cfg_t  cfg_rd,
    input  stress_mdir_cfg_t  cfg_wr,
    input  stress_win_t       cfg_win [NWIN],
    input  logic [31:0]       cfg_hash_seed,
    output stress_mdir_sts_t  sts_rd,
    output stress_mdir_sts_t  sts_wr,

    output logic [IW-1:0]     m_axi_awid,
    output logic [31:0]       m_axi_awaddr,
    output logic [7:0]        m_axi_awlen,
    output logic [2:0]        m_axi_awsize,
    output logic [1:0]        m_axi_awburst,
    output logic              m_axi_awlock,
    output logic [3:0]        m_axi_awcache,
    output logic [2:0]        m_axi_awprot,
    output logic [3:0]        m_axi_awqos,
    output logic [UW-1:0]     m_axi_awuser,
    output logic              m_axi_awvalid,
    input  logic              m_axi_awready,
    output logic [5:0]        m_axi_awatop,
    output logic [3:0]        m_axi_awnsaid,
    output logic              m_axi_awtrace,
    output logic [10:0]       m_axi_awmpam,
    output logic [15:0]       m_axi_awmecid,
    output logic              m_axi_awidunq,
    output logic [1:0]        m_axi_awtagop,
    output logic              m_axi_awakeup,
    output logic [DW-1:0]     m_axi_wdata,
    output logic [DW/8-1:0]   m_axi_wstrb,
    output logic              m_axi_wlast,
    output logic [UW-1:0]     m_axi_wuser,
    output logic              m_axi_wvalid,
    input  logic              m_axi_wready,
    output logic              m_axi_wpoison,
    output logic [TW-1:0]     m_axi_wtag,
    output logic [NUM_TAGS-1:0] m_axi_wtagupdate,
    input  logic [IW-1:0]     m_axi_bid,
    input  logic [1:0]        m_axi_bresp,
    input  logic [UW-1:0]     m_axi_buser,
    input  logic              m_axi_bvalid,
    output logic              m_axi_bready,
    input  logic              m_axi_btrace,
    input  logic              m_axi_bidunq,
    input  logic [1:0]        m_axi_btagmatch,
    output logic [IW-1:0]     m_axi_arid,
    output logic [31:0]       m_axi_araddr,
    output logic [7:0]        m_axi_arlen,
    output logic [2:0]        m_axi_arsize,
    output logic [1:0]        m_axi_arburst,
    output logic              m_axi_arlock,
    output logic [3:0]        m_axi_arcache,
    output logic [2:0]        m_axi_arprot,
    output logic [3:0]        m_axi_arqos,
    output logic [UW-1:0]     m_axi_aruser,
    output logic              m_axi_arvalid,
    input  logic              m_axi_arready,
    output logic [3:0]        m_axi_arnsaid,
    output logic              m_axi_artrace,
    output logic [10:0]       m_axi_armpam,
    output logic [15:0]       m_axi_armecid,
    output logic              m_axi_aridunq,
    output logic              m_axi_archunken,
    output logic [1:0]        m_axi_artagop,
    input  logic [IW-1:0]     m_axi_rid,
    input  logic [DW-1:0]     m_axi_rdata,
    input  logic [1:0]        m_axi_rresp,
    input  logic              m_axi_rlast,
    input  logic [UW-1:0]     m_axi_ruser,
    input  logic              m_axi_rvalid,
    output logic              m_axi_rready,
    input  logic              m_axi_rtrace,
    input  logic              m_axi_ridunq,
    input  logic              m_axi_rpoison,
    input  logic              m_axi_rchunkv,
    input  logic [3:0]        m_axi_rchunknum,
    input  logic [NUM_TAGS-1:0] m_axi_rchunkstrb,
    input  logic [TW-1:0]     m_axi_rtag
);

    localparam logic [31:0] SB_MASK  = (EN_NSAID ? SB_M_NSAID : '0) | (EN_TRACE ? SB_M_TRACE : '0)
                                     | (EN_MPAM  ? SB_M_MPAM  : '0) | (EN_MECID ? SB_M_MECID : '0);
    localparam logic [7:0]  RSB_MASK = EN_TRACE ? RSB_M_TRACE : '0;

    // =========================================================================
    // Read
    // =========================================================================
    generate if (EN_RD) begin : g_rd
        logic [IW-1:0]     f_arid;
        logic [31:0]       f_araddr;
        logic [7:0]        f_arlen;
        logic [2:0]        f_arsize;
        logic [1:0]        f_arburst;
        logic              f_arlock;
        logic [3:0]        f_arcache;
        logic [2:0]        f_arprot;
        logic [3:0]        f_arqos;
        logic [3:0]        f_arregion;
        logic [UW-1:0]     f_aruser;
        logic [31:0]       f_arsb;
        logic              f_arvalid, f_arready;
        logic [IW-1:0]     f_rid;
        logic [DW-1:0]     f_rdata;
        logic [1:0]        f_rresp;
        logic              f_rlast;
        logic [UW-1:0]     f_ruser;
        logic              f_rvalid, f_rready;
        logic              f_rtrace, f_rpoison;

        axi_stress_mst_rd #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(UW),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON)
        ) u_core (
            .aclk, .aresetn, .go, .stop,
            .cfg (cfg_rd), .cfg_win, .cfg_hash_seed, .sts (sts_rd),
            .fub_axi_arid      (f_arid),
            .fub_axi_araddr    (f_araddr),
            .fub_axi_arlen     (f_arlen),
            .fub_axi_arsize    (f_arsize),
            .fub_axi_arburst   (f_arburst),
            .fub_axi_arlock    (f_arlock),
            .fub_axi_arcache   (f_arcache),
            .fub_axi_arprot    (f_arprot),
            .fub_axi_arqos     (f_arqos),
            .fub_axi_arregion  (f_arregion),
            .fub_axi_aruser    (f_aruser),
            .fub_axi_arsb      (f_arsb),
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (f_rlast),
            .fub_axi_ruser     (f_ruser),
            .fub_axi_rsb       ({7'd0, f_rtrace}),
            .fub_axi_rpoison   (f_rpoison),
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready)
        );

        axi5_master_rd #(
            .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(32), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW),
            .ENABLE_NSAID(EN_NSAID), .ENABLE_TRACE(EN_TRACE), .ENABLE_MPAM(EN_MPAM),
            .ENABLE_MECID(EN_MECID), .ENABLE_UNIQUE(1'b0), .ENABLE_CHUNKING(1'b0),
            .ENABLE_MTE(1'b0), .ENABLE_POISON(EN_POISON), .ENABLE_WAKEUP(1'b0)
        ) u_chan (
            .aclk, .aresetn,
            .fub_axi_arid      (f_arid),
            .fub_axi_araddr    (f_araddr),
            .fub_axi_arlen     (f_arlen),
            .fub_axi_arsize    (f_arsize),
            .fub_axi_arburst   (f_arburst),
            .fub_axi_arlock    (f_arlock),
            .fub_axi_arcache   (f_arcache),
            .fub_axi_arprot    (f_arprot),
            .fub_axi_arqos     (f_arqos),
            .fub_axi_aruser    (f_aruser),
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_awakeup   (1'b0),
            .fub_axi_arready   (f_arready),
            .fub_axi_arnsaid   (f_arsb[3:0]),
            .fub_axi_artrace   (f_arsb[4]),
            .fub_axi_armpam    (f_arsb[15:5]),
            .fub_axi_armecid   (f_arsb[31:16]),
            .fub_axi_aridunq   (1'b0),
            .fub_axi_archunken (1'b0),
            .fub_axi_artagop   (2'b00),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (f_rlast),
            .fub_axi_ruser     (f_ruser),
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready),
            .fub_axi_rtrace    (f_rtrace),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_ridunq    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rpoison   (f_rpoison),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rchunkv   (),
            .fub_axi_rchunknum (),
            .fub_axi_rchunkstrb(),
            .fub_axi_rtag      (),
            /* verilator lint_on PINCONNECTEMPTY */
            .m_axi_arid        (m_axi_arid),
            .m_axi_araddr      (m_axi_araddr),
            .m_axi_arlen       (m_axi_arlen),
            .m_axi_arsize      (m_axi_arsize),
            .m_axi_arburst     (m_axi_arburst),
            .m_axi_arlock      (m_axi_arlock),
            .m_axi_arcache     (m_axi_arcache),
            .m_axi_arprot      (m_axi_arprot),
            .m_axi_arqos       (m_axi_arqos),
            .m_axi_aruser      (m_axi_aruser),
            .m_axi_arvalid     (m_axi_arvalid),
            /* verilator lint_off PINCONNECTEMPTY */
            .m_axi_awakeup     (),
            /* verilator lint_on PINCONNECTEMPTY */
            .m_axi_arready     (m_axi_arready),
            .m_axi_arnsaid     (m_axi_arnsaid),
            .m_axi_artrace     (m_axi_artrace),
            .m_axi_armpam      (m_axi_armpam),
            .m_axi_armecid     (m_axi_armecid),
            .m_axi_aridunq     (m_axi_aridunq),
            .m_axi_archunken   (m_axi_archunken),
            .m_axi_artagop     (m_axi_artagop),
            .m_axi_rid         (m_axi_rid),
            .m_axi_rdata       (m_axi_rdata),
            .m_axi_rresp       (m_axi_rresp),
            .m_axi_rlast       (m_axi_rlast),
            .m_axi_ruser       (m_axi_ruser),
            .m_axi_rvalid      (m_axi_rvalid),
            .m_axi_rready      (m_axi_rready),
            .m_axi_rtrace      (m_axi_rtrace),
            .m_axi_ridunq      (m_axi_ridunq),
            .m_axi_rpoison     (m_axi_rpoison),
            .m_axi_rchunkv     (m_axi_rchunkv),
            .m_axi_rchunknum   (m_axi_rchunknum),
            .m_axi_rchunkstrb  (m_axi_rchunkstrb),
            .m_axi_rtag        (m_axi_rtag),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        wire unused_rd = ^{f_arregion};
    end else begin : g_no_rd
        always_comb begin
            sts_rd      = '0;
            sts_rd.done = 1'b1;
        end
        assign m_axi_arid = '0;
        assign m_axi_araddr = '0;
        assign m_axi_arlen = '0;
        assign m_axi_arsize = '0;
        assign m_axi_arburst = '0;
        assign m_axi_arlock = '0;
        assign m_axi_arcache = '0;
        assign m_axi_arprot = '0;
        assign m_axi_arqos = '0;
        assign m_axi_aruser = '0;
        assign m_axi_arnsaid = '0;
        assign m_axi_artrace = '0;
        assign m_axi_armpam = '0;
        assign m_axi_armecid = '0;
        assign m_axi_aridunq = '0;
        assign m_axi_archunken = '0;
        assign m_axi_artagop = '0;
        assign m_axi_arvalid = 1'b0;
        assign m_axi_rready  = 1'b1;
    end endgenerate

    // =========================================================================
    // Write
    // =========================================================================
    generate if (EN_WR) begin : g_wr
        logic [IW-1:0]     f_awid;
        logic [31:0]       f_awaddr;
        logic [7:0]        f_awlen;
        logic [2:0]        f_awsize;
        logic [1:0]        f_awburst;
        logic              f_awlock;
        logic [3:0]        f_awcache;
        logic [2:0]        f_awprot;
        logic [3:0]        f_awqos;
        logic [3:0]        f_awregion;
        logic [UW-1:0]     f_awuser;
        logic [31:0]       f_awsb;
        logic              f_awvalid, f_awready;
        logic [DW-1:0]     f_wdata;
        logic [DW/8-1:0]   f_wstrb;
        logic [IW-1:0]     f_wid;
        logic              f_wlast, f_wpoison;
        logic [UW-1:0]     f_wuser;
        logic              f_wvalid, f_wready;
        logic [IW-1:0]     f_bid;
        logic [1:0]        f_bresp;
        logic [UW-1:0]     f_buser;
        logic              f_bvalid, f_bready, f_btrace;

        axi_stress_mst_wr #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(UW),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON)
        ) u_core (
            .aclk, .aresetn, .go, .stop,
            .cfg (cfg_wr), .cfg_win, .cfg_hash_seed, .sts (sts_wr),
            .fub_axi_awid      (f_awid),
            .fub_axi_awaddr    (f_awaddr),
            .fub_axi_awlen     (f_awlen),
            .fub_axi_awsize    (f_awsize),
            .fub_axi_awburst   (f_awburst),
            .fub_axi_awlock    (f_awlock),
            .fub_axi_awcache   (f_awcache),
            .fub_axi_awprot    (f_awprot),
            .fub_axi_awqos     (f_awqos),
            .fub_axi_awregion  (f_awregion),
            .fub_axi_awuser    (f_awuser),
            .fub_axi_awsb      (f_awsb),
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            .fub_axi_wid       (f_wid),
            .fub_axi_wlast     (f_wlast),
            .fub_axi_wuser     (f_wuser),
            .fub_axi_wpoison   (f_wpoison),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (f_buser),
            .fub_axi_bsb       ({7'd0, f_btrace}),
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready)
        );

        axi5_master_wr #(
            .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(32), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW),
            .ENABLE_ATOMIC(1'b0), .ENABLE_NSAID(EN_NSAID), .ENABLE_TRACE(EN_TRACE),
            .ENABLE_MPAM(EN_MPAM), .ENABLE_MECID(EN_MECID), .ENABLE_UNIQUE(1'b0),
            .ENABLE_MTE(1'b0), .ENABLE_POISON(EN_POISON), .ENABLE_WAKEUP(1'b0)
        ) u_chan (
            .aclk, .aresetn,
            .fub_axi_awid      (f_awid),
            .fub_axi_awaddr    (f_awaddr),
            .fub_axi_awlen     (f_awlen),
            .fub_axi_awsize    (f_awsize),
            .fub_axi_awburst   (f_awburst),
            .fub_axi_awlock    (f_awlock),
            .fub_axi_awcache   (f_awcache),
            .fub_axi_awprot    (f_awprot),
            .fub_axi_awqos     (f_awqos),
            .fub_axi_awuser    (f_awuser),
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awakeup   (1'b0),
            .fub_axi_awready   (f_awready),
            .fub_axi_awatop    (6'd0),
            .fub_axi_awnsaid   (f_awsb[3:0]),
            .fub_axi_awtrace   (f_awsb[4]),
            .fub_axi_awmpam    (f_awsb[15:5]),
            .fub_axi_awmecid   (f_awsb[31:16]),
            .fub_axi_awidunq   (1'b0),
            .fub_axi_awtagop   (2'b00),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            .fub_axi_wlast     (f_wlast),
            .fub_axi_wuser     (f_wuser),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_wpoison   (f_wpoison),
            .fub_axi_wtag      ('0),
            .fub_axi_wtagupdate('0),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (f_buser),
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready),
            .fub_axi_btrace    (f_btrace),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_bidunq    (),
            .fub_axi_btagmatch (),
            /* verilator lint_on PINCONNECTEMPTY */
            .m_axi_awid        (m_axi_awid),
            .m_axi_awaddr      (m_axi_awaddr),
            .m_axi_awlen       (m_axi_awlen),
            .m_axi_awsize      (m_axi_awsize),
            .m_axi_awburst     (m_axi_awburst),
            .m_axi_awlock      (m_axi_awlock),
            .m_axi_awcache     (m_axi_awcache),
            .m_axi_awprot      (m_axi_awprot),
            .m_axi_awqos       (m_axi_awqos),
            .m_axi_awuser      (m_axi_awuser),
            .m_axi_awvalid     (m_axi_awvalid),
            .m_axi_awakeup     (m_axi_awakeup),
            .m_axi_awready     (m_axi_awready),
            .m_axi_awatop      (m_axi_awatop),
            .m_axi_awnsaid     (m_axi_awnsaid),
            .m_axi_awtrace     (m_axi_awtrace),
            .m_axi_awmpam      (m_axi_awmpam),
            .m_axi_awmecid     (m_axi_awmecid),
            .m_axi_awidunq     (m_axi_awidunq),
            .m_axi_awtagop     (m_axi_awtagop),
            .m_axi_wdata       (m_axi_wdata),
            .m_axi_wstrb       (m_axi_wstrb),
            .m_axi_wlast       (m_axi_wlast),
            .m_axi_wuser       (m_axi_wuser),
            .m_axi_wvalid      (m_axi_wvalid),
            .m_axi_wready      (m_axi_wready),
            .m_axi_wpoison     (m_axi_wpoison),
            .m_axi_wtag        (m_axi_wtag),
            .m_axi_wtagupdate  (m_axi_wtagupdate),
            .m_axi_bid         (m_axi_bid),
            .m_axi_bresp       (m_axi_bresp),
            .m_axi_buser       (m_axi_buser),
            .m_axi_bvalid      (m_axi_bvalid),
            .m_axi_bready      (m_axi_bready),
            .m_axi_btrace      (m_axi_btrace),
            .m_axi_bidunq      (m_axi_bidunq),
            .m_axi_btagmatch   (m_axi_btagmatch),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        wire unused_wr = ^{f_awregion, f_wid};
    end else begin : g_no_wr
        always_comb begin
            sts_wr      = '0;
            sts_wr.done = 1'b1;
        end
        assign m_axi_awid = '0;
        assign m_axi_awaddr = '0;
        assign m_axi_awlen = '0;
        assign m_axi_awsize = '0;
        assign m_axi_awburst = '0;
        assign m_axi_awlock = '0;
        assign m_axi_awcache = '0;
        assign m_axi_awprot = '0;
        assign m_axi_awqos = '0;
        assign m_axi_awuser = '0;
        assign m_axi_awatop = '0;
        assign m_axi_awnsaid = '0;
        assign m_axi_awtrace = '0;
        assign m_axi_awmpam = '0;
        assign m_axi_awmecid = '0;
        assign m_axi_awidunq = '0;
        assign m_axi_awtagop = '0;
        assign m_axi_awakeup = '0;
        assign m_axi_wdata = '0;
        assign m_axi_wstrb = '0;
        assign m_axi_wlast = '0;
        assign m_axi_wuser = '0;
        assign m_axi_wpoison = '0;
        assign m_axi_wtag = '0;
        assign m_axi_wtagupdate = '0;
        assign m_axi_awvalid = 1'b0;
        assign m_axi_wvalid  = 1'b0;
        assign m_axi_bready  = 1'b1;
    end endgenerate

endmodule : axi5_master_stress
