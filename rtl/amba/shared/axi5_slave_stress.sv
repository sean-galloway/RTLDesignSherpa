// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_stress
// Purpose: AXI5 bus-stress slave: axi_stress_slv_rd / axi_stress_slv_wr behind
//          the axi5_slave_rd / axi5_slave_wr channel modules.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// The AXI5 shell of the stress slave. Same cores and status as
// axi4_slave_stress, plus the AXI5 fields this build carries:
//   AxNSAID, AxTRACE, AxMPAM, AxMECID   (EN_NSAID / EN_TRACE / EN_MPAM /
//            EN_MECID) packed at the axi_stress_pkg SB_M_* positions and
//            checked against f_sb(fabric address) for a request from a master
//            in cfg.sb_src (identified by the fabric's master-index ID field,
//            ID[SRC_LSB +: SRC_W]), against 0 for any other (ERR_S_SB).
//   BTRACE, RTRACE   (EN_TRACE) echo the burst's AWTRACE / ARTRACE.
//   WPOISON  (EN_POISON) checked against f_poison(beat address,
//            cfg.poison_lg2); RPOISON driven with the same function.
//   AxIDUNQ  (EN_UNIQUE) checked against the IDUNQ rule at this slave
//            (ERR_S_SB); BIDUNQ / RIDUNQ echo it.
//   AWATOP   (EN_ATOMIC) checked against the shapes the stress master issues
//            (ERR_S_PROTO); a read-return class answers with one R beat,
//            merged onto R between read bursts (axi_stress_r_merge).
// AxTAGOP, WTAG, ARCHUNKEN and AWAKEUP are ignored; BTAGMATCH, RCHUNK* and
// RTAG are driven 0. Every AXI5 pin is on the
// port whatever the build; a pin of a disabled feature is tied off by the
// channel module.
// A port built for one direction (EN_RD / EN_WR = 0) elaborates no logic for
// the other; it never accepts a request on it and its status reads zero.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi5_slave_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD     = 1'b1,
    parameter bit EN_WR     = 1'b1,
    parameter bit EN_NSAID  = 1'b0,
    parameter bit EN_TRACE  = 1'b0,
    parameter bit EN_MPAM   = 1'b0,
    parameter bit EN_MECID  = 1'b0,
    parameter bit EN_POISON = 1'b0,
    parameter bit EN_UNIQUE = 1'b0,
    parameter bit EN_ATOMIC = 1'b0,      // needs EN_RD and EN_WR
    parameter int SRC_LSB   = 0,     // master-index field of the ID
    parameter int SRC_W     = 0,     //   (0: one master)
    parameter int DEPTH   = 16,
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

    input  logic              clear,
    input  stress_sdir_cfg_t  cfg_rd,
    input  stress_sdir_cfg_t  cfg_wr,
    input  logic [31:0]       cfg_hash_seed,
    output stress_sdir_sts_t  sts_rd,
    output stress_sdir_sts_t  sts_wr,

    input  logic [IW-1:0]     s_axi_awid,
    input  logic [31:0]       s_axi_awaddr,
    input  logic [7:0]        s_axi_awlen,
    input  logic [2:0]        s_axi_awsize,
    input  logic [1:0]        s_axi_awburst,
    input  logic              s_axi_awlock,
    input  logic [3:0]        s_axi_awcache,
    input  logic [2:0]        s_axi_awprot,
    input  logic [3:0]        s_axi_awqos,
    input  logic [UW-1:0]     s_axi_awuser,
    input  logic              s_axi_awvalid,
    output logic              s_axi_awready,
    input  logic [5:0]        s_axi_awatop,
    input  logic [3:0]        s_axi_awnsaid,
    input  logic              s_axi_awtrace,
    input  logic [10:0]       s_axi_awmpam,
    input  logic [15:0]       s_axi_awmecid,
    input  logic              s_axi_awidunq,
    input  logic [1:0]        s_axi_awtagop,
    input  logic              s_axi_awakeup,
    input  logic [DW-1:0]     s_axi_wdata,
    input  logic [DW/8-1:0]   s_axi_wstrb,
    input  logic              s_axi_wlast,
    input  logic [UW-1:0]     s_axi_wuser,
    input  logic              s_axi_wvalid,
    output logic              s_axi_wready,
    input  logic              s_axi_wpoison,
    input  logic [TW-1:0]     s_axi_wtag,
    input  logic [NUM_TAGS-1:0] s_axi_wtagupdate,
    output logic [IW-1:0]     s_axi_bid,
    output logic [1:0]        s_axi_bresp,
    output logic [UW-1:0]     s_axi_buser,
    output logic              s_axi_bvalid,
    input  logic              s_axi_bready,
    output logic              s_axi_btrace,
    output logic              s_axi_bidunq,
    output logic [1:0]        s_axi_btagmatch,
    input  logic [IW-1:0]     s_axi_arid,
    input  logic [31:0]       s_axi_araddr,
    input  logic [7:0]        s_axi_arlen,
    input  logic [2:0]        s_axi_arsize,
    input  logic [1:0]        s_axi_arburst,
    input  logic              s_axi_arlock,
    input  logic [3:0]        s_axi_arcache,
    input  logic [2:0]        s_axi_arprot,
    input  logic [3:0]        s_axi_arqos,
    input  logic [UW-1:0]     s_axi_aruser,
    input  logic              s_axi_arvalid,
    output logic              s_axi_arready,
    input  logic [3:0]        s_axi_arnsaid,
    input  logic              s_axi_artrace,
    input  logic [10:0]       s_axi_armpam,
    input  logic [15:0]       s_axi_armecid,
    input  logic              s_axi_aridunq,
    input  logic              s_axi_archunken,
    input  logic [1:0]        s_axi_artagop,
    output logic [IW-1:0]     s_axi_rid,
    output logic [DW-1:0]     s_axi_rdata,
    output logic [1:0]        s_axi_rresp,
    output logic              s_axi_rlast,
    output logic [UW-1:0]     s_axi_ruser,
    output logic              s_axi_rvalid,
    input  logic              s_axi_rready,
    output logic              s_axi_rtrace,
    output logic              s_axi_ridunq,
    output logic              s_axi_rpoison,
    output logic              s_axi_rchunkv,
    output logic [3:0]        s_axi_rchunknum,
    output logic [NUM_TAGS-1:0] s_axi_rchunkstrb,
    output logic [TW-1:0]     s_axi_rtag
);

    localparam logic [31:0] SB_MASK  = (EN_NSAID ? SB_M_NSAID : '0) | (EN_TRACE ? SB_M_TRACE : '0)
                                     | (EN_MPAM  ? SB_M_MPAM  : '0) | (EN_MECID ? SB_M_MECID : '0);
    localparam logic [7:0]  RSB_MASK = EN_TRACE ? RSB_M_TRACE : '0;

    wire unused_wakeup = s_axi_awakeup;   // AWAKEUP is not modelled

    // AXI5 read-return atomics: the write core's R beats, to the read side
    logic          atr_valid, atr_ready, atr_poison, atr_ridunq;
    logic [IW-1:0] atr_id;
    logic [DW-1:0] atr_data;
    logic [1:0]    atr_resp;
    logic [7:0]    atr_rsb;

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
        logic [UW-1:0]     f_aruser;
        logic              f_arvalid, f_arready;
        logic [3:0]        f_arnsaid;
        logic              f_artrace;
        logic [10:0]       f_armpam;
        logic [15:0]       f_armecid;
        logic [IW-1:0]     f_rid;
        logic [DW-1:0]     f_rdata;
        logic [1:0]        f_rresp;
        logic              f_rlast;
        logic [UW-1:0]     f_ruser;
        logic              f_rvalid, f_rready;
        logic [7:0]        f_rsb_w;
        logic              f_rpoison, f_aridunq, f_ridunq;
        // the read core's R, before the atomic merge
        logic [IW-1:0]     a_rid;
        logic [DW-1:0]     a_rdata;
        logic [1:0]        a_rresp;
        logic              a_rlast, a_rvalid, a_rready, a_rpoison, a_ridunq;
        logic [7:0]        a_rsb;

        axi5_slave_rd #(
            .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(32), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW),
            .ENABLE_NSAID(EN_NSAID), .ENABLE_TRACE(EN_TRACE), .ENABLE_MPAM(EN_MPAM),
            .ENABLE_MECID(EN_MECID), .ENABLE_UNIQUE(EN_UNIQUE), .ENABLE_CHUNKING(1'b0),
            .ENABLE_MTE(1'b0), .ENABLE_POISON(EN_POISON), .ENABLE_WAKEUP(1'b0)
        ) u_chan (
            .aclk, .aresetn,
            .s_axi_arid        (s_axi_arid),
            .s_axi_araddr      (s_axi_araddr),
            .s_axi_arlen       (s_axi_arlen),
            .s_axi_arsize      (s_axi_arsize),
            .s_axi_arburst     (s_axi_arburst),
            .s_axi_arlock      (s_axi_arlock),
            .s_axi_arcache     (s_axi_arcache),
            .s_axi_arprot      (s_axi_arprot),
            .s_axi_arqos       (s_axi_arqos),
            .s_axi_aruser      (s_axi_aruser),
            .s_axi_arvalid     (s_axi_arvalid),
            .s_axi_awakeup     (1'b0),
            .s_axi_arready     (s_axi_arready),
            .s_axi_arnsaid     (s_axi_arnsaid),
            .s_axi_artrace     (s_axi_artrace),
            .s_axi_armpam      (s_axi_armpam),
            .s_axi_armecid     (s_axi_armecid),
            .s_axi_aridunq     (s_axi_aridunq),
            .s_axi_archunken   (s_axi_archunken),
            .s_axi_artagop     (s_axi_artagop),
            .s_axi_rid         (s_axi_rid),
            .s_axi_rdata       (s_axi_rdata),
            .s_axi_rresp       (s_axi_rresp),
            .s_axi_rlast       (s_axi_rlast),
            .s_axi_ruser       (s_axi_ruser),
            .s_axi_rvalid      (s_axi_rvalid),
            .s_axi_rready      (s_axi_rready),
            .s_axi_rtrace      (s_axi_rtrace),
            .s_axi_ridunq      (s_axi_ridunq),
            .s_axi_rpoison     (s_axi_rpoison),
            .s_axi_rchunkv     (s_axi_rchunkv),
            .s_axi_rchunknum   (s_axi_rchunknum),
            .s_axi_rchunkstrb  (s_axi_rchunkstrb),
            .s_axi_rtag        (s_axi_rtag),
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
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awakeup   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_arready   (f_arready),
            .fub_axi_arnsaid   (f_arnsaid),
            .fub_axi_artrace   (f_artrace),
            .fub_axi_armpam    (f_armpam),
            .fub_axi_armecid   (f_armecid),
            .fub_axi_aridunq   (f_aridunq),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_archunken (),
            .fub_axi_artagop   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (f_rlast),
            .fub_axi_ruser     (f_ruser),
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready),
            .fub_axi_rtrace    (f_rsb_w[0]),
            .fub_axi_ridunq    (f_ridunq),
            .fub_axi_rpoison   (f_rpoison),
            .fub_axi_rchunkv   (1'b0),
            .fub_axi_rchunknum (4'd0),
            .fub_axi_rchunkstrb('0),
            .fub_axi_rtag      ('0),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        axi_stress_slv_rd #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(UW),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON), .UNIQUE(EN_UNIQUE),
            .SRC_LSB(SRC_LSB), .SRC_W(SRC_W)
        ) u_core (
            .aclk, .aresetn, .clear,
            .cfg (cfg_rd), .cfg_hash_seed, .sts (sts_rd),
            .fub_axi_arid      (f_arid),
            .fub_axi_araddr    (f_araddr),
            .fub_axi_arlen     (f_arlen),
            .fub_axi_arsize    (f_arsize),
            .fub_axi_arburst   (f_arburst),
            .fub_axi_arlock    (f_arlock),
            .fub_axi_arcache   (f_arcache),
            .fub_axi_arprot    (f_arprot),
            .fub_axi_arqos     (f_arqos),
            .fub_axi_arregion  (4'd0),
            .fub_axi_aruser    (f_aruser),
            .fub_axi_arsb      ({f_armecid, f_armpam, f_artrace, f_arnsaid}),
            .fub_axi_aridunq   (f_aridunq),
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            .fub_axi_rid       (a_rid),
            .fub_axi_rdata     (a_rdata),
            .fub_axi_rresp     (a_rresp),
            .fub_axi_rlast     (a_rlast),
            .fub_axi_ruser     (f_ruser),
            .fub_axi_rsb       (a_rsb),
            .fub_axi_rpoison   (a_rpoison),
            .fub_axi_ridunq    (a_ridunq),
            .fub_axi_rvalid    (a_rvalid),
            .fub_axi_rready    (a_rready)
        );

        if (EN_ATOMIC) begin : g_merge
            logic [2:0] m_x;
            axi_stress_r_merge #(.IW(IW), .DW(DW), .XW(3)) u_merge (
                .aclk, .aresetn,
                .a_valid (a_rvalid), .a_ready (a_rready), .a_id (a_rid), .a_data (a_rdata),
                .a_resp  (a_rresp),  .a_last  (a_rlast),
                .a_x     ({a_rsb[0], a_rpoison, a_ridunq}),
                .b_valid (atr_valid), .b_ready (atr_ready), .b_id (atr_id), .b_data (atr_data),
                .b_resp  (atr_resp),
                .b_x     ({atr_rsb[0], atr_poison, atr_ridunq}),
                .m_valid (f_rvalid), .m_ready (f_rready), .m_id (f_rid), .m_data (f_rdata),
                .m_resp  (f_rresp),  .m_last  (f_rlast),  .m_x  (m_x)
            );
            assign f_rsb_w   = {7'd0, m_x[2]};
            assign f_rpoison = m_x[1];
            assign f_ridunq  = m_x[0];
        end else begin : g_no_merge
            assign f_rid     = a_rid;
            assign f_rdata   = a_rdata;
            assign f_rresp   = a_rresp;
            assign f_rlast   = a_rlast;
            assign f_rvalid  = a_rvalid;
            assign a_rready  = f_rready;
            assign f_rsb_w   = a_rsb;
            assign f_rpoison = a_rpoison;
            assign f_ridunq  = a_ridunq;
            assign atr_ready = 1'b1;
        end

        wire unused_rd = ^{f_rsb_w[7:1], a_rsb[7:1], atr_rsb[7:1]};
    end else begin : g_no_rd
        assign atr_ready     = 1'b1;
        assign sts_rd        = '0;
        assign s_axi_arready = 1'b0;
        assign s_axi_rvalid  = 1'b0;
        assign s_axi_rid = '0;
        assign s_axi_rdata = '0;
        assign s_axi_rresp = '0;
        assign s_axi_rlast = '0;
        assign s_axi_ruser = '0;
        assign s_axi_rtrace = '0;
        assign s_axi_ridunq = '0;
        assign s_axi_rpoison = '0;
        assign s_axi_rchunkv = '0;
        assign s_axi_rchunknum = '0;
        assign s_axi_rchunkstrb = '0;
        assign s_axi_rtag = '0;
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
        logic [UW-1:0]     f_awuser;
        logic              f_awvalid, f_awready;
        logic [3:0]        f_awnsaid;
        logic              f_awtrace;
        logic [10:0]       f_awmpam;
        logic [15:0]       f_awmecid;
        logic [DW-1:0]     f_wdata;
        logic [DW/8-1:0]   f_wstrb;
        logic              f_wlast, f_wpoison;
        logic [UW-1:0]     f_wuser;
        logic              f_wvalid, f_wready;
        logic [IW-1:0]     f_bid;
        logic [1:0]        f_bresp;
        logic [UW-1:0]     f_buser;
        logic              f_bvalid, f_bready;
        logic [7:0]        f_bsb;
        logic              f_awidunq, f_bidunq;
        logic [5:0]        f_awatop;

        axi5_slave_wr #(
            .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(32), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW),
            .ENABLE_ATOMIC(EN_ATOMIC), .ENABLE_NSAID(EN_NSAID), .ENABLE_TRACE(EN_TRACE),
            .ENABLE_MPAM(EN_MPAM), .ENABLE_MECID(EN_MECID), .ENABLE_UNIQUE(EN_UNIQUE),
            .ENABLE_MTE(1'b0), .ENABLE_POISON(EN_POISON), .ENABLE_WAKEUP(1'b0)
        ) u_chan (
            .aclk, .aresetn,
            .s_axi_awid        (s_axi_awid),
            .s_axi_awaddr      (s_axi_awaddr),
            .s_axi_awlen       (s_axi_awlen),
            .s_axi_awsize      (s_axi_awsize),
            .s_axi_awburst     (s_axi_awburst),
            .s_axi_awlock      (s_axi_awlock),
            .s_axi_awcache     (s_axi_awcache),
            .s_axi_awprot      (s_axi_awprot),
            .s_axi_awqos       (s_axi_awqos),
            .s_axi_awuser      (s_axi_awuser),
            .s_axi_awvalid     (s_axi_awvalid),
            .s_axi_awakeup     (1'b0),
            .s_axi_awready     (s_axi_awready),
            .s_axi_awatop      (s_axi_awatop),
            .s_axi_awnsaid     (s_axi_awnsaid),
            .s_axi_awtrace     (s_axi_awtrace),
            .s_axi_awmpam      (s_axi_awmpam),
            .s_axi_awmecid     (s_axi_awmecid),
            .s_axi_awidunq     (s_axi_awidunq),
            .s_axi_awtagop     (s_axi_awtagop),
            .s_axi_wdata       (s_axi_wdata),
            .s_axi_wstrb       (s_axi_wstrb),
            .s_axi_wlast       (s_axi_wlast),
            .s_axi_wuser       (s_axi_wuser),
            .s_axi_wvalid      (s_axi_wvalid),
            .s_axi_wready      (s_axi_wready),
            .s_axi_wpoison     (s_axi_wpoison),
            .s_axi_wtag        (s_axi_wtag),
            .s_axi_wtagupdate  (s_axi_wtagupdate),
            .s_axi_bid         (s_axi_bid),
            .s_axi_bresp       (s_axi_bresp),
            .s_axi_buser       (s_axi_buser),
            .s_axi_bvalid      (s_axi_bvalid),
            .s_axi_bready      (s_axi_bready),
            .s_axi_btrace      (s_axi_btrace),
            .s_axi_bidunq      (s_axi_bidunq),
            .s_axi_btagmatch   (s_axi_btagmatch),
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
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awakeup   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awready   (f_awready),
            .fub_axi_awatop    (f_awatop),
            .fub_axi_awnsaid   (f_awnsaid),
            .fub_axi_awtrace   (f_awtrace),
            .fub_axi_awmpam    (f_awmpam),
            .fub_axi_awmecid   (f_awmecid),
            .fub_axi_awidunq   (f_awidunq),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awtagop   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            .fub_axi_wlast     (f_wlast),
            .fub_axi_wuser     (f_wuser),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_wpoison   (f_wpoison),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_wtag      (),
            .fub_axi_wtagupdate(),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (f_buser),
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready),
            .fub_axi_btrace    (f_bsb[0]),
            .fub_axi_bidunq    (f_bidunq),
            .fub_axi_btagmatch (2'b00),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        axi_stress_slv_wr #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(UW),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON), .UNIQUE(EN_UNIQUE),
            .ATOMIC(EN_ATOMIC), .SRC_LSB(SRC_LSB), .SRC_W(SRC_W)
        ) u_core (
            .aclk, .aresetn, .clear,
            .cfg (cfg_wr), .cfg_hash_seed, .sts (sts_wr),
            .fub_axi_awid      (f_awid),
            .fub_axi_awaddr    (f_awaddr),
            .fub_axi_awlen     (f_awlen),
            .fub_axi_awsize    (f_awsize),
            .fub_axi_awburst   (f_awburst),
            .fub_axi_awlock    (f_awlock),
            .fub_axi_awcache   (f_awcache),
            .fub_axi_awprot    (f_awprot),
            .fub_axi_awqos     (f_awqos),
            .fub_axi_awregion  (4'd0),
            .fub_axi_awuser    (f_awuser),
            .fub_axi_awsb      ({f_awmecid, f_awmpam, f_awtrace, f_awnsaid}),
            .fub_axi_awidunq   (f_awidunq),
            .fub_axi_awatop    (f_awatop),
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            .fub_axi_wid       (IW'(0)),
            .fub_axi_wlast     (f_wlast),
            .fub_axi_wuser     (f_wuser),
            .fub_axi_wpoison   (f_wpoison),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (f_buser),
            .fub_axi_bsb       (f_bsb),
            .fub_axi_bidunq    (f_bidunq),
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready),
            .fub_axi_atr_valid (atr_valid),
            .fub_axi_atr_ready (atr_ready),
            .fub_axi_atr_id    (atr_id),
            .fub_axi_atr_data  (atr_data),
            .fub_axi_atr_resp  (atr_resp),
            .fub_axi_atr_rsb   (atr_rsb),
            .fub_axi_atr_poison(atr_poison),
            .fub_axi_atr_ridunq(atr_ridunq)
        );

        wire unused_wr = ^{f_bsb[7:1]};
    end else begin : g_no_wr
        assign atr_valid     = 1'b0;
        assign atr_id        = '0;
        assign atr_data      = '0;
        assign atr_resp      = '0;
        assign atr_rsb       = '0;
        assign atr_poison    = 1'b0;
        assign atr_ridunq    = 1'b0;
        assign sts_wr        = '0;
        assign s_axi_awready = 1'b0;
        assign s_axi_wready  = 1'b0;
        assign s_axi_bvalid  = 1'b0;
        assign s_axi_bid = '0;
        assign s_axi_bresp = '0;
        assign s_axi_buser = '0;
        assign s_axi_btrace = '0;
        assign s_axi_bidunq = '0;
        assign s_axi_btagmatch = '0;
    end endgenerate

endmodule : axi5_slave_stress
