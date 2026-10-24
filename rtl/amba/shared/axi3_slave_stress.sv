// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi3_slave_stress
// Purpose: AXI3 bus-stress slave: axi_stress_slv_rd / axi_stress_slv_wr on
//          the axi4_slave_rd / axi4_slave_wr channel modules, with AXI3 pins.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// The AXI3 shell of the stress slave. Same cores and status as
// axi4_slave_stress; what differs is the pin set:
//   AxLEN   4 bits, zero-extended to the cores.
//   AxLOCK  2 bits; bit 0 (exclusive) goes to the cores, which ignore it.
//   WID     rides through the W skid buffer in the user field (the write
//           channel module is built AXI_USER_WIDTH = UW + IW) and the write
//           core checks it (CHECK_WID): a beat whose WID is not the AWID of
//           the burst it belongs to is ERR_S_WID. This slave accepts W in AW
//           order only (write-interleave depth 1), so interleaved write data
//           from the fabric is caught here, as is a mis-stamped WID.
//   no AxQOS / AxREGION pins (the cores see 0).
// A port built for one direction (EN_RD / EN_WR = 0) elaborates no logic for
// the other; its READYs are tied low and it never answers.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi3_slave_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD   = 1'b1,
    parameter bit EN_WR   = 1'b1,
    parameter int DEPTH   = 16,
    parameter int IW      = 8,
    parameter int DW      = 64,
    parameter int UW      = 1,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 4,
    parameter int SKID_DEPTH_B  = 2
) (
    input  logic              aclk,
    input  logic              aresetn,

    input  logic              clear,
    input  stress_sdir_cfg_t cfg_rd,
    input  stress_sdir_cfg_t cfg_wr,
    input  logic [31:0]       cfg_hash_seed,
    output stress_sdir_sts_t sts_rd,
    output stress_sdir_sts_t sts_wr,

    input  logic [IW-1:0]     s_axi_awid,
    input  logic [31:0]       s_axi_awaddr,
    input  logic [3:0]        s_axi_awlen,
    input  logic [2:0]        s_axi_awsize,
    input  logic [1:0]        s_axi_awburst,
    input  logic [1:0]        s_axi_awlock,
    input  logic [3:0]        s_axi_awcache,
    input  logic [2:0]        s_axi_awprot,
    input  logic [UW-1:0]     s_axi_awuser,
    input  logic              s_axi_awvalid,
    output logic              s_axi_awready,
    input  logic [IW-1:0]     s_axi_wid,
    input  logic [DW-1:0]     s_axi_wdata,
    input  logic [DW/8-1:0]   s_axi_wstrb,
    input  logic              s_axi_wlast,
    input  logic [UW-1:0]     s_axi_wuser,
    input  logic              s_axi_wvalid,
    output logic              s_axi_wready,
    output logic [IW-1:0]     s_axi_bid,
    output logic [1:0]        s_axi_bresp,
    output logic [UW-1:0]     s_axi_buser,
    output logic              s_axi_bvalid,
    input  logic              s_axi_bready,
    input  logic [IW-1:0]     s_axi_arid,
    input  logic [31:0]       s_axi_araddr,
    input  logic [3:0]        s_axi_arlen,
    input  logic [2:0]        s_axi_arsize,
    input  logic [1:0]        s_axi_arburst,
    input  logic [1:0]        s_axi_arlock,
    input  logic [3:0]        s_axi_arcache,
    input  logic [2:0]        s_axi_arprot,
    input  logic [UW-1:0]     s_axi_aruser,
    input  logic              s_axi_arvalid,
    output logic              s_axi_arready,
    output logic [IW-1:0]     s_axi_rid,
    output logic [DW-1:0]     s_axi_rdata,
    output logic [1:0]        s_axi_rresp,
    output logic              s_axi_rlast,
    output logic [UW-1:0]     s_axi_ruser,
    output logic              s_axi_rvalid,
    input  logic              s_axi_rready
);

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
        logic              f_arvalid, f_arready;
        logic [IW-1:0]     f_rid;
        logic [DW-1:0]     f_rdata;
        logic [1:0]        f_rresp;
        logic              f_rlast;
        logic [UW-1:0]     f_ruser;
        logic              f_rvalid, f_rready;

        axi4_slave_rd #(
            .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(32), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW)
        ) u_chan (
            .aclk, .aresetn,
            .s_axi_arid      (s_axi_arid),
            .s_axi_araddr    (s_axi_araddr),
            .s_axi_arlen     ({4'd0, s_axi_arlen}),
            .s_axi_arsize    (s_axi_arsize),
            .s_axi_arburst   (s_axi_arburst),
            .s_axi_arlock    (s_axi_arlock[0]),
            .s_axi_arcache   (s_axi_arcache),
            .s_axi_arprot    (s_axi_arprot),
            .s_axi_arqos     (4'd0),
            .s_axi_arregion  (4'd0),
            .s_axi_aruser    (s_axi_aruser),
            .s_axi_arvalid   (s_axi_arvalid),
            .s_axi_arready   (s_axi_arready),
            .s_axi_rid       (s_axi_rid),
            .s_axi_rdata     (s_axi_rdata),
            .s_axi_rresp     (s_axi_rresp),
            .s_axi_rlast     (s_axi_rlast),
            .s_axi_ruser     (s_axi_ruser),
            .s_axi_rvalid    (s_axi_rvalid),
            .s_axi_rready    (s_axi_rready),
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
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (f_rlast),
            .fub_axi_ruser     (f_ruser),
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        axi_stress_slv_rd #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(UW)
        ) u_core (
            .aclk, .aresetn, .clear,
            .fub_axi_artagop   (2'b00),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rtag      (),
            /* verilator lint_on PINCONNECTEMPTY */
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
            .fub_axi_arregion  (f_arregion),
            .fub_axi_aruser    (f_aruser),
            .fub_axi_arsb      ('0),
            .fub_axi_aridunq   (1'b0),
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (f_rlast),
            .fub_axi_ruser     (f_ruser),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rsb       (),
            .fub_axi_rpoison   (),
            .fub_axi_ridunq    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready)
        );
        wire unused_rd = s_axi_arlock[1];
    end else begin : g_no_rd
        assign sts_rd        = '0;
        assign s_axi_arready = 1'b0;
        assign s_axi_rvalid  = 1'b0;
        assign s_axi_rid = '0;
        assign s_axi_rdata = '0;
        assign s_axi_rresp = '0;
        assign s_axi_rlast = '0;
        assign s_axi_ruser = '0;
    end endgenerate

    // =========================================================================
    // Write
    // =========================================================================
    generate if (EN_WR) begin : g_wr
        localparam int CUW = UW + IW;   // channel user width: {WID, user} on W

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
        logic [CUW-1:0]    f_awuser, f_wuser;
        logic              f_awvalid, f_awready;
        logic [DW-1:0]     f_wdata;
        logic [DW/8-1:0]   f_wstrb;
        logic              f_wlast;
        logic              f_wvalid, f_wready;
        logic [IW-1:0]     f_bid;
        logic [1:0]        f_bresp;
        logic [UW-1:0]     f_buser;
        logic              f_bvalid, f_bready;
        logic [CUW-1:0]    c_buser;

        // W_FIRST (cfg w_first): take an AW only once write data is in sight -- a W
        // beat offered, or a W burst already taken ahead (axi_stress_w_first_gate), as a
        // slave that waits for write data first does (AXI A3.3.1 allows it)
        logic w_aw_gate, w_ch_awready;
        axi_stress_w_first_gate u_w_first (
            .aclk, .aresetn, .clear,
            .en         (cfg_wr.w_first),
            .awvalid    (s_axi_awvalid),
            .ch_awready (w_ch_awready),
            .wvalid     (s_axi_wvalid),
            .wready     (s_axi_wready),
            .wlast      (s_axi_wlast),
            .aw_gate    (w_aw_gate),
            .awready    (s_axi_awready)
        );

        axi4_slave_wr #(
            .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B),
            .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(32), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(CUW)
        ) u_chan (
            .aclk, .aresetn,
            .s_axi_awid      (s_axi_awid),
            .s_axi_awaddr    (s_axi_awaddr),
            .s_axi_awlen     ({4'd0, s_axi_awlen}),
            .s_axi_awsize    (s_axi_awsize),
            .s_axi_awburst   (s_axi_awburst),
            .s_axi_awlock    (s_axi_awlock[0]),
            .s_axi_awcache   (s_axi_awcache),
            .s_axi_awprot    (s_axi_awprot),
            .s_axi_awqos     (4'd0),
            .s_axi_awregion  (4'd0),
            .s_axi_awuser    ({IW'(0), s_axi_awuser}),
            .s_axi_awvalid   (s_axi_awvalid && w_aw_gate),
            .s_axi_awready   (w_ch_awready),
            .s_axi_wdata     (s_axi_wdata),
            .s_axi_wstrb     (s_axi_wstrb),
            .s_axi_wlast     (s_axi_wlast),
            .s_axi_wuser     ({s_axi_wid, s_axi_wuser}),
            .s_axi_wvalid    (s_axi_wvalid),
            .s_axi_wready    (s_axi_wready),
            .s_axi_bid       (s_axi_bid),
            .s_axi_bresp     (s_axi_bresp),
            .s_axi_buser     (c_buser),
            .s_axi_bvalid    (s_axi_bvalid),
            .s_axi_bready    (s_axi_bready),
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
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            .fub_axi_wlast     (f_wlast),
            .fub_axi_wuser     (f_wuser),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     ({IW'(0), f_buser}),
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        axi_stress_slv_wr #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(UW), .CHECK_WID(1'b1)
        ) u_core (
            .aclk, .aresetn, .clear,
            .fub_axi_awtagop   (2'b00),
            .fub_axi_wtag      ('0),
            .fub_axi_wtagupdate('0),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_btagmatch (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awatop    (6'd0),
            .fub_axi_atr_ready (1'b1),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_atr_valid (),
            .fub_axi_atr_id    (),
            .fub_axi_atr_data  (),
            .fub_axi_atr_resp  (),
            .fub_axi_atr_rsb   (),
            .fub_axi_atr_poison(),
            .fub_axi_atr_ridunq(),
            /* verilator lint_on PINCONNECTEMPTY */
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
            .fub_axi_awregion  (f_awregion),
            .fub_axi_awuser    (f_awuser[UW-1:0]),
            .fub_axi_awsb      ('0),
            .fub_axi_awidunq   (1'b0),
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            .fub_axi_wid       (f_wuser[CUW-1:UW]),
            .fub_axi_wlast     (f_wlast),
            .fub_axi_wuser     (f_wuser[UW-1:0]),
            .fub_axi_wpoison   (1'b0),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (f_buser),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_bsb       (),
            .fub_axi_bidunq    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready)
        );

        assign s_axi_buser = c_buser[UW-1:0];
        wire unused_wr = ^{s_axi_awlock[1], f_awuser[CUW-1:UW], c_buser[CUW-1:UW]};
    end else begin : g_no_wr
        assign sts_wr        = '0;
        assign s_axi_awready = 1'b0;
        assign s_axi_wready  = 1'b0;
        assign s_axi_bvalid  = 1'b0;
        assign s_axi_bid = '0;
        assign s_axi_bresp = '0;
        assign s_axi_buser = '0;
    end endgenerate

endmodule : axi3_slave_stress
