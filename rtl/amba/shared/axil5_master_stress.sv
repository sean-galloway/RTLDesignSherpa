// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_master_stress
// Purpose: AXI5-Lite bus-stress master: axi_stress_mst_rd / axi_stress_mst_wr
//          on the axil5_master_rd / axil5_master_wr channel modules.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-23
//==============================================================================
// The AXI5-Lite shell of the stress master. AXI5-Lite is AXI4-Lite plus the
// transaction ID and the optional USER / TRACE / POISON groups (IHI 0022L
// B2.1.5, Table B2.2):
//
//   bursts  as axil4_master_stress: the cores are built LEN_MASK = 8'h00 and
//           SIZE_FIXED, so every transfer is one aligned, bus-wide beat.
//   IDs     the cores' IDs go on the bus (AWID / ARID, IW bits) and come back
//           on BID / RID. AXI5-Lite permits responses with different IDs to
//           return in any order (B2.1.5), so there is no ID FIFO: the cores
//           score per ID exactly as on AXI4, and a stray or mis-stamped ID is
//           RD_STRAY / WR_STRAY.
//   TRACE   (EN_TRACE) AxTRACE is the TRACE bit of f_sb(start address);
//           BTRACE / RTRACE are checked as on AXI5 (echo of the request's
//           TRACE on a window with sb set, else 0).
//   POISON  (EN_POISON) WPOISON driven and RPOISON checked, f_poison(beat
//           address). One bit per 64 data bits, so with DW 32 or 64 it is the
//           cores' one bit per beat; DW is held to those two widths.
//   USER    not driven (USER groups disabled): no stress check covers it.
//
// A port built for one direction (EN_RD / EN_WR = 0) elaborates no logic for
// the other; its outputs are tied idle and its status reads done, no errors.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil5_master_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD     = 1'b1,
    parameter bit EN_WR     = 1'b1,
    parameter bit EN_TRACE  = 1'b0,
    parameter bit EN_POISON = 1'b0,
    parameter int DEPTH   = 16,
    parameter int NWIN    = 8,
    parameter int IW      = 8,          // AWID / ARID on the bus
    parameter int DW      = 32,         // 32 or 64
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 4,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 4,
    parameter int SKID_DEPTH_B  = 2
) (
    input  logic              aclk,
    input  logic              aresetn,

    input  logic              go,
    input  logic              stop,
    input  stress_mdir_cfg_t cfg_rd,
    input  stress_mdir_cfg_t cfg_wr,
    input  stress_win_t      cfg_win [NWIN],
    input  logic [31:0]       cfg_hash_seed,
    output stress_mdir_sts_t sts_rd,
    output stress_mdir_sts_t sts_wr,

    output logic [IW-1:0]     m_axil_awid,
    output logic [31:0]       m_axil_awaddr,
    output logic [2:0]        m_axil_awprot,
    output logic              m_axil_awtrace,
    output logic              m_axil_awvalid,
    input  logic              m_axil_awready,
    output logic [DW-1:0]     m_axil_wdata,
    output logic [DW/8-1:0]   m_axil_wstrb,
    output logic              m_axil_wpoison,
    output logic              m_axil_wvalid,
    input  logic              m_axil_wready,
    input  logic [IW-1:0]     m_axil_bid,
    input  logic [1:0]        m_axil_bresp,
    input  logic              m_axil_btrace,
    input  logic              m_axil_bvalid,
    output logic              m_axil_bready,
    output logic [IW-1:0]     m_axil_arid,
    output logic [31:0]       m_axil_araddr,
    output logic [2:0]        m_axil_arprot,
    output logic              m_axil_artrace,
    output logic              m_axil_arvalid,
    input  logic              m_axil_arready,
    input  logic [IW-1:0]     m_axil_rid,
    input  logic [DW-1:0]     m_axil_rdata,
    input  logic [1:0]        m_axil_rresp,
    input  logic              m_axil_rtrace,
    input  logic              m_axil_rpoison,
    input  logic              m_axil_rvalid,
    output logic              m_axil_rready
);

    localparam logic [7:0]  L_LEN_MASK = 8'h00;    // one beat per transfer
    localparam logic [31:0] SB_MASK    = EN_TRACE ? SB_M_TRACE : '0;
    localparam logic [7:0]  RSB_MASK   = EN_TRACE ? RSB_M_TRACE : '0;

`ifndef SYNTHESIS
    initial begin : param_check
        if (DW != 32 && DW != 64)
            $fatal(1, "axil5_master_stress: DW %0d; 32 or 64 (one POISON bit per beat)", DW);
    end
`endif

    // =========================================================================
    // Read
    // =========================================================================
    generate if (EN_RD) begin : g_rd
        logic [IW-1:0]     f_arid;
        logic [31:0]       f_araddr;
        logic [2:0]        f_arprot;
        logic [31:0]       f_arsb;
        logic              f_arvalid, f_arready;
        logic [IW-1:0]     f_rid;
        logic [DW-1:0]     f_rdata;
        logic [1:0]        f_rresp;
        logic              f_rtrace, f_rpoison;
        logic              f_rvalid, f_rready;

        axi_stress_mst_rd #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1),
            .LEN_MASK(L_LEN_MASK), .SIZE_FIXED(1'b1),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON)
        ) u_core (
            .aclk, .aresetn, .go, .stop,
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_artagop   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rtag      ('0),
            .cfg (cfg_rd), .cfg_win, .cfg_hash_seed, .sts (sts_rd),
            .fub_axi_arid      (f_arid),
            .fub_axi_araddr    (f_araddr),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_arlen     (),
            .fub_axi_arsize    (),
            .fub_axi_arburst   (),
            .fub_axi_arlock    (),
            .fub_axi_arcache   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_arprot    (f_arprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_arqos     (),
            .fub_axi_arregion  (),
            .fub_axi_aruser    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_arsb      (f_arsb),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_aridunq   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (1'b1),
            .fub_axi_ruser     (1'b0),
            .fub_axi_rsb       ({7'd0, f_rtrace}),
            .fub_axi_rpoison   (f_rpoison),
            .fub_axi_ridunq    (1'b0),
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready)
        );

        axil5_master_rd #(
            .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(DW), .ID_WIDTH(IW),
            .USER_WIDTH(1), .ENABLE_USER(1'b0),
            .ENABLE_TRACE(EN_TRACE), .ENABLE_POISON(EN_POISON),
            .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R)
        ) u_chan (
            .aclk, .aresetn,
            .fub_arid        (f_arid),
            .fub_araddr      (f_araddr),
            .fub_arprot      (f_arprot),
            .fub_aruser      (1'b0),
            .fub_artrace     (f_arsb[4]),
            .fub_arvalid     (f_arvalid),
            .fub_arready     (f_arready),
            .fub_rid         (f_rid),
            .fub_rdata       (f_rdata),
            .fub_rresp       (f_rresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_ruser       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_rtrace      (f_rtrace),
            .fub_rpoison     (f_rpoison),
            .fub_rvalid      (f_rvalid),
            .fub_rready      (f_rready),
            .m_axil_arid     (m_axil_arid),
            .m_axil_araddr   (m_axil_araddr),
            .m_axil_arprot   (m_axil_arprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .m_axil_aruser   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .m_axil_artrace  (m_axil_artrace),
            .m_axil_arvalid  (m_axil_arvalid),
            .m_axil_arready  (m_axil_arready),
            .m_axil_rid      (m_axil_rid),
            .m_axil_rdata    (m_axil_rdata),
            .m_axil_rresp    (m_axil_rresp),
            .m_axil_ruser    (1'b0),
            .m_axil_rtrace   (m_axil_rtrace),
            .m_axil_rpoison  (m_axil_rpoison),
            .m_axil_rvalid   (m_axil_rvalid),
            .m_axil_rready   (m_axil_rready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );
    end else begin : g_no_rd
        always_comb begin
            sts_rd      = '0;
            sts_rd.done = 1'b1;
        end
        assign m_axil_arid    = '0;
        assign m_axil_araddr  = '0;
        assign m_axil_arprot  = '0;
        assign m_axil_artrace = 1'b0;
        assign m_axil_arvalid = 1'b0;
        assign m_axil_rready  = 1'b1;
    end endgenerate

    // =========================================================================
    // Write
    // =========================================================================
    generate if (EN_WR) begin : g_wr
        logic [IW-1:0]     f_awid;
        logic [31:0]       f_awaddr;
        logic [2:0]        f_awprot;
        logic [31:0]       f_awsb;
        logic              f_awvalid, f_awready;
        logic [DW-1:0]     f_wdata;
        logic [DW/8-1:0]   f_wstrb;
        logic              f_wpoison;
        logic              f_wvalid, f_wready;
        logic [IW-1:0]     f_bid;
        logic [1:0]        f_bresp;
        logic              f_btrace;
        logic              f_bvalid, f_bready;

        axi_stress_mst_wr #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1),
            .LEN_MASK(L_LEN_MASK), .SIZE_FIXED(1'b1),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON)
        ) u_core (
            .aclk, .aresetn, .go, .stop,
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awtagop     (),
            .fub_axi_wtag        (),
            .fub_axi_wtagupdate  (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_btagmatch   (2'b00),
            .cfg (cfg_wr), .cfg_win, .cfg_hash_seed, .sts (sts_wr),
            .fub_axi_awid      (f_awid),
            .fub_axi_awaddr    (f_awaddr),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awlen     (),
            .fub_axi_awsize    (),
            .fub_axi_awburst   (),
            .fub_axi_awlock    (),
            .fub_axi_awcache   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awprot    (f_awprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awqos     (),
            .fub_axi_awregion  (),
            .fub_axi_awuser    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awsb      (f_awsb),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_awidunq   (),
            .fub_axi_awatop    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_wlast     (),
            .fub_axi_wid       (),          // AXI5-Lite has no WID
            .fub_axi_wuser     (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_wpoison   (f_wpoison),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (1'b0),
            .fub_axi_bsb       ({7'd0, f_btrace}),
            .fub_axi_bidunq    (1'b0),
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready),
            // No atomics on AXI5-Lite: the read-return path stays idle.
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_atr_ready (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_atr_valid (1'b0),
            .fub_axi_atr_id    ('0),
            .fub_axi_atr_data  ('0),
            .fub_axi_atr_resp  (2'b00),
            .fub_axi_atr_last  (1'b0),
            .fub_axi_atr_rsb   (8'd0),
            .fub_axi_atr_poison(1'b0),
            .fub_axi_atr_ridunq(1'b0)
        );

        axil5_master_wr #(
            .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(DW), .ID_WIDTH(IW),
            .USER_WIDTH(1), .ENABLE_USER(1'b0),
            .ENABLE_TRACE(EN_TRACE), .ENABLE_POISON(EN_POISON),
            .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W),
            .SKID_DEPTH_B(SKID_DEPTH_B)
        ) u_chan (
            .aclk, .aresetn,
            .fub_awid        (f_awid),
            .fub_awaddr      (f_awaddr),
            .fub_awprot      (f_awprot),
            .fub_awuser      (1'b0),
            .fub_awtrace     (f_awsb[4]),
            .fub_awvalid     (f_awvalid),
            .fub_awready     (f_awready),
            .fub_wdata       (f_wdata),
            .fub_wstrb       (f_wstrb),
            .fub_wuser       (1'b0),
            .fub_wpoison     (f_wpoison),
            .fub_wvalid      (f_wvalid),
            .fub_wready      (f_wready),
            .fub_bid         (f_bid),
            .fub_bresp       (f_bresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_buser       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_btrace      (f_btrace),
            .fub_bvalid      (f_bvalid),
            .fub_bready      (f_bready),
            .m_axil_awid     (m_axil_awid),
            .m_axil_awaddr   (m_axil_awaddr),
            .m_axil_awprot   (m_axil_awprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .m_axil_awuser   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .m_axil_awtrace  (m_axil_awtrace),
            .m_axil_awvalid  (m_axil_awvalid),
            .m_axil_awready  (m_axil_awready),
            .m_axil_wdata    (m_axil_wdata),
            .m_axil_wstrb    (m_axil_wstrb),
            /* verilator lint_off PINCONNECTEMPTY */
            .m_axil_wuser    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .m_axil_wpoison  (m_axil_wpoison),
            .m_axil_wvalid   (m_axil_wvalid),
            .m_axil_wready   (m_axil_wready),
            .m_axil_bid      (m_axil_bid),
            .m_axil_bresp    (m_axil_bresp),
            .m_axil_buser    (1'b0),
            .m_axil_btrace   (m_axil_btrace),
            .m_axil_bvalid   (m_axil_bvalid),
            .m_axil_bready   (m_axil_bready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );
    end else begin : g_no_wr
        always_comb begin
            sts_wr      = '0;
            sts_wr.done = 1'b1;
        end
        assign m_axil_awid    = '0;
        assign m_axil_awaddr  = '0;
        assign m_axil_awprot  = '0;
        assign m_axil_awtrace = 1'b0;
        assign m_axil_awvalid = 1'b0;
        assign m_axil_wdata   = '0;
        assign m_axil_wstrb   = '0;
        assign m_axil_wpoison = 1'b0;
        assign m_axil_wvalid  = 1'b0;
        assign m_axil_bready  = 1'b1;
    end endgenerate

endmodule : axil5_master_stress
