// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_master_stress
// Purpose: AXI4-Lite bus-stress master: axi_stress_mst_rd / axi_stress_mst_wr
//          on the axil4_master_rd / axil4_master_wr channel modules.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-23
//==============================================================================
// The AXI4-Lite shell of the stress master. AXI4-Lite carries one bus-wide
// beat per transfer and no ID, so:
//
//   bursts  the cores are built with LEN_MASK = 8'h00 and SIZE_FIXED, so
//           every transfer is one aligned, bus-wide beat. AxLEN, AxSIZE,
//           AxBURST, AxLOCK, AxCACHE, AxQOS, AxREGION and AxUSER are not
//           driven onto the bus.
//   IDs     the cores still issue IDs and score per ID. AXI4-Lite returns a
//           direction's responses in issue order, so the shell keeps each
//           direction's issued IDs in a FIFO (pushed at the fub address
//           handshake, popped at the response handshake) and stamps the
//           head onto R / B. A fabric that reordered Lite read responses
//           would hand the core data under the wrong burst, and RD_DATA fails
//           (the data are a function of the address). B carries no data:
//           two swapped B's are caught only when their responses differ.
//   RLAST   always 1.
//
// DW is 32 or 64 (AXI4-Lite). A port built for one direction (EN_RD / EN_WR
// = 0) elaborates no logic for the other; its outputs are tied idle and its
// status reads done with no errors.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil4_master_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD   = 1'b1,
    parameter bit EN_WR   = 1'b1,
    parameter int DEPTH   = 16,
    parameter int NWIN    = 8,
    parameter int IW      = 8,          // the cores' ID width (not on the bus)
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

    output logic [31:0]       m_axil_awaddr,
    output logic [2:0]        m_axil_awprot,
    output logic              m_axil_awvalid,
    input  logic              m_axil_awready,
    output logic [DW-1:0]     m_axil_wdata,
    output logic [DW/8-1:0]   m_axil_wstrb,
    output logic              m_axil_wvalid,
    input  logic              m_axil_wready,
    input  logic [1:0]        m_axil_bresp,
    input  logic              m_axil_bvalid,
    output logic              m_axil_bready,
    output logic [31:0]       m_axil_araddr,
    output logic [2:0]        m_axil_arprot,
    output logic              m_axil_arvalid,
    input  logic              m_axil_arready,
    input  logic [DW-1:0]     m_axil_rdata,
    input  logic [1:0]        m_axil_rresp,
    input  logic              m_axil_rvalid,
    output logic              m_axil_rready
);

    localparam logic [7:0] L_LEN_MASK = 8'h00;    // one beat per transfer

    // =========================================================================
    // Read
    // =========================================================================
    generate if (EN_RD) begin : g_rd
        logic [IW-1:0]     f_arid;
        logic [31:0]       f_araddr;
        logic [2:0]        f_arprot;
        logic              f_arvalid, f_arready;
        logic [IW-1:0]     f_rid;
        logic [DW-1:0]     f_rdata;
        logic [1:0]        f_rresp;
        logic              f_rvalid, f_rready;
        logic              idq_wr_ready, idq_rd_valid;

        axi_stress_mst_rd #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1),
            .LEN_MASK(L_LEN_MASK), .SIZE_FIXED(1'b1)
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
            .fub_axi_arsb      (),
            .fub_axi_aridunq   (),
            /* verilator lint_on PINCONNECTEMPTY */
            // An address goes out only when its ID has a slot to wait in.
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready && idq_wr_ready),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            .fub_axi_rlast     (1'b1),
            .fub_axi_ruser     (1'b0),
            .fub_axi_rsb       ('0),
            .fub_axi_rpoison   (1'b0),
            .fub_axi_ridunq    (1'b0),
            .fub_axi_rvalid    (f_rvalid && idq_rd_valid),
            .fub_axi_rready    (f_rready)
        );

        // Issued ARIDs, oldest first. A response with no ID to pair with is
        // held (the core cannot take it as stray without an ID), so it shows
        // as HANG rather than corrupting the next burst's score.
        gaxi_fifo_sync #(
            .REGISTERED(0), .DATA_WIDTH(IW), .DEPTH(DEPTH)
        ) u_idq (
            .axi_aclk    (aclk),
            .axi_aresetn (aresetn),
            .wr_valid    (f_arvalid && f_arready),
            .wr_ready    (idq_wr_ready),
            .wr_data     (f_arid),
            .rd_ready    (f_rvalid && f_rready && idq_rd_valid),
            /* verilator lint_off PINCONNECTEMPTY */
            .count       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .rd_valid    (idq_rd_valid),
            .rd_data     (f_rid)
        );

        axil4_master_rd #(
            .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(DW),
            .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R)
        ) u_chan (
            .aclk, .aresetn,
            .fub_araddr      (f_araddr),
            .fub_arprot      (f_arprot),
            .fub_arvalid     (f_arvalid && idq_wr_ready),
            .fub_arready     (f_arready),
            .fub_rdata       (f_rdata),
            .fub_rresp       (f_rresp),
            .fub_rvalid      (f_rvalid),
            .fub_rready      (f_rready && idq_rd_valid),
            .m_axil_araddr   (m_axil_araddr),
            .m_axil_arprot   (m_axil_arprot),
            .m_axil_arvalid  (m_axil_arvalid),
            .m_axil_arready  (m_axil_arready),
            .m_axil_rdata    (m_axil_rdata),
            .m_axil_rresp    (m_axil_rresp),
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
        assign m_axil_araddr  = '0;
        assign m_axil_arprot  = '0;
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
        logic              f_awvalid, f_awready;
        logic [DW-1:0]     f_wdata;
        logic [DW/8-1:0]   f_wstrb;
        logic              f_wvalid, f_wready;
        logic [IW-1:0]     f_bid;
        logic [1:0]        f_bresp;
        logic              f_bvalid, f_bready;
        logic              idq_wr_ready, idq_rd_valid;

        axi_stress_mst_wr #(
            .DEPTH(DEPTH), .NWIN(NWIN), .IW(IW), .DW(DW), .UW(1),
            .LEN_MASK(L_LEN_MASK), .SIZE_FIXED(1'b1)
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
            .fub_axi_awsb      (),
            .fub_axi_awidunq   (),
            .fub_axi_awatop    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready && idq_wr_ready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_wlast     (),
            .fub_axi_wid       (),          // AXI4-Lite has no WID
            .fub_axi_wuser     (),
            .fub_axi_wpoison   (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            .fub_axi_buser     (1'b0),
            .fub_axi_bsb       ('0),
            .fub_axi_bidunq    (1'b0),
            .fub_axi_bvalid    (f_bvalid && idq_rd_valid),
            .fub_axi_bready    (f_bready),
            // No atomics on AXI4-Lite: the read-return path stays idle.
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

        // Issued AWIDs, oldest first (see the read side).
        gaxi_fifo_sync #(
            .REGISTERED(0), .DATA_WIDTH(IW), .DEPTH(DEPTH)
        ) u_idq (
            .axi_aclk    (aclk),
            .axi_aresetn (aresetn),
            .wr_valid    (f_awvalid && f_awready),
            .wr_ready    (idq_wr_ready),
            .wr_data     (f_awid),
            .rd_ready    (f_bvalid && f_bready && idq_rd_valid),
            /* verilator lint_off PINCONNECTEMPTY */
            .count       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .rd_valid    (idq_rd_valid),
            .rd_data     (f_bid)
        );

        axil4_master_wr #(
            .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(DW),
            .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W),
            .SKID_DEPTH_B(SKID_DEPTH_B)
        ) u_chan (
            .aclk, .aresetn,
            .fub_awaddr      (f_awaddr),
            .fub_awprot      (f_awprot),
            .fub_awvalid     (f_awvalid && idq_wr_ready),
            .fub_awready     (f_awready),
            .fub_wdata       (f_wdata),
            .fub_wstrb       (f_wstrb),
            .fub_wvalid      (f_wvalid),
            .fub_wready      (f_wready),
            .fub_bresp       (f_bresp),
            .fub_bvalid      (f_bvalid),
            .fub_bready      (f_bready && idq_rd_valid),
            .m_axil_awaddr   (m_axil_awaddr),
            .m_axil_awprot   (m_axil_awprot),
            .m_axil_awvalid  (m_axil_awvalid),
            .m_axil_awready  (m_axil_awready),
            .m_axil_wdata    (m_axil_wdata),
            .m_axil_wstrb    (m_axil_wstrb),
            .m_axil_wvalid   (m_axil_wvalid),
            .m_axil_wready   (m_axil_wready),
            .m_axil_bresp    (m_axil_bresp),
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
        assign m_axil_awaddr  = '0;
        assign m_axil_awprot  = '0;
        assign m_axil_awvalid = 1'b0;
        assign m_axil_wdata   = '0;
        assign m_axil_wstrb   = '0;
        assign m_axil_wvalid  = 1'b0;
        assign m_axil_bready  = 1'b1;
    end endgenerate

endmodule : axil4_master_stress
