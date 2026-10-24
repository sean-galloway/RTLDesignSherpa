// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil5_slave_stress
// Purpose: AXI5-Lite bus-stress slave: axi_stress_slv_rd / axi_stress_slv_wr
//          on the axil5_slave_rd / axil5_slave_wr channel modules.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-23
//==============================================================================
// The AXI5-Lite shell of the stress slave. Every request reaches the core as
// a one-beat, bus-wide INCR burst on the request's own ID (AWID / ARID), so
// the core may answer requests of different IDs in any order, as AXI5-Lite
// permits (IHI 0022L B2.1.5), and keeps each ID in order. Its reorder option
// therefore acts here, unlike on AXI4-Lite.
//
//   TRACE   (EN_TRACE) AxTRACE is checked against f_sb(start address) from a
//           sideband-carrying master (cfg sb_src, by the ID's SRC field),
//           else against 0; BTRACE / RTRACE echo the request's TRACE.
//   POISON  (EN_POISON) WPOISON checked and RPOISON driven, f_poison(beat
//           address); one bit per 64 data bits, so DW is held to 32 or 64.
//   USER    ignored (USER groups disabled).
//   W_FIRST (cfg w_first) gated at the pins, as in axi4_slave_stress.
//
// A port built for one direction (EN_RD / EN_WR = 0) elaborates no logic for
// the other; its READYs are tied low and it never answers.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil5_slave_stress
    import axi_stress_pkg::*;
#(
    parameter bit EN_RD     = 1'b1,
    parameter bit EN_WR     = 1'b1,
    parameter bit EN_TRACE  = 1'b0,
    parameter bit EN_POISON = 1'b0,
    parameter int SRC_LSB   = 0,     // master-index field of the ID
    parameter int SRC_W     = 0,     //   (0: one master)
    parameter int DEPTH   = 16,
    parameter int IW      = 8,
    parameter int DW      = 32,      // 32 or 64
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

    input  logic [IW-1:0]     s_axil_awid,
    input  logic [31:0]       s_axil_awaddr,
    input  logic [2:0]        s_axil_awprot,
    input  logic              s_axil_awtrace,
    input  logic              s_axil_awvalid,
    output logic              s_axil_awready,
    input  logic [DW-1:0]     s_axil_wdata,
    input  logic [DW/8-1:0]   s_axil_wstrb,
    input  logic              s_axil_wpoison,
    input  logic              s_axil_wvalid,
    output logic              s_axil_wready,
    output logic [IW-1:0]     s_axil_bid,
    output logic [1:0]        s_axil_bresp,
    output logic              s_axil_btrace,
    output logic              s_axil_bvalid,
    input  logic              s_axil_bready,
    input  logic [IW-1:0]     s_axil_arid,
    input  logic [31:0]       s_axil_araddr,
    input  logic [2:0]        s_axil_arprot,
    input  logic              s_axil_artrace,
    input  logic              s_axil_arvalid,
    output logic              s_axil_arready,
    output logic [IW-1:0]     s_axil_rid,
    output logic [DW-1:0]     s_axil_rdata,
    output logic [1:0]        s_axil_rresp,
    output logic              s_axil_rtrace,
    output logic              s_axil_rpoison,
    output logic              s_axil_rvalid,
    input  logic              s_axil_rready
);

    localparam int BUS_LG2 = $clog2(DW / 8);
    localparam logic [31:0] SB_MASK  = EN_TRACE ? SB_M_TRACE : '0;
    localparam logic [7:0]  RSB_MASK = EN_TRACE ? RSB_M_TRACE : '0;

`ifndef SYNTHESIS
    initial begin : param_check
        if (DW != 32 && DW != 64)
            $fatal(1, "axil5_slave_stress: DW %0d; 32 or 64 (one POISON bit per beat)", DW);
    end
`endif

    // =========================================================================
    // Read
    // =========================================================================
    generate if (EN_RD) begin : g_rd
        logic [IW-1:0]     f_arid;
        logic [31:0]       f_araddr;
        logic [2:0]        f_arprot;
        logic              f_artrace;
        logic              f_arvalid, f_arready;
        logic [IW-1:0]     f_rid;
        logic [DW-1:0]     f_rdata;
        logic [1:0]        f_rresp;
        logic [7:0]        c_rsb;
        logic              f_rpoison;
        logic              f_rvalid, f_rready;

        axil5_slave_rd #(
            .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(DW), .ID_WIDTH(IW),
            .USER_WIDTH(1), .ENABLE_USER(1'b0),
            .ENABLE_TRACE(EN_TRACE), .ENABLE_POISON(EN_POISON),
            .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R)
        ) u_chan (
            .aclk, .aresetn,
            .s_axil_arid     (s_axil_arid),
            .s_axil_araddr   (s_axil_araddr),
            .s_axil_arprot   (s_axil_arprot),
            .s_axil_aruser   (1'b0),
            .s_axil_artrace  (s_axil_artrace),
            .s_axil_arvalid  (s_axil_arvalid),
            .s_axil_arready  (s_axil_arready),
            .s_axil_rid      (s_axil_rid),
            .s_axil_rdata    (s_axil_rdata),
            .s_axil_rresp    (s_axil_rresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .s_axil_ruser    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .s_axil_rtrace   (s_axil_rtrace),
            .s_axil_rpoison  (s_axil_rpoison),
            .s_axil_rvalid   (s_axil_rvalid),
            .s_axil_rready   (s_axil_rready),
            .fub_arid        (f_arid),
            .fub_araddr      (f_araddr),
            .fub_arprot      (f_arprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_aruser      (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_artrace     (f_artrace),
            .fub_arvalid     (f_arvalid),
            .fub_arready     (f_arready),
            .fub_rid         (f_rid),
            .fub_rdata       (f_rdata),
            .fub_rresp       (f_rresp),
            .fub_ruser       (1'b0),
            .fub_rtrace      (c_rsb[0]),
            .fub_rpoison     (f_rpoison),
            .fub_rvalid      (f_rvalid),
            .fub_rready      (f_rready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        axi_stress_slv_rd #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(1),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON),
            .SRC_LSB(SRC_LSB), .SRC_W(SRC_W)
        ) u_core (
            .aclk, .aresetn, .clear,
            .fub_axi_artagop   (2'b00),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rtag      (),
            /* verilator lint_on PINCONNECTEMPTY */
            .cfg (cfg_rd), .cfg_hash_seed, .sts (sts_rd),
            .fub_axi_arid      (f_arid),
            .fub_axi_araddr    (f_araddr),
            .fub_axi_arlen     (8'd0),
            .fub_axi_arsize    (3'(BUS_LG2)),
            .fub_axi_arburst   (BURST_INCR),
            .fub_axi_arlock    (1'b0),
            .fub_axi_arcache   (4'd0),
            .fub_axi_arprot    (f_arprot),
            .fub_axi_arqos     (4'd0),
            .fub_axi_arregion  (4'd0),
            .fub_axi_aruser    (1'b0),
            .fub_axi_arsb      ({27'd0, f_artrace, 4'd0}),   // SB_M_TRACE = bit 4
            .fub_axi_aridunq   (1'b0),
            .fub_axi_arvalid   (f_arvalid),
            .fub_axi_arready   (f_arready),
            .fub_axi_rid       (f_rid),
            .fub_axi_rdata     (f_rdata),
            .fub_axi_rresp     (f_rresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_rlast     (),
            .fub_axi_ruser     (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rsb       (c_rsb),
            .fub_axi_rpoison   (f_rpoison),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_ridunq    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_rvalid    (f_rvalid),
            .fub_axi_rready    (f_rready)
        );
    end else begin : g_no_rd
        assign sts_rd         = '0;
        assign s_axil_arready = 1'b0;
        assign s_axil_rid     = '0;
        assign s_axil_rdata   = '0;
        assign s_axil_rresp   = '0;
        assign s_axil_rtrace  = 1'b0;
        assign s_axil_rpoison = 1'b0;
        assign s_axil_rvalid  = 1'b0;
    end endgenerate

    // =========================================================================
    // Write
    // =========================================================================
    generate if (EN_WR) begin : g_wr
        logic [IW-1:0]     f_awid;
        logic [31:0]       f_awaddr;
        logic [2:0]        f_awprot;
        logic              f_awtrace;
        logic              f_awvalid, f_awready;
        logic [DW-1:0]     f_wdata;
        logic [DW/8-1:0]   f_wstrb;
        logic              f_wpoison;
        logic              f_wvalid, f_wready;
        logic [IW-1:0]     f_bid;
        logic [1:0]        f_bresp;
        logic [7:0]        c_bsb;
        logic              f_bvalid, f_bready;

        // W_FIRST (cfg w_first): take an AW only while a W beat is offered
        // (AXI A3.3.1 allows it), at the pins -- behind the channel module's
        // AW skid the gate would never be seen on the wire.
        logic w_aw_gate, w_ch_awready;
        assign w_aw_gate      = !cfg_wr.w_first || s_axil_wvalid;
        assign s_axil_awready = w_ch_awready && w_aw_gate;

        axil5_slave_wr #(
            .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(DW), .ID_WIDTH(IW),
            .USER_WIDTH(1), .ENABLE_USER(1'b0),
            .ENABLE_TRACE(EN_TRACE), .ENABLE_POISON(EN_POISON),
            .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W),
            .SKID_DEPTH_B(SKID_DEPTH_B)
        ) u_chan (
            .aclk, .aresetn,
            .s_axil_awid     (s_axil_awid),
            .s_axil_awaddr   (s_axil_awaddr),
            .s_axil_awprot   (s_axil_awprot),
            .s_axil_awuser   (1'b0),
            .s_axil_awtrace  (s_axil_awtrace),
            .s_axil_awvalid  (s_axil_awvalid && w_aw_gate),
            .s_axil_awready  (w_ch_awready),
            .s_axil_wdata    (s_axil_wdata),
            .s_axil_wstrb    (s_axil_wstrb),
            .s_axil_wuser    (1'b0),
            .s_axil_wpoison  (s_axil_wpoison),
            .s_axil_wvalid   (s_axil_wvalid),
            .s_axil_wready   (s_axil_wready),
            .s_axil_bid      (s_axil_bid),
            .s_axil_bresp    (s_axil_bresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .s_axil_buser    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .s_axil_btrace   (s_axil_btrace),
            .s_axil_bvalid   (s_axil_bvalid),
            .s_axil_bready   (s_axil_bready),
            .fub_awid        (f_awid),
            .fub_awaddr      (f_awaddr),
            .fub_awprot      (f_awprot),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_awuser      (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_awtrace     (f_awtrace),
            .fub_awvalid     (f_awvalid),
            .fub_awready     (f_awready),
            .fub_wdata       (f_wdata),
            .fub_wstrb       (f_wstrb),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_wuser       (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_wpoison     (f_wpoison),
            .fub_wvalid      (f_wvalid),
            .fub_wready      (f_wready),
            .fub_bid         (f_bid),
            .fub_bresp       (f_bresp),
            .fub_buser       (1'b0),
            .fub_btrace      (c_bsb[0]),
            .fub_bvalid      (f_bvalid),
            .fub_bready      (f_bready),
            /* verilator lint_off PINCONNECTEMPTY */
            .busy ()
            /* verilator lint_on PINCONNECTEMPTY */
        );

        axi_stress_slv_wr #(
            .DEPTH(DEPTH), .IW(IW), .DW(DW), .UW(1),
            .SB_MASK(SB_MASK), .RSB_MASK(RSB_MASK), .POISON(EN_POISON),
            .SRC_LSB(SRC_LSB), .SRC_W(SRC_W)
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
            .fub_axi_awlen     (8'd0),
            .fub_axi_awsize    (3'(BUS_LG2)),
            .fub_axi_awburst   (BURST_INCR),
            .fub_axi_awlock    (1'b0),
            .fub_axi_awcache   (4'd0),
            .fub_axi_awprot    (f_awprot),
            .fub_axi_awqos     (4'd0),
            .fub_axi_awregion  (4'd0),
            .fub_axi_awuser    (1'b0),
            .fub_axi_awsb      ({27'd0, f_awtrace, 4'd0}),   // SB_M_TRACE = bit 4
            .fub_axi_awidunq   (1'b0),
            .fub_axi_awvalid   (f_awvalid),
            .fub_axi_awready   (f_awready),
            .fub_axi_wdata     (f_wdata),
            .fub_axi_wstrb     (f_wstrb),
            .fub_axi_wid       (IW'(0)),    // AXI5-Lite has no WID
            .fub_axi_wlast     (1'b1),      // every write is one beat
            .fub_axi_wuser     (1'b0),
            .fub_axi_wpoison   (f_wpoison),
            .fub_axi_wvalid    (f_wvalid),
            .fub_axi_wready    (f_wready),
            .fub_axi_bid       (f_bid),
            .fub_axi_bresp     (f_bresp),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_buser     (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_bsb       (c_bsb),
            /* verilator lint_off PINCONNECTEMPTY */
            .fub_axi_bidunq    (),
            /* verilator lint_on PINCONNECTEMPTY */
            .fub_axi_bvalid    (f_bvalid),
            .fub_axi_bready    (f_bready)
        );
    end else begin : g_no_wr
        assign sts_wr         = '0;
        assign s_axil_awready = 1'b0;
        assign s_axil_wready  = 1'b0;
        assign s_axil_bid     = '0;
        assign s_axil_bresp   = '0;
        assign s_axil_btrace  = 1'b0;
        assign s_axil_bvalid  = 1'b0;
    end endgenerate

endmodule : axil5_slave_stress
