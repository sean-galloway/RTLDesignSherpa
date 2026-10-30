// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_wr_aggregator
// Purpose: Poor man's AXI4 write aggregator. Two adjacent single-beat writes
//          to the two halves of a 2-beat-aligned pair (lo then hi) leave as
//          one 2-beat write flagged m_axi_aw_agg. W passes through with WLAST
//          reframed; the one B that comes back is replayed twice upstream.
//
// Documentation: docs/markdown/rtl-amba/shared/axi4_wr_aggregator.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-28
//
// Structure (no CAM, no state machine):
//   axi4_aggregator_cmd   the pairing core on AW (see its header for the rule)
//   w side queue          gaxi_fifo_sync, one bit per presented AW: agg. W
//                         beats are released once their AW has been PRESENTED
//                         downstream (not handshaken: AXI forbids a master to
//                         wait for AWREADY before WVALID), and for an
//                         aggregated pair WLAST is 0 on the first beat and 1
//                         on the second.
//   b side queue          gaxi_fifo_sync, one bit per presented AW: agg. An
//                         aggregated B is presented upstream twice (same ID,
//                         same response); a plain B once.
//
// The side queues are written the first cycle an AW is presented
// (r_aw_logged marks an AW that is presented but not yet accepted), which is
// safe because the core holds the payload, agg included, stable until the
// handshake.
//
// Assumptions (the price of no CAM):
//   1. B responses return in AW issue order. True for a single-ID stream and
//      for an in-order slave such as a memory controller; NOT guaranteed by
//      AXI across IDs. Do not put this block in front of a slave that
//      reorders B across IDs.
//   2. W beats arrive in AW order (they always do for single-beat commands
//      from one master).
//   3. Both upstream halves get the one downstream response: a SLVERR on the
//      merged write is reported on both.
//   4. Only modifiable writes (AWCACHE[1] = 1) pair; a non-modifiable write
//      passes through alone, as AXI requires.
// The side queues are AGG_FIFO_DEPTH (>= 2) deep and bound the outstanding
// AWs; a new AW is not presented while either is full.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_wr_aggregator
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    parameter int HOLD_CYCLES    = 4,   // how long a lone lo waits for its hi; 0 = pass-through
    parameter int AGG_FIFO_DEPTH = 4,   // outstanding AWs the side queues can hold (>= 2)
    // short names
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH
)
(
    input  logic            aclk,
    input  logic            aresetn,

    // ---- upstream (fub) ------------------------------------------------------
    input  logic [IW-1:0]   fub_awid,
    input  logic [AW-1:0]   fub_awaddr,
    input  logic [7:0]      fub_awlen,
    input  logic [2:0]      fub_awsize,
    input  logic [1:0]      fub_awburst,
    input  logic            fub_awlock,
    input  logic [3:0]      fub_awcache,
    input  logic [2:0]      fub_awprot,
    input  logic [3:0]      fub_awqos,
    input  logic [3:0]      fub_awregion,
    input  logic [UW-1:0]   fub_awuser,
    input  logic            fub_awvalid,
    output logic            fub_awready,

    input  logic [DW-1:0]   fub_wdata,
    input  logic [DW/8-1:0] fub_wstrb,
    input  logic            fub_wlast,
    input  logic [UW-1:0]   fub_wuser,
    input  logic            fub_wvalid,
    output logic            fub_wready,

    output logic [IW-1:0]   fub_bid,
    output logic [1:0]      fub_bresp,
    output logic [UW-1:0]   fub_buser,
    output logic            fub_bvalid,
    input  logic            fub_bready,

    // ---- downstream (m_axi) --------------------------------------------------
    output logic [IW-1:0]   m_axi_awid,
    output logic [AW-1:0]   m_axi_awaddr,
    output logic [7:0]      m_axi_awlen,
    output logic [2:0]      m_axi_awsize,
    output logic [1:0]      m_axi_awburst,
    output logic            m_axi_awlock,
    output logic [3:0]      m_axi_awcache,
    output logic [2:0]      m_axi_awprot,
    output logic [3:0]      m_axi_awqos,
    output logic [3:0]      m_axi_awregion,
    output logic [UW-1:0]   m_axi_awuser,
    output logic            m_axi_aw_agg,    // 1: this AW is two upstream writes
    output logic            m_axi_awvalid,
    input  logic            m_axi_awready,

    output logic [DW-1:0]   m_axi_wdata,
    output logic [DW/8-1:0] m_axi_wstrb,
    output logic            m_axi_wlast,
    output logic [UW-1:0]   m_axi_wuser,
    output logic            m_axi_wvalid,
    input  logic            m_axi_wready,

    input  logic [IW-1:0]   m_axi_bid,
    input  logic [1:0]      m_axi_bresp,
    input  logic [UW-1:0]   m_axi_buser,
    input  logic            m_axi_bvalid,
    output logic            m_axi_bready
);

    localparam int QW = 4 + 3 + 4 + 4 + UW;   // cache, prot, qos, region, user

    // ---- AW: the pairing core ------------------------------------------------
    logic [QW-1:0] w_s_qual, w_m_qual;
    logic          w_core_valid, w_core_ready, w_core_agg;
    logic          w_aw_log;            // first cycle this AW is presented: record it
    logic          w_aw_hs;             // the AW handshakes downstream
    logic          w_winfo_ready, w_binfo_ready, w_info_room;
    logic          r_aw_logged;         // the presented AW is already in the side queues

    assign w_s_qual = {fub_awcache, fub_awprot, fub_awqos, fub_awregion, fub_awuser};

    axi4_aggregator_cmd #(
        .ID_WIDTH    (IW),
        .ADDR_WIDTH  (AW),
        .DATA_WIDTH  (DW),
        .QUAL_WIDTH  (QW),
        .HOLD_CYCLES (HOLD_CYCLES)
    ) u_cmd (
        .aclk    (aclk),
        .aresetn (aresetn),
        .s_id    (fub_awid),
        .s_addr  (fub_awaddr),
        .s_len   (fub_awlen),
        .s_size  (fub_awsize),
        .s_burst (fub_awburst),
        .s_lock  (fub_awlock),
        .s_mergeable (fub_awcache[1]),
        .s_qual  (w_s_qual),
        .s_valid (fub_awvalid),
        .s_ready (fub_awready),
        .m_id    (m_axi_awid),
        .m_addr  (m_axi_awaddr),
        .m_len   (m_axi_awlen),
        .m_size  (m_axi_awsize),
        .m_burst (m_axi_awburst),
        .m_lock  (m_axi_awlock),
        .m_qual  (w_m_qual),
        .m_agg   (w_core_agg),
        .m_valid (w_core_valid),
        .m_ready (w_core_ready)
    );

    assign {m_axi_awcache, m_axi_awprot, m_axi_awqos, m_axi_awregion, m_axi_awuser} = w_m_qual;
    assign m_axi_aw_agg  = w_core_agg;

    // an AW is presented only when both side queues can record it; once
    // recorded (r_aw_logged) it stays presented until the slave takes it
    assign w_info_room   = w_winfo_ready && w_binfo_ready;
    assign m_axi_awvalid = w_core_valid  && (r_aw_logged || w_info_room);
    assign w_core_ready  = m_axi_awready && (r_aw_logged || w_info_room);
    assign w_aw_log      = m_axi_awvalid && !r_aw_logged;
    assign w_aw_hs       = m_axi_awvalid && m_axi_awready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_aw_logged <= 1'b0;
        end else if (w_aw_hs) begin
            r_aw_logged <= 1'b0;
        end else if (w_aw_log) begin
            r_aw_logged <= 1'b1;
        end
    )

    // ---- W side queue: agg per presented AW, popped at the downstream WLAST ---
    logic w_winfo_valid, w_winfo_agg;
    logic w_w_hs;
    logic r_w_second;        // second beat of an aggregated pair

    gaxi_fifo_sync #(
        .DATA_WIDTH (1),
        .DEPTH      (AGG_FIFO_DEPTH)
    ) u_winfo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_aw_log),
        .wr_ready    (w_winfo_ready),
        .wr_data     (w_core_agg),
        .rd_ready    (w_w_hs && m_axi_wlast),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_winfo_valid),
        .rd_data     (w_winfo_agg)
    );

    assign m_axi_wdata  = fub_wdata;
    assign m_axi_wstrb  = fub_wstrb;
    assign m_axi_wuser  = fub_wuser;
    assign m_axi_wlast  = w_winfo_agg ? r_w_second : fub_wlast;
    assign m_axi_wvalid = fub_wvalid   && w_winfo_valid;
    assign fub_wready   = m_axi_wready && w_winfo_valid;
    assign w_w_hs       = m_axi_wvalid && m_axi_wready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_w_second <= 1'b0;
        end else if (w_w_hs) begin
            r_w_second <= w_winfo_agg && !r_w_second;
        end
    )

    // ---- B side queue: agg per presented AW, popped at the downstream B ------
    logic w_binfo_valid, w_binfo_agg;
    logic w_fub_b_hs, w_m_b_hs;
    logic r_b_second;        // second upstream copy of an aggregated B

    gaxi_fifo_sync #(
        .DATA_WIDTH (1),
        .DEPTH      (AGG_FIFO_DEPTH)
    ) u_binfo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_aw_log),
        .wr_ready    (w_binfo_ready),
        .wr_data     (w_core_agg),
        .rd_ready    (w_m_b_hs),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_binfo_valid),
        .rd_data     (w_binfo_agg)
    );

    assign fub_bid      = m_axi_bid;
    assign fub_bresp    = m_axi_bresp;
    assign fub_buser    = m_axi_buser;
    assign fub_bvalid   = m_axi_bvalid && w_binfo_valid;
    // the downstream B is released on its last upstream copy
    assign m_axi_bready = fub_bready && w_binfo_valid && (!w_binfo_agg || r_b_second);
    assign w_fub_b_hs   = fub_bvalid && fub_bready;
    assign w_m_b_hs     = m_axi_bvalid && m_axi_bready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_b_second <= 1'b0;
        end else if (w_fub_b_hs) begin
            r_b_second <= w_binfo_agg && !r_b_second;
        end
    )

endmodule : axi4_wr_aggregator
