// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_rd_aggregator
// Purpose: Poor man's AXI4 read aggregator. Two adjacent single-beat reads
//          of the two halves of a 2-beat-aligned pair (lo then hi) leave as
//          one 2-beat read flagged m_axi_ar_agg. The 2-beat R burst that
//          comes back goes upstream as two single-beat bursts (RLAST on both).
//
// Documentation: docs/markdown/rtl-amba/shared/axi4_rd_aggregator.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-28
//
// Structure (no CAM, no state machine):
//   axi4_aggregator_cmd   the pairing core on AR (see its header for the rule)
//   r side queue          gaxi_fifo_sync, one bit per issued AR: agg. For an
//                         aggregated AR, RLAST is forced high on both beats;
//                         otherwise R passes through. Popped at the downstream
//                         RLAST.
//
// Assumptions (the price of no CAM):
//   1. R bursts return in AR issue order. True for a single-ID stream and for
//      an in-order slave; NOT guaranteed by AXI across IDs.
//   2. Beats of one burst are not interleaved with another burst's beats
//      (AXI4 forbids this).
//   3. Only modifiable reads (ARCACHE[1] = 1) pair; a non-modifiable read
//      passes through alone, as AXI requires.
// The side queue is AGG_FIFO_DEPTH (>= 2) deep and bounds the outstanding
// ARs; AR stalls when it is full.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_rd_aggregator
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 32,
    parameter int AXI_USER_WIDTH = 1,
    parameter int HOLD_CYCLES    = 4,   // how long a lone lo waits for its hi; 0 = pass-through
    parameter int AGG_FIFO_DEPTH = 4,   // outstanding ARs the side queue can hold (>= 2)
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
    input  logic [IW-1:0]   fub_arid,
    input  logic [AW-1:0]   fub_araddr,
    input  logic [7:0]      fub_arlen,
    input  logic [2:0]      fub_arsize,
    input  logic [1:0]      fub_arburst,
    input  logic            fub_arlock,
    input  logic [3:0]      fub_arcache,
    input  logic [2:0]      fub_arprot,
    input  logic [3:0]      fub_arqos,
    input  logic [3:0]      fub_arregion,
    input  logic [UW-1:0]   fub_aruser,
    input  logic            fub_arvalid,
    output logic            fub_arready,

    output logic [IW-1:0]   fub_rid,
    output logic [DW-1:0]   fub_rdata,
    output logic [1:0]      fub_rresp,
    output logic            fub_rlast,
    output logic [UW-1:0]   fub_ruser,
    output logic            fub_rvalid,
    input  logic            fub_rready,

    // ---- downstream (m_axi) --------------------------------------------------
    output logic [IW-1:0]   m_axi_arid,
    output logic [AW-1:0]   m_axi_araddr,
    output logic [7:0]      m_axi_arlen,
    output logic [2:0]      m_axi_arsize,
    output logic [1:0]      m_axi_arburst,
    output logic            m_axi_arlock,
    output logic [3:0]      m_axi_arcache,
    output logic [2:0]      m_axi_arprot,
    output logic [3:0]      m_axi_arqos,
    output logic [3:0]      m_axi_arregion,
    output logic [UW-1:0]   m_axi_aruser,
    output logic            m_axi_ar_agg,    // 1: this AR is two upstream reads
    output logic            m_axi_arvalid,
    input  logic            m_axi_arready,

    input  logic [IW-1:0]   m_axi_rid,
    input  logic [DW-1:0]   m_axi_rdata,
    input  logic [1:0]      m_axi_rresp,
    input  logic            m_axi_rlast,
    input  logic [UW-1:0]   m_axi_ruser,
    input  logic            m_axi_rvalid,
    output logic            m_axi_rready
);

    localparam int QW = 4 + 3 + 4 + 4 + UW;   // cache, prot, qos, region, user

    // ---- AR: the pairing core ------------------------------------------------
    logic [QW-1:0] w_s_qual, w_m_qual;
    logic          w_core_valid, w_core_ready, w_core_agg;
    logic          w_ar_issue;
    logic          w_rinfo_ready;

    assign w_s_qual = {fub_arcache, fub_arprot, fub_arqos, fub_arregion, fub_aruser};

    axi4_aggregator_cmd #(
        .ID_WIDTH    (IW),
        .ADDR_WIDTH  (AW),
        .DATA_WIDTH  (DW),
        .QUAL_WIDTH  (QW),
        .HOLD_CYCLES (HOLD_CYCLES)
    ) u_cmd (
        .aclk    (aclk),
        .aresetn (aresetn),
        .s_id    (fub_arid),
        .s_addr  (fub_araddr),
        .s_len   (fub_arlen),
        .s_size  (fub_arsize),
        .s_burst (fub_arburst),
        .s_lock  (fub_arlock),
        .s_mergeable (fub_arcache[1]),
        .s_qual  (w_s_qual),
        .s_valid (fub_arvalid),
        .s_ready (fub_arready),
        .m_id    (m_axi_arid),
        .m_addr  (m_axi_araddr),
        .m_len   (m_axi_arlen),
        .m_size  (m_axi_arsize),
        .m_burst (m_axi_arburst),
        .m_lock  (m_axi_arlock),
        .m_qual  (w_m_qual),
        .m_agg   (w_core_agg),
        .m_valid (w_core_valid),
        .m_ready (w_core_ready)
    );

    assign {m_axi_arcache, m_axi_arprot, m_axi_arqos, m_axi_arregion, m_axi_aruser} = w_m_qual;
    assign m_axi_ar_agg  = w_core_agg;

    // an AR issues only when the side queue can record it
    assign m_axi_arvalid = w_core_valid  && w_rinfo_ready;
    assign w_core_ready  = m_axi_arready && w_rinfo_ready;
    assign w_ar_issue    = m_axi_arvalid && m_axi_arready;

    // ---- R side queue: agg per issued AR, popped at the downstream RLAST -----
    logic w_rinfo_valid, w_rinfo_agg;
    logic w_r_hs;

    gaxi_fifo_sync #(
        .DATA_WIDTH (1),
        .DEPTH      (AGG_FIFO_DEPTH)
    ) u_rinfo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_ar_issue),
        .wr_ready    (w_rinfo_ready),
        .wr_data     (w_core_agg),
        .rd_ready    (w_r_hs && m_axi_rlast),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_rinfo_valid),
        .rd_data     (w_rinfo_agg)
    );

    assign fub_rid      = m_axi_rid;
    assign fub_rdata    = m_axi_rdata;
    assign fub_rresp    = m_axi_rresp;
    assign fub_ruser    = m_axi_ruser;
    assign fub_rlast    = w_rinfo_agg ? 1'b1 : m_axi_rlast;   // each half is its own burst upstream
    assign fub_rvalid   = m_axi_rvalid && w_rinfo_valid;
    assign m_axi_rready = fub_rready   && w_rinfo_valid;
    assign w_r_hs       = m_axi_rvalid && m_axi_rready;

endmodule : axi4_rd_aggregator
