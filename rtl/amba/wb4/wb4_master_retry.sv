// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_master_retry
// Purpose: wb4_master with the RTY retry block on its FUB side.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_master_retry.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   The same cmd/rsp queue contract and Wishbone ports as wb4_master; RTY
//   terminations are retried up to cfg_max_retries times, cfg_retry_delay
//   clocks apart, before the FUB sees one. INFLIGHT is the retry block's
//   completion-buffer depth (1 = strict program order, see wb4_retry.sv);
//   RSP_DEPTH stays the master's bus-side bound.
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_wb4_master_retry.py
//==============================================================================

`timescale 1ns / 1ps

module wb4_master_retry
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int CMD_DEPTH  = 4,
    parameter int RSP_DEPTH  = 4,
    parameter int CLASSIC    = 0,
    parameter int INFLIGHT   = 1,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int STW = WB4_STATUS_WIDTH
)
(
    input  logic              clk,
    input  logic              aresetn,

    input  logic [7:0]        cfg_max_retries,
    input  logic [15:0]       cfg_retry_delay,

    // Wishbone B4 master
    output logic              m_wb_CYC,
    output logic              m_wb_STB,
    output logic              m_wb_WE,
    output logic [AW-1:0]     m_wb_ADR,
    output logic [DW-1:0]     m_wb_DAT_W,
    output logic [SW-1:0]     m_wb_SEL,
    input  logic              m_wb_STALL,
    input  logic              m_wb_ACK,
    input  logic              m_wb_ERR,
    input  logic              m_wb_RTY,
    input  logic [DW-1:0]     m_wb_DAT_R,

    // FUB side
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_we,
    input  logic [AW-1:0]     cmd_adr,
    input  logic [DW-1:0]     cmd_dat,
    input  logic [SW-1:0]     cmd_sel,
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [STW-1:0]    rsp_status,
    output logic [DW-1:0]     rsp_dat,

    output logic [31:0]       retry_count,
    output logic [7:0]        active_count
);

    logic           w_cmd_valid, w_cmd_ready, w_cmd_we;
    logic [AW-1:0]  w_cmd_adr;
    logic [DW-1:0]  w_cmd_dat, w_rsp_dat;
    logic [SW-1:0]  w_cmd_sel;
    logic           w_rsp_valid, w_rsp_ready;
    logic [STW-1:0] w_rsp_status;

    wb4_retry #(
        .ADDR_WIDTH (AW),
        .DATA_WIDTH (DW),
        .INFLIGHT   (INFLIGHT)
    ) u_retry (
        .clk             (clk),
        .aresetn         (aresetn),
        .cfg_max_retries (cfg_max_retries),
        .cfg_retry_delay (cfg_retry_delay),
        .cmd_valid       (cmd_valid),
        .cmd_ready       (cmd_ready),
        .cmd_we          (cmd_we),
        .cmd_adr         (cmd_adr),
        .cmd_dat         (cmd_dat),
        .cmd_sel         (cmd_sel),
        .rsp_valid       (rsp_valid),
        .rsp_ready       (rsp_ready),
        .rsp_status      (rsp_status),
        .rsp_dat         (rsp_dat),
        .mst_cmd_valid   (w_cmd_valid),
        .mst_cmd_ready   (w_cmd_ready),
        .mst_cmd_we      (w_cmd_we),
        .mst_cmd_adr     (w_cmd_adr),
        .mst_cmd_dat     (w_cmd_dat),
        .mst_cmd_sel     (w_cmd_sel),
        .mst_rsp_valid   (w_rsp_valid),
        .mst_rsp_ready   (w_rsp_ready),
        .mst_rsp_status  (w_rsp_status),
        .mst_rsp_dat     (w_rsp_dat),
        .retry_count     (retry_count),
        .active_count    (active_count)
    );

    wb4_master #(
        .ADDR_WIDTH (AW),
        .DATA_WIDTH (DW),
        .CMD_DEPTH  (CMD_DEPTH),
        .RSP_DEPTH  (RSP_DEPTH),
        .CLASSIC    (CLASSIC)
    ) u_master (
        .clk        (clk),
        .aresetn    (aresetn),
        .m_wb_CYC   (m_wb_CYC),
        .m_wb_STB   (m_wb_STB),
        .m_wb_WE    (m_wb_WE),
        .m_wb_ADR   (m_wb_ADR),
        .m_wb_DAT_W (m_wb_DAT_W),
        .m_wb_SEL   (m_wb_SEL),
        .m_wb_STALL (m_wb_STALL),
        .m_wb_ACK   (m_wb_ACK),
        .m_wb_ERR   (m_wb_ERR),
        .m_wb_RTY   (m_wb_RTY),
        .m_wb_DAT_R (m_wb_DAT_R),
        .cmd_valid  (w_cmd_valid),
        .cmd_ready  (w_cmd_ready),
        .cmd_we     (w_cmd_we),
        .cmd_adr    (w_cmd_adr),
        .cmd_dat    (w_cmd_dat),
        .cmd_sel    (w_cmd_sel),
        .rsp_valid  (w_rsp_valid),
        .rsp_ready  (w_rsp_ready),
        .rsp_status (w_rsp_status),
        .rsp_dat    (w_rsp_dat)
    );

endmodule : wb4_master_retry
