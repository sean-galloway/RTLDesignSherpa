// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_slave_cdc
// Purpose: wb4_slave with its command and response queues carried across a
//          clock-domain boundary: the Wishbone bus in wb_clk, the FUB
//          queues in aclk.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_slave_cdc.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   wb4_slave in the wb_clk domain, plus two gaxi_fifo_async instances:
//   cmd (wb_clk -> aclk) and rsp (aclk -> wb_clk). Same shape as
//   apb4_slave_cdc, whose reset analysis applies here unchanged: each FIFO
//   resets its own side's pointers from that side's reset, so a ONE-SIDED
//   reset while transfers are in the FIFOs is not safe (a write-side reset
//   alone lets the read side see phantom occupancy, a read-side reset alone
//   replays consumed entries). Quiesce the bus before resetting one side.
//
//   In-order termination is preserved: both FIFOs are FIFOs, so the n-th
//   response returned by the FUB terminates the n-th accepted request.
//   MAX_OUTSTANDING still bounds the requests the slave accepts while
//   responses are pending, so the response FIFO can never overflow the
//   slave's response queue.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   wb4_slave's, plus
//   CDC_DEPTH   - async FIFO depth (floored at 4; power of two preferred)
//   USE_JOHNSON - 0 = Gray pointers (power-of-two depth), 1 = Johnson
//==============================================================================

`timescale 1ns / 1ps

module wb4_slave_cdc
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int CMD_DEPTH       = 2,
    parameter int RSP_DEPTH       = 2,
    parameter int MAX_OUTSTANDING = 16,
    parameter int CLASSIC         = 0,
    parameter int CDC_DEPTH       = 4,
    parameter int USE_JOHNSON     = 0,
    parameter int SEL_WIDTH       = DATA_WIDTH / 8,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = SEL_WIDTH,
    parameter int STW = WB4_STATUS_WIDTH,
    parameter int CPW = 1 + AW + DW + SW,   // {we, adr, dat, sel}
    parameter int RPW = STW + DW            // {status, dat}
)
(
    // Wishbone domain
    input  logic              wb_clk,
    input  logic              wb_resetn,
    // FUB domain
    input  logic              aclk,
    input  logic              aresetn,

    // Wishbone B4 slave (wb_clk)
    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [AW-1:0]     s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [SW-1:0]     s_wb_SEL,
    output logic              s_wb_STALL,
    output logic              s_wb_ACK,
    output logic              s_wb_ERR,
    output logic              s_wb_RTY,
    output logic [DW-1:0]     s_wb_DAT_R,

    // Command queue (aclk)
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_we,
    output logic [AW-1:0]     cmd_adr,
    output logic [DW-1:0]     cmd_dat,
    output logic [SW-1:0]     cmd_sel,

    // Response queue (aclk)
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [STW-1:0]    rsp_status,
    input  logic [DW-1:0]     rsp_dat
);

    localparam int CDC_FIFO_DEPTH = (CDC_DEPTH < 4) ? 4 : CDC_DEPTH;

    // Slave-side queues, wb_clk domain
    logic           w_cmd_valid, w_cmd_ready, w_cmd_we;
    logic [AW-1:0]  w_cmd_adr;
    logic [DW-1:0]  w_cmd_dat, w_rsp_dat;
    logic [SW-1:0]  w_cmd_sel;
    logic           w_rsp_valid, w_rsp_ready;
    logic [STW-1:0] w_rsp_status;

    wb4_slave #(
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DATA_WIDTH      (DATA_WIDTH),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .MAX_OUTSTANDING (MAX_OUTSTANDING),
        .CLASSIC         (CLASSIC),
        .SEL_WIDTH       (SEL_WIDTH)
    ) u_wb4_slave (
        .clk        (wb_clk),
        .aresetn    (wb_resetn),
        .s_wb_CYC   (s_wb_CYC),
        .s_wb_STB   (s_wb_STB),
        .s_wb_WE    (s_wb_WE),
        .s_wb_ADR   (s_wb_ADR),
        .s_wb_DAT_W (s_wb_DAT_W),
        .s_wb_SEL   (s_wb_SEL),
        .s_wb_STALL (s_wb_STALL),
        .s_wb_ACK   (s_wb_ACK),
        .s_wb_ERR   (s_wb_ERR),
        .s_wb_RTY   (s_wb_RTY),
        .s_wb_DAT_R (s_wb_DAT_R),
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

    // cmd: wb_clk -> aclk
    gaxi_fifo_async #(
        .DATA_WIDTH   (CPW),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_cmd_cdc_fifo (
        .axi_wr_aclk    (wb_clk),
        .axi_wr_aresetn (wb_resetn),
        .axi_rd_aclk    (aclk),
        .axi_rd_aresetn (aresetn),
        .wr_valid       (w_cmd_valid),
        .wr_ready       (w_cmd_ready),
        .wr_data        ({w_cmd_we, w_cmd_adr, w_cmd_dat, w_cmd_sel}),
        .rd_ready       (cmd_ready),
        .rd_valid       (cmd_valid),
        .rd_data        ({cmd_we, cmd_adr, cmd_dat, cmd_sel})
    );

    // rsp: aclk -> wb_clk
    gaxi_fifo_async #(
        .DATA_WIDTH   (RPW),
        .DEPTH        (CDC_FIFO_DEPTH),
        .USE_JOHNSON  (USE_JOHNSON),
        .N_FLOP_CROSS (2)
    ) u_rsp_cdc_fifo (
        .axi_wr_aclk    (aclk),
        .axi_wr_aresetn (aresetn),
        .axi_rd_aclk    (wb_clk),
        .axi_rd_aresetn (wb_resetn),
        .wr_valid       (rsp_valid),
        .wr_ready       (rsp_ready),
        .wr_data        ({rsp_status, rsp_dat}),
        .rd_ready       (w_rsp_ready),
        .rd_valid       (w_rsp_valid),
        .rd_data        ({w_rsp_status, w_rsp_dat})
    );

endmodule : wb4_slave_cdc
