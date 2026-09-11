// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_slave_cdc_cg
// Purpose: wb4_slave_cdc with the Wishbone-side clock gated.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_slave_cdc_cg.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   The combined variant, matching apb4_slave_cdc_cg / apb5_slave_cdc_cg:
//   the queues cross to another clock domain AND the bus-side clock is gated
//   when the Wishbone side is idle.
//
//   ONLY the Wishbone domain is gated. The FUB domain (aclk) keeps running,
//   so a consumer can keep draining commands and posting responses while the
//   bus sleeps; the async FIFOs make that safe. Gating both would need a
//   second controller and buys nothing the caller cannot do by gating its own
//   clock.
//
//   The wake term is wb4_slave_cdc's `wb_busy`, which is built from wb_clk
//   signals only: a cycle open on the bus, a command waiting to cross, or a
//   response that has crossed and not yet been driven. Nothing from the aclk
//   side may be used, because sampling it in wb_clk would be an
//   unsynchronised crossing -- the failure this wrapper would otherwise
//   invite.
//
//   MASK. `s_wb_STALL` is held HIGH while gated, for the reason wb4_slave_cg
//   documents: a pipelined accept is `STB && !STALL` in the master's clock,
//   and a frozen "room" would let a master move on from a request the slave
//   never sampled. `cmd_valid` is deliberately NOT masked here -- it lives in
//   aclk, and masking it with a wb_clk-domain gating signal would be exactly
//   the crossing this module is built to avoid.
//==============================================================================

`timescale 1ns / 1ps

module wb4_slave_cdc_cg
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int CMD_DEPTH           = 2,
    parameter int RSP_DEPTH           = 2,
    parameter int MAX_OUTSTANDING     = 16,
    parameter int CLASSIC             = 0,
    parameter int USE_BURST_HINTS     = 0,
    parameter int CDC_DEPTH           = 4,
    parameter int USE_JOHNSON         = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,
    parameter int SEL_WIDTH           = DATA_WIDTH / 8,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = SEL_WIDTH,
    parameter int STW = WB4_STATUS_WIDTH,
    parameter int CTW = WB4_CTI_WIDTH,
    parameter int BTW = WB4_BTE_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH
)
(
    // Wishbone domain (gated)
    input  logic              wb_clk,
    input  logic              wb_resetn,
    // FUB domain (free running)
    input  logic              aclk,
    input  logic              aresetn,

    // Clock gating control (wb_clk domain)
    input  logic              cfg_cg_enable,
    input  logic [ICW-1:0]    cfg_cg_idle_count,

    // Wishbone B4 slave
    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [AW-1:0]     s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [SW-1:0]     s_wb_SEL,
    input  logic [CTW-1:0]    s_wb_CTI,
    input  logic [BTW-1:0]    s_wb_BTE,
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
    output logic [CTW-1:0]    cmd_cti,
    output logic [BTW-1:0]    cmd_bte,

    // Response queue (aclk)
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [STW-1:0]    rsp_status,
    input  logic [DW-1:0]     rsp_dat,

    // Clock gating status (wb_clk domain)
    output logic              cg_gating,
    output logic              cg_idle
);

    logic w_wakeup, gated_wb_clk, w_stall, w_wb_busy;

    // Combinational into the controller, which registers it once itself: a
    // second local flop only adds wake latency (formal/amba/apb4_slave_cg/
    // KNOWN_BUG.md).
    assign w_wakeup = w_wb_busy;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) u_clock_gate_ctrl (
        .clk_in            (wb_clk),
        .aresetn           (wb_resetn),
        .cfg_cg_enable     (cfg_cg_enable),
        .cfg_cg_idle_count (cfg_cg_idle_count),
        .user_valid        (w_wakeup),
        .axi_valid         (1'b0),
        .clk_out           (gated_wb_clk),
        .gating            (cg_gating),
        .idle              (cg_idle)
    );

    wb4_slave_cdc #(
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DATA_WIDTH      (DATA_WIDTH),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .MAX_OUTSTANDING (MAX_OUTSTANDING),
        .CLASSIC         (CLASSIC),
        .USE_BURST_HINTS (USE_BURST_HINTS),
        .CDC_DEPTH       (CDC_DEPTH),
        .USE_JOHNSON     (USE_JOHNSON),
        .SEL_WIDTH       (SEL_WIDTH)
    ) u_wb4_slave_cdc (
        .wb_clk     (gated_wb_clk),
        .wb_resetn  (wb_resetn),
        .aclk       (aclk),
        .aresetn    (aresetn),
        .s_wb_CYC   (s_wb_CYC),
        .s_wb_STB   (s_wb_STB),
        .s_wb_WE    (s_wb_WE),
        .s_wb_ADR   (s_wb_ADR),
        .s_wb_DAT_W (s_wb_DAT_W),
        .s_wb_SEL   (s_wb_SEL),
        .s_wb_CTI   (s_wb_CTI),
        .s_wb_BTE   (s_wb_BTE),
        .s_wb_STALL (w_stall),
        .s_wb_ACK   (s_wb_ACK),
        .s_wb_ERR   (s_wb_ERR),
        .s_wb_RTY   (s_wb_RTY),
        .s_wb_DAT_R (s_wb_DAT_R),
        .cmd_valid  (cmd_valid),
        .cmd_ready  (cmd_ready),
        .cmd_we     (cmd_we),
        .cmd_adr    (cmd_adr),
        .cmd_dat    (cmd_dat),
        .cmd_sel    (cmd_sel),
        .cmd_cti    (cmd_cti),
        .cmd_bte    (cmd_bte),
        .rsp_valid  (rsp_valid),
        .rsp_ready  (rsp_ready),
        .rsp_status (rsp_status),
        .rsp_dat    (rsp_dat),
        .wb_busy    (w_wb_busy)
    );

    // Nothing is accepted on the bus while its clock is stopped.
    assign s_wb_STALL = w_stall || cg_gating;

endmodule : wb4_slave_cdc_cg
