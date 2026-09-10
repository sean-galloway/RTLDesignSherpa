// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_slave_cg
// Purpose: Clock-gated wb4_slave: an amba_clock_gate_ctrl instance produces
//          the gated clock that feeds an otherwise unmodified wb4_slave.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_slave_cg.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   Same ports, parameters and behaviour as wb4_slave, plus the runtime
//   clock-gating controls of the *_cg family.
//
//   Activity terms (vault/handbook/design/clock-gating-activity-terms.md):
//     s_wb_CYC    a bus cycle open (requests arriving, terminations due)
//     rsp_valid   a FUB response offered (peer valid)
//     cmd_valid   a command parked on the FUB output (pending work)
//   Never cmd_ready / the master's readiness.
//
//   Masks for the wake-latency overlap (a gated clock cannot register an
//   accept, and the wake takes a clock or two): the command valid seen by
//   the FUB, the response ready seen by the FUB, and -- the one Wishbone
//   adds -- s_wb_STALL, which is held HIGH while gated. In pipelined mode
//   an accept is STB && !STALL in the master's clock; a frozen STALL of
//   "room" would let the master move on from a request the slave never
//   sampled. STALL stays high until the clock runs, and the master holds
//   the request while stalled (B4 rule). Classic mode holds the request
//   until termination and needs no STALL, but is masked the same way.
//==============================================================================

`timescale 1ns / 1ps

module wb4_slave_cg
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int CMD_DEPTH           = 2,
    parameter int RSP_DEPTH           = 2,
    parameter int MAX_OUTSTANDING     = 16,
    parameter int CLASSIC             = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,
    parameter int SEL_WIDTH           = DATA_WIDTH / 8,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = SEL_WIDTH,
    parameter int STW = WB4_STATUS_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH
)
(
    input  logic              clk,
    input  logic              aresetn,

    // Clock gating control
    input  logic              cfg_cg_enable,
    input  logic [ICW-1:0]    cfg_cg_idle_count,

    // Wishbone B4 slave
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

    // Command queue (FUB side)
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_we,
    output logic [AW-1:0]     cmd_adr,
    output logic [DW-1:0]     cmd_dat,
    output logic [SW-1:0]     cmd_sel,

    // Response queue (FUB side)
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [STW-1:0]    rsp_status,
    input  logic [DW-1:0]     rsp_dat,

    // Clock gating status
    output logic              cg_gating,
    output logic              cg_idle
);

    logic w_wakeup;
    logic gated_clk;
    logic w_cmd_valid, w_rsp_ready, w_stall;

    // Combinational wake term: the controller registers it once itself;
    // a second local flop (the apb4_*_cg shape) adds a clock of wake
    // latency for nothing (formal/amba/apb4_slave_cg/KNOWN_BUG.md).
    assign w_wakeup = s_wb_CYC || rsp_valid || w_cmd_valid;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) u_clock_gate_ctrl (
        .clk_in            (clk),
        .aresetn           (aresetn),
        .cfg_cg_enable     (cfg_cg_enable),
        .cfg_cg_idle_count (cfg_cg_idle_count),
        .user_valid        (w_wakeup),
        .axi_valid         (1'b0),
        .clk_out           (gated_clk),
        .gating            (cg_gating),
        .idle              (cg_idle)
    );

    wb4_slave #(
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DATA_WIDTH      (DATA_WIDTH),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .MAX_OUTSTANDING (MAX_OUTSTANDING),
        .CLASSIC         (CLASSIC),
        .SEL_WIDTH       (SEL_WIDTH)
    ) u_wb4_slave (
        .clk        (gated_clk),
        .aresetn    (aresetn),
        .s_wb_CYC   (s_wb_CYC),
        .s_wb_STB   (s_wb_STB),
        .s_wb_WE    (s_wb_WE),
        .s_wb_ADR   (s_wb_ADR),
        .s_wb_DAT_W (s_wb_DAT_W),
        .s_wb_SEL   (s_wb_SEL),
        .s_wb_STALL (w_stall),
        .s_wb_ACK   (s_wb_ACK),
        .s_wb_ERR   (s_wb_ERR),
        .s_wb_RTY   (s_wb_RTY),
        .s_wb_DAT_R (s_wb_DAT_R),
        .cmd_valid  (w_cmd_valid),
        .cmd_ready  (cmd_ready),
        .cmd_we     (cmd_we),
        .cmd_adr    (cmd_adr),
        .cmd_dat    (cmd_dat),
        .cmd_sel    (cmd_sel),
        .rsp_valid  (rsp_valid),
        .rsp_ready  (w_rsp_ready),
        .rsp_status (rsp_status),
        .rsp_dat    (rsp_dat)
    );

    // Nothing is accepted, in either direction, while the clock is stopped.
    assign cmd_valid  = w_cmd_valid && !cg_gating;
    assign rsp_ready  = w_rsp_ready && !cg_gating;
    assign s_wb_STALL = w_stall || cg_gating;

endmodule : wb4_slave_cg
