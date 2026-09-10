// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_master_cg
// Purpose: Clock-gated wb4_master: an amba_clock_gate_ctrl instance produces
//          the gated clock that feeds an otherwise unmodified wb4_master.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_master_cg.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   Same ports, parameters and behaviour as wb4_master, plus the runtime
//   clock-gating controls of the *_cg family: cfg_cg_enable, a programmable
//   idle count, and the cg_gating / cg_idle observers.
//
//   Activity terms (vault/handbook/design/clock-gating-activity-terms.md):
//   peer VALIDs and every place work can be pending, never a peer READY.
//     cmd_valid   a FUB command offered (peer valid)
//     rsp_valid   a response parked on the output (pending work)
//     m_wb_CYC    a bus cycle open: requests queued or terminations due
//   Masks for the wake-latency overlap (a gated clock cannot register an
//   accept, and the wake takes a clock or two): the response valid and the
//   command ready seen by the FUB are both held low while gated, so a FUB
//   never has a command taken, or a response retired, by a stopped clock.
//   On the bus nothing needs masking: the master only drives CYC/STB from
//   registered state that is idle whenever the clock is allowed to stop,
//   and a slave terminates only inside a cycle.
//==============================================================================

`timescale 1ns / 1ps

module wb4_master_cg
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int CMD_DEPTH           = 4,
    parameter int RSP_DEPTH           = 4,
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

    // Command queue (FUB side)
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_we,
    input  logic [AW-1:0]     cmd_adr,
    input  logic [DW-1:0]     cmd_dat,
    input  logic [SW-1:0]     cmd_sel,

    // Response queue (FUB side)
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [STW-1:0]    rsp_status,
    output logic [DW-1:0]     rsp_dat,

    // Clock gating status
    output logic              cg_gating,
    output logic              cg_idle
);

    logic w_wakeup;
    logic gated_clk;
    logic w_rsp_valid, w_cmd_ready;

    // Combinational wake term: the controller registers it once itself;
    // a second local flop (the apb4_*_cg shape) adds a clock of wake
    // latency for nothing (formal/amba/apb4_slave_cg/KNOWN_BUG.md).
    assign w_wakeup = cmd_valid || w_rsp_valid || m_wb_CYC;

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

    wb4_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .CMD_DEPTH  (CMD_DEPTH),
        .RSP_DEPTH  (RSP_DEPTH),
        .CLASSIC    (CLASSIC),
        .SEL_WIDTH  (SEL_WIDTH)
    ) u_wb4_master (
        .clk        (gated_clk),
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
        .cmd_valid  (cmd_valid),
        .cmd_ready  (w_cmd_ready),
        .cmd_we     (cmd_we),
        .cmd_adr    (cmd_adr),
        .cmd_dat    (cmd_dat),
        .cmd_sel    (cmd_sel),
        .rsp_valid  (w_rsp_valid),
        .rsp_ready  (rsp_ready),
        .rsp_status (rsp_status),
        .rsp_dat    (rsp_dat)
    );

    // Nothing is accepted, in either direction, while the clock is stopped.
    assign rsp_valid = w_rsp_valid && !cg_gating;
    assign cmd_ready = w_cmd_ready && !cg_gating;

endmodule : wb4_master_cg
