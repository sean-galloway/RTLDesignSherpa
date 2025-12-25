// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_slave_cdc_cg
// Purpose: APB5 Slave with Clock Domain Crossing and Clock Gating
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes (from master)
// - PWUSER: User-defined write data attributes (from master)
// - PRUSER: User-defined read data attributes (to master)
// - PBUSER: User-defined response attributes (to master)
// - PWAKEUP: Wake-up signal (to master)
// - Optional parity support for data integrity
// - CDC handshake for crossing clock domains
// - Clock gating for power reduction during idle
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-23

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_slave_cdc_cg #(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int STRB_WIDTH          = DATA_WIDTH / 8,
    parameter int PROT_WIDTH          = 3,
    parameter int AUSER_WIDTH         = 4,
    parameter int WUSER_WIDTH         = 4,
    parameter int RUSER_WIDTH         = 4,
    parameter int BUSER_WIDTH         = 4,
    parameter int DEPTH               = 2,
    parameter bit ENABLE_PARITY       = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + AUW + WUW + 1,
    parameter int RPW = DW + RUW + BUW + 1
) (
    // APB Clock Domain
    input  logic              pclk,
    input  logic              presetn,

    // User Clock Domain
    input  logic              aclk,
    input  logic              aresetn,

    // Clock gating configuration
    input  logic              cfg_cg_enable,
    input  logic [ICW-1:0]    cfg_cg_idle_count,

    // APB5 interface (slave side - pclk domain)
    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [AW-1:0]     s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [SW-1:0]     s_apb_PSTRB,
    input  logic [PW-1:0]     s_apb_PPROT,
    input  logic [AUW-1:0]    s_apb_PAUSER,
    input  logic [WUW-1:0]    s_apb_PWUSER,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR,
    output logic              s_apb_PWAKEUP,
    output logic [RUW-1:0]    s_apb_PRUSER,
    output logic [BUW-1:0]    s_apb_PBUSER,

    // Optional parity signals (active when ENABLE_PARITY=1)
    input  logic [SW-1:0]     s_apb_PWDATAPARITY,
    input  logic              s_apb_PADDRPARITY,
    input  logic              s_apb_PCTRLPARITY,
    output logic [SW-1:0]     s_apb_PRDATAPARITY,
    output logic              s_apb_PREADYPARITY,
    output logic              s_apb_PSLVERRPARITY,

    // Command Interface (aclk domain)
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_pwrite,
    output logic [AW-1:0]     cmd_paddr,
    output logic [DW-1:0]     cmd_pwdata,
    output logic [SW-1:0]     cmd_pstrb,
    output logic [PW-1:0]     cmd_pprot,
    output logic [AUW-1:0]    cmd_pauser,
    output logic [WUW-1:0]    cmd_pwuser,

    // Response Interface (aclk domain)
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [DW-1:0]     rsp_prdata,
    input  logic              rsp_pslverr,
    input  logic [RUW-1:0]    rsp_pruser,
    input  logic [BUW-1:0]    rsp_pbuser,

    // Wake-up control (aclk domain)
    input  logic              wakeup_request,

    // Parity error flags (aclk domain, active when ENABLE_PARITY=1)
    output logic              parity_error_wdata,
    output logic              parity_error_ctrl,

    // Clock gating indicator
    output logic              apb_clock_gating
);

    // Local clock gating signals
    logic r_wakeup;
    logic gated_pclk;

    `ALWAYS_FF_RST(pclk, presetn,
        if (!presetn)
            r_wakeup <= 1'b1;
        else
            // Keep active when APB transaction in progress, command/response activity,
            // or when wakeup is requested
            r_wakeup <= s_apb_PSEL || s_apb_PENABLE || cmd_valid || rsp_valid || wakeup_request;
    )

    // Instantiate clock gate controller for pclk domain
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) amba_clock_gate_ctrl (
        .clk_in              (pclk),
        .aresetn             (presetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (r_wakeup),
        .axi_valid           ('b0),
        .clk_out             (gated_pclk),
        .gating              (apb_clock_gating),
        /* verilator lint_off PINCONNECTEMPTY */
        .idle                ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Instantiate APB5 slave with CDC (uses gated pclk)
    apb5_slave_cdc #(
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (DATA_WIDTH),
        .STRB_WIDTH    (STRB_WIDTH),
        .PROT_WIDTH    (PROT_WIDTH),
        .AUSER_WIDTH   (AUSER_WIDTH),
        .WUSER_WIDTH   (WUSER_WIDTH),
        .RUSER_WIDTH   (RUSER_WIDTH),
        .BUSER_WIDTH   (BUSER_WIDTH),
        .DEPTH         (DEPTH),
        .ENABLE_PARITY (ENABLE_PARITY)
    ) u_apb5_slave_cdc (
        // APB Clock Domain (gated)
        .pclk              (gated_pclk),
        .presetn           (presetn),

        // User Clock Domain
        .aclk              (aclk),
        .aresetn           (aresetn),

        // APB5 interface
        .s_apb_PSEL        (s_apb_PSEL),
        .s_apb_PENABLE     (s_apb_PENABLE),
        .s_apb_PREADY      (s_apb_PREADY),
        .s_apb_PADDR       (s_apb_PADDR),
        .s_apb_PWRITE      (s_apb_PWRITE),
        .s_apb_PWDATA      (s_apb_PWDATA),
        .s_apb_PSTRB       (s_apb_PSTRB),
        .s_apb_PPROT       (s_apb_PPROT),
        .s_apb_PAUSER      (s_apb_PAUSER),
        .s_apb_PWUSER      (s_apb_PWUSER),
        .s_apb_PRDATA      (s_apb_PRDATA),
        .s_apb_PSLVERR     (s_apb_PSLVERR),
        .s_apb_PWAKEUP     (s_apb_PWAKEUP),
        .s_apb_PRUSER      (s_apb_PRUSER),
        .s_apb_PBUSER      (s_apb_PBUSER),

        // Parity signals
        .s_apb_PWDATAPARITY  (s_apb_PWDATAPARITY),
        .s_apb_PADDRPARITY   (s_apb_PADDRPARITY),
        .s_apb_PCTRLPARITY   (s_apb_PCTRLPARITY),
        .s_apb_PRDATAPARITY  (s_apb_PRDATAPARITY),
        .s_apb_PREADYPARITY  (s_apb_PREADYPARITY),
        .s_apb_PSLVERRPARITY (s_apb_PSLVERRPARITY),

        // Command Interface
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_pwrite        (cmd_pwrite),
        .cmd_paddr         (cmd_paddr),
        .cmd_pwdata        (cmd_pwdata),
        .cmd_pstrb         (cmd_pstrb),
        .cmd_pprot         (cmd_pprot),
        .cmd_pauser        (cmd_pauser),
        .cmd_pwuser        (cmd_pwuser),

        // Response Interface
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_prdata        (rsp_prdata),
        .rsp_pslverr       (rsp_pslverr),
        .rsp_pruser        (rsp_pruser),
        .rsp_pbuser        (rsp_pbuser),

        // Wake-up control
        .wakeup_request    (wakeup_request),

        // Parity error flags
        .parity_error_wdata(parity_error_wdata),
        .parity_error_ctrl (parity_error_ctrl)
    );

endmodule : apb5_slave_cdc_cg
