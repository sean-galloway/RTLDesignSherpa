// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_master_cg
// Purpose: APB5 Master with Clock Gating for power management
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes
// - PWUSER: User-defined write data attributes
// - PWAKEUP: Wake-up signal handling (input from slave)
// - Optional parity support for data integrity
// - Clock gating for power reduction during idle
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-23

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb5_master_cg #(
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter int PROT_WIDTH          = 3,
    parameter int AUSER_WIDTH         = 4,
    parameter int WUSER_WIDTH         = 4,
    parameter int RUSER_WIDTH         = 4,
    parameter int BUSER_WIDTH         = 4,
    parameter int CMD_DEPTH           = 6,
    parameter int RSP_DEPTH           = 6,
    parameter bit ENABLE_PARITY       = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,
    parameter int STRB_WIDTH          = DATA_WIDTH / 8,
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + AUW + WUW + 1,
    parameter int RPW = DW + RUW + BUW + 2
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // Clock gating configuration
    input  logic              cfg_cg_enable,
    input  logic [ICW-1:0]    cfg_cg_idle_count,

    // APB5 interface (master side)
    output logic              m_apb_PSEL,
    output logic              m_apb_PENABLE,
    output logic [AW-1:0]     m_apb_PADDR,
    output logic              m_apb_PWRITE,
    output logic [DW-1:0]     m_apb_PWDATA,
    output logic [SW-1:0]     m_apb_PSTRB,
    output logic [PW-1:0]     m_apb_PPROT,
    output logic [AUW-1:0]    m_apb_PAUSER,
    output logic [WUW-1:0]    m_apb_PWUSER,
    input  logic [DW-1:0]     m_apb_PRDATA,
    input  logic              m_apb_PSLVERR,
    input  logic              m_apb_PREADY,
    input  logic              m_apb_PWAKEUP,
    input  logic [RUW-1:0]    m_apb_PRUSER,
    input  logic [BUW-1:0]    m_apb_PBUSER,

    // Optional parity signals (active when ENABLE_PARITY=1)
    output logic [SW-1:0]     m_apb_PWDATAPARITY,
    output logic              m_apb_PADDRPARITY,
    output logic              m_apb_PCTRLPARITY,
    input  logic [SW-1:0]     m_apb_PRDATAPARITY,
    input  logic              m_apb_PREADYPARITY,
    input  logic              m_apb_PSLVERRPARITY,

    // Command Packet interface
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_pwrite,
    input  logic [AW-1:0]     cmd_paddr,
    input  logic [DW-1:0]     cmd_pwdata,
    input  logic [SW-1:0]     cmd_pstrb,
    input  logic [PW-1:0]     cmd_pprot,
    input  logic [AUW-1:0]    cmd_pauser,
    input  logic [WUW-1:0]    cmd_pwuser,

    // Response interface
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [DW-1:0]     rsp_prdata,
    output logic              rsp_pslverr,
    output logic              rsp_pwakeup,
    output logic [RUW-1:0]    rsp_pruser,
    output logic [BUW-1:0]    rsp_pbuser,

    // Parity error flags (active when ENABLE_PARITY=1)
    output logic              parity_error_rdata,
    output logic              parity_error_ctrl,

    // Wake-up status
    output logic              wakeup_pending,

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
            // Wake up when there's a command, a response pending,
            // when the master is in the middle of a transaction,
            // or when the slave requests wakeup
            r_wakeup <= cmd_valid || rsp_valid || m_apb_PSEL || m_apb_PENABLE || m_apb_PWAKEUP;
    )

    // Instantiate clock gate controller
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

    // Instantiate the APB5 master
    apb5_master #(
        .ADDR_WIDTH        (ADDR_WIDTH),
        .DATA_WIDTH        (DATA_WIDTH),
        .PROT_WIDTH        (PROT_WIDTH),
        .AUSER_WIDTH       (AUSER_WIDTH),
        .WUSER_WIDTH       (WUSER_WIDTH),
        .RUSER_WIDTH       (RUSER_WIDTH),
        .BUSER_WIDTH       (BUSER_WIDTH),
        .CMD_DEPTH         (CMD_DEPTH),
        .RSP_DEPTH         (RSP_DEPTH),
        .ENABLE_PARITY     (ENABLE_PARITY),
        .STRB_WIDTH        (STRB_WIDTH)
    ) u_apb5_master (
        // Clock / Reset
        .pclk              (gated_pclk),
        .presetn           (presetn),
        // APB5 interface
        .m_apb_PSEL        (m_apb_PSEL),
        .m_apb_PENABLE     (m_apb_PENABLE),
        .m_apb_PADDR       (m_apb_PADDR),
        .m_apb_PWRITE      (m_apb_PWRITE),
        .m_apb_PWDATA      (m_apb_PWDATA),
        .m_apb_PSTRB       (m_apb_PSTRB),
        .m_apb_PPROT       (m_apb_PPROT),
        .m_apb_PAUSER      (m_apb_PAUSER),
        .m_apb_PWUSER      (m_apb_PWUSER),
        .m_apb_PRDATA      (m_apb_PRDATA),
        .m_apb_PSLVERR     (m_apb_PSLVERR),
        .m_apb_PREADY      (m_apb_PREADY),
        .m_apb_PWAKEUP     (m_apb_PWAKEUP),
        .m_apb_PRUSER      (m_apb_PRUSER),
        .m_apb_PBUSER      (m_apb_PBUSER),
        // Parity signals
        .m_apb_PWDATAPARITY  (m_apb_PWDATAPARITY),
        .m_apb_PADDRPARITY   (m_apb_PADDRPARITY),
        .m_apb_PCTRLPARITY   (m_apb_PCTRLPARITY),
        .m_apb_PRDATAPARITY  (m_apb_PRDATAPARITY),
        .m_apb_PREADYPARITY  (m_apb_PREADYPARITY),
        .m_apb_PSLVERRPARITY (m_apb_PSLVERRPARITY),
        // Command interface
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_pwrite        (cmd_pwrite),
        .cmd_paddr         (cmd_paddr),
        .cmd_pwdata        (cmd_pwdata),
        .cmd_pstrb         (cmd_pstrb),
        .cmd_pprot         (cmd_pprot),
        .cmd_pauser        (cmd_pauser),
        .cmd_pwuser        (cmd_pwuser),
        // Response interface
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_prdata        (rsp_prdata),
        .rsp_pslverr       (rsp_pslverr),
        .rsp_pwakeup       (rsp_pwakeup),
        .rsp_pruser        (rsp_pruser),
        .rsp_pbuser        (rsp_pbuser),
        // Parity error flags
        .parity_error_rdata(parity_error_rdata),
        .parity_error_ctrl (parity_error_ctrl),
        // Wake-up status
        .wakeup_pending    (wakeup_pending)
    );

endmodule : apb5_master_cg
