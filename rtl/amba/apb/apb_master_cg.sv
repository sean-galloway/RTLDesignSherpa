// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_master_cg
// Purpose: Apb Master Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_master_cg #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int PROT_WIDTH      = 3,
    parameter int CMD_DEPTH       = 6,
    parameter int RSP_DEPTH       = 6,
    parameter int STRB_WIDTH      = DATA_WIDTH / 8,
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Default width of idle counter
    // Short Parameters
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int ICW = CG_IDLE_COUNT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1,
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              pclk,
    input  logic              presetn,

    // Configs
    input  logic              cfg_cg_enable,     // Global clock gate enable
    input  logic [ICW-1:0]    cfg_cg_idle_count, // Idle countdown value

    // APB interface
    output logic              m_apb_PSEL,
    output logic              m_apb_PENABLE,
    output logic [AW-1:0]     m_apb_PADDR,
    output logic              m_apb_PWRITE,
    output logic [DW-1:0]     m_apb_PWDATA,
    output logic [SW-1:0]     m_apb_PSTRB,
    output logic [PW-1:0]     m_apb_PPROT,
    input  logic [DW-1:0]     m_apb_PRDATA,
    input  logic              m_apb_PSLVERR,
    input  logic              m_apb_PREADY,

    // Command Packet
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic              cmd_pwrite,
    input  logic [AW-1:0]     cmd_paddr,
    input  logic [DW-1:0]     cmd_pwdata,
    input  logic [SW-1:0]     cmd_pstrb,
    input  logic [PW-1:0]     cmd_pprot,

    // Read Return interface
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [DW-1:0]     rsp_prdata,
    output logic              rsp_pslverr,

    // Clock gating indicator
    output logic              apb_clock_gating
);

    // Local clock gating signals
    logic  r_wakeup;
    logic  gated_pclk;

    `ALWAYS_FF_RST(pclk, presetn,
        if (!presetn)
            r_wakeup <= 1'b1;
        else
            // Wake up when there's a command, a response pending,
            // or when the master is in the middle of a transaction
            r_wakeup <= cmd_valid || rsp_valid || m_apb_PSEL || m_apb_PENABLE;
    )


    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH (CG_IDLE_COUNT_WIDTH)
    ) amba_clock_gate_ctrl(
        .clk_in              (pclk),
        .aresetn             (presetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (r_wakeup),
        .axi_valid           ('b0),
        .clk_out             (gated_pclk),
        .gating              (apb_clock_gating),
        .idle                ()
    );

    // Instantiate the APB master
    apb_master #(
        .ADDR_WIDTH        (ADDR_WIDTH),
        .DATA_WIDTH        (DATA_WIDTH),
        .PROT_WIDTH        (PROT_WIDTH),
        .CMD_DEPTH         (CMD_DEPTH),
        .RSP_DEPTH         (RSP_DEPTH),
        .STRB_WIDTH        (STRB_WIDTH)
    ) u_apb_master(
        // Clock / Reset
        .pclk              (gated_pclk),
        .presetn           (presetn),
        // APB interface
        .m_apb_PSEL        (m_apb_PSEL),
        .m_apb_PENABLE     (m_apb_PENABLE),
        .m_apb_PADDR       (m_apb_PADDR),
        .m_apb_PWRITE      (m_apb_PWRITE),
        .m_apb_PWDATA      (m_apb_PWDATA),
        .m_apb_PSTRB       (m_apb_PSTRB),
        .m_apb_PPROT       (m_apb_PPROT),
        .m_apb_PRDATA      (m_apb_PRDATA),
        .m_apb_PSLVERR     (m_apb_PSLVERR),
        .m_apb_PREADY      (m_apb_PREADY),
        // Command interface
        .cmd_valid         (cmd_valid),
        .cmd_ready         (cmd_ready),
        .cmd_pwrite        (cmd_pwrite),
        .cmd_paddr         (cmd_paddr),
        .cmd_pwdata        (cmd_pwdata),
        .cmd_pstrb         (cmd_pstrb),
        .cmd_pprot         (cmd_pprot),
        // Response interface
        .rsp_valid         (rsp_valid),
        .rsp_ready         (rsp_ready),
        .rsp_prdata        (rsp_prdata),
        .rsp_pslverr       (rsp_pslverr)
    );

endmodule : apb_master_cg
