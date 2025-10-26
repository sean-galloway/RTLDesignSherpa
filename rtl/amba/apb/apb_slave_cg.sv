// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_slave_cg
// Purpose: Apb Slave Cg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_slave_cg #(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int STRB_WIDTH      = 32 / 8,
    parameter int PROT_WIDTH      = 3,
    parameter int DEPTH      = 2,
    parameter int CG_IDLE_COUNT_WIDTH = 4,  // Default width of idle counter
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
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
    input logic               cfg_cg_enable,     // Global clock gate enable
    input logic  [ICW-1:0]    cfg_cg_idle_count, // Idle countdown value

    // APB interface
    input  logic              s_apb_PSEL,
    input  logic              s_apb_PENABLE,
    output logic              s_apb_PREADY,
    input  logic [AW-1:0]     s_apb_PADDR,
    input  logic              s_apb_PWRITE,
    input  logic [DW-1:0]     s_apb_PWDATA,
    input  logic [SW-1:0]     s_apb_PSTRB,
    input  logic [PW-1:0]     s_apb_PPROT,
    output logic [DW-1:0]     s_apb_PRDATA,
    output logic              s_apb_PSLVERR,

    // Command Interface
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_pwrite,
    output logic [AW-1:0]     cmd_paddr,
    output logic [DW-1:0]     cmd_pwdata,
    output logic [SW-1:0]     cmd_pstrb,
    output logic [PW-1:0]     cmd_pprot,

    // Response Interface
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [DW-1:0]     rsp_prdata,
    input  logic              rsp_pslverr,
    // Clock gating indicator
    output logic              apb_clock_gating
);

    // local clock gating signals
    logic  r_wakeup;
    logic  gated_pclk;

    `ALWAYS_FF_RST(pclk, presetn,
        if (!presetn)
            r_wakeup <= 1'b1;
        else
            // Keep active when APB transaction in progress or command/response activity
            r_wakeup <= s_apb_PSEL || s_apb_PENABLE || cmd_valid || rsp_valid;
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
        /* verilator lint_off PINCONNECTEMPTY */
        .idle                ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    apb_slave #(
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH),
        .STRB_WIDTH       (STRB_WIDTH),
        .PROT_WIDTH       (PROT_WIDTH),
        .DEPTH            (DEPTH)
    ) u_apb_slave(
        // Clock / Reset
        .pclk             (gated_pclk),
        .presetn          (presetn),
        // APB interface
        .s_apb_PSEL       (s_apb_PSEL),
        .s_apb_PENABLE    (s_apb_PENABLE),
        .s_apb_PREADY     (s_apb_PREADY),
        .s_apb_PADDR      (s_apb_PADDR),
        .s_apb_PWRITE     (s_apb_PWRITE),
        .s_apb_PWDATA     (s_apb_PWDATA),
        .s_apb_PSTRB      (s_apb_PSTRB),
        .s_apb_PPROT      (s_apb_PPROT),
        .s_apb_PRDATA     (s_apb_PRDATA),
        .s_apb_PSLVERR    (s_apb_PSLVERR),
        // Command interface
        .cmd_valid        (cmd_valid),
        .cmd_ready        (cmd_ready),
        .cmd_pwrite       (cmd_pwrite),
        .cmd_paddr        (cmd_paddr),
        .cmd_pwdata       (cmd_pwdata),
        .cmd_pstrb        (cmd_pstrb),
        .cmd_pprot        (cmd_pprot),
        // Response interface
        .rsp_valid        (rsp_valid),
        .rsp_ready        (rsp_ready),
        .rsp_prdata       (rsp_prdata),
        .rsp_pslverr      (rsp_pslverr)
    );

endmodule : apb_slave_cg
