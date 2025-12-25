// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb5_master_stub
// Purpose: APB5 Master Stub for packed command/response interface testing
//
// APB5 Extensions:
// - PAUSER: User-defined request attributes
// - PWUSER: User-defined write data attributes
// - PWAKEUP: Wake-up signal handling (input from slave)
// - Optional parity support for data integrity
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-23

`timescale 1ns / 1ps

module apb5_master_stub #(
    parameter int CMD_DEPTH         = 6,
    parameter int RSP_DEPTH         = 6,
    parameter int DATA_WIDTH        = 32,
    parameter int ADDR_WIDTH        = 32,
    parameter int PROT_WIDTH        = 3,
    parameter int AUSER_WIDTH       = 4,
    parameter int WUSER_WIDTH       = 4,
    parameter int RUSER_WIDTH       = 4,
    parameter int BUSER_WIDTH       = 4,
    parameter bit ENABLE_PARITY     = 0,
    parameter int STRB_WIDTH        = DATA_WIDTH / 8,
    // Command packet: addr, data, strb, prot, pwrite, pauser, pwuser, first, last
    parameter int CMD_PACKET_WIDTH  = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + PROT_WIDTH +
                                      AUSER_WIDTH + WUSER_WIDTH + 1 + 1 + 1,
    // Response packet: data, ruser, buser, wakeup, pslverr, first, last
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + RUSER_WIDTH + BUSER_WIDTH + 1 + 1 + 1 + 1,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int AUW = AUSER_WIDTH,
    parameter int WUW = WUSER_WIDTH,
    parameter int RUW = RUSER_WIDTH,
    parameter int BUW = BUSER_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH
) (
    // Clock and Reset
    input  logic                         pclk,
    input  logic                         presetn,

    // APB5 interface
    output logic                         m_apb_PSEL,
    output logic                         m_apb_PENABLE,
    output logic [AW-1:0]                m_apb_PADDR,
    output logic                         m_apb_PWRITE,
    output logic [DW-1:0]                m_apb_PWDATA,
    output logic [SW-1:0]                m_apb_PSTRB,
    output logic [PW-1:0]                m_apb_PPROT,
    output logic [AUW-1:0]               m_apb_PAUSER,
    output logic [WUW-1:0]               m_apb_PWUSER,
    input  logic [DW-1:0]                m_apb_PRDATA,
    input  logic                         m_apb_PSLVERR,
    input  logic                         m_apb_PREADY,
    input  logic                         m_apb_PWAKEUP,
    input  logic [RUW-1:0]               m_apb_PRUSER,
    input  logic [BUW-1:0]               m_apb_PBUSER,

    // Optional parity signals (active when ENABLE_PARITY=1)
    output logic [SW-1:0]                m_apb_PWDATAPARITY,
    output logic                         m_apb_PADDRPARITY,
    output logic                         m_apb_PCTRLPARITY,
    input  logic [SW-1:0]                m_apb_PRDATAPARITY,
    input  logic                         m_apb_PREADYPARITY,
    input  logic                         m_apb_PSLVERRPARITY,

    // Command Packet (packed)
    input  logic                         cmd_valid,
    output logic                         cmd_ready,
    input  logic [CPW-1:0]               cmd_data,

    // Response Packet (packed)
    output logic                         rsp_valid,
    input  logic                         rsp_ready,
    output logic [RPW-1:0]               rsp_data,

    // Parity error flags (active when ENABLE_PARITY=1)
    output logic                         parity_error_rdata,
    output logic                         parity_error_ctrl,

    // Wake-up status
    output logic                         wakeup_pending
);

    // Unpack command packet
    logic [DW-1:0]       cmd_pwdata;
    logic [AW-1:0]       cmd_paddr;
    logic [SW-1:0]       cmd_pstrb;
    logic [PW-1:0]       cmd_pprot;
    logic [AUW-1:0]      cmd_pauser;
    logic [WUW-1:0]      cmd_pwuser;
    logic                cmd_pwrite;
    logic                cmd_first;
    logic                cmd_last;

    assign {cmd_last, cmd_first, cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata,
            cmd_pauser, cmd_pwuser} = cmd_data;

    // Response signals from apb5_master
    logic [DW-1:0]       rsp_prdata;
    logic                rsp_pslverr;
    logic                rsp_pwakeup;
    logic [RUW-1:0]      rsp_pruser;
    logic [BUW-1:0]      rsp_pbuser;

    // Pack response packet (include first/last from command)
    assign rsp_data = {cmd_last, cmd_first, rsp_pslverr, rsp_pwakeup, rsp_prdata,
                       rsp_pruser, rsp_pbuser};

    // Instantiate fully-tested apb5_master
    apb5_master #(
        .ADDR_WIDTH    (ADDR_WIDTH),
        .DATA_WIDTH    (DATA_WIDTH),
        .PROT_WIDTH    (PROT_WIDTH),
        .AUSER_WIDTH   (AUSER_WIDTH),
        .WUSER_WIDTH   (WUSER_WIDTH),
        .RUSER_WIDTH   (RUSER_WIDTH),
        .BUSER_WIDTH   (BUSER_WIDTH),
        .CMD_DEPTH     (CMD_DEPTH),
        .RSP_DEPTH     (RSP_DEPTH),
        .ENABLE_PARITY (ENABLE_PARITY),
        .STRB_WIDTH    (STRB_WIDTH)
    ) u_apb5_master (
        .pclk               (pclk),
        .presetn            (presetn),
        // APB5 interface
        .m_apb_PSEL         (m_apb_PSEL),
        .m_apb_PENABLE      (m_apb_PENABLE),
        .m_apb_PADDR        (m_apb_PADDR),
        .m_apb_PWRITE       (m_apb_PWRITE),
        .m_apb_PWDATA       (m_apb_PWDATA),
        .m_apb_PSTRB        (m_apb_PSTRB),
        .m_apb_PPROT        (m_apb_PPROT),
        .m_apb_PAUSER       (m_apb_PAUSER),
        .m_apb_PWUSER       (m_apb_PWUSER),
        .m_apb_PRDATA       (m_apb_PRDATA),
        .m_apb_PSLVERR      (m_apb_PSLVERR),
        .m_apb_PREADY       (m_apb_PREADY),
        .m_apb_PWAKEUP      (m_apb_PWAKEUP),
        .m_apb_PRUSER       (m_apb_PRUSER),
        .m_apb_PBUSER       (m_apb_PBUSER),
        // Parity signals
        .m_apb_PWDATAPARITY (m_apb_PWDATAPARITY),
        .m_apb_PADDRPARITY  (m_apb_PADDRPARITY),
        .m_apb_PCTRLPARITY  (m_apb_PCTRLPARITY),
        .m_apb_PRDATAPARITY (m_apb_PRDATAPARITY),
        .m_apb_PREADYPARITY (m_apb_PREADYPARITY),
        .m_apb_PSLVERRPARITY(m_apb_PSLVERRPARITY),
        // Command interface (unpacked)
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),
        .cmd_pprot          (cmd_pprot),
        .cmd_pauser         (cmd_pauser),
        .cmd_pwuser         (cmd_pwuser),
        // Response interface (unpacked)
        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),
        .rsp_pwakeup        (rsp_pwakeup),
        .rsp_pruser         (rsp_pruser),
        .rsp_pbuser         (rsp_pbuser),
        // Parity error flags
        .parity_error_rdata (parity_error_rdata),
        .parity_error_ctrl  (parity_error_ctrl),
        // Wake-up status
        .wakeup_pending     (wakeup_pending)
    );

endmodule : apb5_master_stub
