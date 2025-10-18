// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_master_stub
// Purpose: Apb Master Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb_master_stub #(
    parameter int CMD_DEPTH         = 6,
    parameter int RSP_DEPTH         = 6,
    parameter int DATA_WIDTH        = 32,
    parameter int ADDR_WIDTH        = 32,
    parameter int STRB_WIDTH        = DATA_WIDTH / 8,
    parameter int CMD_PACKET_WIDTH  = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 3 + 1 + 1 + 1,
                                        // addr, data, strb, prot, pwrite, first, last
    parameter int RESP_PACKET_WIDTH = DATA_WIDTH + 1 + 1 +  1, // data, pslverr, first, last
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int CPW = CMD_PACKET_WIDTH,
    parameter int RPW = RESP_PACKET_WIDTH
) (
    // Clock and Reset
    input  logic                         pclk,
    input  logic                         presetn,

    // APB interface
    output logic                         m_apb_PSEL,
    output logic                         m_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0]        m_apb_PADDR,
    output logic                         m_apb_PWRITE,
    output logic [DATA_WIDTH-1:0]        m_apb_PWDATA,
    output logic [STRB_WIDTH-1:0]        m_apb_PSTRB,
    output logic [2:0]                   m_apb_PPROT,
    input  logic [DATA_WIDTH-1:0]        m_apb_PRDATA,
    input  logic                         m_apb_PSLVERR,
    input  logic                         m_apb_PREADY,

    // Command Packet (packed)
    input  logic                         cmd_valid,
    output logic                         cmd_ready,
    input  logic [CMD_PACKET_WIDTH-1:0]  cmd_data,

    // Read Return interface (packed)
    output logic                         rsp_valid,
    input  logic                         rsp_ready,
    output logic [RESP_PACKET_WIDTH-1:0] rsp_data
);

    // Unpack command packet
    logic [DW-1:0]       cmd_pwdata;
    logic [AW-1:0]       cmd_paddr;
    logic [SW-1:0]       cmd_pstrb;
    logic [2:0]          cmd_pprot;
    logic                cmd_pwrite;
    logic                cmd_first;
    logic                cmd_last;

    assign {cmd_last, cmd_first, cmd_pwrite, cmd_pprot, cmd_pstrb, cmd_paddr, cmd_pwdata} = cmd_data;

    // Response signals from apb_master
    logic [DW-1:0]       rsp_prdata;
    logic                rsp_pslverr;

    // Pack response packet (include first/last from command)
    assign rsp_data = {cmd_last, cmd_first, rsp_pslverr, rsp_prdata};

    // Instantiate fully-tested apb_master
    apb_master #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .DATA_WIDTH  (DATA_WIDTH),
        .CMD_DEPTH   (CMD_DEPTH),
        .RSP_DEPTH   (RSP_DEPTH)
    ) u_apb_master (
        .pclk           (pclk),
        .presetn        (presetn),
        // APB interface
        .m_apb_PSEL     (m_apb_PSEL),
        .m_apb_PENABLE  (m_apb_PENABLE),
        .m_apb_PADDR    (m_apb_PADDR),
        .m_apb_PWRITE   (m_apb_PWRITE),
        .m_apb_PWDATA   (m_apb_PWDATA),
        .m_apb_PSTRB    (m_apb_PSTRB),
        .m_apb_PPROT    (m_apb_PPROT),
        .m_apb_PRDATA   (m_apb_PRDATA),
        .m_apb_PSLVERR  (m_apb_PSLVERR),
        .m_apb_PREADY   (m_apb_PREADY),
        // Command interface (unpacked)
        .cmd_valid      (cmd_valid),
        .cmd_ready      (cmd_ready),
        .cmd_pwrite     (cmd_pwrite),
        .cmd_paddr      (cmd_paddr),
        .cmd_pwdata     (cmd_pwdata),
        .cmd_pstrb      (cmd_pstrb),
        .cmd_pprot      (cmd_pprot),
        // Response interface (unpacked)
        .rsp_valid      (rsp_valid),
        .rsp_ready      (rsp_ready),
        .rsp_prdata     (rsp_prdata),
        .rsp_pslverr    (rsp_pslverr)
    );

endmodule : apb_master_stub
