// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_1to1_wrap
// Purpose: Apb Xbar 1To1 Wrap module
//
// Documentation: PRD.md
// Subsystem: integ_amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Test wrapper for 1-to-1 APB crossbar
// Single master, single slave for basic functional testing

module apb_xbar_1to1_wrap #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input  logic pclk,
    input  logic presetn
);

    localparam int STRB_WIDTH = DATA_WIDTH / 8;

    // Master APB interface
    logic                  m_apb_PSEL;
    logic                  m_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] m_apb_PADDR;
    logic                  m_apb_PWRITE;
    logic [DATA_WIDTH-1:0] m_apb_PWDATA;
    logic [STRB_WIDTH-1:0] m_apb_PSTRB;
    logic [2:0]            m_apb_PPROT;
    logic [DATA_WIDTH-1:0] m_apb_PRDATA;
    logic                  m_apb_PSLVERR;
    logic                  m_apb_PREADY;

    // Slave APB interface
    logic                  s_apb_PSEL;
    logic                  s_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] s_apb_PADDR;
    logic                  s_apb_PWRITE;
    logic [DATA_WIDTH-1:0] s_apb_PWDATA;
    logic [STRB_WIDTH-1:0] s_apb_PSTRB;
    logic [2:0]            s_apb_PPROT;
    logic [DATA_WIDTH-1:0] s_apb_PRDATA;
    logic                  s_apb_PSLVERR;
    logic                  s_apb_PREADY;

    // Instantiate 1-to-1 crossbar
    apb_xbar_1to1 #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH)
    ) u_xbar (
        .pclk          (pclk),
        .presetn       (presetn),
        // Master side
        .m0_apb_PSEL    (m_apb_PSEL),
        .m0_apb_PENABLE (m_apb_PENABLE),
        .m0_apb_PADDR   (m_apb_PADDR),
        .m0_apb_PWRITE  (m_apb_PWRITE),
        .m0_apb_PWDATA  (m_apb_PWDATA),
        .m0_apb_PSTRB   (m_apb_PSTRB),
        .m0_apb_PPROT   (m_apb_PPROT),
        .m0_apb_PRDATA  (m_apb_PRDATA),
        .m0_apb_PSLVERR (m_apb_PSLVERR),
        .m0_apb_PREADY  (m_apb_PREADY),
        // Slave side
        .s0_apb_PSEL    (s_apb_PSEL),
        .s0_apb_PENABLE (s_apb_PENABLE),
        .s0_apb_PADDR   (s_apb_PADDR),
        .s0_apb_PWRITE  (s_apb_PWRITE),
        .s0_apb_PWDATA  (s_apb_PWDATA),
        .s0_apb_PSTRB   (s_apb_PSTRB),
        .s0_apb_PPROT   (s_apb_PPROT),
        .s0_apb_PRDATA  (s_apb_PRDATA),
        .s0_apb_PSLVERR (s_apb_PSLVERR),
        .s0_apb_PREADY  (s_apb_PREADY)
    );

endmodule : apb_xbar_1to1_wrap
