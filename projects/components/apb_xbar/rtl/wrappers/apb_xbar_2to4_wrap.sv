// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_2to4_wrap
// Purpose: Apb Xbar 2To4 Wrap module
//
// Documentation: PRD.md
// Subsystem: integ_amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Test wrapper for 2-to-4 APB crossbar
// Two masters, four slaves for arbitration and address decode testing

module apb_xbar_2to4_wrap #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'h1000_0000
) (
    input  logic pclk,
    input  logic presetn
);

    localparam int STRB_WIDTH = DATA_WIDTH / 8;

    // Master 0 APB interface
    logic                  m0_apb_PSEL;
    logic                  m0_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] m0_apb_PADDR;
    logic                  m0_apb_PWRITE;
    logic [DATA_WIDTH-1:0] m0_apb_PWDATA;
    logic [STRB_WIDTH-1:0] m0_apb_PSTRB;
    logic [2:0]            m0_apb_PPROT;
    logic [DATA_WIDTH-1:0] m0_apb_PRDATA;
    logic                  m0_apb_PSLVERR;
    logic                  m0_apb_PREADY;

    // Master 1 APB interface
    logic                  m1_apb_PSEL;
    logic                  m1_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] m1_apb_PADDR;
    logic                  m1_apb_PWRITE;
    logic [DATA_WIDTH-1:0] m1_apb_PWDATA;
    logic [STRB_WIDTH-1:0] m1_apb_PSTRB;
    logic [2:0]            m1_apb_PPROT;
    logic [DATA_WIDTH-1:0] m1_apb_PRDATA;
    logic                  m1_apb_PSLVERR;
    logic                  m1_apb_PREADY;

    // Slave 0 APB interface
    logic                  s0_apb_PSEL;
    logic                  s0_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] s0_apb_PADDR;
    logic                  s0_apb_PWRITE;
    logic [DATA_WIDTH-1:0] s0_apb_PWDATA;
    logic [STRB_WIDTH-1:0] s0_apb_PSTRB;
    logic [2:0]            s0_apb_PPROT;
    logic [DATA_WIDTH-1:0] s0_apb_PRDATA;
    logic                  s0_apb_PSLVERR;
    logic                  s0_apb_PREADY;

    // Slave 1 APB interface
    logic                  s1_apb_PSEL;
    logic                  s1_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] s1_apb_PADDR;
    logic                  s1_apb_PWRITE;
    logic [DATA_WIDTH-1:0] s1_apb_PWDATA;
    logic [STRB_WIDTH-1:0] s1_apb_PSTRB;
    logic [2:0]            s1_apb_PPROT;
    logic [DATA_WIDTH-1:0] s1_apb_PRDATA;
    logic                  s1_apb_PSLVERR;
    logic                  s1_apb_PREADY;

    // Slave 2 APB interface
    logic                  s2_apb_PSEL;
    logic                  s2_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] s2_apb_PADDR;
    logic                  s2_apb_PWRITE;
    logic [DATA_WIDTH-1:0] s2_apb_PWDATA;
    logic [STRB_WIDTH-1:0] s2_apb_PSTRB;
    logic [2:0]            s2_apb_PPROT;
    logic [DATA_WIDTH-1:0] s2_apb_PRDATA;
    logic                  s2_apb_PSLVERR;
    logic                  s2_apb_PREADY;

    // Slave 3 APB interface
    logic                  s3_apb_PSEL;
    logic                  s3_apb_PENABLE;
    logic [ADDR_WIDTH-1:0] s3_apb_PADDR;
    logic                  s3_apb_PWRITE;
    logic [DATA_WIDTH-1:0] s3_apb_PWDATA;
    logic [STRB_WIDTH-1:0] s3_apb_PSTRB;
    logic [2:0]            s3_apb_PPROT;
    logic [DATA_WIDTH-1:0] s3_apb_PRDATA;
    logic                  s3_apb_PSLVERR;
    logic                  s3_apb_PREADY;

    // Instantiate 2-to-4 crossbar
    apb_xbar_2to4 #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .BASE_ADDR  (BASE_ADDR)
    ) u_xbar (
        .pclk          (pclk),
        .presetn       (presetn),
        // Master 0
        .m0_apb_PSEL    (m0_apb_PSEL),
        .m0_apb_PENABLE (m0_apb_PENABLE),
        .m0_apb_PADDR   (m0_apb_PADDR),
        .m0_apb_PWRITE  (m0_apb_PWRITE),
        .m0_apb_PWDATA  (m0_apb_PWDATA),
        .m0_apb_PSTRB   (m0_apb_PSTRB),
        .m0_apb_PPROT   (m0_apb_PPROT),
        .m0_apb_PRDATA  (m0_apb_PRDATA),
        .m0_apb_PSLVERR (m0_apb_PSLVERR),
        .m0_apb_PREADY  (m0_apb_PREADY),
        // Master 1
        .m1_apb_PSEL    (m1_apb_PSEL),
        .m1_apb_PENABLE (m1_apb_PENABLE),
        .m1_apb_PADDR   (m1_apb_PADDR),
        .m1_apb_PWRITE  (m1_apb_PWRITE),
        .m1_apb_PWDATA  (m1_apb_PWDATA),
        .m1_apb_PSTRB   (m1_apb_PSTRB),
        .m1_apb_PPROT   (m1_apb_PPROT),
        .m1_apb_PRDATA  (m1_apb_PRDATA),
        .m1_apb_PSLVERR (m1_apb_PSLVERR),
        .m1_apb_PREADY  (m1_apb_PREADY),
        // Slave 0
        .s0_apb_PSEL    (s0_apb_PSEL),
        .s0_apb_PENABLE (s0_apb_PENABLE),
        .s0_apb_PADDR   (s0_apb_PADDR),
        .s0_apb_PWRITE  (s0_apb_PWRITE),
        .s0_apb_PWDATA  (s0_apb_PWDATA),
        .s0_apb_PSTRB   (s0_apb_PSTRB),
        .s0_apb_PPROT   (s0_apb_PPROT),
        .s0_apb_PRDATA  (s0_apb_PRDATA),
        .s0_apb_PSLVERR (s0_apb_PSLVERR),
        .s0_apb_PREADY  (s0_apb_PREADY),
        // Slave 1
        .s1_apb_PSEL    (s1_apb_PSEL),
        .s1_apb_PENABLE (s1_apb_PENABLE),
        .s1_apb_PADDR   (s1_apb_PADDR),
        .s1_apb_PWRITE  (s1_apb_PWRITE),
        .s1_apb_PWDATA  (s1_apb_PWDATA),
        .s1_apb_PSTRB   (s1_apb_PSTRB),
        .s1_apb_PPROT   (s1_apb_PPROT),
        .s1_apb_PRDATA  (s1_apb_PRDATA),
        .s1_apb_PSLVERR (s1_apb_PSLVERR),
        .s1_apb_PREADY  (s1_apb_PREADY),
        // Slave 2
        .s2_apb_PSEL    (s2_apb_PSEL),
        .s2_apb_PENABLE (s2_apb_PENABLE),
        .s2_apb_PADDR   (s2_apb_PADDR),
        .s2_apb_PWRITE  (s2_apb_PWRITE),
        .s2_apb_PWDATA  (s2_apb_PWDATA),
        .s2_apb_PSTRB   (s2_apb_PSTRB),
        .s2_apb_PPROT   (s2_apb_PPROT),
        .s2_apb_PRDATA  (s2_apb_PRDATA),
        .s2_apb_PSLVERR (s2_apb_PSLVERR),
        .s2_apb_PREADY  (s2_apb_PREADY),
        // Slave 3
        .s3_apb_PSEL    (s3_apb_PSEL),
        .s3_apb_PENABLE (s3_apb_PENABLE),
        .s3_apb_PADDR   (s3_apb_PADDR),
        .s3_apb_PWRITE  (s3_apb_PWRITE),
        .s3_apb_PWDATA  (s3_apb_PWDATA),
        .s3_apb_PSTRB   (s3_apb_PSTRB),
        .s3_apb_PPROT   (s3_apb_PPROT),
        .s3_apb_PRDATA  (s3_apb_PRDATA),
        .s3_apb_PSLVERR (s3_apb_PSLVERR),
        .s3_apb_PREADY  (s3_apb_PREADY)
    );

endmodule : apb_xbar_2to4_wrap
