// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apbx_xbar_1to1
// Purpose: Apbx Xbar 1to1 module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

// 1-to-1 APB crossbar with address decoding and arbitration
// 1 master to 1 slave using apb4_slave and apb4_master modules
//
// Address Map (same for all masters):
//   Slave 0: the ONLY slave -- this variant does no address decode.
//   BASE_ADDR is declared for interface uniformity but is UNUSED:
//   every access is forwarded regardless of address.

module apbx_xbar_1to1 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'h10000000
) (
    // Clock and Reset
    input  logic                  pclk,
    input  logic                  presetn,

    // Master 0 APB interface (from external master 0)
    input  logic                  m0_apb_PSEL,
    input  logic                  m0_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] m0_apb_PADDR,
    input  logic                  m0_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0] m0_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0] m0_apb_PSTRB,
    input  logic [2:0]            m0_apb_PPROT,
    output logic [DATA_WIDTH-1:0] m0_apb_PRDATA,
    output logic                  m0_apb_PSLVERR,
    output logic                  m0_apb_PREADY,

    // Slave 0 APB interface (to external slave 0)
    output logic                  s0_apb_PSEL,
    output logic                  s0_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] s0_apb_PADDR,
    output logic                  s0_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] s0_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] s0_apb_PSTRB,
    output logic [2:0]            s0_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] s0_apb_PRDATA,
    input  logic                  s0_apb_PSLVERR,
    input  logic                  s0_apb_PREADY
);

    // Command/Response interfaces for master 0 apb4_slave
    logic                  m0_cmd_valid;
    logic                  m0_cmd_ready;
    logic                  m0_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] m0_cmd_paddr;
    logic [DATA_WIDTH-1:0] m0_cmd_pwdata;
    logic [STRB_WIDTH-1:0] m0_cmd_pstrb;
    logic [2:0]            m0_cmd_pprot;
    logic                  m0_rsp_valid;
    logic                  m0_rsp_ready;
    logic [DATA_WIDTH-1:0] m0_rsp_prdata;
    logic                  m0_rsp_pslverr;

    // Command/Response interfaces for slave apb4_masters
    logic                  s0_cmd_valid;
    logic                  s0_cmd_ready;
    logic                  s0_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] s0_cmd_paddr;
    logic [DATA_WIDTH-1:0] s0_cmd_pwdata;
    logic [STRB_WIDTH-1:0] s0_cmd_pstrb;
    logic [2:0]            s0_cmd_pprot;
    logic                  s0_rsp_valid;
    logic                  s0_rsp_ready;
    logic [DATA_WIDTH-1:0] s0_rsp_prdata;
    logic                  s0_rsp_pslverr;

    // APB Slave 0 - converts master 0 APB4 to cmd/rsp
    apb4_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb4_slave_m0 (
        .pclk           (pclk),
        .presetn        (presetn),
        .s_apb_PSEL     (m0_apb_PSEL),
        .s_apb_PENABLE  (m0_apb_PENABLE),
        .s_apb_PREADY   (m0_apb_PREADY),
        .s_apb_PADDR    (m0_apb_PADDR),
        .s_apb_PWRITE   (m0_apb_PWRITE),
        .s_apb_PWDATA   (m0_apb_PWDATA),
        .s_apb_PSTRB    (m0_apb_PSTRB),
        .s_apb_PPROT    (m0_apb_PPROT),
        .s_apb_PRDATA   (m0_apb_PRDATA),
        .s_apb_PSLVERR  (m0_apb_PSLVERR),
        .cmd_valid      (m0_cmd_valid),
        .cmd_ready      (m0_cmd_ready),
        .cmd_pwrite     (m0_cmd_pwrite),
        .cmd_paddr      (m0_cmd_paddr),
        .cmd_pwdata     (m0_cmd_pwdata),
        .cmd_pstrb      (m0_cmd_pstrb),
        .cmd_pprot      (m0_cmd_pprot),
        .rsp_valid      (m0_rsp_valid),
        .rsp_ready      (m0_rsp_ready),
        .rsp_prdata     (m0_rsp_prdata),
        .rsp_pslverr    (m0_rsp_pslverr)
    );

    // Simple 1-to-1 passthrough
    assign s0_cmd_valid = m0_cmd_valid;
    assign s0_cmd_pwrite = m0_cmd_pwrite;
    assign s0_cmd_paddr = m0_cmd_paddr;
    assign s0_cmd_pwdata = m0_cmd_pwdata;
    assign s0_cmd_pstrb = m0_cmd_pstrb;
    assign s0_cmd_pprot = m0_cmd_pprot;
    assign m0_cmd_ready = s0_cmd_ready;

    assign m0_rsp_valid = s0_rsp_valid;
    assign m0_rsp_prdata = s0_rsp_prdata;
    assign m0_rsp_pslverr = s0_rsp_pslverr;
    assign s0_rsp_ready = m0_rsp_ready;

    // APB Master 0 - converts cmd/rsp to slave 0 APB4
    apb4_master #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb4_master_s0 (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (s0_apb_PSEL),
        .m_apb_PENABLE  (s0_apb_PENABLE),
        .m_apb_PREADY   (s0_apb_PREADY),
        .m_apb_PADDR    (s0_apb_PADDR),
        .m_apb_PWRITE   (s0_apb_PWRITE),
        .m_apb_PWDATA   (s0_apb_PWDATA),
        .m_apb_PSTRB    (s0_apb_PSTRB),
        .m_apb_PPROT    (s0_apb_PPROT),
        .m_apb_PRDATA   (s0_apb_PRDATA),
        .m_apb_PSLVERR  (s0_apb_PSLVERR),
        .cmd_valid      (s0_cmd_valid),
        .cmd_ready      (s0_cmd_ready),
        .cmd_pwrite     (s0_cmd_pwrite),
        .cmd_paddr      (s0_cmd_paddr),
        .cmd_pwdata     (s0_cmd_pwdata),
        .cmd_pstrb      (s0_cmd_pstrb),
        .cmd_pprot      (s0_cmd_pprot),
        .rsp_valid      (s0_rsp_valid),
        .rsp_ready      (s0_rsp_ready),
        .rsp_prdata     (s0_rsp_prdata),
        .rsp_pslverr    (s0_rsp_pslverr)
    );

endmodule : apbx_xbar_1to1
