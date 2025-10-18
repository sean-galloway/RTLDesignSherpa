// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_slave_cdc
// Purpose: Apb Slave Cdc module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb_slave_cdc #(
    parameter int ADDR_WIDTH  = 32,
    parameter int DATA_WIDTH  = 32,
    parameter int STRB_WIDTH  = DATA_WIDTH / 8,
    parameter int PROT_WIDTH  = 3,
    parameter int DEPTH       = 2,
    // Short Parameters
    parameter int DW  = DATA_WIDTH,
    parameter int AW  = ADDR_WIDTH,
    parameter int SW  = STRB_WIDTH,
    parameter int PW  = PROT_WIDTH,
    parameter int CPW = AW + DW + SW + PW + 1, // verilog_lint: waive line-length
    parameter int RPW = DW + 1
) (
    // Clock and Reset
    input  logic              aclk,
    input  logic              aresetn,
    input  logic              pclk,
    input  logic              presetn,

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
    input  logic              rsp_pslverr
);

    // local signal to pass between the handshake
    logic              w_cmd_valid;
    logic              w_cmd_ready;
    logic              w_cmd_pwrite;
    logic [AW-1:0]     w_cmd_paddr;
    logic [DW-1:0]     w_cmd_pwdata;
    logic [SW-1:0]     w_cmd_pstrb;
    logic [PW-1:0]     w_cmd_pprot;


    logic              w_rsp_valid;
    logic              w_rsp_ready;
    logic [DW-1:0]     w_rsp_prdata;
    logic              w_rsp_pslverr;

    apb_slave #(
        .ADDR_WIDTH   (AW),
        .DATA_WIDTH   (DW),
        .STRB_WIDTH   (SW),
        .PROT_WIDTH   (PW),
        .DEPTH        (DEPTH)
    ) u_apb_slave(
        // Clock and Reset
        .pclk         (pclk),
        .presetn      (presetn),

        // APB interface
        .s_apb_PSEL   (s_apb_PSEL),
        .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY (s_apb_PREADY),
        .s_apb_PADDR  (s_apb_PADDR),
        .s_apb_PWRITE (s_apb_PWRITE),
        .s_apb_PWDATA (s_apb_PWDATA),
        .s_apb_PSTRB  (s_apb_PSTRB),
        .s_apb_PPROT  (s_apb_PPROT),
        .s_apb_PRDATA (s_apb_PRDATA),
        .s_apb_PSLVERR(s_apb_PSLVERR),

        // Command Interface
        .cmd_valid    (w_cmd_valid),
        .cmd_ready    (w_cmd_ready),
        .cmd_pwrite   (w_cmd_pwrite),
        .cmd_paddr    (w_cmd_paddr),
        .cmd_pwdata   (w_cmd_pwdata),
        .cmd_pstrb    (w_cmd_pstrb),
        .cmd_pprot    (w_cmd_pprot),

        // Response Interface
        .rsp_valid    (w_rsp_valid),
        .rsp_ready    (w_rsp_ready),
        .rsp_prdata   (w_rsp_prdata),
        .rsp_pslverr  (w_rsp_pslverr)
    );

    cdc_handshake #(
        .DATA_WIDTH      (CPW)
    ) u_cmd_cdc_handshake (
        .clk_src         (pclk),
        .rst_src_n       (presetn),
        .src_valid       (w_cmd_valid),
        .src_ready       (w_cmd_ready),
        .src_data        ({w_cmd_pwrite, w_cmd_paddr, w_cmd_pwdata, w_cmd_pstrb, w_cmd_pprot}),

        .clk_dst         (aclk),
        .rst_dst_n       (aresetn),
        .dst_valid       (cmd_valid),
        .dst_ready       (cmd_ready),
        .dst_data        (
            {cmd_pwrite, cmd_paddr, cmd_pwdata, cmd_pstrb, cmd_pprot})
    );

    cdc_handshake #(
        .DATA_WIDTH      (RPW)
    ) u_rsp_cdc_handshake (
        .clk_src         (aclk),
        .rst_src_n       (aresetn),
        .src_valid       (rsp_valid),
        .src_ready       (rsp_ready),
        .src_data        ({rsp_pslverr, rsp_prdata}),

        .clk_dst         (pclk),
        .rst_dst_n       (presetn),
        .dst_valid       (w_rsp_valid),
        .dst_ready       (w_rsp_ready),
        .dst_data        ({w_rsp_pslverr, w_rsp_prdata})
    );

endmodule : apb_slave_cdc
