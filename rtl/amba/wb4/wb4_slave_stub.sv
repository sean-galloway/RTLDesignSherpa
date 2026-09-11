// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_slave_stub
// Purpose: wb4_slave with its command and response queues as PACKED
//          vectors, for shim-style converters.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_slave_stub.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   wb4_slave with a single `cmd_data` vector on the FUB side instead of
//   named fields, matching apb4_slave_stub / apb5_slave_stub. Same packing
//   as wb4_master_stub, so a stub pair connects directly:
//     cmd_data = {we, adr, dat, sel, cti, bte}
//     rsp_data = {status, dat}
//==============================================================================

`timescale 1ns / 1ps

module wb4_slave_stub
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int CMD_DEPTH       = 2,
    parameter int RSP_DEPTH       = 2,
    parameter int MAX_OUTSTANDING = 16,
    parameter int CLASSIC         = 0,
    parameter int USE_BURST_HINTS = 0,
    parameter int SEL_WIDTH       = DATA_WIDTH / 8,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = SEL_WIDTH,
    parameter int STW = WB4_STATUS_WIDTH,
    parameter int CTW = WB4_CTI_WIDTH,
    parameter int BTW = WB4_BTE_WIDTH,
    parameter int CPW = 1 + AW + DW + SW + CTW + BTW,
    parameter int RPW = STW + DW
)
(
    input  logic              clk,
    input  logic              aresetn,

    // Wishbone B4 slave
    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [AW-1:0]     s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [SW-1:0]     s_wb_SEL,
    input  logic [CTW-1:0]    s_wb_CTI,
    input  logic [BTW-1:0]    s_wb_BTE,
    output logic              s_wb_STALL,
    output logic              s_wb_ACK,
    output logic              s_wb_ERR,
    output logic              s_wb_RTY,
    output logic [DW-1:0]     s_wb_DAT_R,

    // Packed command / response
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic [CPW-1:0]    cmd_data,
    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [RPW-1:0]    rsp_data
);

    logic           w_cmd_we;
    logic [AW-1:0]  w_cmd_adr;
    logic [DW-1:0]  w_cmd_dat, w_rsp_dat;
    logic [SW-1:0]  w_cmd_sel;
    logic [CTW-1:0] w_cmd_cti;
    logic [BTW-1:0] w_cmd_bte;
    logic [STW-1:0] w_rsp_status;

    assign cmd_data = {w_cmd_we, w_cmd_adr, w_cmd_dat, w_cmd_sel, w_cmd_cti, w_cmd_bte};
    assign {w_rsp_status, w_rsp_dat} = rsp_data;

    wb4_slave #(
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DATA_WIDTH      (DATA_WIDTH),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .MAX_OUTSTANDING (MAX_OUTSTANDING),
        .CLASSIC         (CLASSIC),
        .USE_BURST_HINTS (USE_BURST_HINTS),
        .SEL_WIDTH       (SEL_WIDTH)
    ) u_wb4_slave (
        .clk        (clk),
        .aresetn    (aresetn),
        .s_wb_CYC   (s_wb_CYC),
        .s_wb_STB   (s_wb_STB),
        .s_wb_WE    (s_wb_WE),
        .s_wb_ADR   (s_wb_ADR),
        .s_wb_DAT_W (s_wb_DAT_W),
        .s_wb_SEL   (s_wb_SEL),
        .s_wb_CTI   (s_wb_CTI),
        .s_wb_BTE   (s_wb_BTE),
        .s_wb_STALL (s_wb_STALL),
        .s_wb_ACK   (s_wb_ACK),
        .s_wb_ERR   (s_wb_ERR),
        .s_wb_RTY   (s_wb_RTY),
        .s_wb_DAT_R (s_wb_DAT_R),
        .cmd_valid  (cmd_valid),
        .cmd_ready  (cmd_ready),
        .cmd_we     (w_cmd_we),
        .cmd_adr    (w_cmd_adr),
        .cmd_dat    (w_cmd_dat),
        .cmd_sel    (w_cmd_sel),
        .cmd_cti    (w_cmd_cti),
        .cmd_bte    (w_cmd_bte),
        .rsp_valid  (rsp_valid),
        .rsp_ready  (rsp_ready),
        .rsp_status (w_rsp_status),
        .rsp_dat    (w_rsp_dat)
    );

endmodule : wb4_slave_stub
