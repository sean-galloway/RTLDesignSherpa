// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_master_stub
// Purpose: wb4_master with its command and response queues as PACKED
//          vectors, for shim-style converters.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_stubs.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   The same block as wb4_master with one difference: the FUB side is a
//   single `cmd_data` vector instead of named fields, matching what
//   apb4_master_stub / apb5_master_stub offer. A converter that already
//   carries a packed command through its own pipeline connects one bus
//   instead of six, and the packing lives HERE rather than being re-derived
//   by every consumer.
//
//   Field order, most significant first:
//     cmd_data = {we, adr, dat, sel, cti, bte}
//     rsp_data = {status, dat}
//
//   `cti`/`bte` occupy their bits whatever USE_BURST_HINTS is, so the
//   vector width does not move with the parameter; with the hints off the
//   inner master ignores them and drives CLASSIC/LINEAR.
//==============================================================================

`timescale 1ns / 1ps

module wb4_master_stub
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int CMD_DEPTH       = 4,
    parameter int RSP_DEPTH       = 4,
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
    parameter int CPW = 1 + AW + DW + SW + CTW + BTW,   // {we, adr, dat, sel, cti, bte}
    parameter int RPW = STW + DW                        // {status, dat}
)
(
    input  logic              clk,
    input  logic              aresetn,

    // Wishbone B4 master
    output logic              m_wb_CYC,
    output logic              m_wb_STB,
    output logic              m_wb_WE,
    output logic [AW-1:0]     m_wb_ADR,
    output logic [DW-1:0]     m_wb_DAT_W,
    output logic [SW-1:0]     m_wb_SEL,
    output logic [CTW-1:0]    m_wb_CTI,
    output logic [BTW-1:0]    m_wb_BTE,
    input  logic              m_wb_STALL,
    input  logic              m_wb_ACK,
    input  logic              m_wb_ERR,
    input  logic              m_wb_RTY,
    input  logic [DW-1:0]     m_wb_DAT_R,

    // Packed command / response
    input  logic              cmd_valid,
    output logic              cmd_ready,
    input  logic [CPW-1:0]    cmd_data,
    output logic              rsp_valid,
    input  logic              rsp_ready,
    output logic [RPW-1:0]    rsp_data
);

    logic           w_cmd_we;
    logic [AW-1:0]  w_cmd_adr;
    logic [DW-1:0]  w_cmd_dat, w_rsp_dat;
    logic [SW-1:0]  w_cmd_sel;
    logic [CTW-1:0] w_cmd_cti;
    logic [BTW-1:0] w_cmd_bte;
    logic [STW-1:0] w_rsp_status;

    assign {w_cmd_we, w_cmd_adr, w_cmd_dat, w_cmd_sel, w_cmd_cti, w_cmd_bte} = cmd_data;
    assign rsp_data = {w_rsp_status, w_rsp_dat};

    wb4_master #(
        .ADDR_WIDTH      (ADDR_WIDTH),
        .DATA_WIDTH      (DATA_WIDTH),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .CLASSIC         (CLASSIC),
        .USE_BURST_HINTS (USE_BURST_HINTS),
        .SEL_WIDTH       (SEL_WIDTH)
    ) u_wb4_master (
        .clk        (clk),
        .aresetn    (aresetn),
        .m_wb_CYC   (m_wb_CYC),
        .m_wb_STB   (m_wb_STB),
        .m_wb_WE    (m_wb_WE),
        .m_wb_ADR   (m_wb_ADR),
        .m_wb_DAT_W (m_wb_DAT_W),
        .m_wb_SEL   (m_wb_SEL),
        .m_wb_CTI   (m_wb_CTI),
        .m_wb_BTE   (m_wb_BTE),
        .m_wb_STALL (m_wb_STALL),
        .m_wb_ACK   (m_wb_ACK),
        .m_wb_ERR   (m_wb_ERR),
        .m_wb_RTY   (m_wb_RTY),
        .m_wb_DAT_R (m_wb_DAT_R),
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

endmodule : wb4_master_stub
