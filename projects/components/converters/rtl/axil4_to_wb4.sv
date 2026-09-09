// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_to_wb4
// Purpose: AXI4-Lite slave in, Wishbone B4 master out.
//
// Documentation: projects/components/converters/docs/converter_mas/ch03_protocol_blocks/10_axil4_to_wb4.md
// Subsystem: converters
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   axil4_slave_wr + axil4_slave_rd (skid buffers on every AXI4-Lite channel)
//   -> axil4_to_wb4_core (channel set to command/response queues)
//   -> wb4_master (queues to the Wishbone bus, pipelined or classic).
//   Same address and data width on both sides; no width conversion.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH, DATA_WIDTH
//   SKID_DEPTH_AW/W/B/AR/R  - AXI4-Lite side skid depths (2..8)
//   CMD_DEPTH, RSP_DEPTH     - wb4_master queue depths; RSP_DEPTH bounds
//                              the transfers on the bus
//   SIDE_DEPTH               - core direction queue (>= CMD_DEPTH + RSP_DEPTH)
//   CLASSIC                  - 0 = B4 pipelined, 1 = B4 standard (classic)
//   RTY_RESP                 - AXI response for a Wishbone RTY (SLVERR)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/converters/dv/tests/test_axil4_to_wb4.py
//==============================================================================

`timescale 1ns / 1ps

module axil4_to_wb4 #(
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 32,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 2,
    parameter int CMD_DEPTH     = 4,
    parameter int RSP_DEPTH     = 4,
    parameter int SIDE_DEPTH    = 8,
    parameter int CLASSIC       = 0,
    parameter logic [1:0] RTY_RESP = 2'b10,
    // Short params
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int SW = DW/8
)
(
    input  logic              aclk,
    input  logic              aresetn,

    // AXI4-Lite slave
    input  logic [AW-1:0]     s_axil_awaddr,
    input  logic [2:0]        s_axil_awprot,
    input  logic              s_axil_awvalid,
    output logic              s_axil_awready,
    input  logic [DW-1:0]     s_axil_wdata,
    input  logic [SW-1:0]     s_axil_wstrb,
    input  logic              s_axil_wvalid,
    output logic              s_axil_wready,
    output logic [1:0]        s_axil_bresp,
    output logic              s_axil_bvalid,
    input  logic              s_axil_bready,
    input  logic [AW-1:0]     s_axil_araddr,
    input  logic [2:0]        s_axil_arprot,
    input  logic              s_axil_arvalid,
    output logic              s_axil_arready,
    output logic [DW-1:0]     s_axil_rdata,
    output logic [1:0]        s_axil_rresp,
    output logic              s_axil_rvalid,
    input  logic              s_axil_rready,

    // Wishbone B4 master
    output logic              m_wb_CYC,
    output logic              m_wb_STB,
    output logic              m_wb_WE,
    output logic [AW-1:0]     m_wb_ADR,
    output logic [DW-1:0]     m_wb_DAT_W,
    output logic [SW-1:0]     m_wb_SEL,
    input  logic              m_wb_STALL,
    input  logic              m_wb_ACK,
    input  logic              m_wb_ERR,
    input  logic              m_wb_RTY,
    input  logic [DW-1:0]     m_wb_DAT_R,

    output logic              busy
);

    // AXI4-Lite channels after the skids
    logic [AW-1:0] w_fub_awaddr, w_fub_araddr;
    logic [2:0]    w_fub_awprot, w_fub_arprot;
    logic          w_fub_awvalid, w_fub_awready, w_fub_wvalid, w_fub_wready;
    logic          w_fub_bvalid, w_fub_bready, w_fub_arvalid, w_fub_arready;
    logic          w_fub_rvalid, w_fub_rready;
    logic [DW-1:0] w_fub_wdata, w_fub_rdata;
    logic [SW-1:0] w_fub_wstrb;
    logic [1:0]    w_fub_bresp, w_fub_rresp;
    logic          w_busy_wr, w_busy_rd;

    // Command / response queues
    logic          w_cmd_valid, w_cmd_ready, w_cmd_we;
    logic [AW-1:0] w_cmd_adr;
    logic [DW-1:0] w_cmd_dat, w_rsp_dat;
    logic [SW-1:0] w_cmd_sel;
    logic          w_rsp_valid, w_rsp_ready;
    logic [1:0]    w_rsp_status;

    axil4_slave_wr #(
        .AXIL_ADDR_WIDTH (AW),
        .AXIL_DATA_WIDTH (DW),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_slave_wr (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .s_axil_awaddr  (s_axil_awaddr),
        .s_axil_awprot  (s_axil_awprot),
        .s_axil_awvalid (s_axil_awvalid),
        .s_axil_awready (s_axil_awready),
        .s_axil_wdata   (s_axil_wdata),
        .s_axil_wstrb   (s_axil_wstrb),
        .s_axil_wvalid  (s_axil_wvalid),
        .s_axil_wready  (s_axil_wready),
        .s_axil_bresp   (s_axil_bresp),
        .s_axil_bvalid  (s_axil_bvalid),
        .s_axil_bready  (s_axil_bready),
        .fub_awaddr     (w_fub_awaddr),
        .fub_awprot     (w_fub_awprot),
        .fub_awvalid    (w_fub_awvalid),
        .fub_awready    (w_fub_awready),
        .fub_wdata      (w_fub_wdata),
        .fub_wstrb      (w_fub_wstrb),
        .fub_wvalid     (w_fub_wvalid),
        .fub_wready     (w_fub_wready),
        .fub_bresp      (w_fub_bresp),
        .fub_bvalid     (w_fub_bvalid),
        .fub_bready     (w_fub_bready),
        .busy           (w_busy_wr)
    );

    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH (AW),
        .AXIL_DATA_WIDTH (DW),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_slave_rd (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (s_axil_arvalid),
        .s_axil_arready (s_axil_arready),
        .s_axil_rdata   (s_axil_rdata),
        .s_axil_rresp   (s_axil_rresp),
        .s_axil_rvalid  (s_axil_rvalid),
        .s_axil_rready  (s_axil_rready),
        .fub_araddr     (w_fub_araddr),
        .fub_arprot     (w_fub_arprot),
        .fub_arvalid    (w_fub_arvalid),
        .fub_arready    (w_fub_arready),
        .fub_rdata      (w_fub_rdata),
        .fub_rresp      (w_fub_rresp),
        .fub_rvalid     (w_fub_rvalid),
        .fub_rready     (w_fub_rready),
        .busy           (w_busy_rd)
    );

    axil4_to_wb4_core #(
        .ADDR_WIDTH (AW),
        .DATA_WIDTH (DW),
        .SIDE_DEPTH (SIDE_DEPTH),
        .RTY_RESP   (RTY_RESP)
    ) u_core (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .fub_awaddr  (w_fub_awaddr),
        .fub_awprot  (w_fub_awprot),
        .fub_awvalid (w_fub_awvalid),
        .fub_awready (w_fub_awready),
        .fub_wdata   (w_fub_wdata),
        .fub_wstrb   (w_fub_wstrb),
        .fub_wvalid  (w_fub_wvalid),
        .fub_wready  (w_fub_wready),
        .fub_bresp   (w_fub_bresp),
        .fub_bvalid  (w_fub_bvalid),
        .fub_bready  (w_fub_bready),
        .fub_araddr  (w_fub_araddr),
        .fub_arprot  (w_fub_arprot),
        .fub_arvalid (w_fub_arvalid),
        .fub_arready (w_fub_arready),
        .fub_rdata   (w_fub_rdata),
        .fub_rresp   (w_fub_rresp),
        .fub_rvalid  (w_fub_rvalid),
        .fub_rready  (w_fub_rready),
        .cmd_valid   (w_cmd_valid),
        .cmd_ready   (w_cmd_ready),
        .cmd_we      (w_cmd_we),
        .cmd_adr     (w_cmd_adr),
        .cmd_dat     (w_cmd_dat),
        .cmd_sel     (w_cmd_sel),
        .rsp_valid   (w_rsp_valid),
        .rsp_ready   (w_rsp_ready),
        .rsp_status  (w_rsp_status),
        .rsp_dat     (w_rsp_dat)
    );

    wb4_master #(
        .ADDR_WIDTH (AW),
        .DATA_WIDTH (DW),
        .CMD_DEPTH  (CMD_DEPTH),
        .RSP_DEPTH  (RSP_DEPTH),
        .CLASSIC    (CLASSIC)
    ) u_wb_master (
        .clk        (aclk),
        .aresetn    (aresetn),
        .m_wb_CYC   (m_wb_CYC),
        .m_wb_STB   (m_wb_STB),
        .m_wb_WE    (m_wb_WE),
        .m_wb_ADR   (m_wb_ADR),
        .m_wb_DAT_W (m_wb_DAT_W),
        .m_wb_SEL   (m_wb_SEL),
        .m_wb_STALL (m_wb_STALL),
        .m_wb_ACK   (m_wb_ACK),
        .m_wb_ERR   (m_wb_ERR),
        .m_wb_RTY   (m_wb_RTY),
        .m_wb_DAT_R (m_wb_DAT_R),
        .cmd_valid  (w_cmd_valid),
        .cmd_ready  (w_cmd_ready),
        .cmd_we     (w_cmd_we),
        .cmd_adr    (w_cmd_adr),
        .cmd_dat    (w_cmd_dat),
        .cmd_sel    (w_cmd_sel),
        .rsp_valid  (w_rsp_valid),
        .rsp_ready  (w_rsp_ready),
        .rsp_status (w_rsp_status),
        .rsp_dat    (w_rsp_dat)
    );

    assign busy = w_busy_wr || w_busy_rd || m_wb_CYC;

endmodule : axil4_to_wb4
