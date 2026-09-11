// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_to_axil4
// Purpose: Wishbone B4 slave in, AXI4-Lite master out.
//
// Documentation: projects/components/converters/docs/converter_mas/ch03_protocol_blocks/11_wb4_to_axil4.md
// Subsystem: converters
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   wb4_slave (Wishbone bus to command/response queues)
//   -> wb4_to_axil4_core (queues to the five AXI4-Lite channels, merging the
//      two response channels back into one in-order termination stream)
//   -> axil4_master_wr + axil4_master_rd (channels to the bus).
//
//   The mirror of axil4_to_wb4. Same address and data width on both sides.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH, DATA_WIDTH
//   CMD_DEPTH, RSP_DEPTH, MAX_OUTSTANDING - the wb4_slave's queues and bound
//   CLASSIC          - 0 = B4 pipelined, 1 = B4 standard; match the master
//   OUTSTANDING      - commands in flight through the core (1 = serialised)
//   SKID_DEPTH_*     - the AXI4-Lite masters' channel skids
//   AXIL_PROT        - AWPROT/ARPROT driven on every command
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/converters/dv/tests/test_wb4_to_axil4.py
//==============================================================================

`timescale 1ns / 1ps

module wb4_to_axil4
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH      = 32,
    parameter int DATA_WIDTH      = 32,
    parameter int CMD_DEPTH       = 2,
    parameter int RSP_DEPTH       = 2,
    parameter int MAX_OUTSTANDING = 16,
    parameter int CLASSIC         = 0,
    parameter int OUTSTANDING     = 1,
    parameter int SKID_DEPTH_AW   = 2,
    parameter int SKID_DEPTH_W    = 2,
    parameter int SKID_DEPTH_B    = 2,
    parameter int SKID_DEPTH_AR   = 2,
    parameter int SKID_DEPTH_R    = 2,
    parameter logic [2:0] AXIL_PROT = 3'b000,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int CTW = WB4_CTI_WIDTH,
    parameter int BTW = WB4_BTE_WIDTH
)
(
    input  logic              aclk,
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

    // AXI4-Lite master
    output logic [AW-1:0]     m_axil_awaddr,
    output logic [2:0]        m_axil_awprot,
    output logic              m_axil_awvalid,
    input  logic              m_axil_awready,
    output logic [DW-1:0]     m_axil_wdata,
    output logic [SW-1:0]     m_axil_wstrb,
    output logic              m_axil_wvalid,
    input  logic              m_axil_wready,
    input  logic [1:0]        m_axil_bresp,
    input  logic              m_axil_bvalid,
    output logic              m_axil_bready,
    output logic [AW-1:0]     m_axil_araddr,
    output logic [2:0]        m_axil_arprot,
    output logic              m_axil_arvalid,
    input  logic              m_axil_arready,
    input  logic [DW-1:0]     m_axil_rdata,
    input  logic [1:0]        m_axil_rresp,
    input  logic              m_axil_rvalid,
    output logic              m_axil_rready,

    output logic              busy
);

    // wb4_slave FUB side
    logic          w_cmd_valid, w_cmd_ready, w_cmd_we;
    logic [AW-1:0] w_cmd_adr;
    logic [DW-1:0] w_cmd_dat, w_rsp_dat;
    logic [SW-1:0] w_cmd_sel;
    logic [CTW-1:0] w_cmd_cti;
    logic [BTW-1:0] w_cmd_bte;
    logic          w_rsp_valid, w_rsp_ready;
    logic [1:0]    w_rsp_status;

    // core <-> axil masters
    logic [AW-1:0] w_awaddr, w_araddr;
    logic [2:0]    w_awprot, w_arprot;
    logic          w_awvalid, w_awready, w_wvalid, w_wready;
    logic          w_bvalid, w_bready, w_arvalid, w_arready, w_rvalid, w_rready;
    logic [DW-1:0] w_wdata, w_rdata;
    logic [SW-1:0] w_wstrb;
    logic [1:0]    w_bresp, w_rresp;
    logic          w_busy_wr, w_busy_rd;

    wb4_slave #(
        .ADDR_WIDTH      (AW),
        .DATA_WIDTH      (DW),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .MAX_OUTSTANDING (MAX_OUTSTANDING),
        .CLASSIC         (CLASSIC)
    ) u_wb_slave (
        .clk        (aclk),
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
        .cmd_valid  (w_cmd_valid),
        .cmd_ready  (w_cmd_ready),
        .cmd_we     (w_cmd_we),
        .cmd_adr    (w_cmd_adr),
        .cmd_dat    (w_cmd_dat),
        .cmd_sel    (w_cmd_sel),
        .cmd_cti    (w_cmd_cti),
        .cmd_bte    (w_cmd_bte),
        .rsp_valid  (w_rsp_valid),
        .rsp_ready  (w_rsp_ready),
        .rsp_status (w_rsp_status),
        .rsp_dat    (w_rsp_dat)
    );

    // The burst hints stop here: AXI4-Lite is single-beat and has no field to
    // carry them. A burst-aware target behind AXI4-Lite is a contradiction.
    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused_hints;
    assign w_unused_hints = ^{w_cmd_cti, w_cmd_bte};
    /* verilator lint_on UNUSEDSIGNAL */

    wb4_to_axil4_core #(
        .ADDR_WIDTH  (AW),
        .DATA_WIDTH  (DW),
        .OUTSTANDING (OUTSTANDING),
        .AXIL_PROT   (AXIL_PROT)
    ) u_core (
        .aclk        (aclk),
        .aresetn     (aresetn),
        .cmd_valid   (w_cmd_valid),
        .cmd_ready   (w_cmd_ready),
        .cmd_we      (w_cmd_we),
        .cmd_adr     (w_cmd_adr),
        .cmd_dat     (w_cmd_dat),
        .cmd_sel     (w_cmd_sel),
        .rsp_valid   (w_rsp_valid),
        .rsp_ready   (w_rsp_ready),
        .rsp_status  (w_rsp_status),
        .rsp_dat     (w_rsp_dat),
        .fub_awaddr  (w_awaddr),
        .fub_awprot  (w_awprot),
        .fub_awvalid (w_awvalid),
        .fub_awready (w_awready),
        .fub_wdata   (w_wdata),
        .fub_wstrb   (w_wstrb),
        .fub_wvalid  (w_wvalid),
        .fub_wready  (w_wready),
        .fub_bresp   (w_bresp),
        .fub_bvalid  (w_bvalid),
        .fub_bready  (w_bready),
        .fub_araddr  (w_araddr),
        .fub_arprot  (w_arprot),
        .fub_arvalid (w_arvalid),
        .fub_arready (w_arready),
        .fub_rdata   (w_rdata),
        .fub_rresp   (w_rresp),
        .fub_rvalid  (w_rvalid),
        .fub_rready  (w_rready)
    );

    axil4_master_wr #(
        .AXIL_ADDR_WIDTH (AW),
        .AXIL_DATA_WIDTH (DW),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .fub_awaddr     (w_awaddr),
        .fub_awprot     (w_awprot),
        .fub_awvalid    (w_awvalid),
        .fub_awready    (w_awready),
        .fub_wdata      (w_wdata),
        .fub_wstrb      (w_wstrb),
        .fub_wvalid     (w_wvalid),
        .fub_wready     (w_wready),
        .fub_bresp      (w_bresp),
        .fub_bvalid     (w_bvalid),
        .fub_bready     (w_bready),
        .m_axil_awaddr  (m_axil_awaddr),
        .m_axil_awprot  (m_axil_awprot),
        .m_axil_awvalid (m_axil_awvalid),
        .m_axil_awready (m_axil_awready),
        .m_axil_wdata   (m_axil_wdata),
        .m_axil_wstrb   (m_axil_wstrb),
        .m_axil_wvalid  (m_axil_wvalid),
        .m_axil_wready  (m_axil_wready),
        .m_axil_bresp   (m_axil_bresp),
        .m_axil_bvalid  (m_axil_bvalid),
        .m_axil_bready  (m_axil_bready),
        .busy           (w_busy_wr)
    );

    axil4_master_rd #(
        .AXIL_ADDR_WIDTH (AW),
        .AXIL_DATA_WIDTH (DW),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .fub_araddr     (w_araddr),
        .fub_arprot     (w_arprot),
        .fub_arvalid    (w_arvalid),
        .fub_arready    (w_arready),
        .fub_rdata      (w_rdata),
        .fub_rresp      (w_rresp),
        .fub_rvalid     (w_rvalid),
        .fub_rready     (w_rready),
        .m_axil_araddr  (m_axil_araddr),
        .m_axil_arprot  (m_axil_arprot),
        .m_axil_arvalid (m_axil_arvalid),
        .m_axil_arready (m_axil_arready),
        .m_axil_rdata   (m_axil_rdata),
        .m_axil_rresp   (m_axil_rresp),
        .m_axil_rvalid  (m_axil_rvalid),
        .m_axil_rready  (m_axil_rready),
        .busy           (w_busy_rd)
    );

    assign busy = w_busy_wr || w_busy_rd || s_wb_CYC;

endmodule : wb4_to_axil4
