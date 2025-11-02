// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_wr
// Purpose: Axi4 Master Wr module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi4_master_wr
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+SW+1+UW,
    parameter int BSize    = IW+2+UW
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI Interface (Input Side)
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_axi_awid,
    input  logic [AW-1:0]              fub_axi_awaddr,
    input  logic [7:0]                 fub_axi_awlen,
    input  logic [2:0]                 fub_axi_awsize,
    input  logic [1:0]                 fub_axi_awburst,
    input  logic                       fub_axi_awlock,
    input  logic [3:0]                 fub_axi_awcache,
    input  logic [2:0]                 fub_axi_awprot,
    input  logic [3:0]                 fub_axi_awqos,
    input  logic [3:0]                 fub_axi_awregion,
    input  logic [UW-1:0]              fub_axi_awuser,
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_axi_wdata,
    input  logic [SW-1:0]              fub_axi_wstrb,
    input  logic                       fub_axi_wlast,
    input  logic [UW-1:0]              fub_axi_wuser,
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,

    // Write response channel (B)
    output logic [IW-1:0]              fub_axi_bid,
    output logic [1:0]                 fub_axi_bresp,
    output logic [UW-1:0]              fub_axi_buser,
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,

    // Master AXI Interface (Output Side)
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Status outputs for clock gating
    output logic                       busy
);

    // SKID buffer connections
    logic [3:0]                 int_aw_count;
    logic [AWSize-1:0]          int_aw_pkt;
    logic                       int_skid_awvalid;
    logic                       int_skid_awready;

    logic [3:0]                 int_w_count;
    logic [WSize-1:0]           int_w_pkt;
    logic                       int_skid_wvalid;
    logic                       int_skid_wready;

    logic [3:0]                 int_b_count;
    logic [BSize-1:0]           int_b_pkt;
    logic                       int_skid_bvalid;
    logic                       int_skid_bready;

    // Busy signal indicates activity in the buffers
    assign busy = (int_aw_count > 0) || (int_w_count > 0) || (int_b_count > 0) ||
                    fub_axi_awvalid || fub_axi_wvalid || m_axi_bvalid;

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize),
        .INSTANCE_NAME("AW_SKID")
    ) aw_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_awvalid),
        .wr_ready               (fub_axi_awready),
        .wr_data                ({fub_axi_awid, fub_axi_awaddr, fub_axi_awlen, fub_axi_awsize,
                                    fub_axi_awburst, fub_axi_awlock, fub_axi_awcache, fub_axi_awprot,
                                    fub_axi_awqos, fub_axi_awregion, fub_axi_awuser}),
        .rd_valid               (int_skid_awvalid),
        .rd_ready               (int_skid_awready),
        .rd_count               (int_aw_count),
        .rd_data                (int_aw_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack AW signals from SKID buffer
    assign {m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
            m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos,
            m_axi_awregion, m_axi_awuser} = int_aw_pkt;
    assign m_axi_awvalid = int_skid_awvalid;
    assign int_skid_awready = m_axi_awready;

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize),
        .INSTANCE_NAME("W_SKID")
    ) w_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_wvalid),
        .wr_ready               (fub_axi_wready),
        .wr_data                ({fub_axi_wdata, fub_axi_wstrb, fub_axi_wlast, fub_axi_wuser}),
        .rd_valid               (int_skid_wvalid),
        .rd_ready               (int_skid_wready),
        .rd_count               (int_w_count),
        .rd_data                (int_w_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // Unpack W signals from SKID buffer
    assign {m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser} = int_w_pkt;
    assign m_axi_wvalid = int_skid_wvalid;
    assign int_skid_wready = m_axi_wready;

    // Instantiate B channel for write response back
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize),
        .INSTANCE_NAME("B_SKID")
    ) b_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_bvalid),
        .wr_ready               (m_axi_bready),
        .wr_data                ({m_axi_bid, m_axi_bresp, m_axi_buser}),
        .rd_valid               (int_skid_bvalid),
        .rd_ready               (int_skid_bready),
        .rd_count               (int_b_count),
        .rd_data                ({fub_axi_bid, fub_axi_bresp, fub_axi_buser}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_axi_bvalid = int_skid_bvalid;
    assign int_skid_bready = fub_axi_bready;

endmodule : axi4_master_wr
