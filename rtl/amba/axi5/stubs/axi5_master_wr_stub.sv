// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_wr_stub
// Purpose: AXI5 Master Write Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_wr_stub
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
    parameter int AXI_ATOP_WIDTH    = 6,
    parameter int AXI_NSAID_WIDTH   = 4,
    parameter int AXI_MPAM_WIDTH    = 11,
    parameter int AXI_MECID_WIDTH   = 16,
    parameter int AXI_TAG_WIDTH     = 4,
    parameter int AXI_TAGOP_WIDTH   = 2,

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,

    // AW channel: ID + ADDR + LEN + SIZE + BURST + LOCK + CACHE + PROT + QOS + USER + AXI5 signals
    parameter int AWSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             AXI_ATOP_WIDTH + AXI_NSAID_WIDTH + 1 + AXI_MPAM_WIDTH +
                             AXI_MECID_WIDTH + 1 + AXI_TAGOP_WIDTH + TW,
    // W channel: DATA + STRB + LAST + USER + AXI5 signals
    parameter int WSize    = DW + SW + 1 + UW + 1 + TW + NUM_TAGS,
    // B channel: ID + RESP + USER + AXI5 signals
    parameter int BSize    = IW + 2 + UW + 1 + TW + 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

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
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // AXI5 AW signals
    output logic [AXI_ATOP_WIDTH-1:0]  m_axi_awatop,
    output logic [AXI_NSAID_WIDTH-1:0] m_axi_awnsaid,
    output logic                       m_axi_awtrace,
    output logic [AXI_MPAM_WIDTH-1:0]  m_axi_awmpam,
    output logic [AXI_MECID_WIDTH-1:0] m_axi_awmecid,
    output logic                       m_axi_awunique,
    output logic [AXI_TAGOP_WIDTH-1:0] m_axi_awtagop,
    output logic [TW-1:0]              m_axi_awtag,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [SW-1:0]              m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // AXI5 W signals
    output logic                       m_axi_wpoison,
    output logic [TW-1:0]              m_axi_wtag,
    output logic [NUM_TAGS-1:0]        m_axi_wtagupdate,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // AXI5 B signals
    input  logic                       m_axi_btrace,
    input  logic [TW-1:0]              m_axi_btag,
    input  logic                       m_axi_btagmatch,

    // Stub Outputs/Inputs
    // AW interface
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,
    output logic [3:0]                 fub_axi_aw_count,
    input  logic [AWSize-1:0]          fub_axi_aw_pkt,

    // W interface
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,
    input  logic [WSize-1:0]           fub_axi_w_pkt,

    // B interface
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,
    output logic [BSize-1:0]           fub_axi_b_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AW), .DATA_WIDTH(AWSize), .INSTANCE_NAME("AW-Phase")) inst_aw_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_awvalid),
        .wr_ready               (fub_axi_awready),
        .wr_data                (fub_axi_aw_pkt),
        .rd_valid               (m_axi_awvalid),
        .rd_ready               (m_axi_awready),
        .rd_data                ({m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
                                  m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos, m_axi_awuser,
                                  m_axi_awatop, m_axi_awnsaid, m_axi_awtrace, m_axi_awmpam,
                                  m_axi_awmecid, m_axi_awunique, m_axi_awtagop, m_axi_awtag}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write data channel (W)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_W), .DATA_WIDTH(WSize), .INSTANCE_NAME("W-Phase")) inst_w_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_wvalid),
        .wr_ready               (fub_axi_wready),
        .wr_data                (fub_axi_w_pkt),
        .rd_valid               (m_axi_wvalid),
        .rd_ready               (m_axi_wready),
        .rd_data                ({m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser,
                                  m_axi_wpoison, m_axi_wtag, m_axi_wtagupdate}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write response channel (B)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_B), .DATA_WIDTH(BSize), .INSTANCE_NAME("B-Phase")) inst_b_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_bvalid),
        .wr_ready               (m_axi_bready),
        .wr_data                ({m_axi_bid, m_axi_bresp, m_axi_buser,
                                  m_axi_btrace, m_axi_btag, m_axi_btagmatch}),
        .rd_valid               (fub_axi_bvalid),
        .rd_ready               (fub_axi_bready),
        .rd_data                (fub_axi_b_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi5_master_wr_stub
