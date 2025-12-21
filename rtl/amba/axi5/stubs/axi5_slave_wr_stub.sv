// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_wr_stub
// Purpose: AXI5 Slave Write Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_wr_stub
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

    // Slave Write address channel (AW)
    input  logic [IW-1:0]              s_axi_awid,
    input  logic [AW-1:0]              s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [UW-1:0]              s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // AXI5 AW signals
    input  logic [AXI_ATOP_WIDTH-1:0]  s_axi_awatop,
    input  logic [AXI_NSAID_WIDTH-1:0] s_axi_awnsaid,
    input  logic                       s_axi_awtrace,
    input  logic [AXI_MPAM_WIDTH-1:0]  s_axi_awmpam,
    input  logic [AXI_MECID_WIDTH-1:0] s_axi_awmecid,
    input  logic                       s_axi_awunique,
    input  logic [AXI_TAGOP_WIDTH-1:0] s_axi_awtagop,
    input  logic [TW-1:0]              s_axi_awtag,

    // Slave Write data channel (W)
    input  logic [DW-1:0]              s_axi_wdata,
    input  logic [SW-1:0]              s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [UW-1:0]              s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // AXI5 W signals
    input  logic                       s_axi_wpoison,
    input  logic [TW-1:0]              s_axi_wtag,
    input  logic [NUM_TAGS-1:0]        s_axi_wtagupdate,

    // Slave Write response channel (B)
    output logic [IW-1:0]              s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [UW-1:0]              s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    // AXI5 B signals
    output logic                       s_axi_btrace,
    output logic [TW-1:0]              s_axi_btag,
    output logic                       s_axi_btagmatch,

    // Stub Outputs/Inputs
    // AW interface
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,
    output logic [AWSize-1:0]          fub_axi_aw_pkt,

    // W interface
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,
    output logic [WSize-1:0]           fub_axi_w_pkt,

    // B interface
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,
    output logic [2:0]                 fub_axi_b_count,
    input  logic [BSize-1:0]           fub_axi_b_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Write address channel (AW)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AW), .DATA_WIDTH(AWSize), .INSTANCE_NAME("AW-Phase")) inst_aw_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axi_awvalid),
        .wr_ready               (s_axi_awready),
        .wr_data                ({s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst,
                                  s_axi_awlock, s_axi_awcache, s_axi_awprot, s_axi_awqos, s_axi_awuser,
                                  s_axi_awatop, s_axi_awnsaid, s_axi_awtrace, s_axi_awmpam,
                                  s_axi_awmecid, s_axi_awunique, s_axi_awtagop, s_axi_awtag}),
        .rd_valid               (fub_axi_awvalid),
        .rd_ready               (fub_axi_awready),
        .rd_data                (fub_axi_aw_pkt),
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
        .wr_valid               (s_axi_wvalid),
        .wr_ready               (s_axi_wready),
        .wr_data                ({s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser,
                                  s_axi_wpoison, s_axi_wtag, s_axi_wtagupdate}),
        .rd_valid               (fub_axi_wvalid),
        .rd_ready               (fub_axi_wready),
        .rd_data                (fub_axi_w_pkt),
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
        .wr_valid               (fub_axi_bvalid),
        .wr_ready               (fub_axi_bready),
        .wr_data                (fub_axi_b_pkt),
        .rd_valid               (s_axi_bvalid),
        .rd_ready               (s_axi_bready),
        .rd_data                ({s_axi_bid, s_axi_bresp, s_axi_buser,
                                  s_axi_btrace, s_axi_btag, s_axi_btagmatch}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi5_slave_wr_stub
