// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_stub
// Purpose: AXI5 Slave Stub module (combined read and write)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_stub
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

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
    parameter int AXI_CHUNKNUM_WIDTH = 4,

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,

    // Write channel sizes
    parameter int AWSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             AXI_ATOP_WIDTH + AXI_NSAID_WIDTH + 1 + AXI_MPAM_WIDTH +
                             AXI_MECID_WIDTH + 1 + AXI_TAGOP_WIDTH + TW,
    parameter int WSize    = DW + SW + 1 + UW + 1 + TW + NUM_TAGS,
    parameter int BSize    = IW + 2 + UW + 1 + TW + 1,

    // Read channel sizes
    parameter int ARSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             AXI_NSAID_WIDTH + 1 + AXI_MPAM_WIDTH + AXI_MECID_WIDTH +
                             1 + 1 + AXI_TAGOP_WIDTH,
    parameter int RSize    = IW + DW + 2 + 1 + UW + 1 + 1 + 1 + AXI_CHUNKNUM_WIDTH +
                             CHUNK_STRB_WIDTH + TW + 1
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
    input  logic                       s_axi_wpoison,
    input  logic [TW-1:0]              s_axi_wtag,
    input  logic [NUM_TAGS-1:0]        s_axi_wtagupdate,

    // Slave Write response channel (B)
    output logic [IW-1:0]              s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [UW-1:0]              s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,
    output logic                       s_axi_btrace,
    output logic [TW-1:0]              s_axi_btag,
    output logic                       s_axi_btagmatch,

    // Slave Read address channel (AR)
    input  logic [IW-1:0]              s_axi_arid,
    input  logic [AW-1:0]              s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [UW-1:0]              s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,
    input  logic [AXI_NSAID_WIDTH-1:0] s_axi_arnsaid,
    input  logic                       s_axi_artrace,
    input  logic [AXI_MPAM_WIDTH-1:0]  s_axi_armpam,
    input  logic [AXI_MECID_WIDTH-1:0] s_axi_armecid,
    input  logic                       s_axi_arunique,
    input  logic                       s_axi_archunken,
    input  logic [AXI_TAGOP_WIDTH-1:0] s_axi_artagop,

    // Slave Read data channel (R)
    output logic [IW-1:0]              s_axi_rid,
    output logic [DW-1:0]              s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [UW-1:0]              s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,
    output logic                       s_axi_rtrace,
    output logic                       s_axi_rpoison,
    output logic                       s_axi_rchunkv,
    output logic [AXI_CHUNKNUM_WIDTH-1:0] s_axi_rchunknum,
    output logic [CHUNK_STRB_WIDTH-1:0] s_axi_rchunkstrb,
    output logic [TW-1:0]              s_axi_rtag,
    output logic                       s_axi_rtagmatch,

    // Stub Write Interfaces
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,
    output logic [AWSize-1:0]          fub_axi_aw_pkt,

    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,
    output logic [WSize-1:0]           fub_axi_w_pkt,

    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,
    output logic [2:0]                 fub_axi_b_count,
    input  logic [BSize-1:0]           fub_axi_b_pkt,

    // Stub Read Interfaces
    output logic                       fub_axi_arvalid,
    input  logic                       fub_axi_arready,
    output logic [ARSize-1:0]          fub_axi_ar_pkt,

    input  logic                       fub_axi_rvalid,
    output logic                       fub_axi_rready,
    output logic [2:0]                 fub_axi_r_count,
    input  logic [RSize-1:0]           fub_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Instantiate Write Stub
    axi5_slave_wr_stub #(
        .SKID_DEPTH_AW     (SKID_DEPTH_AW),
        .SKID_DEPTH_W      (SKID_DEPTH_W),
        .SKID_DEPTH_B      (SKID_DEPTH_B),
        .AXI_ID_WIDTH      (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH    (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH    (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH    (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH   (AXI_WSTRB_WIDTH),
        .AXI_ATOP_WIDTH    (AXI_ATOP_WIDTH),
        .AXI_NSAID_WIDTH   (AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH    (AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH   (AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH     (AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH   (AXI_TAGOP_WIDTH)
    ) inst_wr_stub (
        .aclk              (aclk),
        .aresetn           (aresetn),
        .s_axi_awid        (s_axi_awid),
        .s_axi_awaddr      (s_axi_awaddr),
        .s_axi_awlen       (s_axi_awlen),
        .s_axi_awsize      (s_axi_awsize),
        .s_axi_awburst     (s_axi_awburst),
        .s_axi_awlock      (s_axi_awlock),
        .s_axi_awcache     (s_axi_awcache),
        .s_axi_awprot      (s_axi_awprot),
        .s_axi_awqos       (s_axi_awqos),
        .s_axi_awuser      (s_axi_awuser),
        .s_axi_awvalid     (s_axi_awvalid),
        .s_axi_awready     (s_axi_awready),
        .s_axi_awatop      (s_axi_awatop),
        .s_axi_awnsaid     (s_axi_awnsaid),
        .s_axi_awtrace     (s_axi_awtrace),
        .s_axi_awmpam      (s_axi_awmpam),
        .s_axi_awmecid     (s_axi_awmecid),
        .s_axi_awunique    (s_axi_awunique),
        .s_axi_awtagop     (s_axi_awtagop),
        .s_axi_awtag       (s_axi_awtag),
        .s_axi_wdata       (s_axi_wdata),
        .s_axi_wstrb       (s_axi_wstrb),
        .s_axi_wlast       (s_axi_wlast),
        .s_axi_wuser       (s_axi_wuser),
        .s_axi_wvalid      (s_axi_wvalid),
        .s_axi_wready      (s_axi_wready),
        .s_axi_wpoison     (s_axi_wpoison),
        .s_axi_wtag        (s_axi_wtag),
        .s_axi_wtagupdate  (s_axi_wtagupdate),
        .s_axi_bid         (s_axi_bid),
        .s_axi_bresp       (s_axi_bresp),
        .s_axi_buser       (s_axi_buser),
        .s_axi_bvalid      (s_axi_bvalid),
        .s_axi_bready      (s_axi_bready),
        .s_axi_btrace      (s_axi_btrace),
        .s_axi_btag        (s_axi_btag),
        .s_axi_btagmatch   (s_axi_btagmatch),
        .fub_axi_awvalid   (fub_axi_awvalid),
        .fub_axi_awready   (fub_axi_awready),
        .fub_axi_aw_pkt    (fub_axi_aw_pkt),
        .fub_axi_wvalid    (fub_axi_wvalid),
        .fub_axi_wready    (fub_axi_wready),
        .fub_axi_w_pkt     (fub_axi_w_pkt),
        .fub_axi_bvalid    (fub_axi_bvalid),
        .fub_axi_bready    (fub_axi_bready),
        .fub_axi_b_count   (fub_axi_b_count),
        .fub_axi_b_pkt     (fub_axi_b_pkt)
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Instantiate Read Stub
    axi5_slave_rd_stub #(
        .SKID_DEPTH_AR     (SKID_DEPTH_AR),
        .SKID_DEPTH_R      (SKID_DEPTH_R),
        .AXI_ID_WIDTH      (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH    (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH    (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH    (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH   (AXI_WSTRB_WIDTH),
        .AXI_NSAID_WIDTH   (AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH    (AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH   (AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH     (AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH   (AXI_TAGOP_WIDTH),
        .AXI_CHUNKNUM_WIDTH(AXI_CHUNKNUM_WIDTH)
    ) inst_rd_stub (
        .aclk              (aclk),
        .aresetn           (aresetn),
        .s_axi_arid        (s_axi_arid),
        .s_axi_araddr      (s_axi_araddr),
        .s_axi_arlen       (s_axi_arlen),
        .s_axi_arsize      (s_axi_arsize),
        .s_axi_arburst     (s_axi_arburst),
        .s_axi_arlock      (s_axi_arlock),
        .s_axi_arcache     (s_axi_arcache),
        .s_axi_arprot      (s_axi_arprot),
        .s_axi_arqos       (s_axi_arqos),
        .s_axi_aruser      (s_axi_aruser),
        .s_axi_arvalid     (s_axi_arvalid),
        .s_axi_arready     (s_axi_arready),
        .s_axi_arnsaid     (s_axi_arnsaid),
        .s_axi_artrace     (s_axi_artrace),
        .s_axi_armpam      (s_axi_armpam),
        .s_axi_armecid     (s_axi_armecid),
        .s_axi_arunique    (s_axi_arunique),
        .s_axi_archunken   (s_axi_archunken),
        .s_axi_artagop     (s_axi_artagop),
        .s_axi_rid         (s_axi_rid),
        .s_axi_rdata       (s_axi_rdata),
        .s_axi_rresp       (s_axi_rresp),
        .s_axi_rlast       (s_axi_rlast),
        .s_axi_ruser       (s_axi_ruser),
        .s_axi_rvalid      (s_axi_rvalid),
        .s_axi_rready      (s_axi_rready),
        .s_axi_rtrace      (s_axi_rtrace),
        .s_axi_rpoison     (s_axi_rpoison),
        .s_axi_rchunkv     (s_axi_rchunkv),
        .s_axi_rchunknum   (s_axi_rchunknum),
        .s_axi_rchunkstrb  (s_axi_rchunkstrb),
        .s_axi_rtag        (s_axi_rtag),
        .s_axi_rtagmatch   (s_axi_rtagmatch),
        .fub_axi_arvalid   (fub_axi_arvalid),
        .fub_axi_arready   (fub_axi_arready),
        .fub_axi_ar_pkt    (fub_axi_ar_pkt),
        .fub_axi_rvalid    (fub_axi_rvalid),
        .fub_axi_rready    (fub_axi_rready),
        .fub_axi_r_count   (fub_axi_r_count),
        .fub_axi_r_pkt     (fub_axi_r_pkt)
    );

endmodule : axi5_slave_stub
