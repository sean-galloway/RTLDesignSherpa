// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_stub
// Purpose: AXI5 Master Stub module (combined read and write)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_stub
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
    output logic                       m_axi_wpoison,
    output logic [TW-1:0]              m_axi_wtag,
    output logic [NUM_TAGS-1:0]        m_axi_wtagupdate,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,
    input  logic                       m_axi_btrace,
    input  logic [TW-1:0]              m_axi_btag,
    input  logic                       m_axi_btagmatch,

    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,
    output logic [AXI_NSAID_WIDTH-1:0] m_axi_arnsaid,
    output logic                       m_axi_artrace,
    output logic [AXI_MPAM_WIDTH-1:0]  m_axi_armpam,
    output logic [AXI_MECID_WIDTH-1:0] m_axi_armecid,
    output logic                       m_axi_arunique,
    output logic                       m_axi_archunken,
    output logic [AXI_TAGOP_WIDTH-1:0] m_axi_artagop,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,
    input  logic                       m_axi_rtrace,
    input  logic                       m_axi_rpoison,
    input  logic                       m_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] m_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0] m_axi_rchunkstrb,
    input  logic [TW-1:0]              m_axi_rtag,
    input  logic                       m_axi_rtagmatch,

    // Stub Write Interfaces
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,
    output logic [3:0]                 fub_axi_aw_count,
    input  logic [AWSize-1:0]          fub_axi_aw_pkt,

    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,
    input  logic [WSize-1:0]           fub_axi_w_pkt,

    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,
    output logic [BSize-1:0]           fub_axi_b_pkt,

    // Stub Read Interfaces
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,
    output logic [2:0]                 fub_axi_ar_count,
    input  logic [ARSize-1:0]          fub_axi_ar_pkt,

    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,
    output logic [RSize-1:0]           fub_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Instantiate Write Stub
    axi5_master_wr_stub #(
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
        .m_axi_awid        (m_axi_awid),
        .m_axi_awaddr      (m_axi_awaddr),
        .m_axi_awlen       (m_axi_awlen),
        .m_axi_awsize      (m_axi_awsize),
        .m_axi_awburst     (m_axi_awburst),
        .m_axi_awlock      (m_axi_awlock),
        .m_axi_awcache     (m_axi_awcache),
        .m_axi_awprot      (m_axi_awprot),
        .m_axi_awqos       (m_axi_awqos),
        .m_axi_awuser      (m_axi_awuser),
        .m_axi_awvalid     (m_axi_awvalid),
        .m_axi_awready     (m_axi_awready),
        .m_axi_awatop      (m_axi_awatop),
        .m_axi_awnsaid     (m_axi_awnsaid),
        .m_axi_awtrace     (m_axi_awtrace),
        .m_axi_awmpam      (m_axi_awmpam),
        .m_axi_awmecid     (m_axi_awmecid),
        .m_axi_awunique    (m_axi_awunique),
        .m_axi_awtagop     (m_axi_awtagop),
        .m_axi_awtag       (m_axi_awtag),
        .m_axi_wdata       (m_axi_wdata),
        .m_axi_wstrb       (m_axi_wstrb),
        .m_axi_wlast       (m_axi_wlast),
        .m_axi_wuser       (m_axi_wuser),
        .m_axi_wvalid      (m_axi_wvalid),
        .m_axi_wready      (m_axi_wready),
        .m_axi_wpoison     (m_axi_wpoison),
        .m_axi_wtag        (m_axi_wtag),
        .m_axi_wtagupdate  (m_axi_wtagupdate),
        .m_axi_bid         (m_axi_bid),
        .m_axi_bresp       (m_axi_bresp),
        .m_axi_buser       (m_axi_buser),
        .m_axi_bvalid      (m_axi_bvalid),
        .m_axi_bready      (m_axi_bready),
        .m_axi_btrace      (m_axi_btrace),
        .m_axi_btag        (m_axi_btag),
        .m_axi_btagmatch   (m_axi_btagmatch),
        .fub_axi_awvalid   (fub_axi_awvalid),
        .fub_axi_awready   (fub_axi_awready),
        .fub_axi_aw_count  (fub_axi_aw_count),
        .fub_axi_aw_pkt    (fub_axi_aw_pkt),
        .fub_axi_wvalid    (fub_axi_wvalid),
        .fub_axi_wready    (fub_axi_wready),
        .fub_axi_w_pkt     (fub_axi_w_pkt),
        .fub_axi_bvalid    (fub_axi_bvalid),
        .fub_axi_bready    (fub_axi_bready),
        .fub_axi_b_pkt     (fub_axi_b_pkt)
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Instantiate Read Stub
    axi5_master_rd_stub #(
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
        .m_axi_arid        (m_axi_arid),
        .m_axi_araddr      (m_axi_araddr),
        .m_axi_arlen       (m_axi_arlen),
        .m_axi_arsize      (m_axi_arsize),
        .m_axi_arburst     (m_axi_arburst),
        .m_axi_arlock      (m_axi_arlock),
        .m_axi_arcache     (m_axi_arcache),
        .m_axi_arprot      (m_axi_arprot),
        .m_axi_arqos       (m_axi_arqos),
        .m_axi_aruser      (m_axi_aruser),
        .m_axi_arvalid     (m_axi_arvalid),
        .m_axi_arready     (m_axi_arready),
        .m_axi_arnsaid     (m_axi_arnsaid),
        .m_axi_artrace     (m_axi_artrace),
        .m_axi_armpam      (m_axi_armpam),
        .m_axi_armecid     (m_axi_armecid),
        .m_axi_arunique    (m_axi_arunique),
        .m_axi_archunken   (m_axi_archunken),
        .m_axi_artagop     (m_axi_artagop),
        .m_axi_rid         (m_axi_rid),
        .m_axi_rdata       (m_axi_rdata),
        .m_axi_rresp       (m_axi_rresp),
        .m_axi_rlast       (m_axi_rlast),
        .m_axi_ruser       (m_axi_ruser),
        .m_axi_rvalid      (m_axi_rvalid),
        .m_axi_rready      (m_axi_rready),
        .m_axi_rtrace      (m_axi_rtrace),
        .m_axi_rpoison     (m_axi_rpoison),
        .m_axi_rchunkv     (m_axi_rchunkv),
        .m_axi_rchunknum   (m_axi_rchunknum),
        .m_axi_rchunkstrb  (m_axi_rchunkstrb),
        .m_axi_rtag        (m_axi_rtag),
        .m_axi_rtagmatch   (m_axi_rtagmatch),
        .fub_axi_arvalid   (fub_axi_arvalid),
        .fub_axi_arready   (fub_axi_arready),
        .fub_axi_ar_count  (fub_axi_ar_count),
        .fub_axi_ar_pkt    (fub_axi_ar_pkt),
        .fub_axi_rvalid    (fub_axi_rvalid),
        .fub_axi_rready    (fub_axi_rready),
        .fub_axi_r_pkt     (fub_axi_r_pkt)
    );

endmodule : axi5_master_stub
