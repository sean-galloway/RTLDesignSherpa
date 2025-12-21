// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_rd_stub
// Purpose: AXI5 Master Read Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_rd_stub
#(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
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

    // AR channel: ID + ADDR + LEN + SIZE + BURST + LOCK + CACHE + PROT + QOS + USER + AXI5 signals
    parameter int ARSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             AXI_NSAID_WIDTH + 1 + AXI_MPAM_WIDTH + AXI_MECID_WIDTH +
                             1 + 1 + AXI_TAGOP_WIDTH,
    // R channel: ID + DATA + RESP + LAST + USER + AXI5 signals
    parameter int RSize    = IW + DW + 2 + 1 + UW + 1 + 1 + 1 + AXI_CHUNKNUM_WIDTH +
                             CHUNK_STRB_WIDTH + TW + 1
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

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

    // AXI5 AR signals
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

    // AXI5 R signals
    input  logic                       m_axi_rtrace,
    input  logic                       m_axi_rpoison,
    input  logic                       m_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] m_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0] m_axi_rchunkstrb,
    input  logic [TW-1:0]              m_axi_rtag,
    input  logic                       m_axi_rtagmatch,

    // Stub Outputs/Inputs
    // AR interface
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,
    output logic [2:0]                 fub_axi_ar_count,
    input  logic [ARSize-1:0]          fub_axi_ar_pkt,

    // R interface
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,
    output logic [RSize-1:0]           fub_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AR), .DATA_WIDTH(ARSize), .INSTANCE_NAME("AR-Phase")) inst_ar_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_arvalid),
        .wr_ready               (fub_axi_arready),
        .wr_data                (fub_axi_ar_pkt),
        .rd_valid               (m_axi_arvalid),
        .rd_ready               (m_axi_arready),
        .rd_data                ({m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
                                  m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos, m_axi_aruser,
                                  m_axi_arnsaid, m_axi_artrace, m_axi_armpam, m_axi_armecid,
                                  m_axi_arunique, m_axi_archunken, m_axi_artagop}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read data channel (R)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_R), .DATA_WIDTH(RSize), .INSTANCE_NAME("R-Phase")) inst_r_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_rvalid),
        .wr_ready               (m_axi_rready),
        .wr_data                ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser,
                                  m_axi_rtrace, m_axi_rpoison, m_axi_rchunkv, m_axi_rchunknum,
                                  m_axi_rchunkstrb, m_axi_rtag, m_axi_rtagmatch}),
        .rd_valid               (fub_axi_rvalid),
        .rd_ready               (fub_axi_rready),
        .rd_data                (fub_axi_r_pkt),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi5_master_rd_stub
