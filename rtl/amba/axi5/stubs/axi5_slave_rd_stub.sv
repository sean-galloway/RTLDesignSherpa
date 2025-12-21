// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_rd_stub
// Purpose: AXI5 Slave Read Stub module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_rd_stub
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

    // AXI5 AR signals
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

    // AXI5 R signals
    output logic                       s_axi_rtrace,
    output logic                       s_axi_rpoison,
    output logic                       s_axi_rchunkv,
    output logic [AXI_CHUNKNUM_WIDTH-1:0] s_axi_rchunknum,
    output logic [CHUNK_STRB_WIDTH-1:0] s_axi_rchunkstrb,
    output logic [TW-1:0]              s_axi_rtag,
    output logic                       s_axi_rtagmatch,

    // Stub Outputs/Inputs
    // AR interface
    output logic                       fub_axi_arvalid,
    input  logic                       fub_axi_arready,
    output logic [ARSize-1:0]          fub_axi_ar_pkt,

    // R interface
    input  logic                       fub_axi_rvalid,
    output logic                       fub_axi_rready,
    output logic [2:0]                 fub_axi_r_count,
    input  logic [RSize-1:0]           fub_axi_r_pkt
);

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Read address channel (AR)
    gaxi_skid_buffer #(.DEPTH(SKID_DEPTH_AR), .DATA_WIDTH(ARSize), .INSTANCE_NAME("AR-Phase")) inst_ar_phase (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axi_arvalid),
        .wr_ready               (s_axi_arready),
        .wr_data                ({s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst,
                                  s_axi_arlock, s_axi_arcache, s_axi_arprot, s_axi_arqos, s_axi_aruser,
                                  s_axi_arnsaid, s_axi_artrace, s_axi_armpam, s_axi_armecid,
                                  s_axi_arunique, s_axi_archunken, s_axi_artagop}),
        .rd_valid               (fub_axi_arvalid),
        .rd_ready               (fub_axi_arready),
        .rd_data                (fub_axi_ar_pkt),
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
        .wr_valid               (fub_axi_rvalid),
        .wr_ready               (fub_axi_rready),
        .wr_data                (fub_axi_r_pkt),
        .rd_valid               (s_axi_rvalid),
        .rd_ready               (s_axi_rready),
        .rd_data                ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser,
                                  s_axi_rtrace, s_axi_rpoison, s_axi_rchunkv, s_axi_rchunknum,
                                  s_axi_rchunkstrb, s_axi_rtag, s_axi_rtagmatch}),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  (),
        .rd_count               ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi5_slave_rd_stub
