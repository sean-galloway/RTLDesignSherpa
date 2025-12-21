// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_rd
// Purpose: AXI5 Master Read module with full AXI5 protocol support
//
// AXI5 Enhancements over AXI4:
// - ARNSAID: Non-secure access identifier
// - ARTRACE: Trace signal for debug
// - ARMPAM: Memory Partitioning and Monitoring
// - ARMECID: Memory Encryption Context ID
// - ARUNIQUE: Unique ID indicator
// - ARCHUNKEN: Read data chunking enable
// - ARTAGOP: Memory tag operation (MTE)
// - RTRACE: Read data trace signal
// - RPOISON: Data poison indicator
// - RCHUNKV: Read chunk valid
// - RCHUNKNUM: Read chunk number
// - RCHUNKSTRB: Read chunk strobe
// - RTAG: Memory tags (MTE)
// - RTAGMATCH: Tag match response
//
// Removed from AXI4:
// - ARREGION: Deprecated (not recommended for new designs)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_rd
#(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // AXI5 specific parameters
    parameter int AXI_NSAID_WIDTH   = 4,      // Non-secure access ID width
    parameter int AXI_MPAM_WIDTH    = 11,     // MPAM width (PartID + PMG)
    parameter int AXI_MECID_WIDTH   = 16,     // Memory encryption context ID width
    parameter int AXI_TAG_WIDTH     = 4,      // Memory tag width per 16 bytes
    parameter int AXI_TAGOP_WIDTH   = 2,      // Tag operation width
    parameter int AXI_CHUNKNUM_WIDTH = 4,     // Chunk number width

    // Feature enables (set to 0 to disable optional signals)
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_CHUNKING   = 1,
    parameter bit ENABLE_MTE        = 1,      // Memory Tagging Extension
    parameter bit ENABLE_POISON     = 1,

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    // Number of tags based on data width (1 tag per 16 bytes)
    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,

    // Chunk strobe width (128-bit granules)
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,

    // AR channel packet size calculation
    // Base: ID + ADDR + LEN + SIZE + BURST + LOCK + CACHE + PROT + QOS + USER
    // AXI5: + NSAID + TRACE + MPAM + MECID + UNIQUE + CHUNKEN + TAGOP
    parameter int ARSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             (ENABLE_NSAID ? AXI_NSAID_WIDTH : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MPAM ? AXI_MPAM_WIDTH : 0) +
                             (ENABLE_MECID ? AXI_MECID_WIDTH : 0) +
                             (ENABLE_UNIQUE ? 1 : 0) +
                             (ENABLE_CHUNKING ? 1 : 0) +
                             (ENABLE_MTE ? AXI_TAGOP_WIDTH : 0),

    // R channel packet size calculation
    // Base: ID + DATA + RESP + LAST + USER
    // AXI5: + TRACE + POISON + CHUNKV + CHUNKNUM + CHUNKSTRB + TAG + TAGMATCH
    parameter int RSize    = IW + DW + 2 + 1 + UW +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_POISON ? 1 : 0) +
                             (ENABLE_CHUNKING ? (1 + AXI_CHUNKNUM_WIDTH + CHUNK_STRB_WIDTH) : 0) +
                             (ENABLE_MTE ? (TW + 1) : 0)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // =========================================================================
    // Slave AXI5 Interface (Input Side - FUB/Functional Unit Block)
    // =========================================================================

    // Read address channel (AR)
    input  logic [IW-1:0]              fub_axi_arid,
    input  logic [AW-1:0]              fub_axi_araddr,
    input  logic [7:0]                 fub_axi_arlen,
    input  logic [2:0]                 fub_axi_arsize,
    input  logic [1:0]                 fub_axi_arburst,
    input  logic                       fub_axi_arlock,
    input  logic [3:0]                 fub_axi_arcache,
    input  logic [2:0]                 fub_axi_arprot,
    input  logic [3:0]                 fub_axi_arqos,
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // AXI5 AR channel signals
    input  logic [AXI_NSAID_WIDTH-1:0] fub_axi_arnsaid,    // Non-secure access ID
    input  logic                       fub_axi_artrace,    // Trace signal
    input  logic [AXI_MPAM_WIDTH-1:0]  fub_axi_armpam,     // Memory partitioning
    input  logic [AXI_MECID_WIDTH-1:0] fub_axi_armecid,    // Memory encryption context
    input  logic                       fub_axi_arunique,   // Unique ID indicator
    input  logic                       fub_axi_archunken,  // Chunk enable
    input  logic [AXI_TAGOP_WIDTH-1:0] fub_axi_artagop,    // Tag operation (MTE)

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // AXI5 R channel signals
    output logic                       fub_axi_rtrace,     // Trace signal
    output logic                       fub_axi_rpoison,    // Data poison indicator
    output logic                       fub_axi_rchunkv,    // Chunk valid
    output logic [AXI_CHUNKNUM_WIDTH-1:0] fub_axi_rchunknum, // Chunk number
    output logic [CHUNK_STRB_WIDTH-1:0] fub_axi_rchunkstrb, // Chunk strobe
    output logic [TW-1:0]              fub_axi_rtag,       // Memory tags
    output logic                       fub_axi_rtagmatch,  // Tag match response

    // =========================================================================
    // Master AXI5 Interface (Output Side)
    // =========================================================================

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

    // AXI5 AR channel signals
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

    // AXI5 R channel signals
    input  logic                       m_axi_rtrace,
    input  logic                       m_axi_rpoison,
    input  logic                       m_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] m_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0] m_axi_rchunkstrb,
    input  logic [TW-1:0]              m_axi_rtag,
    input  logic                       m_axi_rtagmatch,

    // Status outputs for clock gating
    output logic                       busy
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // SKID buffer connections
    logic [3:0]                int_ar_count;
    logic [ARSize-1:0]         int_ar_pkt;
    logic                      int_skid_arvalid;
    logic                      int_skid_arready;

    logic [3:0]                int_r_count;
    logic [RSize-1:0]          int_r_pkt;
    logic                      int_skid_rvalid;
    logic                      int_skid_rready;

    // AR channel packing signals
    logic [ARSize-1:0]         w_ar_wr_data;
    logic [ARSize-1:0]         w_ar_rd_data;

    // R channel packing signals
    logic [RSize-1:0]          w_r_wr_data;
    logic [RSize-1:0]          w_r_rd_data;

    // =========================================================================
    // Busy Signal
    // =========================================================================

    assign busy = (int_ar_count > 0) || (int_r_count > 0) ||
                  fub_axi_arvalid || m_axi_rvalid;

    // =========================================================================
    // AR Channel Packing
    // =========================================================================

    // Pack AR channel data for SKID buffer
    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        w_ar_wr_data[idx +: IW] = fub_axi_arid;
        idx += IW;
        w_ar_wr_data[idx +: AW] = fub_axi_araddr;
        idx += AW;
        w_ar_wr_data[idx +: 8] = fub_axi_arlen;
        idx += 8;
        w_ar_wr_data[idx +: 3] = fub_axi_arsize;
        idx += 3;
        w_ar_wr_data[idx +: 2] = fub_axi_arburst;
        idx += 2;
        w_ar_wr_data[idx +: 1] = fub_axi_arlock;
        idx += 1;
        w_ar_wr_data[idx +: 4] = fub_axi_arcache;
        idx += 4;
        w_ar_wr_data[idx +: 3] = fub_axi_arprot;
        idx += 3;
        w_ar_wr_data[idx +: 4] = fub_axi_arqos;
        idx += 4;
        w_ar_wr_data[idx +: UW] = fub_axi_aruser;
        idx += UW;

        // AXI5 signals (conditionally packed)
        if (ENABLE_NSAID) begin
            w_ar_wr_data[idx +: AXI_NSAID_WIDTH] = fub_axi_arnsaid;
            idx += AXI_NSAID_WIDTH;
        end
        if (ENABLE_TRACE) begin
            w_ar_wr_data[idx +: 1] = fub_axi_artrace;
            idx += 1;
        end
        if (ENABLE_MPAM) begin
            w_ar_wr_data[idx +: AXI_MPAM_WIDTH] = fub_axi_armpam;
            idx += AXI_MPAM_WIDTH;
        end
        if (ENABLE_MECID) begin
            w_ar_wr_data[idx +: AXI_MECID_WIDTH] = fub_axi_armecid;
            idx += AXI_MECID_WIDTH;
        end
        if (ENABLE_UNIQUE) begin
            w_ar_wr_data[idx +: 1] = fub_axi_arunique;
            idx += 1;
        end
        if (ENABLE_CHUNKING) begin
            w_ar_wr_data[idx +: 1] = fub_axi_archunken;
            idx += 1;
        end
        if (ENABLE_MTE) begin
            w_ar_wr_data[idx +: AXI_TAGOP_WIDTH] = fub_axi_artagop;
            idx += AXI_TAGOP_WIDTH;
        end
    end

    // Unpack AR channel data from SKID buffer
    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        m_axi_arid = w_ar_rd_data[idx +: IW];
        idx += IW;
        m_axi_araddr = w_ar_rd_data[idx +: AW];
        idx += AW;
        m_axi_arlen = w_ar_rd_data[idx +: 8];
        idx += 8;
        m_axi_arsize = w_ar_rd_data[idx +: 3];
        idx += 3;
        m_axi_arburst = w_ar_rd_data[idx +: 2];
        idx += 2;
        m_axi_arlock = w_ar_rd_data[idx +: 1];
        idx += 1;
        m_axi_arcache = w_ar_rd_data[idx +: 4];
        idx += 4;
        m_axi_arprot = w_ar_rd_data[idx +: 3];
        idx += 3;
        m_axi_arqos = w_ar_rd_data[idx +: 4];
        idx += 4;
        m_axi_aruser = w_ar_rd_data[idx +: UW];
        idx += UW;

        // AXI5 signals (conditionally unpacked)
        if (ENABLE_NSAID) begin
            m_axi_arnsaid = w_ar_rd_data[idx +: AXI_NSAID_WIDTH];
            idx += AXI_NSAID_WIDTH;
        end else begin
            m_axi_arnsaid = '0;
        end

        if (ENABLE_TRACE) begin
            m_axi_artrace = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axi_artrace = '0;
        end

        if (ENABLE_MPAM) begin
            m_axi_armpam = w_ar_rd_data[idx +: AXI_MPAM_WIDTH];
            idx += AXI_MPAM_WIDTH;
        end else begin
            m_axi_armpam = '0;
        end

        if (ENABLE_MECID) begin
            m_axi_armecid = w_ar_rd_data[idx +: AXI_MECID_WIDTH];
            idx += AXI_MECID_WIDTH;
        end else begin
            m_axi_armecid = '0;
        end

        if (ENABLE_UNIQUE) begin
            m_axi_arunique = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axi_arunique = '0;
        end

        if (ENABLE_CHUNKING) begin
            m_axi_archunken = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axi_archunken = '0;
        end

        if (ENABLE_MTE) begin
            m_axi_artagop = w_ar_rd_data[idx +: AXI_TAGOP_WIDTH];
            idx += AXI_TAGOP_WIDTH;
        end else begin
            m_axi_artagop = '0;
        end
    end

    // =========================================================================
    // R Channel Packing
    // =========================================================================

    // Pack R channel data for SKID buffer (from master side)
    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        w_r_wr_data[idx +: IW] = m_axi_rid;
        idx += IW;
        w_r_wr_data[idx +: DW] = m_axi_rdata;
        idx += DW;
        w_r_wr_data[idx +: 2] = m_axi_rresp;
        idx += 2;
        w_r_wr_data[idx +: 1] = m_axi_rlast;
        idx += 1;
        w_r_wr_data[idx +: UW] = m_axi_ruser;
        idx += UW;

        // AXI5 signals
        if (ENABLE_TRACE) begin
            w_r_wr_data[idx +: 1] = m_axi_rtrace;
            idx += 1;
        end
        if (ENABLE_POISON) begin
            w_r_wr_data[idx +: 1] = m_axi_rpoison;
            idx += 1;
        end
        if (ENABLE_CHUNKING) begin
            w_r_wr_data[idx +: 1] = m_axi_rchunkv;
            idx += 1;
            w_r_wr_data[idx +: AXI_CHUNKNUM_WIDTH] = m_axi_rchunknum;
            idx += AXI_CHUNKNUM_WIDTH;
            w_r_wr_data[idx +: CHUNK_STRB_WIDTH] = m_axi_rchunkstrb;
            idx += CHUNK_STRB_WIDTH;
        end
        if (ENABLE_MTE) begin
            w_r_wr_data[idx +: TW] = m_axi_rtag;
            idx += TW;
            w_r_wr_data[idx +: 1] = m_axi_rtagmatch;
            idx += 1;
        end
    end

    // Unpack R channel data from SKID buffer (to FUB side)
    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        fub_axi_rid = w_r_rd_data[idx +: IW];
        idx += IW;
        fub_axi_rdata = w_r_rd_data[idx +: DW];
        idx += DW;
        fub_axi_rresp = w_r_rd_data[idx +: 2];
        idx += 2;
        fub_axi_rlast = w_r_rd_data[idx +: 1];
        idx += 1;
        fub_axi_ruser = w_r_rd_data[idx +: UW];
        idx += UW;

        // AXI5 signals
        if (ENABLE_TRACE) begin
            fub_axi_rtrace = w_r_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_rtrace = '0;
        end

        if (ENABLE_POISON) begin
            fub_axi_rpoison = w_r_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_rpoison = '0;
        end

        if (ENABLE_CHUNKING) begin
            fub_axi_rchunkv = w_r_rd_data[idx +: 1];
            idx += 1;
            fub_axi_rchunknum = w_r_rd_data[idx +: AXI_CHUNKNUM_WIDTH];
            idx += AXI_CHUNKNUM_WIDTH;
            fub_axi_rchunkstrb = w_r_rd_data[idx +: CHUNK_STRB_WIDTH];
            idx += CHUNK_STRB_WIDTH;
        end else begin
            fub_axi_rchunkv = '0;
            fub_axi_rchunknum = '0;
            fub_axi_rchunkstrb = '0;
        end

        if (ENABLE_MTE) begin
            fub_axi_rtag = w_r_rd_data[idx +: TW];
            idx += TW;
            fub_axi_rtagmatch = w_r_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_rtag = '0;
            fub_axi_rtagmatch = '0;
        end
    end

    // =========================================================================
    // Instantiate AR Skid Buffer
    // =========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize),
        .INSTANCE_NAME("AR_SKID")
    ) ar_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_arvalid),
        .wr_ready               (fub_axi_arready),
        .wr_data                (w_ar_wr_data),
        .rd_valid               (int_skid_arvalid),
        .rd_ready               (int_skid_arready),
        .rd_count               (int_ar_count),
        .rd_data                (w_ar_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign m_axi_arvalid = int_skid_arvalid;
    assign int_skid_arready = m_axi_arready;

    // =========================================================================
    // Instantiate R Skid Buffer
    // =========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize),
        .INSTANCE_NAME("R_SKID")
    ) r_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_rvalid),
        .wr_ready               (m_axi_rready),
        .wr_data                (w_r_wr_data),
        .rd_valid               (int_skid_rvalid),
        .rd_ready               (int_skid_rready),
        .rd_count               (int_r_count),
        .rd_data                (w_r_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_axi_rvalid = int_skid_rvalid;
    assign int_skid_rready = fub_axi_rready;

endmodule : axi5_master_rd
