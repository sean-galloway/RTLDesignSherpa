// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_rd
// Purpose: AXI5 Slave Read module with full AXI5 protocol support
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

module axi5_slave_rd
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

    // Feature enables
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_CHUNKING   = 1,
    parameter bit ENABLE_MTE        = 1,
    parameter bit ENABLE_POISON     = 1,

    // Short params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,

    parameter int ARSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             (ENABLE_NSAID ? AXI_NSAID_WIDTH : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MPAM ? AXI_MPAM_WIDTH : 0) +
                             (ENABLE_MECID ? AXI_MECID_WIDTH : 0) +
                             (ENABLE_UNIQUE ? 1 : 0) +
                             (ENABLE_CHUNKING ? 1 : 0) +
                             (ENABLE_MTE ? AXI_TAGOP_WIDTH : 0),

    parameter int RSize    = IW + DW + 2 + 1 + UW +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_POISON ? 1 : 0) +
                             (ENABLE_CHUNKING ? (1 + AXI_CHUNKNUM_WIDTH + CHUNK_STRB_WIDTH) : 0) +
                             (ENABLE_MTE ? (TW + 1) : 0)
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // =========================================================================
    // Slave AXI5 Interface (Input Side from external master)
    // =========================================================================

    // Read address channel (AR)
    input  logic [IW-1:0]                s_axi_arid,
    input  logic [AW-1:0]                s_axi_araddr,
    input  logic [7:0]                   s_axi_arlen,
    input  logic [2:0]                   s_axi_arsize,
    input  logic [1:0]                   s_axi_arburst,
    input  logic                         s_axi_arlock,
    input  logic [3:0]                   s_axi_arcache,
    input  logic [2:0]                   s_axi_arprot,
    input  logic [3:0]                   s_axi_arqos,
    input  logic [UW-1:0]                s_axi_aruser,
    input  logic                         s_axi_arvalid,
    output logic                         s_axi_arready,

    // AXI5 AR signals
    input  logic [AXI_NSAID_WIDTH-1:0]   s_axi_arnsaid,
    input  logic                         s_axi_artrace,
    input  logic [AXI_MPAM_WIDTH-1:0]    s_axi_armpam,
    input  logic [AXI_MECID_WIDTH-1:0]   s_axi_armecid,
    input  logic                         s_axi_arunique,
    input  logic                         s_axi_archunken,
    input  logic [AXI_TAGOP_WIDTH-1:0]   s_axi_artagop,

    // Read data channel (R)
    output logic [IW-1:0]                s_axi_rid,
    output logic [DW-1:0]                s_axi_rdata,
    output logic [1:0]                   s_axi_rresp,
    output logic                         s_axi_rlast,
    output logic [UW-1:0]                s_axi_ruser,
    output logic                         s_axi_rvalid,
    input  logic                         s_axi_rready,

    // AXI5 R signals
    output logic                         s_axi_rtrace,
    output logic                         s_axi_rpoison,
    output logic                         s_axi_rchunkv,
    output logic [AXI_CHUNKNUM_WIDTH-1:0] s_axi_rchunknum,
    output logic [CHUNK_STRB_WIDTH-1:0]  s_axi_rchunkstrb,
    output logic [TW-1:0]                s_axi_rtag,
    output logic                         s_axi_rtagmatch,

    // =========================================================================
    // FUB Interface (Output Side to memory or backend)
    // =========================================================================

    // Read address channel (AR)
    output logic [IW-1:0]                fub_axi_arid,
    output logic [AW-1:0]                fub_axi_araddr,
    output logic [7:0]                   fub_axi_arlen,
    output logic [2:0]                   fub_axi_arsize,
    output logic [1:0]                   fub_axi_arburst,
    output logic                         fub_axi_arlock,
    output logic [3:0]                   fub_axi_arcache,
    output logic [2:0]                   fub_axi_arprot,
    output logic [3:0]                   fub_axi_arqos,
    output logic [UW-1:0]                fub_axi_aruser,
    output logic                         fub_axi_arvalid,
    input  logic                         fub_axi_arready,

    // AXI5 AR signals
    output logic [AXI_NSAID_WIDTH-1:0]   fub_axi_arnsaid,
    output logic                         fub_axi_artrace,
    output logic [AXI_MPAM_WIDTH-1:0]    fub_axi_armpam,
    output logic [AXI_MECID_WIDTH-1:0]   fub_axi_armecid,
    output logic                         fub_axi_arunique,
    output logic                         fub_axi_archunken,
    output logic [AXI_TAGOP_WIDTH-1:0]   fub_axi_artagop,

    // Read data channel (R)
    input  logic [IW-1:0]                fub_axi_rid,
    input  logic [DW-1:0]                fub_axi_rdata,
    input  logic [1:0]                   fub_axi_rresp,
    input  logic                         fub_axi_rlast,
    input  logic [UW-1:0]                fub_axi_ruser,
    input  logic                         fub_axi_rvalid,
    output logic                         fub_axi_rready,

    // AXI5 R signals
    input  logic                         fub_axi_rtrace,
    input  logic                         fub_axi_rpoison,
    input  logic                         fub_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] fub_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0]  fub_axi_rchunkstrb,
    input  logic [TW-1:0]                fub_axi_rtag,
    input  logic                         fub_axi_rtagmatch,

    // Status outputs for clock gating
    output logic                         busy
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    logic [3:0]                int_ar_count;
    logic [ARSize-1:0]         int_ar_pkt;
    logic                      int_skid_arvalid;
    logic                      int_skid_arready;

    logic [3:0]                int_r_count;
    logic [RSize-1:0]          int_r_pkt;
    logic                      int_skid_rvalid;
    logic                      int_skid_rready;

    logic [ARSize-1:0]         w_ar_wr_data;
    logic [ARSize-1:0]         w_ar_rd_data;
    logic [RSize-1:0]          w_r_wr_data;
    logic [RSize-1:0]          w_r_rd_data;

    // =========================================================================
    // Busy Signal
    // =========================================================================

    assign busy = (int_ar_count > 0) || (int_r_count > 0) ||
                  s_axi_arvalid || fub_axi_rvalid;

    // =========================================================================
    // AR Channel Packing
    // =========================================================================

    always_comb begin
        automatic int idx = 0;

        w_ar_wr_data[idx +: IW] = s_axi_arid;
        idx += IW;
        w_ar_wr_data[idx +: AW] = s_axi_araddr;
        idx += AW;
        w_ar_wr_data[idx +: 8] = s_axi_arlen;
        idx += 8;
        w_ar_wr_data[idx +: 3] = s_axi_arsize;
        idx += 3;
        w_ar_wr_data[idx +: 2] = s_axi_arburst;
        idx += 2;
        w_ar_wr_data[idx +: 1] = s_axi_arlock;
        idx += 1;
        w_ar_wr_data[idx +: 4] = s_axi_arcache;
        idx += 4;
        w_ar_wr_data[idx +: 3] = s_axi_arprot;
        idx += 3;
        w_ar_wr_data[idx +: 4] = s_axi_arqos;
        idx += 4;
        w_ar_wr_data[idx +: UW] = s_axi_aruser;
        idx += UW;

        if (ENABLE_NSAID) begin
            w_ar_wr_data[idx +: AXI_NSAID_WIDTH] = s_axi_arnsaid;
            idx += AXI_NSAID_WIDTH;
        end
        if (ENABLE_TRACE) begin
            w_ar_wr_data[idx +: 1] = s_axi_artrace;
            idx += 1;
        end
        if (ENABLE_MPAM) begin
            w_ar_wr_data[idx +: AXI_MPAM_WIDTH] = s_axi_armpam;
            idx += AXI_MPAM_WIDTH;
        end
        if (ENABLE_MECID) begin
            w_ar_wr_data[idx +: AXI_MECID_WIDTH] = s_axi_armecid;
            idx += AXI_MECID_WIDTH;
        end
        if (ENABLE_UNIQUE) begin
            w_ar_wr_data[idx +: 1] = s_axi_arunique;
            idx += 1;
        end
        if (ENABLE_CHUNKING) begin
            w_ar_wr_data[idx +: 1] = s_axi_archunken;
            idx += 1;
        end
        if (ENABLE_MTE) begin
            w_ar_wr_data[idx +: AXI_TAGOP_WIDTH] = s_axi_artagop;
            idx += AXI_TAGOP_WIDTH;
        end
    end

    always_comb begin
        automatic int idx = 0;

        fub_axi_arid = w_ar_rd_data[idx +: IW];
        idx += IW;
        fub_axi_araddr = w_ar_rd_data[idx +: AW];
        idx += AW;
        fub_axi_arlen = w_ar_rd_data[idx +: 8];
        idx += 8;
        fub_axi_arsize = w_ar_rd_data[idx +: 3];
        idx += 3;
        fub_axi_arburst = w_ar_rd_data[idx +: 2];
        idx += 2;
        fub_axi_arlock = w_ar_rd_data[idx +: 1];
        idx += 1;
        fub_axi_arcache = w_ar_rd_data[idx +: 4];
        idx += 4;
        fub_axi_arprot = w_ar_rd_data[idx +: 3];
        idx += 3;
        fub_axi_arqos = w_ar_rd_data[idx +: 4];
        idx += 4;
        fub_axi_aruser = w_ar_rd_data[idx +: UW];
        idx += UW;

        if (ENABLE_NSAID) begin
            fub_axi_arnsaid = w_ar_rd_data[idx +: AXI_NSAID_WIDTH];
            idx += AXI_NSAID_WIDTH;
        end else begin
            fub_axi_arnsaid = '0;
        end

        if (ENABLE_TRACE) begin
            fub_axi_artrace = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_artrace = '0;
        end

        if (ENABLE_MPAM) begin
            fub_axi_armpam = w_ar_rd_data[idx +: AXI_MPAM_WIDTH];
            idx += AXI_MPAM_WIDTH;
        end else begin
            fub_axi_armpam = '0;
        end

        if (ENABLE_MECID) begin
            fub_axi_armecid = w_ar_rd_data[idx +: AXI_MECID_WIDTH];
            idx += AXI_MECID_WIDTH;
        end else begin
            fub_axi_armecid = '0;
        end

        if (ENABLE_UNIQUE) begin
            fub_axi_arunique = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_arunique = '0;
        end

        if (ENABLE_CHUNKING) begin
            fub_axi_archunken = w_ar_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_archunken = '0;
        end

        if (ENABLE_MTE) begin
            fub_axi_artagop = w_ar_rd_data[idx +: AXI_TAGOP_WIDTH];
            idx += AXI_TAGOP_WIDTH;
        end else begin
            fub_axi_artagop = '0;
        end
    end

    // =========================================================================
    // R Channel Packing
    // =========================================================================

    always_comb begin
        automatic int idx = 0;

        w_r_wr_data[idx +: IW] = fub_axi_rid;
        idx += IW;
        w_r_wr_data[idx +: DW] = fub_axi_rdata;
        idx += DW;
        w_r_wr_data[idx +: 2] = fub_axi_rresp;
        idx += 2;
        w_r_wr_data[idx +: 1] = fub_axi_rlast;
        idx += 1;
        w_r_wr_data[idx +: UW] = fub_axi_ruser;
        idx += UW;

        if (ENABLE_TRACE) begin
            w_r_wr_data[idx +: 1] = fub_axi_rtrace;
            idx += 1;
        end
        if (ENABLE_POISON) begin
            w_r_wr_data[idx +: 1] = fub_axi_rpoison;
            idx += 1;
        end
        if (ENABLE_CHUNKING) begin
            w_r_wr_data[idx +: 1] = fub_axi_rchunkv;
            idx += 1;
            w_r_wr_data[idx +: AXI_CHUNKNUM_WIDTH] = fub_axi_rchunknum;
            idx += AXI_CHUNKNUM_WIDTH;
            w_r_wr_data[idx +: CHUNK_STRB_WIDTH] = fub_axi_rchunkstrb;
            idx += CHUNK_STRB_WIDTH;
        end
        if (ENABLE_MTE) begin
            w_r_wr_data[idx +: TW] = fub_axi_rtag;
            idx += TW;
            w_r_wr_data[idx +: 1] = fub_axi_rtagmatch;
            idx += 1;
        end
    end

    always_comb begin
        automatic int idx = 0;

        s_axi_rid = w_r_rd_data[idx +: IW];
        idx += IW;
        s_axi_rdata = w_r_rd_data[idx +: DW];
        idx += DW;
        s_axi_rresp = w_r_rd_data[idx +: 2];
        idx += 2;
        s_axi_rlast = w_r_rd_data[idx +: 1];
        idx += 1;
        s_axi_ruser = w_r_rd_data[idx +: UW];
        idx += UW;

        if (ENABLE_TRACE) begin
            s_axi_rtrace = w_r_rd_data[idx +: 1];
            idx += 1;
        end else begin
            s_axi_rtrace = '0;
        end

        if (ENABLE_POISON) begin
            s_axi_rpoison = w_r_rd_data[idx +: 1];
            idx += 1;
        end else begin
            s_axi_rpoison = '0;
        end

        if (ENABLE_CHUNKING) begin
            s_axi_rchunkv = w_r_rd_data[idx +: 1];
            idx += 1;
            s_axi_rchunknum = w_r_rd_data[idx +: AXI_CHUNKNUM_WIDTH];
            idx += AXI_CHUNKNUM_WIDTH;
            s_axi_rchunkstrb = w_r_rd_data[idx +: CHUNK_STRB_WIDTH];
            idx += CHUNK_STRB_WIDTH;
        end else begin
            s_axi_rchunkv = '0;
            s_axi_rchunknum = '0;
            s_axi_rchunkstrb = '0;
        end

        if (ENABLE_MTE) begin
            s_axi_rtag = w_r_rd_data[idx +: TW];
            idx += TW;
            s_axi_rtagmatch = w_r_rd_data[idx +: 1];
            idx += 1;
        end else begin
            s_axi_rtag = '0;
            s_axi_rtagmatch = '0;
        end
    end

    // =========================================================================
    // Instantiate AR Skid Buffer
    // =========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize),
        .INSTANCE_NAME("AR_SKID")
    ) i_ar_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (s_axi_arvalid),
        .wr_ready               (s_axi_arready),
        .wr_data                (w_ar_wr_data),
        .rd_valid               (int_skid_arvalid),
        .rd_ready               (int_skid_arready),
        .rd_count               (int_ar_count),
        .rd_data                (w_ar_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_axi_arvalid = int_skid_arvalid;
    assign int_skid_arready = fub_axi_arready;

    // =========================================================================
    // Instantiate R Skid Buffer
    // =========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize),
        .INSTANCE_NAME("R_SKID")
    ) i_r_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_rvalid),
        .wr_ready               (fub_axi_rready),
        .wr_data                (w_r_wr_data),
        .rd_valid               (int_skid_rvalid),
        .rd_ready               (int_skid_rready),
        .rd_count               (int_r_count),
        .rd_data                (w_r_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign s_axi_rvalid = int_skid_rvalid;
    assign int_skid_rready = s_axi_rready;

endmodule : axi5_slave_rd
