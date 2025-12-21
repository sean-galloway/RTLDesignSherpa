// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_wr
// Purpose: AXI5 Master Write module with full AXI5 protocol support
//
// AXI5 Enhancements over AXI4:
// - AWATOP: Atomic transaction operation type
// - AWNSAID: Non-secure access identifier
// - AWTRACE: Trace signal for debug
// - AWMPAM: Memory Partitioning and Monitoring
// - AWMECID: Memory Encryption Context ID
// - AWUNIQUE: Unique ID indicator
// - AWTAGOP: Memory tag operation (MTE)
// - AWTAG: Memory tags for address
// - WPOISON: Write data poison indicator
// - WTAG: Write data memory tags
// - WTAGUPDATE: Tag update mask
// - BTRACE: Response trace signal
// - BTAG: Response memory tags
// - BTAGMATCH: Tag match response
//
// Removed from AXI4:
// - AWREGION: Deprecated (not recommended for new designs)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_wr
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
    parameter int AXI_ATOP_WIDTH    = 6,      // Atomic operation width
    parameter int AXI_NSAID_WIDTH   = 4,      // Non-secure access ID width
    parameter int AXI_MPAM_WIDTH    = 11,     // MPAM width (PartID + PMG)
    parameter int AXI_MECID_WIDTH   = 16,     // Memory encryption context ID width
    parameter int AXI_TAG_WIDTH     = 4,      // Memory tag width per 16 bytes
    parameter int AXI_TAGOP_WIDTH   = 2,      // Tag operation width

    // Feature enables (set to 0 to disable optional signals)
    parameter bit ENABLE_ATOMIC     = 1,
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
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

    // AW channel packet size calculation
    // Base: ID + ADDR + LEN + SIZE + BURST + LOCK + CACHE + PROT + QOS + USER
    // AXI5: + ATOP + NSAID + TRACE + MPAM + MECID + UNIQUE + TAGOP + TAG
    parameter int AWSize   = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + UW +
                             (ENABLE_ATOMIC ? AXI_ATOP_WIDTH : 0) +
                             (ENABLE_NSAID ? AXI_NSAID_WIDTH : 0) +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MPAM ? AXI_MPAM_WIDTH : 0) +
                             (ENABLE_MECID ? AXI_MECID_WIDTH : 0) +
                             (ENABLE_UNIQUE ? 1 : 0) +
                             (ENABLE_MTE ? (AXI_TAGOP_WIDTH + TW) : 0),

    // W channel packet size calculation
    // Base: DATA + STRB + LAST + USER
    // AXI5: + POISON + TAG + TAGUPDATE
    parameter int WSize    = DW + SW + 1 + UW +
                             (ENABLE_POISON ? 1 : 0) +
                             (ENABLE_MTE ? (TW + NUM_TAGS) : 0),

    // B channel packet size calculation
    // Base: ID + RESP + USER
    // AXI5: + TRACE + TAG + TAGMATCH
    parameter int BSize    = IW + 2 + UW +
                             (ENABLE_TRACE ? 1 : 0) +
                             (ENABLE_MTE ? (TW + 1) : 0)
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // =========================================================================
    // Slave AXI5 Interface (Input Side - FUB/Functional Unit Block)
    // =========================================================================

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
    input  logic [UW-1:0]              fub_axi_awuser,
    input  logic                       fub_axi_awvalid,
    output logic                       fub_axi_awready,

    // AXI5 AW channel signals
    input  logic [AXI_ATOP_WIDTH-1:0]  fub_axi_awatop,     // Atomic operation
    input  logic [AXI_NSAID_WIDTH-1:0] fub_axi_awnsaid,    // Non-secure access ID
    input  logic                       fub_axi_awtrace,    // Trace signal
    input  logic [AXI_MPAM_WIDTH-1:0]  fub_axi_awmpam,     // Memory partitioning
    input  logic [AXI_MECID_WIDTH-1:0] fub_axi_awmecid,    // Memory encryption context
    input  logic                       fub_axi_awunique,   // Unique ID indicator
    input  logic [AXI_TAGOP_WIDTH-1:0] fub_axi_awtagop,    // Tag operation (MTE)
    input  logic [TW-1:0]              fub_axi_awtag,      // Address memory tags

    // Write data channel (W)
    input  logic [DW-1:0]              fub_axi_wdata,
    input  logic [SW-1:0]              fub_axi_wstrb,
    input  logic                       fub_axi_wlast,
    input  logic [UW-1:0]              fub_axi_wuser,
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,

    // AXI5 W channel signals
    input  logic                       fub_axi_wpoison,    // Data poison indicator
    input  logic [TW-1:0]              fub_axi_wtag,       // Write data tags
    input  logic [NUM_TAGS-1:0]        fub_axi_wtagupdate, // Tag update mask

    // Write response channel (B)
    output logic [IW-1:0]              fub_axi_bid,
    output logic [1:0]                 fub_axi_bresp,
    output logic [UW-1:0]              fub_axi_buser,
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,

    // AXI5 B channel signals
    output logic                       fub_axi_btrace,     // Response trace
    output logic [TW-1:0]              fub_axi_btag,       // Response tags
    output logic                       fub_axi_btagmatch,  // Tag match response

    // =========================================================================
    // Master AXI5 Interface (Output Side)
    // =========================================================================

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

    // AXI5 AW channel signals
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

    // AXI5 W channel signals
    output logic                       m_axi_wpoison,
    output logic [TW-1:0]              m_axi_wtag,
    output logic [NUM_TAGS-1:0]        m_axi_wtagupdate,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // AXI5 B channel signals
    input  logic                       m_axi_btrace,
    input  logic [TW-1:0]              m_axi_btag,
    input  logic                       m_axi_btagmatch,

    // Status outputs for clock gating
    output logic                       busy
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

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

    // Channel packing signals
    logic [AWSize-1:0]          w_aw_wr_data;
    logic [AWSize-1:0]          w_aw_rd_data;
    logic [WSize-1:0]           w_w_wr_data;
    logic [WSize-1:0]           w_w_rd_data;
    logic [BSize-1:0]           w_b_wr_data;
    logic [BSize-1:0]           w_b_rd_data;

    // =========================================================================
    // Busy Signal
    // =========================================================================

    assign busy = (int_aw_count > 0) || (int_w_count > 0) || (int_b_count > 0) ||
                  fub_axi_awvalid || fub_axi_wvalid || m_axi_bvalid;

    // =========================================================================
    // AW Channel Packing
    // =========================================================================

    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        w_aw_wr_data[idx +: IW] = fub_axi_awid;
        idx += IW;
        w_aw_wr_data[idx +: AW] = fub_axi_awaddr;
        idx += AW;
        w_aw_wr_data[idx +: 8] = fub_axi_awlen;
        idx += 8;
        w_aw_wr_data[idx +: 3] = fub_axi_awsize;
        idx += 3;
        w_aw_wr_data[idx +: 2] = fub_axi_awburst;
        idx += 2;
        w_aw_wr_data[idx +: 1] = fub_axi_awlock;
        idx += 1;
        w_aw_wr_data[idx +: 4] = fub_axi_awcache;
        idx += 4;
        w_aw_wr_data[idx +: 3] = fub_axi_awprot;
        idx += 3;
        w_aw_wr_data[idx +: 4] = fub_axi_awqos;
        idx += 4;
        w_aw_wr_data[idx +: UW] = fub_axi_awuser;
        idx += UW;

        // AXI5 signals
        if (ENABLE_ATOMIC) begin
            w_aw_wr_data[idx +: AXI_ATOP_WIDTH] = fub_axi_awatop;
            idx += AXI_ATOP_WIDTH;
        end
        if (ENABLE_NSAID) begin
            w_aw_wr_data[idx +: AXI_NSAID_WIDTH] = fub_axi_awnsaid;
            idx += AXI_NSAID_WIDTH;
        end
        if (ENABLE_TRACE) begin
            w_aw_wr_data[idx +: 1] = fub_axi_awtrace;
            idx += 1;
        end
        if (ENABLE_MPAM) begin
            w_aw_wr_data[idx +: AXI_MPAM_WIDTH] = fub_axi_awmpam;
            idx += AXI_MPAM_WIDTH;
        end
        if (ENABLE_MECID) begin
            w_aw_wr_data[idx +: AXI_MECID_WIDTH] = fub_axi_awmecid;
            idx += AXI_MECID_WIDTH;
        end
        if (ENABLE_UNIQUE) begin
            w_aw_wr_data[idx +: 1] = fub_axi_awunique;
            idx += 1;
        end
        if (ENABLE_MTE) begin
            w_aw_wr_data[idx +: AXI_TAGOP_WIDTH] = fub_axi_awtagop;
            idx += AXI_TAGOP_WIDTH;
            w_aw_wr_data[idx +: TW] = fub_axi_awtag;
            idx += TW;
        end
    end

    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        m_axi_awid = w_aw_rd_data[idx +: IW];
        idx += IW;
        m_axi_awaddr = w_aw_rd_data[idx +: AW];
        idx += AW;
        m_axi_awlen = w_aw_rd_data[idx +: 8];
        idx += 8;
        m_axi_awsize = w_aw_rd_data[idx +: 3];
        idx += 3;
        m_axi_awburst = w_aw_rd_data[idx +: 2];
        idx += 2;
        m_axi_awlock = w_aw_rd_data[idx +: 1];
        idx += 1;
        m_axi_awcache = w_aw_rd_data[idx +: 4];
        idx += 4;
        m_axi_awprot = w_aw_rd_data[idx +: 3];
        idx += 3;
        m_axi_awqos = w_aw_rd_data[idx +: 4];
        idx += 4;
        m_axi_awuser = w_aw_rd_data[idx +: UW];
        idx += UW;

        // AXI5 signals
        if (ENABLE_ATOMIC) begin
            m_axi_awatop = w_aw_rd_data[idx +: AXI_ATOP_WIDTH];
            idx += AXI_ATOP_WIDTH;
        end else begin
            m_axi_awatop = '0;
        end

        if (ENABLE_NSAID) begin
            m_axi_awnsaid = w_aw_rd_data[idx +: AXI_NSAID_WIDTH];
            idx += AXI_NSAID_WIDTH;
        end else begin
            m_axi_awnsaid = '0;
        end

        if (ENABLE_TRACE) begin
            m_axi_awtrace = w_aw_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axi_awtrace = '0;
        end

        if (ENABLE_MPAM) begin
            m_axi_awmpam = w_aw_rd_data[idx +: AXI_MPAM_WIDTH];
            idx += AXI_MPAM_WIDTH;
        end else begin
            m_axi_awmpam = '0;
        end

        if (ENABLE_MECID) begin
            m_axi_awmecid = w_aw_rd_data[idx +: AXI_MECID_WIDTH];
            idx += AXI_MECID_WIDTH;
        end else begin
            m_axi_awmecid = '0;
        end

        if (ENABLE_UNIQUE) begin
            m_axi_awunique = w_aw_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axi_awunique = '0;
        end

        if (ENABLE_MTE) begin
            m_axi_awtagop = w_aw_rd_data[idx +: AXI_TAGOP_WIDTH];
            idx += AXI_TAGOP_WIDTH;
            m_axi_awtag = w_aw_rd_data[idx +: TW];
            idx += TW;
        end else begin
            m_axi_awtagop = '0;
            m_axi_awtag = '0;
        end
    end

    // =========================================================================
    // W Channel Packing
    // =========================================================================

    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        w_w_wr_data[idx +: DW] = fub_axi_wdata;
        idx += DW;
        w_w_wr_data[idx +: SW] = fub_axi_wstrb;
        idx += SW;
        w_w_wr_data[idx +: 1] = fub_axi_wlast;
        idx += 1;
        w_w_wr_data[idx +: UW] = fub_axi_wuser;
        idx += UW;

        // AXI5 signals
        if (ENABLE_POISON) begin
            w_w_wr_data[idx +: 1] = fub_axi_wpoison;
            idx += 1;
        end
        if (ENABLE_MTE) begin
            w_w_wr_data[idx +: TW] = fub_axi_wtag;
            idx += TW;
            w_w_wr_data[idx +: NUM_TAGS] = fub_axi_wtagupdate;
            idx += NUM_TAGS;
        end
    end

    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        m_axi_wdata = w_w_rd_data[idx +: DW];
        idx += DW;
        m_axi_wstrb = w_w_rd_data[idx +: SW];
        idx += SW;
        m_axi_wlast = w_w_rd_data[idx +: 1];
        idx += 1;
        m_axi_wuser = w_w_rd_data[idx +: UW];
        idx += UW;

        // AXI5 signals
        if (ENABLE_POISON) begin
            m_axi_wpoison = w_w_rd_data[idx +: 1];
            idx += 1;
        end else begin
            m_axi_wpoison = '0;
        end

        if (ENABLE_MTE) begin
            m_axi_wtag = w_w_rd_data[idx +: TW];
            idx += TW;
            m_axi_wtagupdate = w_w_rd_data[idx +: NUM_TAGS];
            idx += NUM_TAGS;
        end else begin
            m_axi_wtag = '0;
            m_axi_wtagupdate = '0;
        end
    end

    // =========================================================================
    // B Channel Packing
    // =========================================================================

    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        w_b_wr_data[idx +: IW] = m_axi_bid;
        idx += IW;
        w_b_wr_data[idx +: 2] = m_axi_bresp;
        idx += 2;
        w_b_wr_data[idx +: UW] = m_axi_buser;
        idx += UW;

        // AXI5 signals
        if (ENABLE_TRACE) begin
            w_b_wr_data[idx +: 1] = m_axi_btrace;
            idx += 1;
        end
        if (ENABLE_MTE) begin
            w_b_wr_data[idx +: TW] = m_axi_btag;
            idx += TW;
            w_b_wr_data[idx +: 1] = m_axi_btagmatch;
            idx += 1;
        end
    end

    always_comb begin
        automatic int idx = 0;

        // Base AXI signals
        fub_axi_bid = w_b_rd_data[idx +: IW];
        idx += IW;
        fub_axi_bresp = w_b_rd_data[idx +: 2];
        idx += 2;
        fub_axi_buser = w_b_rd_data[idx +: UW];
        idx += UW;

        // AXI5 signals
        if (ENABLE_TRACE) begin
            fub_axi_btrace = w_b_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_btrace = '0;
        end

        if (ENABLE_MTE) begin
            fub_axi_btag = w_b_rd_data[idx +: TW];
            idx += TW;
            fub_axi_btagmatch = w_b_rd_data[idx +: 1];
            idx += 1;
        end else begin
            fub_axi_btag = '0;
            fub_axi_btagmatch = '0;
        end
    end

    // =========================================================================
    // Instantiate AW Skid Buffer
    // =========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize),
        .INSTANCE_NAME("AW_SKID")
    ) aw_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_awvalid),
        .wr_ready               (fub_axi_awready),
        .wr_data                (w_aw_wr_data),
        .rd_valid               (int_skid_awvalid),
        .rd_ready               (int_skid_awready),
        .rd_count               (int_aw_count),
        .rd_data                (w_aw_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign m_axi_awvalid = int_skid_awvalid;
    assign int_skid_awready = m_axi_awready;

    // =========================================================================
    // Instantiate W Skid Buffer
    // =========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize),
        .INSTANCE_NAME("W_SKID")
    ) w_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (fub_axi_wvalid),
        .wr_ready               (fub_axi_wready),
        .wr_data                (w_w_wr_data),
        .rd_valid               (int_skid_wvalid),
        .rd_ready               (int_skid_wready),
        .rd_count               (int_w_count),
        .rd_data                (w_w_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign m_axi_wvalid = int_skid_wvalid;
    assign int_skid_wready = m_axi_wready;

    // =========================================================================
    // Instantiate B Skid Buffer
    // =========================================================================

    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize),
        .INSTANCE_NAME("B_SKID")
    ) b_channel (
        .axi_aclk               (aclk),
        .axi_aresetn            (aresetn),
        .wr_valid               (m_axi_bvalid),
        .wr_ready               (m_axi_bready),
        .wr_data                (w_b_wr_data),
        .rd_valid               (int_skid_bvalid),
        .rd_ready               (int_skid_bready),
        .rd_count               (int_b_count),
        .rd_data                (w_b_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count                  ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign fub_axi_bvalid = int_skid_bvalid;
    assign int_skid_bready = fub_axi_bready;

endmodule : axi5_master_wr
