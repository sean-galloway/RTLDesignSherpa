// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_master_wr_cg
// Purpose: AXI5 Master Write with Clock Gating support
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_master_wr_cg
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

    // Feature enables
    parameter bit ENABLE_ATOMIC     = 1,
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
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

    // Clock gating parameters
    parameter int CG_IDLE_COUNT_WIDTH = 4
)
(
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Clock gating configuration
    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI5 Interface (Input Side)
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

    // AXI5 AW signals
    input  logic [AXI_ATOP_WIDTH-1:0]  fub_axi_awatop,
    input  logic [AXI_NSAID_WIDTH-1:0] fub_axi_awnsaid,
    input  logic                       fub_axi_awtrace,
    input  logic [AXI_MPAM_WIDTH-1:0]  fub_axi_awmpam,
    input  logic [AXI_MECID_WIDTH-1:0] fub_axi_awmecid,
    input  logic                       fub_axi_awunique,
    input  logic [AXI_TAGOP_WIDTH-1:0] fub_axi_awtagop,
    input  logic [TW-1:0]              fub_axi_awtag,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_axi_wdata,
    input  logic [SW-1:0]              fub_axi_wstrb,
    input  logic                       fub_axi_wlast,
    input  logic [UW-1:0]              fub_axi_wuser,
    input  logic                       fub_axi_wvalid,
    output logic                       fub_axi_wready,

    // AXI5 W signals
    input  logic                       fub_axi_wpoison,
    input  logic [TW-1:0]              fub_axi_wtag,
    input  logic [NUM_TAGS-1:0]        fub_axi_wtagupdate,

    // Write response channel (B)
    output logic [IW-1:0]              fub_axi_bid,
    output logic [1:0]                 fub_axi_bresp,
    output logic [UW-1:0]              fub_axi_buser,
    output logic                       fub_axi_bvalid,
    input  logic                       fub_axi_bready,

    // AXI5 B signals
    output logic                       fub_axi_btrace,
    output logic [TW-1:0]              fub_axi_btag,
    output logic                       fub_axi_btagmatch,

    // Master AXI5 Interface (Output Side)
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

    // Clock gating status
    output logic                       cg_gating,
    output logic                       cg_idle
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals for clock gating control
    logic user_valid;
    logic axi_valid;

    // Internal ready signals from base module
    logic int_awready;
    logic int_wready;
    logic int_bready;
    logic int_busy;

    // OR all user-side valid signals
    assign user_valid = fub_axi_awvalid || fub_axi_wvalid || fub_axi_bready || int_busy;

    // OR all AXI-side valid signals
    assign axi_valid = m_axi_awvalid || m_axi_wvalid || m_axi_bvalid;

    // Force ready signals to 0 when clock gating is active
    assign fub_axi_awready = cg_gating ? 1'b0 : int_awready;
    assign fub_axi_wready = cg_gating ? 1'b0 : int_wready;
    assign m_axi_bready = cg_gating ? 1'b0 : int_bready;

    // Instantiate clock gate controller
    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in              (aclk),
        .aresetn             (aresetn),
        .cfg_cg_enable       (cfg_cg_enable),
        .cfg_cg_idle_count   (cfg_cg_idle_count),
        .user_valid          (user_valid),
        .axi_valid           (axi_valid),
        .clk_out             (gated_aclk),
        .gating              (cg_gating),
        .idle                (cg_idle)
    );

    // Instantiate the base AXI5 master write module with gated clock
    axi5_master_wr #(
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH      (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH      (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .SKID_DEPTH_AW       (SKID_DEPTH_AW),
        .SKID_DEPTH_W        (SKID_DEPTH_W),
        .SKID_DEPTH_B        (SKID_DEPTH_B),
        .AXI_ATOP_WIDTH      (AXI_ATOP_WIDTH),
        .AXI_NSAID_WIDTH     (AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH      (AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH     (AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH       (AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH     (AXI_TAGOP_WIDTH),
        .ENABLE_ATOMIC       (ENABLE_ATOMIC),
        .ENABLE_NSAID        (ENABLE_NSAID),
        .ENABLE_TRACE        (ENABLE_TRACE),
        .ENABLE_MPAM         (ENABLE_MPAM),
        .ENABLE_MECID        (ENABLE_MECID),
        .ENABLE_UNIQUE       (ENABLE_UNIQUE),
        .ENABLE_MTE          (ENABLE_MTE),
        .ENABLE_POISON       (ENABLE_POISON)
    ) i_axi5_master_wr (
        .aclk                (gated_aclk),
        .aresetn             (aresetn),

        // Slave AXI5 Interface
        .fub_axi_awid        (fub_axi_awid),
        .fub_axi_awaddr      (fub_axi_awaddr),
        .fub_axi_awlen       (fub_axi_awlen),
        .fub_axi_awsize      (fub_axi_awsize),
        .fub_axi_awburst     (fub_axi_awburst),
        .fub_axi_awlock      (fub_axi_awlock),
        .fub_axi_awcache     (fub_axi_awcache),
        .fub_axi_awprot      (fub_axi_awprot),
        .fub_axi_awqos       (fub_axi_awqos),
        .fub_axi_awuser      (fub_axi_awuser),
        .fub_axi_awvalid     (fub_axi_awvalid),
        .fub_axi_awready     (int_awready),
        .fub_axi_awatop      (fub_axi_awatop),
        .fub_axi_awnsaid     (fub_axi_awnsaid),
        .fub_axi_awtrace     (fub_axi_awtrace),
        .fub_axi_awmpam      (fub_axi_awmpam),
        .fub_axi_awmecid     (fub_axi_awmecid),
        .fub_axi_awunique    (fub_axi_awunique),
        .fub_axi_awtagop     (fub_axi_awtagop),
        .fub_axi_awtag       (fub_axi_awtag),

        .fub_axi_wdata       (fub_axi_wdata),
        .fub_axi_wstrb       (fub_axi_wstrb),
        .fub_axi_wlast       (fub_axi_wlast),
        .fub_axi_wuser       (fub_axi_wuser),
        .fub_axi_wvalid      (fub_axi_wvalid),
        .fub_axi_wready      (int_wready),
        .fub_axi_wpoison     (fub_axi_wpoison),
        .fub_axi_wtag        (fub_axi_wtag),
        .fub_axi_wtagupdate  (fub_axi_wtagupdate),

        .fub_axi_bid         (fub_axi_bid),
        .fub_axi_bresp       (fub_axi_bresp),
        .fub_axi_buser       (fub_axi_buser),
        .fub_axi_bvalid      (fub_axi_bvalid),
        .fub_axi_bready      (fub_axi_bready),
        .fub_axi_btrace      (fub_axi_btrace),
        .fub_axi_btag        (fub_axi_btag),
        .fub_axi_btagmatch   (fub_axi_btagmatch),

        // Master AXI5 Interface
        .m_axi_awid          (m_axi_awid),
        .m_axi_awaddr        (m_axi_awaddr),
        .m_axi_awlen         (m_axi_awlen),
        .m_axi_awsize        (m_axi_awsize),
        .m_axi_awburst       (m_axi_awburst),
        .m_axi_awlock        (m_axi_awlock),
        .m_axi_awcache       (m_axi_awcache),
        .m_axi_awprot        (m_axi_awprot),
        .m_axi_awqos         (m_axi_awqos),
        .m_axi_awuser        (m_axi_awuser),
        .m_axi_awvalid       (m_axi_awvalid),
        .m_axi_awready       (m_axi_awready),
        .m_axi_awatop        (m_axi_awatop),
        .m_axi_awnsaid       (m_axi_awnsaid),
        .m_axi_awtrace       (m_axi_awtrace),
        .m_axi_awmpam        (m_axi_awmpam),
        .m_axi_awmecid       (m_axi_awmecid),
        .m_axi_awunique      (m_axi_awunique),
        .m_axi_awtagop       (m_axi_awtagop),
        .m_axi_awtag         (m_axi_awtag),

        .m_axi_wdata         (m_axi_wdata),
        .m_axi_wstrb         (m_axi_wstrb),
        .m_axi_wlast         (m_axi_wlast),
        .m_axi_wuser         (m_axi_wuser),
        .m_axi_wvalid        (m_axi_wvalid),
        .m_axi_wready        (m_axi_wready),
        .m_axi_wpoison       (m_axi_wpoison),
        .m_axi_wtag          (m_axi_wtag),
        .m_axi_wtagupdate    (m_axi_wtagupdate),

        .m_axi_bid           (m_axi_bid),
        .m_axi_bresp         (m_axi_bresp),
        .m_axi_buser         (m_axi_buser),
        .m_axi_bvalid        (m_axi_bvalid),
        .m_axi_bready        (int_bready),
        .m_axi_btrace        (m_axi_btrace),
        .m_axi_btag          (m_axi_btag),
        .m_axi_btagmatch     (m_axi_btagmatch),

        .busy                (int_busy)
    );

endmodule : axi5_master_wr_cg
