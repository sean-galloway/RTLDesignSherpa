// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_wr_cg
// Purpose: AXI5 Slave Write with Clock Gating support
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_wr_cg
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
    input  logic [IW-1:0]               s_axi_awid,
    input  logic [AW-1:0]               s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [UW-1:0]               s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // AXI5 AW signals
    input  logic [AXI_ATOP_WIDTH-1:0]   s_axi_awatop,
    input  logic [AXI_NSAID_WIDTH-1:0]  s_axi_awnsaid,
    input  logic                        s_axi_awtrace,
    input  logic [AXI_MPAM_WIDTH-1:0]   s_axi_awmpam,
    input  logic [AXI_MECID_WIDTH-1:0]  s_axi_awmecid,
    input  logic                        s_axi_awunique,
    input  logic [AXI_TAGOP_WIDTH-1:0]  s_axi_awtagop,
    input  logic [TW-1:0]               s_axi_awtag,

    // Write data channel (W)
    input  logic [DW-1:0]               s_axi_wdata,
    input  logic [SW-1:0]               s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [UW-1:0]               s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // AXI5 W signals
    input  logic                        s_axi_wpoison,
    input  logic [TW-1:0]               s_axi_wtag,
    input  logic [NUM_TAGS-1:0]         s_axi_wtagupdate,

    // Write response channel (B)
    output logic [IW-1:0]               s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [UW-1:0]               s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    // AXI5 B signals
    output logic                        s_axi_btrace,
    output logic [TW-1:0]               s_axi_btag,
    output logic                        s_axi_btagmatch,

    // FUB Interface (Output Side)
    output logic [IW-1:0]              fub_axi_awid,
    output logic [AW-1:0]              fub_axi_awaddr,
    output logic [7:0]                 fub_axi_awlen,
    output logic [2:0]                 fub_axi_awsize,
    output logic [1:0]                 fub_axi_awburst,
    output logic                       fub_axi_awlock,
    output logic [3:0]                 fub_axi_awcache,
    output logic [2:0]                 fub_axi_awprot,
    output logic [3:0]                 fub_axi_awqos,
    output logic [UW-1:0]              fub_axi_awuser,
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,

    // AXI5 AW signals
    output logic [AXI_ATOP_WIDTH-1:0]  fub_axi_awatop,
    output logic [AXI_NSAID_WIDTH-1:0] fub_axi_awnsaid,
    output logic                       fub_axi_awtrace,
    output logic [AXI_MPAM_WIDTH-1:0]  fub_axi_awmpam,
    output logic [AXI_MECID_WIDTH-1:0] fub_axi_awmecid,
    output logic                       fub_axi_awunique,
    output logic [AXI_TAGOP_WIDTH-1:0] fub_axi_awtagop,
    output logic [TW-1:0]              fub_axi_awtag,

    // Write data channel (W)
    output logic [DW-1:0]              fub_axi_wdata,
    output logic [SW-1:0]              fub_axi_wstrb,
    output logic                       fub_axi_wlast,
    output logic [UW-1:0]              fub_axi_wuser,
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,

    // AXI5 W signals
    output logic                       fub_axi_wpoison,
    output logic [TW-1:0]              fub_axi_wtag,
    output logic [NUM_TAGS-1:0]        fub_axi_wtagupdate,

    // Write response channel (B)
    input  logic [IW-1:0]              fub_axi_bid,
    input  logic [1:0]                 fub_axi_bresp,
    input  logic [UW-1:0]              fub_axi_buser,
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,

    // AXI5 B signals
    input  logic                       fub_axi_btrace,
    input  logic [TW-1:0]              fub_axi_btag,
    input  logic                       fub_axi_btagmatch,

    // Clock gating status
    output logic                       cg_gating,
    output logic                       cg_idle
);

    // Gated clock signal
    logic gated_aclk;

    // Combined valid signals
    logic user_valid;
    logic axi_valid;

    // Internal signals
    logic int_awready;
    logic int_wready;
    logic int_bready;
    logic int_busy;

    assign user_valid = s_axi_awvalid || s_axi_wvalid || s_axi_bready || int_busy;
    assign axi_valid = fub_axi_awvalid || fub_axi_wvalid || fub_axi_bvalid;

    assign s_axi_awready = cg_gating ? 1'b0 : int_awready;
    assign s_axi_wready = cg_gating ? 1'b0 : int_wready;
    assign fub_axi_bready = cg_gating ? 1'b0 : int_bready;

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

    axi5_slave_wr #(
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
    ) i_axi5_slave_wr (
        .aclk                (gated_aclk),
        .aresetn             (aresetn),

        .s_axi_awid          (s_axi_awid),
        .s_axi_awaddr        (s_axi_awaddr),
        .s_axi_awlen         (s_axi_awlen),
        .s_axi_awsize        (s_axi_awsize),
        .s_axi_awburst       (s_axi_awburst),
        .s_axi_awlock        (s_axi_awlock),
        .s_axi_awcache       (s_axi_awcache),
        .s_axi_awprot        (s_axi_awprot),
        .s_axi_awqos         (s_axi_awqos),
        .s_axi_awuser        (s_axi_awuser),
        .s_axi_awvalid       (s_axi_awvalid),
        .s_axi_awready       (int_awready),
        .s_axi_awatop        (s_axi_awatop),
        .s_axi_awnsaid       (s_axi_awnsaid),
        .s_axi_awtrace       (s_axi_awtrace),
        .s_axi_awmpam        (s_axi_awmpam),
        .s_axi_awmecid       (s_axi_awmecid),
        .s_axi_awunique      (s_axi_awunique),
        .s_axi_awtagop       (s_axi_awtagop),
        .s_axi_awtag         (s_axi_awtag),

        .s_axi_wdata         (s_axi_wdata),
        .s_axi_wstrb         (s_axi_wstrb),
        .s_axi_wlast         (s_axi_wlast),
        .s_axi_wuser         (s_axi_wuser),
        .s_axi_wvalid        (s_axi_wvalid),
        .s_axi_wready        (int_wready),
        .s_axi_wpoison       (s_axi_wpoison),
        .s_axi_wtag          (s_axi_wtag),
        .s_axi_wtagupdate    (s_axi_wtagupdate),

        .s_axi_bid           (s_axi_bid),
        .s_axi_bresp         (s_axi_bresp),
        .s_axi_buser         (s_axi_buser),
        .s_axi_bvalid        (s_axi_bvalid),
        .s_axi_bready        (s_axi_bready),
        .s_axi_btrace        (s_axi_btrace),
        .s_axi_btag          (s_axi_btag),
        .s_axi_btagmatch     (s_axi_btagmatch),

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
        .fub_axi_awready     (fub_axi_awready),
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
        .fub_axi_wready      (fub_axi_wready),
        .fub_axi_wpoison     (fub_axi_wpoison),
        .fub_axi_wtag        (fub_axi_wtag),
        .fub_axi_wtagupdate  (fub_axi_wtagupdate),

        .fub_axi_bid         (fub_axi_bid),
        .fub_axi_bresp       (fub_axi_bresp),
        .fub_axi_buser       (fub_axi_buser),
        .fub_axi_bvalid      (fub_axi_bvalid),
        .fub_axi_bready      (int_bready),
        .fub_axi_btrace      (fub_axi_btrace),
        .fub_axi_btag        (fub_axi_btag),
        .fub_axi_btagmatch   (fub_axi_btagmatch),

        .busy                (int_busy)
    );

endmodule : axi5_slave_wr_cg
