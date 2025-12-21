// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_wr_mon_cg
// Purpose: AXI5 Slave Write with Monitor and Clock Gating
//
// This module wraps axi5_slave_wr_mon with clock gating support.
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_wr_mon_cg
    import monitor_pkg::*;
#(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    parameter int AXI_ATOP_WIDTH    = 6,
    parameter int AXI_NSAID_WIDTH   = 4,
    parameter int AXI_MPAM_WIDTH    = 11,
    parameter int AXI_MECID_WIDTH   = 16,
    parameter int AXI_TAG_WIDTH     = 4,
    parameter int AXI_TAGOP_WIDTH   = 2,

    parameter bit ENABLE_ATOMIC     = 1,
    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_MTE        = 1,
    parameter bit ENABLE_POISON     = 1,

    parameter int UNIT_ID           = 1,
    parameter int AGENT_ID          = 13,
    parameter int MAX_TRANSACTIONS  = 16,
    parameter bit ENABLE_FILTERING  = 1,
    parameter bit ADD_PIPELINE_STAGE = 0,
    parameter int CG_IDLE_COUNT_WIDTH = 4,

    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS
)
(
    input  logic aclk,
    input  logic aresetn,

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
    input  logic [AXI_ATOP_WIDTH-1:0]   s_axi_awatop,
    input  logic [AXI_NSAID_WIDTH-1:0]  s_axi_awnsaid,
    input  logic                        s_axi_awtrace,
    input  logic [AXI_MPAM_WIDTH-1:0]   s_axi_awmpam,
    input  logic [AXI_MECID_WIDTH-1:0]  s_axi_awmecid,
    input  logic                        s_axi_awunique,
    input  logic [AXI_TAGOP_WIDTH-1:0]  s_axi_awtagop,
    input  logic [TW-1:0]               s_axi_awtag,

    input  logic [DW-1:0]               s_axi_wdata,
    input  logic [SW-1:0]               s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [UW-1:0]               s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,
    input  logic                        s_axi_wpoison,
    input  logic [TW-1:0]               s_axi_wtag,
    input  logic [NUM_TAGS-1:0]         s_axi_wtagupdate,

    output logic [IW-1:0]               s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [UW-1:0]               s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,
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
    output logic [AXI_ATOP_WIDTH-1:0]  fub_axi_awatop,
    output logic [AXI_NSAID_WIDTH-1:0] fub_axi_awnsaid,
    output logic                       fub_axi_awtrace,
    output logic [AXI_MPAM_WIDTH-1:0]  fub_axi_awmpam,
    output logic [AXI_MECID_WIDTH-1:0] fub_axi_awmecid,
    output logic                       fub_axi_awunique,
    output logic [AXI_TAGOP_WIDTH-1:0] fub_axi_awtagop,
    output logic [TW-1:0]              fub_axi_awtag,

    output logic [DW-1:0]              fub_axi_wdata,
    output logic [SW-1:0]              fub_axi_wstrb,
    output logic                       fub_axi_wlast,
    output logic [UW-1:0]              fub_axi_wuser,
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,
    output logic                       fub_axi_wpoison,
    output logic [TW-1:0]              fub_axi_wtag,
    output logic [NUM_TAGS-1:0]        fub_axi_wtagupdate,

    input  logic [IW-1:0]              fub_axi_bid,
    input  logic [1:0]                 fub_axi_bresp,
    input  logic [UW-1:0]              fub_axi_buser,
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,
    input  logic                       fub_axi_btrace,
    input  logic [TW-1:0]              fub_axi_btag,
    input  logic                       fub_axi_btagmatch,

    // Monitor configuration
    input  logic                       cfg_monitor_enable,
    input  logic                       cfg_error_enable,
    input  logic                       cfg_timeout_enable,
    input  logic                       cfg_perf_enable,
    input  logic [15:0]                cfg_timeout_cycles,
    input  logic [31:0]                cfg_latency_threshold,
    input  logic [15:0]                cfg_axi_pkt_mask,
    input  logic [15:0]                cfg_axi_err_select,
    input  logic [15:0]                cfg_axi_error_mask,
    input  logic [15:0]                cfg_axi_timeout_mask,
    input  logic [15:0]                cfg_axi_compl_mask,
    input  logic [15:0]                cfg_axi_thresh_mask,
    input  logic [15:0]                cfg_axi_perf_mask,
    input  logic [15:0]                cfg_axi_addr_mask,
    input  logic [15:0]                cfg_axi_debug_mask,

    output logic                       monbus_valid,
    input  logic                       monbus_ready,
    output logic [63:0]                monbus_packet,
    output logic                       busy,
    output logic [7:0]                 active_transactions,
    output logic [15:0]                error_count,
    output logic [31:0]                transaction_count,
    output logic                       cfg_conflict_error,
    output logic                       cg_gating,
    output logic                       cg_idle
);

    logic gated_aclk;
    logic user_valid, axi_valid;
    logic int_awready, int_wready, int_bready, int_busy;

    assign user_valid = s_axi_awvalid || s_axi_wvalid || s_axi_bready || int_busy;
    assign axi_valid = fub_axi_awvalid || fub_axi_wvalid || fub_axi_bvalid;

    assign s_axi_awready = cg_gating ? 1'b0 : int_awready;
    assign s_axi_wready = cg_gating ? 1'b0 : int_wready;
    assign fub_axi_bready = cg_gating ? 1'b0 : int_bready;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in(aclk), .aresetn(aresetn),
        .cfg_cg_enable(cfg_cg_enable), .cfg_cg_idle_count(cfg_cg_idle_count),
        .user_valid(user_valid), .axi_valid(axi_valid),
        .clk_out(gated_aclk), .gating(cg_gating), .idle(cg_idle)
    );

    axi5_slave_wr_mon #(
        .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B),
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_ATOP_WIDTH(AXI_ATOP_WIDTH), .AXI_NSAID_WIDTH(AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH(AXI_MPAM_WIDTH), .AXI_MECID_WIDTH(AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH(AXI_TAG_WIDTH), .AXI_TAGOP_WIDTH(AXI_TAGOP_WIDTH),
        .ENABLE_ATOMIC(ENABLE_ATOMIC), .ENABLE_NSAID(ENABLE_NSAID),
        .ENABLE_TRACE(ENABLE_TRACE), .ENABLE_MPAM(ENABLE_MPAM),
        .ENABLE_MECID(ENABLE_MECID), .ENABLE_UNIQUE(ENABLE_UNIQUE),
        .ENABLE_MTE(ENABLE_MTE), .ENABLE_POISON(ENABLE_POISON),
        .UNIT_ID(UNIT_ID), .AGENT_ID(AGENT_ID), .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .ENABLE_FILTERING(ENABLE_FILTERING), .ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE)
    ) i_axi5_slave_wr_mon (
        .aclk(gated_aclk), .aresetn(aresetn),
        .s_axi_awid(s_axi_awid), .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awlen(s_axi_awlen), .s_axi_awsize(s_axi_awsize),
        .s_axi_awburst(s_axi_awburst), .s_axi_awlock(s_axi_awlock),
        .s_axi_awcache(s_axi_awcache), .s_axi_awprot(s_axi_awprot),
        .s_axi_awqos(s_axi_awqos), .s_axi_awuser(s_axi_awuser),
        .s_axi_awvalid(s_axi_awvalid), .s_axi_awready(int_awready),
        .s_axi_awatop(s_axi_awatop), .s_axi_awnsaid(s_axi_awnsaid),
        .s_axi_awtrace(s_axi_awtrace), .s_axi_awmpam(s_axi_awmpam),
        .s_axi_awmecid(s_axi_awmecid), .s_axi_awunique(s_axi_awunique),
        .s_axi_awtagop(s_axi_awtagop), .s_axi_awtag(s_axi_awtag),
        .s_axi_wdata(s_axi_wdata), .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wlast(s_axi_wlast), .s_axi_wuser(s_axi_wuser),
        .s_axi_wvalid(s_axi_wvalid), .s_axi_wready(int_wready),
        .s_axi_wpoison(s_axi_wpoison), .s_axi_wtag(s_axi_wtag),
        .s_axi_wtagupdate(s_axi_wtagupdate),
        .s_axi_bid(s_axi_bid), .s_axi_bresp(s_axi_bresp),
        .s_axi_buser(s_axi_buser), .s_axi_bvalid(s_axi_bvalid),
        .s_axi_bready(s_axi_bready), .s_axi_btrace(s_axi_btrace),
        .s_axi_btag(s_axi_btag), .s_axi_btagmatch(s_axi_btagmatch),
        .fub_axi_awid(fub_axi_awid), .fub_axi_awaddr(fub_axi_awaddr),
        .fub_axi_awlen(fub_axi_awlen), .fub_axi_awsize(fub_axi_awsize),
        .fub_axi_awburst(fub_axi_awburst), .fub_axi_awlock(fub_axi_awlock),
        .fub_axi_awcache(fub_axi_awcache), .fub_axi_awprot(fub_axi_awprot),
        .fub_axi_awqos(fub_axi_awqos), .fub_axi_awuser(fub_axi_awuser),
        .fub_axi_awvalid(fub_axi_awvalid), .fub_axi_awready(fub_axi_awready),
        .fub_axi_awatop(fub_axi_awatop), .fub_axi_awnsaid(fub_axi_awnsaid),
        .fub_axi_awtrace(fub_axi_awtrace), .fub_axi_awmpam(fub_axi_awmpam),
        .fub_axi_awmecid(fub_axi_awmecid), .fub_axi_awunique(fub_axi_awunique),
        .fub_axi_awtagop(fub_axi_awtagop), .fub_axi_awtag(fub_axi_awtag),
        .fub_axi_wdata(fub_axi_wdata), .fub_axi_wstrb(fub_axi_wstrb),
        .fub_axi_wlast(fub_axi_wlast), .fub_axi_wuser(fub_axi_wuser),
        .fub_axi_wvalid(fub_axi_wvalid), .fub_axi_wready(fub_axi_wready),
        .fub_axi_wpoison(fub_axi_wpoison), .fub_axi_wtag(fub_axi_wtag),
        .fub_axi_wtagupdate(fub_axi_wtagupdate),
        .fub_axi_bid(fub_axi_bid), .fub_axi_bresp(fub_axi_bresp),
        .fub_axi_buser(fub_axi_buser), .fub_axi_bvalid(fub_axi_bvalid),
        .fub_axi_bready(int_bready), .fub_axi_btrace(fub_axi_btrace),
        .fub_axi_btag(fub_axi_btag), .fub_axi_btagmatch(fub_axi_btagmatch),
        .cfg_monitor_enable(cfg_monitor_enable), .cfg_error_enable(cfg_error_enable),
        .cfg_timeout_enable(cfg_timeout_enable), .cfg_perf_enable(cfg_perf_enable),
        .cfg_timeout_cycles(cfg_timeout_cycles), .cfg_latency_threshold(cfg_latency_threshold),
        .cfg_axi_pkt_mask(cfg_axi_pkt_mask), .cfg_axi_err_select(cfg_axi_err_select),
        .cfg_axi_error_mask(cfg_axi_error_mask), .cfg_axi_timeout_mask(cfg_axi_timeout_mask),
        .cfg_axi_compl_mask(cfg_axi_compl_mask), .cfg_axi_thresh_mask(cfg_axi_thresh_mask),
        .cfg_axi_perf_mask(cfg_axi_perf_mask), .cfg_axi_addr_mask(cfg_axi_addr_mask),
        .cfg_axi_debug_mask(cfg_axi_debug_mask),
        .monbus_valid(monbus_valid), .monbus_ready(monbus_ready), .monbus_packet(monbus_packet),
        .busy(int_busy), .active_transactions(active_transactions),
        .error_count(error_count), .transaction_count(transaction_count),
        .cfg_conflict_error(cfg_conflict_error)
    );

    assign busy = int_busy;

endmodule : axi5_slave_wr_mon_cg
