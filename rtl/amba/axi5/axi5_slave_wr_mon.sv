// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_wr_mon
// Purpose: AXI5 Slave Write with Integrated Filtered Monitoring
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_wr_mon
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

    // Slave interface (all AXI5 AW, W, B channel signals)
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

    // FUB interface (all AXI5 AW, W, B channel signals)
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
    output logic                       cfg_conflict_error
);

    axi5_slave_wr #(
        .SKID_DEPTH_AW(SKID_DEPTH_AW), .SKID_DEPTH_W(SKID_DEPTH_W), .SKID_DEPTH_B(SKID_DEPTH_B),
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_ATOP_WIDTH(AXI_ATOP_WIDTH), .AXI_NSAID_WIDTH(AXI_NSAID_WIDTH),
        .AXI_MPAM_WIDTH(AXI_MPAM_WIDTH), .AXI_MECID_WIDTH(AXI_MECID_WIDTH),
        .AXI_TAG_WIDTH(AXI_TAG_WIDTH), .AXI_TAGOP_WIDTH(AXI_TAGOP_WIDTH),
        .ENABLE_ATOMIC(ENABLE_ATOMIC), .ENABLE_NSAID(ENABLE_NSAID),
        .ENABLE_TRACE(ENABLE_TRACE), .ENABLE_MPAM(ENABLE_MPAM),
        .ENABLE_MECID(ENABLE_MECID), .ENABLE_UNIQUE(ENABLE_UNIQUE),
        .ENABLE_MTE(ENABLE_MTE), .ENABLE_POISON(ENABLE_POISON)
    ) axi5_slave_wr_inst (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_awid(s_axi_awid), .s_axi_awaddr(s_axi_awaddr), .s_axi_awlen(s_axi_awlen),
        .s_axi_awsize(s_axi_awsize), .s_axi_awburst(s_axi_awburst), .s_axi_awlock(s_axi_awlock),
        .s_axi_awcache(s_axi_awcache), .s_axi_awprot(s_axi_awprot), .s_axi_awqos(s_axi_awqos),
        .s_axi_awuser(s_axi_awuser), .s_axi_awvalid(s_axi_awvalid), .s_axi_awready(s_axi_awready),
        .s_axi_awatop(s_axi_awatop), .s_axi_awnsaid(s_axi_awnsaid), .s_axi_awtrace(s_axi_awtrace),
        .s_axi_awmpam(s_axi_awmpam), .s_axi_awmecid(s_axi_awmecid), .s_axi_awunique(s_axi_awunique),
        .s_axi_awtagop(s_axi_awtagop), .s_axi_awtag(s_axi_awtag),
        .s_axi_wdata(s_axi_wdata), .s_axi_wstrb(s_axi_wstrb), .s_axi_wlast(s_axi_wlast),
        .s_axi_wuser(s_axi_wuser), .s_axi_wvalid(s_axi_wvalid), .s_axi_wready(s_axi_wready),
        .s_axi_wpoison(s_axi_wpoison), .s_axi_wtag(s_axi_wtag), .s_axi_wtagupdate(s_axi_wtagupdate),
        .s_axi_bid(s_axi_bid), .s_axi_bresp(s_axi_bresp), .s_axi_buser(s_axi_buser),
        .s_axi_bvalid(s_axi_bvalid), .s_axi_bready(s_axi_bready), .s_axi_btrace(s_axi_btrace),
        .s_axi_btag(s_axi_btag), .s_axi_btagmatch(s_axi_btagmatch),
        .fub_axi_awid(fub_axi_awid), .fub_axi_awaddr(fub_axi_awaddr), .fub_axi_awlen(fub_axi_awlen),
        .fub_axi_awsize(fub_axi_awsize), .fub_axi_awburst(fub_axi_awburst), .fub_axi_awlock(fub_axi_awlock),
        .fub_axi_awcache(fub_axi_awcache), .fub_axi_awprot(fub_axi_awprot), .fub_axi_awqos(fub_axi_awqos),
        .fub_axi_awuser(fub_axi_awuser), .fub_axi_awvalid(fub_axi_awvalid), .fub_axi_awready(fub_axi_awready),
        .fub_axi_awatop(fub_axi_awatop), .fub_axi_awnsaid(fub_axi_awnsaid), .fub_axi_awtrace(fub_axi_awtrace),
        .fub_axi_awmpam(fub_axi_awmpam), .fub_axi_awmecid(fub_axi_awmecid), .fub_axi_awunique(fub_axi_awunique),
        .fub_axi_awtagop(fub_axi_awtagop), .fub_axi_awtag(fub_axi_awtag),
        .fub_axi_wdata(fub_axi_wdata), .fub_axi_wstrb(fub_axi_wstrb), .fub_axi_wlast(fub_axi_wlast),
        .fub_axi_wuser(fub_axi_wuser), .fub_axi_wvalid(fub_axi_wvalid), .fub_axi_wready(fub_axi_wready),
        .fub_axi_wpoison(fub_axi_wpoison), .fub_axi_wtag(fub_axi_wtag), .fub_axi_wtagupdate(fub_axi_wtagupdate),
        .fub_axi_bid(fub_axi_bid), .fub_axi_bresp(fub_axi_bresp), .fub_axi_buser(fub_axi_buser),
        .fub_axi_bvalid(fub_axi_bvalid), .fub_axi_bready(fub_axi_bready), .fub_axi_btrace(fub_axi_btrace),
        .fub_axi_btag(fub_axi_btag), .fub_axi_btagmatch(fub_axi_btagmatch),
        .busy(busy)
    );

    axi_monitor_filtered #(
        .UNIT_ID(UNIT_ID), .AGENT_ID(AGENT_ID), .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .ADDR_WIDTH(AW), .ID_WIDTH(IW), .IS_READ(0), .IS_AXI(1),
        .ENABLE_PERF_PACKETS(1), .ENABLE_DEBUG_MODULE(0),
        .ENABLE_FILTERING(ENABLE_FILTERING), .ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE)
    ) axi_monitor_inst (
        .aclk(aclk), .aresetn(aresetn),
        .cmd_addr(fub_axi_awaddr), .cmd_id(fub_axi_awid), .cmd_len(fub_axi_awlen),
        .cmd_size(fub_axi_awsize), .cmd_burst(fub_axi_awburst),
        .cmd_valid(fub_axi_awvalid), .cmd_ready(fub_axi_awready),
        .data_id(fub_axi_bid), .data_last(fub_axi_wlast), .data_resp(fub_axi_bresp),
        .data_valid(fub_axi_wvalid), .data_ready(fub_axi_wready),
        .resp_id(fub_axi_bid), .resp_code(fub_axi_bresp),
        .resp_valid(fub_axi_bvalid), .resp_ready(fub_axi_bready),
        .cfg_freq_sel(4'b0001), .cfg_addr_cnt(4'd15), .cfg_data_cnt(4'd15), .cfg_resp_cnt(4'd15),
        .cfg_error_enable(cfg_error_enable), .cfg_compl_enable(cfg_monitor_enable),
        .cfg_threshold_enable(cfg_perf_enable), .cfg_timeout_enable(cfg_timeout_enable),
        .cfg_perf_enable(cfg_perf_enable), .cfg_debug_enable(1'b0),
        .cfg_debug_level(4'h0), .cfg_debug_mask(16'h0),
        .cfg_active_trans_threshold(16'd8), .cfg_latency_threshold(cfg_latency_threshold),
        .cfg_axi_pkt_mask(cfg_axi_pkt_mask), .cfg_axi_err_select(cfg_axi_err_select),
        .cfg_axi_error_mask(cfg_axi_error_mask), .cfg_axi_timeout_mask(cfg_axi_timeout_mask),
        .cfg_axi_compl_mask(cfg_axi_compl_mask), .cfg_axi_thresh_mask(cfg_axi_thresh_mask),
        .cfg_axi_perf_mask(cfg_axi_perf_mask), .cfg_axi_addr_mask(cfg_axi_addr_mask),
        .cfg_axi_debug_mask(cfg_axi_debug_mask),
        .monbus_valid(monbus_valid), .monbus_ready(monbus_ready), .monbus_packet(monbus_packet),
        /* verilator lint_off PINCONNECTEMPTY */
        .block_ready(), .busy(),
        /* verilator lint_on PINCONNECTEMPTY */
        .active_count(active_transactions), .cfg_conflict_error(cfg_conflict_error)
    );

    assign error_count = 16'h0;
    assign transaction_count = 32'h0;

endmodule : axi5_slave_wr_mon
