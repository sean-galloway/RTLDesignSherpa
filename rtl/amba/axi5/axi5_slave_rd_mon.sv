// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_rd_mon
// Purpose: AXI5 Slave Read with Integrated Filtered Monitoring
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_rd_mon
    import monitor_pkg::*;
#(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    parameter int AXI_NSAID_WIDTH   = 4,
    parameter int AXI_MPAM_WIDTH    = 11,
    parameter int AXI_MECID_WIDTH   = 16,
    parameter int AXI_TAG_WIDTH     = 4,
    parameter int AXI_TAGOP_WIDTH   = 2,
    parameter int AXI_CHUNKNUM_WIDTH = 4,

    parameter bit ENABLE_NSAID      = 1,
    parameter bit ENABLE_TRACE      = 1,
    parameter bit ENABLE_MPAM       = 1,
    parameter bit ENABLE_MECID      = 1,
    parameter bit ENABLE_UNIQUE     = 1,
    parameter bit ENABLE_CHUNKING   = 1,
    parameter bit ENABLE_MTE        = 1,
    parameter bit ENABLE_POISON     = 1,

    parameter int UNIT_ID           = 1,
    parameter int AGENT_ID          = 12,
    parameter int MAX_TRANSACTIONS  = 16,
    parameter bit ENABLE_FILTERING  = 1,
    parameter bit ADD_PIPELINE_STAGE = 0,

    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,

    parameter int NUM_TAGS = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1,
    parameter int TW       = AXI_TAG_WIDTH * NUM_TAGS,
    parameter int CHUNK_STRB_WIDTH = (AXI_DATA_WIDTH / 128) > 0 ? (AXI_DATA_WIDTH / 128) : 1
)
(
    input  logic aclk,
    input  logic aresetn,

    // Slave interface signals (all AXI5 AR and R channel signals)
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
    input  logic [AXI_NSAID_WIDTH-1:0]   s_axi_arnsaid,
    input  logic                         s_axi_artrace,
    input  logic [AXI_MPAM_WIDTH-1:0]    s_axi_armpam,
    input  logic [AXI_MECID_WIDTH-1:0]   s_axi_armecid,
    input  logic                         s_axi_arunique,
    input  logic                         s_axi_archunken,
    input  logic [AXI_TAGOP_WIDTH-1:0]   s_axi_artagop,

    output logic [IW-1:0]                s_axi_rid,
    output logic [DW-1:0]                s_axi_rdata,
    output logic [1:0]                   s_axi_rresp,
    output logic                         s_axi_rlast,
    output logic [UW-1:0]                s_axi_ruser,
    output logic                         s_axi_rvalid,
    input  logic                         s_axi_rready,
    output logic                         s_axi_rtrace,
    output logic                         s_axi_rpoison,
    output logic                         s_axi_rchunkv,
    output logic [AXI_CHUNKNUM_WIDTH-1:0] s_axi_rchunknum,
    output logic [CHUNK_STRB_WIDTH-1:0]  s_axi_rchunkstrb,
    output logic [TW-1:0]                s_axi_rtag,
    output logic                         s_axi_rtagmatch,

    // FUB interface signals (all AXI5 AR and R channel signals)
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
    output logic [AXI_NSAID_WIDTH-1:0]   fub_axi_arnsaid,
    output logic                         fub_axi_artrace,
    output logic [AXI_MPAM_WIDTH-1:0]    fub_axi_armpam,
    output logic [AXI_MECID_WIDTH-1:0]   fub_axi_armecid,
    output logic                         fub_axi_arunique,
    output logic                         fub_axi_archunken,
    output logic [AXI_TAGOP_WIDTH-1:0]   fub_axi_artagop,

    input  logic [IW-1:0]                fub_axi_rid,
    input  logic [DW-1:0]                fub_axi_rdata,
    input  logic [1:0]                   fub_axi_rresp,
    input  logic                         fub_axi_rlast,
    input  logic [UW-1:0]                fub_axi_ruser,
    input  logic                         fub_axi_rvalid,
    output logic                         fub_axi_rready,
    input  logic                         fub_axi_rtrace,
    input  logic                         fub_axi_rpoison,
    input  logic                         fub_axi_rchunkv,
    input  logic [AXI_CHUNKNUM_WIDTH-1:0] fub_axi_rchunknum,
    input  logic [CHUNK_STRB_WIDTH-1:0]  fub_axi_rchunkstrb,
    input  logic [TW-1:0]                fub_axi_rtag,
    input  logic                         fub_axi_rtagmatch,

    // Monitor configuration and output
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

    axi5_slave_rd #(
        .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R),
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_NSAID_WIDTH(AXI_NSAID_WIDTH), .AXI_MPAM_WIDTH(AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH(AXI_MECID_WIDTH), .AXI_TAG_WIDTH(AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH(AXI_TAGOP_WIDTH), .AXI_CHUNKNUM_WIDTH(AXI_CHUNKNUM_WIDTH),
        .ENABLE_NSAID(ENABLE_NSAID), .ENABLE_TRACE(ENABLE_TRACE),
        .ENABLE_MPAM(ENABLE_MPAM), .ENABLE_MECID(ENABLE_MECID),
        .ENABLE_UNIQUE(ENABLE_UNIQUE), .ENABLE_CHUNKING(ENABLE_CHUNKING),
        .ENABLE_MTE(ENABLE_MTE), .ENABLE_POISON(ENABLE_POISON)
    ) axi5_slave_rd_inst (
        .aclk(aclk), .aresetn(aresetn),
        .s_axi_arid(s_axi_arid), .s_axi_araddr(s_axi_araddr), .s_axi_arlen(s_axi_arlen),
        .s_axi_arsize(s_axi_arsize), .s_axi_arburst(s_axi_arburst), .s_axi_arlock(s_axi_arlock),
        .s_axi_arcache(s_axi_arcache), .s_axi_arprot(s_axi_arprot), .s_axi_arqos(s_axi_arqos),
        .s_axi_aruser(s_axi_aruser), .s_axi_arvalid(s_axi_arvalid), .s_axi_arready(s_axi_arready),
        .s_axi_arnsaid(s_axi_arnsaid), .s_axi_artrace(s_axi_artrace), .s_axi_armpam(s_axi_armpam),
        .s_axi_armecid(s_axi_armecid), .s_axi_arunique(s_axi_arunique),
        .s_axi_archunken(s_axi_archunken), .s_axi_artagop(s_axi_artagop),
        .s_axi_rid(s_axi_rid), .s_axi_rdata(s_axi_rdata), .s_axi_rresp(s_axi_rresp),
        .s_axi_rlast(s_axi_rlast), .s_axi_ruser(s_axi_ruser), .s_axi_rvalid(s_axi_rvalid),
        .s_axi_rready(s_axi_rready), .s_axi_rtrace(s_axi_rtrace), .s_axi_rpoison(s_axi_rpoison),
        .s_axi_rchunkv(s_axi_rchunkv), .s_axi_rchunknum(s_axi_rchunknum),
        .s_axi_rchunkstrb(s_axi_rchunkstrb), .s_axi_rtag(s_axi_rtag), .s_axi_rtagmatch(s_axi_rtagmatch),
        .fub_axi_arid(fub_axi_arid), .fub_axi_araddr(fub_axi_araddr), .fub_axi_arlen(fub_axi_arlen),
        .fub_axi_arsize(fub_axi_arsize), .fub_axi_arburst(fub_axi_arburst), .fub_axi_arlock(fub_axi_arlock),
        .fub_axi_arcache(fub_axi_arcache), .fub_axi_arprot(fub_axi_arprot), .fub_axi_arqos(fub_axi_arqos),
        .fub_axi_aruser(fub_axi_aruser), .fub_axi_arvalid(fub_axi_arvalid), .fub_axi_arready(fub_axi_arready),
        .fub_axi_arnsaid(fub_axi_arnsaid), .fub_axi_artrace(fub_axi_artrace), .fub_axi_armpam(fub_axi_armpam),
        .fub_axi_armecid(fub_axi_armecid), .fub_axi_arunique(fub_axi_arunique),
        .fub_axi_archunken(fub_axi_archunken), .fub_axi_artagop(fub_axi_artagop),
        .fub_axi_rid(fub_axi_rid), .fub_axi_rdata(fub_axi_rdata), .fub_axi_rresp(fub_axi_rresp),
        .fub_axi_rlast(fub_axi_rlast), .fub_axi_ruser(fub_axi_ruser), .fub_axi_rvalid(fub_axi_rvalid),
        .fub_axi_rready(fub_axi_rready), .fub_axi_rtrace(fub_axi_rtrace), .fub_axi_rpoison(fub_axi_rpoison),
        .fub_axi_rchunkv(fub_axi_rchunkv), .fub_axi_rchunknum(fub_axi_rchunknum),
        .fub_axi_rchunkstrb(fub_axi_rchunkstrb), .fub_axi_rtag(fub_axi_rtag), .fub_axi_rtagmatch(fub_axi_rtagmatch),
        .busy(busy)
    );

    axi_monitor_filtered #(
        .UNIT_ID(UNIT_ID), .AGENT_ID(AGENT_ID), .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .ADDR_WIDTH(AW), .ID_WIDTH(IW), .IS_READ(1), .IS_AXI(1),
        .ENABLE_PERF_PACKETS(1), .ENABLE_DEBUG_MODULE(0),
        .ENABLE_FILTERING(ENABLE_FILTERING), .ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE)
    ) axi_monitor_inst (
        .aclk(aclk), .aresetn(aresetn),
        .cmd_addr(fub_axi_araddr), .cmd_id(fub_axi_arid), .cmd_len(fub_axi_arlen),
        .cmd_size(fub_axi_arsize), .cmd_burst(fub_axi_arburst),
        .cmd_valid(fub_axi_arvalid), .cmd_ready(fub_axi_arready),
        .data_id(fub_axi_rid), .data_last(fub_axi_rlast), .data_resp(fub_axi_rresp),
        .data_valid(fub_axi_rvalid), .data_ready(fub_axi_rready),
        .resp_id(fub_axi_rid), .resp_code(fub_axi_rresp),
        .resp_valid(fub_axi_rvalid && fub_axi_rlast), .resp_ready(fub_axi_rready),
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

endmodule : axi5_slave_rd_mon
