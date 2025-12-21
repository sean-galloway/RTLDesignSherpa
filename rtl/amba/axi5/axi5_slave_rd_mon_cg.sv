// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi5_slave_rd_mon_cg
// Purpose: AXI5 Slave Read with Monitor and Clock Gating
//
// This module wraps axi5_slave_rd_mon with clock gating support.
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-13

`timescale 1ns / 1ps

module axi5_slave_rd_mon_cg
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
    parameter int CG_IDLE_COUNT_WIDTH = 4,

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

    input  logic                           cfg_cg_enable,
    input  logic [CG_IDLE_COUNT_WIDTH-1:0] cfg_cg_idle_count,

    // Slave AXI5 Interface (Input Side)
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

    // FUB Interface (Output Side)
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
    logic int_arready, int_rready, int_busy;

    assign user_valid = s_axi_arvalid || s_axi_rready || int_busy;
    assign axi_valid = fub_axi_arvalid || fub_axi_rvalid;

    assign s_axi_arready = cg_gating ? 1'b0 : int_arready;
    assign fub_axi_rready = cg_gating ? 1'b0 : int_rready;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(CG_IDLE_COUNT_WIDTH)
    ) i_amba_clock_gate_ctrl (
        .clk_in(aclk), .aresetn(aresetn),
        .cfg_cg_enable(cfg_cg_enable), .cfg_cg_idle_count(cfg_cg_idle_count),
        .user_valid(user_valid), .axi_valid(axi_valid),
        .clk_out(gated_aclk), .gating(cg_gating), .idle(cg_idle)
    );

    axi5_slave_rd_mon #(
        .SKID_DEPTH_AR(SKID_DEPTH_AR), .SKID_DEPTH_R(SKID_DEPTH_R),
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_NSAID_WIDTH(AXI_NSAID_WIDTH), .AXI_MPAM_WIDTH(AXI_MPAM_WIDTH),
        .AXI_MECID_WIDTH(AXI_MECID_WIDTH), .AXI_TAG_WIDTH(AXI_TAG_WIDTH),
        .AXI_TAGOP_WIDTH(AXI_TAGOP_WIDTH), .AXI_CHUNKNUM_WIDTH(AXI_CHUNKNUM_WIDTH),
        .ENABLE_NSAID(ENABLE_NSAID), .ENABLE_TRACE(ENABLE_TRACE),
        .ENABLE_MPAM(ENABLE_MPAM), .ENABLE_MECID(ENABLE_MECID),
        .ENABLE_UNIQUE(ENABLE_UNIQUE), .ENABLE_CHUNKING(ENABLE_CHUNKING),
        .ENABLE_MTE(ENABLE_MTE), .ENABLE_POISON(ENABLE_POISON),
        .UNIT_ID(UNIT_ID), .AGENT_ID(AGENT_ID), .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .ENABLE_FILTERING(ENABLE_FILTERING), .ADD_PIPELINE_STAGE(ADD_PIPELINE_STAGE)
    ) i_axi5_slave_rd_mon (
        .aclk(gated_aclk), .aresetn(aresetn),
        .s_axi_arid(s_axi_arid), .s_axi_araddr(s_axi_araddr),
        .s_axi_arlen(s_axi_arlen), .s_axi_arsize(s_axi_arsize),
        .s_axi_arburst(s_axi_arburst), .s_axi_arlock(s_axi_arlock),
        .s_axi_arcache(s_axi_arcache), .s_axi_arprot(s_axi_arprot),
        .s_axi_arqos(s_axi_arqos), .s_axi_aruser(s_axi_aruser),
        .s_axi_arvalid(s_axi_arvalid), .s_axi_arready(int_arready),
        .s_axi_arnsaid(s_axi_arnsaid), .s_axi_artrace(s_axi_artrace),
        .s_axi_armpam(s_axi_armpam), .s_axi_armecid(s_axi_armecid),
        .s_axi_arunique(s_axi_arunique), .s_axi_archunken(s_axi_archunken),
        .s_axi_artagop(s_axi_artagop),
        .s_axi_rid(s_axi_rid), .s_axi_rdata(s_axi_rdata),
        .s_axi_rresp(s_axi_rresp), .s_axi_rlast(s_axi_rlast),
        .s_axi_ruser(s_axi_ruser), .s_axi_rvalid(s_axi_rvalid),
        .s_axi_rready(s_axi_rready), .s_axi_rtrace(s_axi_rtrace),
        .s_axi_rpoison(s_axi_rpoison), .s_axi_rchunkv(s_axi_rchunkv),
        .s_axi_rchunknum(s_axi_rchunknum), .s_axi_rchunkstrb(s_axi_rchunkstrb),
        .s_axi_rtag(s_axi_rtag), .s_axi_rtagmatch(s_axi_rtagmatch),
        .fub_axi_arid(fub_axi_arid), .fub_axi_araddr(fub_axi_araddr),
        .fub_axi_arlen(fub_axi_arlen), .fub_axi_arsize(fub_axi_arsize),
        .fub_axi_arburst(fub_axi_arburst), .fub_axi_arlock(fub_axi_arlock),
        .fub_axi_arcache(fub_axi_arcache), .fub_axi_arprot(fub_axi_arprot),
        .fub_axi_arqos(fub_axi_arqos), .fub_axi_aruser(fub_axi_aruser),
        .fub_axi_arvalid(fub_axi_arvalid), .fub_axi_arready(fub_axi_arready),
        .fub_axi_arnsaid(fub_axi_arnsaid), .fub_axi_artrace(fub_axi_artrace),
        .fub_axi_armpam(fub_axi_armpam), .fub_axi_armecid(fub_axi_armecid),
        .fub_axi_arunique(fub_axi_arunique), .fub_axi_archunken(fub_axi_archunken),
        .fub_axi_artagop(fub_axi_artagop),
        .fub_axi_rid(fub_axi_rid), .fub_axi_rdata(fub_axi_rdata),
        .fub_axi_rresp(fub_axi_rresp), .fub_axi_rlast(fub_axi_rlast),
        .fub_axi_ruser(fub_axi_ruser), .fub_axi_rvalid(fub_axi_rvalid),
        .fub_axi_rready(int_rready), .fub_axi_rtrace(fub_axi_rtrace),
        .fub_axi_rpoison(fub_axi_rpoison), .fub_axi_rchunkv(fub_axi_rchunkv),
        .fub_axi_rchunknum(fub_axi_rchunknum), .fub_axi_rchunkstrb(fub_axi_rchunkstrb),
        .fub_axi_rtag(fub_axi_rtag), .fub_axi_rtagmatch(fub_axi_rtagmatch),
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

endmodule : axi5_slave_rd_mon_cg
