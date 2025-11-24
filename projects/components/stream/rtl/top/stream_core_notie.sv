// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_core_notie
// Purpose: STREAM Core Wrapper - Monitors Disabled
//
// Description:
//   Wrapper around stream_core.sv with all AXI monitor configurations tied off.
//   This variant reduces resource usage by disabling monitor packet generation.
//
//   Use Cases:
//   - Production systems where monitoring is not needed
//   - Resource-constrained FPGA implementations
//   - Simplified integration (no MonBus handling required)
//
//   Configuration Differences from stream_core:
//   - NO monitor configuration inputs exposed
//   - NO MonBus output (monitors disabled internally)
//   - All monitor enables tied to 0
//   - All monitor masks/thresholds tied to 0
//
//   Functional Equivalence:
//   - DMA transfer functionality identical to stream_core
//   - Scheduler, descriptor engine, AXI engines unchanged
//   - Performance identical (monitors disabled have minimal overhead)
//
// Documentation: rtl/top/INTEGRATION_ARCHITECTURE.md
// Subsystem: stream_top
//
// Author: sean galloway
// Created: 2025-11-21

`timescale 1ns / 1ps

`include "stream_imports.svh"

module stream_core_notie #(
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    parameter int SRAM_DEPTH = 4096,
    parameter int ADDR_WIDTH = 64,
    parameter int AXI_ID_WIDTH = 8,
    parameter int DESC_DATA_WIDTH = 256
) (
    //=========================================================================
    // Clock and Reset
    //=========================================================================
    input  logic                                clk,
    input  logic                                rst_n,

    //=========================================================================
    // Configuration Interface (NO monitor configs)
    //=========================================================================

    // Channel Control
    input  logic [NUM_CHANNELS-1:0]             cfg_channel_enable,
    input  logic [NUM_CHANNELS-1:0]             cfg_channel_reset,

    // Scheduler Configuration
    input  logic                                cfg_sched_enable,
    input  logic [15:0]                         cfg_sched_timeout_cycles,
    input  logic                                cfg_sched_timeout_enable,
    input  logic                                cfg_sched_err_enable,
    input  logic                                cfg_sched_compl_enable,
    input  logic                                cfg_sched_perf_enable,

    // Descriptor Engine Configuration
    input  logic                                cfg_desceng_enable,
    input  logic                                cfg_desceng_prefetch,
    input  logic [3:0]                          cfg_desceng_fifo_thresh,
    input  logic [ADDR_WIDTH-1:0]               cfg_desceng_addr0_base,
    input  logic [ADDR_WIDTH-1:0]               cfg_desceng_addr0_limit,
    input  logic [ADDR_WIDTH-1:0]               cfg_desceng_addr1_base,
    input  logic [ADDR_WIDTH-1:0]               cfg_desceng_addr1_limit,

    // AXI Transfer Configuration
    input  logic [7:0]                          cfg_axi_rd_xfer_beats,
    input  logic [7:0]                          cfg_axi_wr_xfer_beats,

    // Performance Profiler Configuration
    input  logic                                cfg_perf_enable,
    input  logic                                cfg_perf_mode,
    input  logic                                cfg_perf_clear,

    //=========================================================================
    // Status Interface
    //=========================================================================
    output logic [NUM_CHANNELS-1:0]             descriptor_engine_idle,
    output logic [NUM_CHANNELS-1:0]             scheduler_idle,
    output logic [NUM_CHANNELS-1:0][6:0]        scheduler_state,
    output logic [NUM_CHANNELS-1:0]             sched_error,

    //=========================================================================
    // Descriptor Engine APB Kick-off Interface (per channel)
    //=========================================================================
    input  logic [NUM_CHANNELS-1:0]             desc_apb_valid,
    output logic [NUM_CHANNELS-1:0]             desc_apb_ready,
    input  logic [NUM_CHANNELS-1:0][63:0]       desc_apb_addr,

    //=========================================================================
    // AXI Master - Descriptor Fetch (256-bit, shared by all channels)
    //=========================================================================
    output logic                                m_axi_desc_arvalid,
    input  logic                                m_axi_desc_arready,
    output logic [ADDR_WIDTH-1:0]               m_axi_desc_araddr,
    output logic [7:0]                          m_axi_desc_arlen,
    output logic [2:0]                          m_axi_desc_arsize,
    output logic [1:0]                          m_axi_desc_arburst,
    output logic [AXI_ID_WIDTH-1:0]             m_axi_desc_arid,
    output logic                                m_axi_desc_arlock,
    output logic [3:0]                          m_axi_desc_arcache,
    output logic [2:0]                          m_axi_desc_arprot,
    output logic [3:0]                          m_axi_desc_arqos,
    output logic [3:0]                          m_axi_desc_arregion,

    input  logic                                m_axi_desc_rvalid,
    output logic                                m_axi_desc_rready,
    input  logic [DESC_DATA_WIDTH-1:0]          m_axi_desc_rdata,
    input  logic [1:0]                          m_axi_desc_rresp,
    input  logic                                m_axi_desc_rlast,
    input  logic [AXI_ID_WIDTH-1:0]             m_axi_desc_rid,

    //=========================================================================
    // AXI Master - Data Read (parameterizable width, shared by all channels)
    //=========================================================================
    output logic                                m_axi_rd_arvalid,
    input  logic                                m_axi_rd_arready,
    output logic [ADDR_WIDTH-1:0]               m_axi_rd_araddr,
    output logic [7:0]                          m_axi_rd_arlen,
    output logic [2:0]                          m_axi_rd_arsize,
    output logic [1:0]                          m_axi_rd_arburst,
    output logic [AXI_ID_WIDTH-1:0]             m_axi_rd_arid,
    output logic                                m_axi_rd_arlock,
    output logic [3:0]                          m_axi_rd_arcache,
    output logic [2:0]                          m_axi_rd_arprot,
    output logic [3:0]                          m_axi_rd_arqos,
    output logic [3:0]                          m_axi_rd_arregion,

    input  logic                                m_axi_rd_rvalid,
    output logic                                m_axi_rd_rready,
    input  logic [DATA_WIDTH-1:0]               m_axi_rd_rdata,
    input  logic [1:0]                          m_axi_rd_rresp,
    input  logic                                m_axi_rd_rlast,
    input  logic [AXI_ID_WIDTH-1:0]             m_axi_rd_rid,

    //=========================================================================
    // AXI Master - Data Write (parameterizable width, shared by all channels)
    //=========================================================================
    output logic                                m_axi_wr_awvalid,
    input  logic                                m_axi_wr_awready,
    output logic [ADDR_WIDTH-1:0]               m_axi_wr_awaddr,
    output logic [7:0]                          m_axi_wr_awlen,
    output logic [2:0]                          m_axi_wr_awsize,
    output logic [1:0]                          m_axi_wr_awburst,
    output logic [AXI_ID_WIDTH-1:0]             m_axi_wr_awid,
    output logic                                m_axi_wr_awlock,
    output logic [3:0]                          m_axi_wr_awcache,
    output logic [2:0]                          m_axi_wr_awprot,
    output logic [3:0]                          m_axi_wr_awqos,
    output logic [3:0]                          m_axi_wr_awregion,

    output logic                                m_axi_wr_wvalid,
    input  logic                                m_axi_wr_wready,
    output logic [DATA_WIDTH-1:0]               m_axi_wr_wdata,
    output logic [DATA_WIDTH/8-1:0]             m_axi_wr_wstrb,
    output logic                                m_axi_wr_wlast,

    input  logic                                m_axi_wr_bvalid,
    output logic                                m_axi_wr_bready,
    input  logic [1:0]                          m_axi_wr_bresp,
    input  logic [AXI_ID_WIDTH-1:0]             m_axi_wr_bid

    // NOTE: MonBus output NOT present in this variant (monitors disabled)
);

    //=========================================================================
    // Instantiate stream_core with monitors disabled
    //=========================================================================

    stream_core #(
        .NUM_CHANNELS       (NUM_CHANNELS),
        .DATA_WIDTH         (DATA_WIDTH),
        .SRAM_DEPTH         (SRAM_DEPTH),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .DESC_DATA_WIDTH    (DESC_DATA_WIDTH)
    ) u_stream_core (
        // Clock and Reset
        .clk                (clk),
        .rst_n              (rst_n),

        // Configuration - Pass through non-monitor configs
        .cfg_channel_enable         (cfg_channel_enable),
        .cfg_channel_reset          (cfg_channel_reset),

        .cfg_sched_enable           (cfg_sched_enable),
        .cfg_sched_timeout_cycles   (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_enable   (cfg_sched_timeout_enable),
        .cfg_sched_err_enable       (cfg_sched_err_enable),
        .cfg_sched_compl_enable     (cfg_sched_compl_enable),
        .cfg_sched_perf_enable      (cfg_sched_perf_enable),

        .cfg_desceng_enable         (cfg_desceng_enable),
        .cfg_desceng_prefetch       (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh    (cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base     (cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit    (cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base     (cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit    (cfg_desceng_addr1_limit),

        // Monitor configs - ALL TIED OFF
        .cfg_desc_mon_enable        (1'b0),
        .cfg_desc_mon_err_enable    (1'b0),
        .cfg_desc_mon_perf_enable   (1'b0),
        .cfg_desc_mon_timeout_enable(1'b0),
        .cfg_desc_mon_timeout_cycles(32'h0),
        .cfg_desc_mon_latency_thresh(32'h0),
        .cfg_desc_mon_pkt_mask      (16'h0),
        .cfg_desc_mon_err_select    (4'h0),
        .cfg_desc_mon_err_mask      (8'h0),
        .cfg_desc_mon_timeout_mask  (8'h0),
        .cfg_desc_mon_compl_mask    (8'h0),
        .cfg_desc_mon_thresh_mask   (8'h0),
        .cfg_desc_mon_perf_mask     (8'h0),
        .cfg_desc_mon_addr_mask     (8'h0),
        .cfg_desc_mon_debug_mask    (8'h0),

        .cfg_rdeng_mon_enable       (1'b0),
        .cfg_rdeng_mon_err_enable   (1'b0),
        .cfg_rdeng_mon_perf_enable  (1'b0),
        .cfg_rdeng_mon_timeout_enable(1'b0),
        .cfg_rdeng_mon_timeout_cycles(32'h0),
        .cfg_rdeng_mon_latency_thresh(32'h0),
        .cfg_rdeng_mon_pkt_mask     (16'h0),
        .cfg_rdeng_mon_err_select   (4'h0),
        .cfg_rdeng_mon_err_mask     (8'h0),
        .cfg_rdeng_mon_timeout_mask (8'h0),
        .cfg_rdeng_mon_compl_mask   (8'h0),
        .cfg_rdeng_mon_thresh_mask  (8'h0),
        .cfg_rdeng_mon_perf_mask    (8'h0),
        .cfg_rdeng_mon_addr_mask    (8'h0),
        .cfg_rdeng_mon_debug_mask   (8'h0),

        .cfg_wreng_mon_enable       (1'b0),
        .cfg_wreng_mon_err_enable   (1'b0),
        .cfg_wreng_mon_perf_enable  (1'b0),
        .cfg_wreng_mon_timeout_enable(1'b0),
        .cfg_wreng_mon_timeout_cycles(32'h0),
        .cfg_wreng_mon_latency_thresh(32'h0),
        .cfg_wreng_mon_pkt_mask     (16'h0),
        .cfg_wreng_mon_err_select   (4'h0),
        .cfg_wreng_mon_err_mask     (8'h0),
        .cfg_wreng_mon_timeout_mask (8'h0),
        .cfg_wreng_mon_compl_mask   (8'h0),
        .cfg_wreng_mon_thresh_mask  (8'h0),
        .cfg_wreng_mon_perf_mask    (8'h0),
        .cfg_wreng_mon_addr_mask    (8'h0),
        .cfg_wreng_mon_debug_mask   (8'h0),

        .cfg_axi_rd_xfer_beats      (cfg_axi_rd_xfer_beats),
        .cfg_axi_wr_xfer_beats      (cfg_axi_wr_xfer_beats),

        .cfg_perf_enable            (cfg_perf_enable),
        .cfg_perf_mode              (cfg_perf_mode),
        .cfg_perf_clear             (cfg_perf_clear),

        // Status - Pass through
        .descriptor_engine_idle     (descriptor_engine_idle),
        .scheduler_idle             (scheduler_idle),
        .scheduler_state            (scheduler_state),
        .sched_error                (sched_error),

        // Descriptor APB Interface - Pass through
        .desc_apb_valid             (desc_apb_valid),
        .desc_apb_ready             (desc_apb_ready),
        .desc_apb_addr              (desc_apb_addr),

        // AXI Master - Descriptor Fetch - Pass through
        .m_axi_desc_arvalid         (m_axi_desc_arvalid),
        .m_axi_desc_arready         (m_axi_desc_arready),
        .m_axi_desc_araddr          (m_axi_desc_araddr),
        .m_axi_desc_arlen           (m_axi_desc_arlen),
        .m_axi_desc_arsize          (m_axi_desc_arsize),
        .m_axi_desc_arburst         (m_axi_desc_arburst),
        .m_axi_desc_arid            (m_axi_desc_arid),
        .m_axi_desc_arlock          (m_axi_desc_arlock),
        .m_axi_desc_arcache         (m_axi_desc_arcache),
        .m_axi_desc_arprot          (m_axi_desc_arprot),
        .m_axi_desc_arqos           (m_axi_desc_arqos),
        .m_axi_desc_arregion        (m_axi_desc_arregion),
        .m_axi_desc_rvalid          (m_axi_desc_rvalid),
        .m_axi_desc_rready          (m_axi_desc_rready),
        .m_axi_desc_rdata           (m_axi_desc_rdata),
        .m_axi_desc_rresp           (m_axi_desc_rresp),
        .m_axi_desc_rlast           (m_axi_desc_rlast),
        .m_axi_desc_rid             (m_axi_desc_rid),

        // AXI Master - Data Read - Pass through
        .m_axi_rd_arvalid           (m_axi_rd_arvalid),
        .m_axi_rd_arready           (m_axi_rd_arready),
        .m_axi_rd_araddr            (m_axi_rd_araddr),
        .m_axi_rd_arlen             (m_axi_rd_arlen),
        .m_axi_rd_arsize            (m_axi_rd_arsize),
        .m_axi_rd_arburst           (m_axi_rd_arburst),
        .m_axi_rd_arid              (m_axi_rd_arid),
        .m_axi_rd_arlock            (m_axi_rd_arlock),
        .m_axi_rd_arcache           (m_axi_rd_arcache),
        .m_axi_rd_arprot            (m_axi_rd_arprot),
        .m_axi_rd_arqos             (m_axi_rd_arqos),
        .m_axi_rd_arregion          (m_axi_rd_arregion),
        .m_axi_rd_rvalid            (m_axi_rd_rvalid),
        .m_axi_rd_rready            (m_axi_rd_rready),
        .m_axi_rd_rdata             (m_axi_rd_rdata),
        .m_axi_rd_rresp             (m_axi_rd_rresp),
        .m_axi_rd_rlast             (m_axi_rd_rlast),
        .m_axi_rd_rid               (m_axi_rd_rid),

        // AXI Master - Data Write - Pass through
        .m_axi_wr_awvalid           (m_axi_wr_awvalid),
        .m_axi_wr_awready           (m_axi_wr_awready),
        .m_axi_wr_awaddr            (m_axi_wr_awaddr),
        .m_axi_wr_awlen             (m_axi_wr_awlen),
        .m_axi_wr_awsize            (m_axi_wr_awsize),
        .m_axi_wr_awburst           (m_axi_wr_awburst),
        .m_axi_wr_awid              (m_axi_wr_awid),
        .m_axi_wr_awlock            (m_axi_wr_awlock),
        .m_axi_wr_awcache           (m_axi_wr_awcache),
        .m_axi_wr_awprot            (m_axi_wr_awprot),
        .m_axi_wr_awqos             (m_axi_wr_awqos),
        .m_axi_wr_awregion          (m_axi_wr_awregion),
        .m_axi_wr_wvalid            (m_axi_wr_wvalid),
        .m_axi_wr_wready            (m_axi_wr_wready),
        .m_axi_wr_wdata             (m_axi_wr_wdata),
        .m_axi_wr_wstrb             (m_axi_wr_wstrb),
        .m_axi_wr_wlast             (m_axi_wr_wlast),
        .m_axi_wr_bvalid            (m_axi_wr_bvalid),
        .m_axi_wr_bready            (m_axi_wr_bready),
        .m_axi_wr_bresp             (m_axi_wr_bresp),
        .m_axi_wr_bid               (m_axi_wr_bid),

        // MonBus - Tied off (not connected externally)
        .mon_valid                  (/* unconnected */),
        .mon_ready                  (1'b1),  // Always ready (sink disabled packets)
        .mon_packet                 (/* unconnected */)
    );

endmodule : stream_core_notie
