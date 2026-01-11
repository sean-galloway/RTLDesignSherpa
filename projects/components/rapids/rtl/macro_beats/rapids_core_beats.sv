// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_core_beats
// Purpose: RAPIDS Beats Core - Complete Data Engine (No Config/AXIL MonBus)
//
// Description:
//   Top-level RAPIDS "beats" core combining:
//   - beats_scheduler_group_array: 8 scheduler groups with shared descriptor AXI
//   - sink_data_path: Fill -> SRAM -> AXI Write (network-to-memory)
//   - source_data_path: AXI Read -> SRAM -> Drain (memory-to-network)
//
//   This module contains everything EXCEPT:
//   - Configuration registers (AXIL slave) - provided externally
//   - AXIL monitor bus converter - MonBus raw output provided
//
//   For Phase 1 "beats" architecture:
//   - 8 channels with shared resources
//   - No network slave/master (fill/drain interfaces exposed)
//   - No credit management (simplified flow control)
//   - No chunk-based data (direct beats interface)
//
// Data Flows:
//   SINK PATH:   External Fill -> SRAM Controller -> AXI Write Engine -> Memory
//   SOURCE PATH: Memory -> AXI Read Engine -> SRAM Controller -> External Drain
//
// Documentation: projects/components/rapids/docs/rapids_spec/
// Subsystem: rapids_macro_beats
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module rapids_core_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int PIPELINE = 0,
    parameter int AR_MAX_OUTSTANDING = 8,
    parameter int AW_MAX_OUTSTANDING = 8,
    parameter int W_PHASE_FIFO_DEPTH = 64,
    parameter int B_PHASE_FIFO_DEPTH = 16,

    // Monitor Bus Base IDs
    parameter int DESC_MON_BASE_AGENT_ID = 16,   // 0x10 - Descriptor Engines (16-23)
    parameter int SCHED_MON_BASE_AGENT_ID = 48,  // 0x30 - Schedulers (48-55)
    parameter int DESC_AXI_MON_AGENT_ID = 8,     // 0x08 - Descriptor AXI Master Monitor
    parameter int MON_UNIT_ID = 1,               // 0x1
    parameter int MON_MAX_TRANSACTIONS = 16,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // APB Programming Interface (per channel kick-off)
    //=========================================================================
    input  logic [NC-1:0]                       apb_valid,
    output logic [NC-1:0]                       apb_ready,
    input  logic [NC-1:0][AW-1:0]               apb_addr,

    //=========================================================================
    // Configuration Interface (from external config registers)
    //=========================================================================
    // Per-channel configuration
    input  logic [NC-1:0]                       cfg_channel_enable,
    input  logic [NC-1:0]                       cfg_channel_reset,

    // Scheduler Configuration (global)
    input  logic                                cfg_sched_enable,
    input  logic [15:0]                         cfg_sched_timeout_cycles,
    input  logic                                cfg_sched_timeout_enable,
    input  logic                                cfg_sched_err_enable,
    input  logic                                cfg_sched_compl_enable,
    input  logic                                cfg_sched_perf_enable,

    // Descriptor Engine Configuration (global)
    input  logic                                cfg_desceng_enable,
    input  logic                                cfg_desceng_prefetch,
    input  logic [3:0]                          cfg_desceng_fifo_thresh,
    input  logic [AW-1:0]                       cfg_desceng_addr0_base,
    input  logic [AW-1:0]                       cfg_desceng_addr0_limit,
    input  logic [AW-1:0]                       cfg_desceng_addr1_base,
    input  logic [AW-1:0]                       cfg_desceng_addr1_limit,

    // Descriptor AXI Monitor Configuration
    input  logic                                cfg_desc_mon_enable,
    input  logic                                cfg_desc_mon_err_enable,
    input  logic                                cfg_desc_mon_perf_enable,
    input  logic                                cfg_desc_mon_timeout_enable,
    input  logic [31:0]                         cfg_desc_mon_timeout_cycles,
    input  logic [31:0]                         cfg_desc_mon_latency_thresh,
    input  logic [15:0]                         cfg_desc_mon_pkt_mask,
    input  logic [3:0]                          cfg_desc_mon_err_select,
    input  logic [7:0]                          cfg_desc_mon_err_mask,
    input  logic [7:0]                          cfg_desc_mon_timeout_mask,
    input  logic [7:0]                          cfg_desc_mon_compl_mask,
    input  logic [7:0]                          cfg_desc_mon_thresh_mask,
    input  logic [7:0]                          cfg_desc_mon_perf_mask,
    input  logic [7:0]                          cfg_desc_mon_addr_mask,
    input  logic [7:0]                          cfg_desc_mon_debug_mask,

    // AXI Transfer Configuration
    input  logic [7:0]                          cfg_axi_rd_xfer_beats,
    input  logic [7:0]                          cfg_axi_wr_xfer_beats,

    //=========================================================================
    // Status Interface
    //=========================================================================
    output logic                                system_idle,
    output logic [NC-1:0]                       descriptor_engine_idle,
    output logic [NC-1:0]                       scheduler_idle,
    output logic [NC-1:0][6:0]                  scheduler_state,
    output logic [NC-1:0]                       sched_error,

    // Descriptor AXI Monitor Status
    output logic                                cfg_sts_desc_mon_busy,
    output logic [7:0]                          cfg_sts_desc_mon_active_txns,
    output logic [15:0]                         cfg_sts_desc_mon_error_count,
    output logic [31:0]                         cfg_sts_desc_mon_txn_count,
    output logic                                cfg_sts_desc_mon_conflict_error,

    //=========================================================================
    // Sink Path - Fill Interface (External -> SRAM)
    //=========================================================================
    input  logic                        snk_fill_alloc_req,
    input  logic [7:0]                  snk_fill_alloc_size,
    input  logic [CIW-1:0]              snk_fill_alloc_id,
    output logic [NC-1:0][SCW-1:0]      snk_fill_space_free,

    input  logic                        snk_fill_valid,
    output logic                        snk_fill_ready,
    input  logic [CIW-1:0]              snk_fill_id,
    input  logic [DW-1:0]               snk_fill_data,

    //=========================================================================
    // Source Path - Drain Interface (SRAM -> External)
    //=========================================================================
    output logic [NC-1:0][SCW-1:0]      src_drain_data_avail,
    input  logic [NC-1:0]               src_drain_req,
    input  logic [NC-1:0][7:0]          src_drain_size,

    output logic [NC-1:0]               src_drain_valid,
    input  logic                        src_drain_read,
    input  logic [CIW-1:0]              src_drain_id,
    output logic [DW-1:0]               src_drain_data,

    //=========================================================================
    // AXI4 Master - Descriptor Fetch (FIXED 256-bit)
    //=========================================================================
    output logic                        m_axi_desc_arvalid,
    input  logic                        m_axi_desc_arready,
    output logic [AW-1:0]               m_axi_desc_araddr,
    output logic [7:0]                  m_axi_desc_arlen,
    output logic [2:0]                  m_axi_desc_arsize,
    output logic [1:0]                  m_axi_desc_arburst,
    output logic [IW-1:0]               m_axi_desc_arid,
    output logic                        m_axi_desc_arlock,
    output logic [3:0]                  m_axi_desc_arcache,
    output logic [2:0]                  m_axi_desc_arprot,
    output logic [3:0]                  m_axi_desc_arqos,
    output logic [3:0]                  m_axi_desc_arregion,

    input  logic                        m_axi_desc_rvalid,
    output logic                        m_axi_desc_rready,
    input  logic [255:0]                m_axi_desc_rdata,
    input  logic [1:0]                  m_axi_desc_rresp,
    input  logic                        m_axi_desc_rlast,
    input  logic [IW-1:0]               m_axi_desc_rid,

    //=========================================================================
    // AXI4 Master - Data Read (Memory -> Source SRAM)
    //=========================================================================
    output logic [IW-1:0]               m_axi_rd_arid,
    output logic [AW-1:0]               m_axi_rd_araddr,
    output logic [7:0]                  m_axi_rd_arlen,
    output logic [2:0]                  m_axi_rd_arsize,
    output logic [1:0]                  m_axi_rd_arburst,
    output logic                        m_axi_rd_arvalid,
    input  logic                        m_axi_rd_arready,

    input  logic [IW-1:0]               m_axi_rd_rid,
    input  logic [DW-1:0]               m_axi_rd_rdata,
    input  logic [1:0]                  m_axi_rd_rresp,
    input  logic                        m_axi_rd_rlast,
    input  logic                        m_axi_rd_rvalid,
    output logic                        m_axi_rd_rready,

    //=========================================================================
    // AXI4 Master - Data Write (Sink SRAM -> Memory)
    //=========================================================================
    output logic [IW-1:0]               m_axi_wr_awid,
    output logic [AW-1:0]               m_axi_wr_awaddr,
    output logic [7:0]                  m_axi_wr_awlen,
    output logic [2:0]                  m_axi_wr_awsize,
    output logic [1:0]                  m_axi_wr_awburst,
    output logic                        m_axi_wr_awlock,
    output logic [3:0]                  m_axi_wr_awcache,
    output logic [2:0]                  m_axi_wr_awprot,
    output logic [3:0]                  m_axi_wr_awqos,
    output logic [3:0]                  m_axi_wr_awregion,
    output logic                        m_axi_wr_awvalid,
    input  logic                        m_axi_wr_awready,

    output logic [DW-1:0]               m_axi_wr_wdata,
    output logic [(DW/8)-1:0]           m_axi_wr_wstrb,
    output logic                        m_axi_wr_wlast,
    output logic                        m_axi_wr_wvalid,
    input  logic                        m_axi_wr_wready,

    input  logic [IW-1:0]               m_axi_wr_bid,
    input  logic [1:0]                  m_axi_wr_bresp,
    input  logic                        m_axi_wr_bvalid,
    output logic                        m_axi_wr_bready,

    //=========================================================================
    // Monitor Bus Interface (Raw Output - No AXIL Conversion)
    //=========================================================================
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [63:0]                 mon_packet,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [NC-1:0]               dbg_rd_all_complete,
    output logic [31:0]                 dbg_r_beats_rcvd,
    output logic [31:0]                 dbg_sram_writes,
    output logic [NC-1:0]               dbg_arb_request,
    output logic [NC-1:0]               dbg_snk_sram_bridge_pending,
    output logic [NC-1:0]               dbg_snk_sram_bridge_out_valid,
    output logic [NC-1:0]               dbg_src_sram_bridge_pending,
    output logic [NC-1:0]               dbg_src_sram_bridge_out_valid
);

    //=========================================================================
    // Internal Signals - Scheduler Array ↔ Data Paths
    //=========================================================================

    // Scheduler → Sink Data Path (Write Requests)
    logic [NC-1:0]               sched_wr_valid;
    logic [NC-1:0]               sched_wr_ready;
    logic [NC-1:0][AW-1:0]       sched_wr_addr;
    logic [NC-1:0][31:0]         sched_wr_beats;

    // Scheduler → Source Data Path (Read Requests)
    logic [NC-1:0]               sched_rd_valid;
    logic [NC-1:0][AW-1:0]       sched_rd_addr;
    logic [NC-1:0][31:0]         sched_rd_beats;

    // Sink Data Path → Scheduler (Write Completion)
    logic [NC-1:0]               sched_wr_done_strobe;
    logic [NC-1:0][31:0]         sched_wr_beats_done;

    // Source Data Path → Scheduler (Read Completion)
    logic [NC-1:0]               sched_rd_done_strobe;
    logic [NC-1:0][31:0]         sched_rd_beats_done;

    // Data Path → Scheduler (Error Signals)
    logic [NC-1:0]               sched_rd_error;
    logic [NC-1:0]               sched_wr_error;

    //=========================================================================
    // Beats Scheduler Group Array
    //=========================================================================

    scheduler_group_array_beats #(
        .NUM_CHANNELS           (NC),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (AW),
        .DATA_WIDTH             (DW),
        .AXI_ID_WIDTH           (IW),
        .DESC_MON_BASE_AGENT_ID (DESC_MON_BASE_AGENT_ID),
        .SCHED_MON_BASE_AGENT_ID(SCHED_MON_BASE_AGENT_ID),
        .DESC_AXI_MON_AGENT_ID  (DESC_AXI_MON_AGENT_ID),
        .MON_UNIT_ID            (MON_UNIT_ID),
        .MON_MAX_TRANSACTIONS   (MON_MAX_TRANSACTIONS)
    ) u_scheduler_group_array (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // APB Programming Interface
        .apb_valid              (apb_valid),
        .apb_ready              (apb_ready),
        .apb_addr               (apb_addr),

        // Configuration
        .cfg_channel_enable     (cfg_channel_enable),
        .cfg_channel_reset      (cfg_channel_reset),
        .cfg_sched_enable       (cfg_sched_enable),
        .cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
        .cfg_sched_timeout_enable(cfg_sched_timeout_enable),
        .cfg_sched_err_enable   (cfg_sched_err_enable),
        .cfg_sched_compl_enable (cfg_sched_compl_enable),
        .cfg_sched_perf_enable  (cfg_sched_perf_enable),
        .cfg_desceng_enable     (cfg_desceng_enable),
        .cfg_desceng_prefetch   (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh(cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base (cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit(cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base (cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit(cfg_desceng_addr1_limit),

        // Descriptor AXI Monitor Configuration
        .cfg_desc_mon_enable        (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable(cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles(cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh(cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask      (cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select    (cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask      (cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask  (cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask    (cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask   (cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask     (cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask     (cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask    (cfg_desc_mon_debug_mask),

        // Status
        .descriptor_engine_idle (descriptor_engine_idle),
        .scheduler_idle         (scheduler_idle),
        .scheduler_state        (scheduler_state),
        .sched_error            (sched_error),
        .cfg_sts_desc_mon_busy          (cfg_sts_desc_mon_busy),
        .cfg_sts_desc_mon_active_txns   (cfg_sts_desc_mon_active_txns),
        .cfg_sts_desc_mon_error_count   (cfg_sts_desc_mon_error_count),
        .cfg_sts_desc_mon_txn_count     (cfg_sts_desc_mon_txn_count),
        .cfg_sts_desc_mon_conflict_error(cfg_sts_desc_mon_conflict_error),

        // Descriptor AXI Master
        .desc_axi_arvalid       (m_axi_desc_arvalid),
        .desc_axi_arready       (m_axi_desc_arready),
        .desc_axi_araddr        (m_axi_desc_araddr),
        .desc_axi_arlen         (m_axi_desc_arlen),
        .desc_axi_arsize        (m_axi_desc_arsize),
        .desc_axi_arburst       (m_axi_desc_arburst),
        .desc_axi_arid          (m_axi_desc_arid),
        .desc_axi_arlock        (m_axi_desc_arlock),
        .desc_axi_arcache       (m_axi_desc_arcache),
        .desc_axi_arprot        (m_axi_desc_arprot),
        .desc_axi_arqos         (m_axi_desc_arqos),
        .desc_axi_arregion      (m_axi_desc_arregion),
        .desc_axi_rvalid        (m_axi_desc_rvalid),
        .desc_axi_rready        (m_axi_desc_rready),
        .desc_axi_rdata         (m_axi_desc_rdata),
        .desc_axi_rresp         (m_axi_desc_rresp),
        .desc_axi_rlast         (m_axi_desc_rlast),
        .desc_axi_rid           (m_axi_desc_rid),

        // Data Read Interface (to Source Data Path)
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),

        // Data Write Interface (to Sink Data Path)
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),

        // Completion Strobes
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),

        // Error Signals
        .sched_rd_error         (sched_rd_error),
        .sched_wr_error         (sched_wr_error),

        // Monitor Bus
        .mon_valid              (mon_valid),
        .mon_ready              (mon_ready),
        .mon_packet             (mon_packet)
    );

    //=========================================================================
    // Sink Data Path (Fill -> SRAM -> AXI Write -> Memory)
    //=========================================================================

    // Note: axi_write_engine expects burst_len per channel
    // Derive from cfg_axi_wr_xfer_beats (same for all channels in simplified flow)
    logic [NC-1:0][7:0] sched_wr_burst_len;
    always_comb begin
        for (int i = 0; i < NC; i++) begin
            sched_wr_burst_len[i] = cfg_axi_wr_xfer_beats;
        end
    end

    snk_data_path_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
        .W_PHASE_FIFO_DEPTH (W_PHASE_FIFO_DEPTH),
        .B_PHASE_FIFO_DEPTH (B_PHASE_FIFO_DEPTH)
    ) u_sink_data_path (
        .clk                (clk),
        .rst_n              (rst_n),

        // Configuration
        .cfg_axi_wr_xfer_beats(cfg_axi_wr_xfer_beats),

        // Fill Interface (External)
        .fill_alloc_req     (snk_fill_alloc_req),
        .fill_alloc_size    (snk_fill_alloc_size),
        .fill_alloc_id      (snk_fill_alloc_id),
        .fill_space_free    (snk_fill_space_free),
        .fill_valid         (snk_fill_valid),
        .fill_ready         (snk_fill_ready),
        .fill_id            (snk_fill_id),
        .fill_data          (snk_fill_data),

        // Scheduler Interface
        .sched_wr_valid     (sched_wr_valid),
        .sched_wr_ready     (sched_wr_ready),
        .sched_wr_addr      (sched_wr_addr),
        .sched_wr_beats     (sched_wr_beats),
        .sched_wr_burst_len (sched_wr_burst_len),

        // Completion Interface
        .sched_wr_done_strobe(sched_wr_done_strobe),
        .sched_wr_beats_done (sched_wr_beats_done),

        // AXI Write Master
        .m_axi_awid         (m_axi_wr_awid),
        .m_axi_awaddr       (m_axi_wr_awaddr),
        .m_axi_awlen        (m_axi_wr_awlen),
        .m_axi_awsize       (m_axi_wr_awsize),
        .m_axi_awburst      (m_axi_wr_awburst),
        .m_axi_awlock       (m_axi_wr_awlock),
        .m_axi_awcache      (m_axi_wr_awcache),
        .m_axi_awprot       (m_axi_wr_awprot),
        .m_axi_awqos        (m_axi_wr_awqos),
        .m_axi_awregion     (m_axi_wr_awregion),
        .m_axi_awvalid      (m_axi_wr_awvalid),
        .m_axi_awready      (m_axi_wr_awready),
        .m_axi_wdata        (m_axi_wr_wdata),
        .m_axi_wstrb        (m_axi_wr_wstrb),
        .m_axi_wlast        (m_axi_wr_wlast),
        .m_axi_wvalid       (m_axi_wr_wvalid),
        .m_axi_wready       (m_axi_wr_wready),
        .m_axi_bid          (m_axi_wr_bid),
        .m_axi_bresp        (m_axi_wr_bresp),
        .m_axi_bvalid       (m_axi_wr_bvalid),
        .m_axi_bready       (m_axi_wr_bready),

        // Debug
        .dbg_sram_bridge_pending  (dbg_snk_sram_bridge_pending),
        .dbg_sram_bridge_out_valid(dbg_snk_sram_bridge_out_valid)
    );

    //=========================================================================
    // Source Data Path (Memory -> AXI Read -> SRAM -> Drain)
    //=========================================================================

    src_data_path_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING)
    ) u_source_data_path (
        .clk                (clk),
        .rst_n              (rst_n),

        // Configuration
        .cfg_axi_rd_xfer_beats(cfg_axi_rd_xfer_beats),

        // Scheduler Interface
        .sched_rd_valid     (sched_rd_valid),
        .sched_rd_addr      (sched_rd_addr),
        .sched_rd_beats     (sched_rd_beats),

        // Completion Interface
        .sched_rd_done_strobe(sched_rd_done_strobe),
        .sched_rd_beats_done (sched_rd_beats_done),
        .sched_rd_error      (sched_rd_error),

        // Drain Interface (External)
        .drain_data_avail   (src_drain_data_avail),
        .drain_req          (src_drain_req),
        .drain_size         (src_drain_size),
        .drain_valid        (src_drain_valid),
        .drain_read         (src_drain_read),
        .drain_id           (src_drain_id),
        .drain_data         (src_drain_data),

        // AXI Read Master
        .m_axi_arid         (m_axi_rd_arid),
        .m_axi_araddr       (m_axi_rd_araddr),
        .m_axi_arlen        (m_axi_rd_arlen),
        .m_axi_arsize       (m_axi_rd_arsize),
        .m_axi_arburst      (m_axi_rd_arburst),
        .m_axi_arvalid      (m_axi_rd_arvalid),
        .m_axi_arready      (m_axi_rd_arready),
        .m_axi_rid          (m_axi_rd_rid),
        .m_axi_rdata        (m_axi_rd_rdata),
        .m_axi_rresp        (m_axi_rd_rresp),
        .m_axi_rlast        (m_axi_rd_rlast),
        .m_axi_rvalid       (m_axi_rd_rvalid),
        .m_axi_rready       (m_axi_rd_rready),

        // Debug
        .dbg_rd_all_complete     (dbg_rd_all_complete),
        .dbg_r_beats_rcvd        (dbg_r_beats_rcvd),
        .dbg_sram_writes         (dbg_sram_writes),
        .dbg_arb_request         (dbg_arb_request),
        .dbg_sram_bridge_pending (dbg_src_sram_bridge_pending),
        .dbg_sram_bridge_out_valid(dbg_src_sram_bridge_out_valid)
    );

    //=========================================================================
    // System-Level Status Logic
    //=========================================================================

    // System is idle when ALL schedulers are idle
    assign system_idle = &scheduler_idle;

    // Write error aggregation (sticky from axi_write_engine - not yet implemented)
    assign sched_wr_error = '0;  // TODO: Add when write engine supports error reporting

endmodule : rapids_core_beats
