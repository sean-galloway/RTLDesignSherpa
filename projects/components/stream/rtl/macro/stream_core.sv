// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_core
// Purpose: STREAM Top-Level Integration - Complete DMA Engine
//
// Description:
//   Integrates all STREAM components into complete scatter-gather DMA engine:
//   - scheduler_group_array: 8 channels + descriptor fetch
//   - axi_read_engine: Shared AXI read master
//   - axi_write_engine: Shared AXI write master
//   - sram_controller: Per-channel FIFO buffering
//   - perf_profiler: Performance monitoring
//   - AXI skid buffers: Improve timing closure
//
// Architecture:
//   1. APB config → scheduler_group_array (8 channels)
//   2. Descriptor fetch via shared AXI master (256-bit)
//   3. Read engine: Memory → SRAM controller
//   4. Write engine: SRAM controller → Memory
//   5. Skid buffers on all external AXI interfaces
//
// Monitor Control (USE_AXI_MONITORS parameter):
//   - USE_AXI_MONITORS = 1: Enable AXI transaction monitors (default)
//     * Monitor configuration inputs connected to scheduler_group_array
//     * MonBus output provides transaction telemetry
//   - USE_AXI_MONITORS = 0: Disable AXI transaction monitors
//     * All monitor configurations tied off internally
//     * MonBus output still present but inactive (no packets generated)
//     * Reduces resource usage for production systems
//
// Documentation: projects/components/stream/PRD.md
// Subsystem: stream_macro
//
// Author: sean galloway
// Created: 2025-11-08

`timescale 1ns / 1ps

// Import STREAM and monitor packages
`include "stream_imports.svh"
`include "reset_defs.svh"

module stream_core #(
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int FIFO_DEPTH = 512,
    parameter int AR_MAX_OUTSTANDING = 8,
    parameter int AW_MAX_OUTSTANDING = 8,

    // Monitor Control
    parameter int USE_AXI_MONITORS = 1,      // 1 = Enable monitors, 0 = Disable monitors

    // AXI skid buffer depths
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R = 4,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W = 4,
    parameter int SKID_DEPTH_B = 2,

    // Monitor Bus Base IDs
    parameter DESC_MON_BASE_AGENT_ID = 16,   // 0x10 - Descriptor Engines (16-23)
    parameter SCHED_MON_BASE_AGENT_ID = 48,  // 0x30 - Schedulers (48-55)
    parameter DESC_AXI_MON_AGENT_ID = 8,     // 0x08 - Descriptor AXI Master Monitor
    parameter MON_UNIT_ID = 1,               // 0x1

    // Desc-bus monitor reporter sub-block enables. Pass-through to
    // scheduler_group_array → axi4_master_rd_mon. Defaults match the
    // unit-level wrapper (5 cones on, debug on for stream's
    // compression dataset use).
    parameter bit DESC_MON_ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit DESC_MON_ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit DESC_MON_ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit DESC_MON_ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit DESC_MON_ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit DESC_MON_ENABLE_DEBUG_LOGIC     = 1'b1,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int UW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1  // AXI user width = channel ID width
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
    // Configuration Interface
    //=========================================================================
    // Per-channel configuration
    input  logic [NC-1:0]                       cfg_channel_enable,
    input  logic [NC-1:0]                       cfg_channel_reset,

    // Global scheduler configuration
    input  logic                                cfg_sched_enable,
    input  logic [31:0]                         cfg_sched_timeout_cycles,
    input  logic                                cfg_sched_timeout_enable,
    input  logic                                cfg_sched_err_enable,
    input  logic                                cfg_sched_compl_enable,
    input  logic                                cfg_sched_perf_enable,

    // Descriptor engine configuration
    input  logic                                cfg_desceng_enable,
    input  logic                                cfg_desceng_prefetch,
    input  logic [3:0]                          cfg_desceng_fifo_thresh,
    input  logic [AW-1:0]                       cfg_desceng_addr0_base,
    input  logic [AW-1:0]                       cfg_desceng_addr0_limit,
    input  logic [AW-1:0]                       cfg_desceng_addr1_base,
    input  logic [AW-1:0]                       cfg_desceng_addr1_limit,

    // Descriptor AXI monitor configuration (expanded with filtering)
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

    // Read Engine AXI monitor configuration
    input  logic                                cfg_rdeng_mon_enable,
    input  logic                                cfg_rdeng_mon_err_enable,
    input  logic                                cfg_rdeng_mon_perf_enable,
    input  logic                                cfg_rdeng_mon_timeout_enable,
    input  logic [31:0]                         cfg_rdeng_mon_timeout_cycles,
    input  logic [31:0]                         cfg_rdeng_mon_latency_thresh,
    input  logic [15:0]                         cfg_rdeng_mon_pkt_mask,
    input  logic [3:0]                          cfg_rdeng_mon_err_select,
    input  logic [7:0]                          cfg_rdeng_mon_err_mask,
    input  logic [7:0]                          cfg_rdeng_mon_timeout_mask,
    input  logic [7:0]                          cfg_rdeng_mon_compl_mask,
    input  logic [7:0]                          cfg_rdeng_mon_thresh_mask,
    input  logic [7:0]                          cfg_rdeng_mon_perf_mask,
    input  logic [7:0]                          cfg_rdeng_mon_addr_mask,
    input  logic [7:0]                          cfg_rdeng_mon_debug_mask,

    // Write Engine AXI monitor configuration
    input  logic                                cfg_wreng_mon_enable,
    input  logic                                cfg_wreng_mon_err_enable,
    input  logic                                cfg_wreng_mon_perf_enable,
    input  logic                                cfg_wreng_mon_timeout_enable,
    input  logic [31:0]                         cfg_wreng_mon_timeout_cycles,
    input  logic [31:0]                         cfg_wreng_mon_latency_thresh,
    input  logic [15:0]                         cfg_wreng_mon_pkt_mask,
    input  logic [3:0]                          cfg_wreng_mon_err_select,
    input  logic [7:0]                          cfg_wreng_mon_err_mask,
    input  logic [7:0]                          cfg_wreng_mon_timeout_mask,
    input  logic [7:0]                          cfg_wreng_mon_compl_mask,
    input  logic [7:0]                          cfg_wreng_mon_thresh_mask,
    input  logic [7:0]                          cfg_wreng_mon_perf_mask,
    input  logic [7:0]                          cfg_wreng_mon_addr_mask,
    input  logic [7:0]                          cfg_wreng_mon_debug_mask,

    // AXI transfer configuration
    input  logic [7:0]                          cfg_axi_rd_xfer_beats,
    input  logic [7:0]                          cfg_axi_wr_xfer_beats,

    // Performance profiler configuration
    input  logic                                cfg_perf_enable,
    input  logic                                cfg_perf_mode,
    input  logic                                cfg_perf_clear,

    //=========================================================================
    // Status Interface
    //=========================================================================
    output logic                                system_idle,           // System-level idle (all channels)
    output logic [NC-1:0]                       descriptor_engine_idle,
    output logic [NC-1:0]                       scheduler_idle,
    output logic [NC-1:0][6:0]                  scheduler_state,  // ONE-HOT encoding (7 bits)
    output logic [NC-1:0]                       sched_error,       // Scheduler error (sticky)
    output logic [NC-1:0]                       axi_rd_all_complete,  // All AXI read txns complete
    output logic [NC-1:0]                       axi_wr_all_complete,  // All AXI write txns complete

    // Performance profiler status
    output logic                                perf_fifo_empty,
    output logic                                perf_fifo_full,
    output logic [15:0]                         perf_fifo_count,
    input  logic                                perf_fifo_rd,
    output logic [31:0]                         perf_fifo_data_low,
    output logic [31:0]                         perf_fifo_data_high,

    //=========================================================================
    // Channel-Observation Mux (internal — drives stream_regs OBS_* fields via
    // stream_config_block). ch_sel + cat_sel select one lane of the per-
    // channel arrays already collected here; three 32-bit words come back.
    //   cat=0  status   data0=sched_rd_beats        data1=sched_wr_beats
    //   cat=1  rd_addr  data0=src_addr[31:0]        data1=src_addr[63:32]
    //   cat=2  wr_addr  data0=dst_addr[31:0]        data1=dst_addr[63:32]
    //   cat=3  sram     data0=rd_alloc_space_free   data1=wr_drain_data_avail
    // obs_flags is always live; see comment block above the mux for bit map.
    //=========================================================================
    input  logic [2:0]                          cfg_obs_ch_sel,
    input  logic [1:0]                          cfg_obs_cat_sel,
    output logic [31:0]                         obs_flags,
    output logic [31:0]                         obs_data0,
    output logic [31:0]                         obs_data1,

    //=========================================================================
    // External AXI4 Master - Descriptor Fetch (FIXED 256-bit)
    //=========================================================================
    // AR channel
    output logic [IW-1:0]                       m_axi_desc_arid,
    output logic [AW-1:0]                       m_axi_desc_araddr,
    output logic [7:0]                          m_axi_desc_arlen,
    output logic [2:0]                          m_axi_desc_arsize,
    output logic [1:0]                          m_axi_desc_arburst,
    output logic                                m_axi_desc_arlock,
    output logic [3:0]                          m_axi_desc_arcache,
    output logic [2:0]                          m_axi_desc_arprot,
    output logic [3:0]                          m_axi_desc_arqos,
    output logic [3:0]                          m_axi_desc_arregion,
    output logic [UW-1:0]                       m_axi_desc_aruser,
    output logic                                m_axi_desc_arvalid,
    input  logic                                m_axi_desc_arready,

    // R channel (FIXED 256-bit for descriptor size)
    input  logic [IW-1:0]                       m_axi_desc_rid,
    input  logic [255:0]                        m_axi_desc_rdata,
    input  logic [1:0]                          m_axi_desc_rresp,
    input  logic                                m_axi_desc_rlast,
    input  logic [UW-1:0]                       m_axi_desc_ruser,
    input  logic                                m_axi_desc_rvalid,
    output logic                                m_axi_desc_rready,

    //=========================================================================
    // External AXI4 Master - Data Read (parameterizable width)
    //=========================================================================
    // AR channel
    output logic [IW-1:0]                       m_axi_rd_arid,
    output logic [AW-1:0]                       m_axi_rd_araddr,
    output logic [7:0]                          m_axi_rd_arlen,
    output logic [2:0]                          m_axi_rd_arsize,
    output logic [1:0]                          m_axi_rd_arburst,
    output logic                                m_axi_rd_arlock,
    output logic [3:0]                          m_axi_rd_arcache,
    output logic [2:0]                          m_axi_rd_arprot,
    output logic [3:0]                          m_axi_rd_arqos,
    output logic [3:0]                          m_axi_rd_arregion,
    output logic [UW-1:0]                       m_axi_rd_aruser,
    output logic                                m_axi_rd_arvalid,
    input  logic                                m_axi_rd_arready,

    // R channel
    input  logic [IW-1:0]                       m_axi_rd_rid,
    input  logic [DW-1:0]                       m_axi_rd_rdata,
    input  logic [1:0]                          m_axi_rd_rresp,
    input  logic                                m_axi_rd_rlast,
    input  logic [UW-1:0]                       m_axi_rd_ruser,
    input  logic                                m_axi_rd_rvalid,
    output logic                                m_axi_rd_rready,

    //=========================================================================
    // External AXI4 Master - Data Write (parameterizable width)
    //=========================================================================
    // AW channel
    output logic [IW-1:0]                       m_axi_wr_awid,
    output logic [AW-1:0]                       m_axi_wr_awaddr,
    output logic [7:0]                          m_axi_wr_awlen,
    output logic [2:0]                          m_axi_wr_awsize,
    output logic [1:0]                          m_axi_wr_awburst,
    output logic                                m_axi_wr_awlock,
    output logic [3:0]                          m_axi_wr_awcache,
    output logic [2:0]                          m_axi_wr_awprot,
    output logic [3:0]                          m_axi_wr_awqos,
    output logic [3:0]                          m_axi_wr_awregion,
    output logic [UW-1:0]                       m_axi_wr_awuser,
    output logic                                m_axi_wr_awvalid,
    input  logic                                m_axi_wr_awready,

    // W channel
    output logic [DW-1:0]                       m_axi_wr_wdata,
    output logic [(DW/8)-1:0]                   m_axi_wr_wstrb,
    output logic                                m_axi_wr_wlast,
    output logic [UW-1:0]                       m_axi_wr_wuser,
    output logic                                m_axi_wr_wvalid,
    input  logic                                m_axi_wr_wready,

    // B channel
    input  logic [IW-1:0]                       m_axi_wr_bid,
    input  logic [1:0]                          m_axi_wr_bresp,
    input  logic [UW-1:0]                       m_axi_wr_buser,
    input  logic                                m_axi_wr_bvalid,
    output logic                                m_axi_wr_bready,

    //=========================================================================
    // Status/Debug Outputs
    //=========================================================================
    // Descriptor AXI Monitor Status
    output logic                                cfg_sts_desc_mon_busy,
    output logic [7:0]                          cfg_sts_desc_mon_active_txns,
    output logic [15:0]                         cfg_sts_desc_mon_error_count,
    output logic [31:0]                         cfg_sts_desc_mon_txn_count,
    output logic                                cfg_sts_desc_mon_conflict_error,

    // Data Read Engine AXI Monitor Status
    output logic                                cfg_sts_rdeng_skid_busy,
    output logic [7:0]                          cfg_sts_rdeng_mon_active_txns,
    output logic [15:0]                         cfg_sts_rdeng_mon_error_count,
    output logic [31:0]                         cfg_sts_rdeng_mon_txn_count,
    output logic                                cfg_sts_rdeng_mon_conflict_error,

    // Data Write Engine AXI Monitor Status
    output logic                                cfg_sts_wreng_skid_busy,
    output logic [7:0]                          cfg_sts_wreng_mon_active_txns,
    output logic [15:0]                         cfg_sts_wreng_mon_error_count,
    output logic [31:0]                         cfg_sts_wreng_mon_txn_count,
    output logic                                cfg_sts_wreng_mon_conflict_error,

    //=========================================================================
    // Unified Monitor Bus Interface (128-bit packet + 64-bit side-band ts)
    //=========================================================================
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output monitor_common_pkg::monitor_packet_t     mon_packet,
    output monitor_common_pkg::monbus_timestamp_t   mon_timestamp,

    //=========================================================================
    // Sideband for FPGA-characterization axi_bus_meter (W channel demux).
    // The W bus in AXI4 has no wid; this sideband mirrors the write engine's
    // internal r_w_channel_id / r_w_active so a bus meter at the wrapper
    // level can attribute per-W-beat activity to the correct channel.
    //=========================================================================
    output logic [$clog2(NC)-1:0]                   o_wr_active_channel_id,
    output logic                                    o_wr_active_channel_valid
);

    //=========================================================================
    // Internal Signals - Data Read AXI (pre-skid)
    //=========================================================================
    // NOTE: Descriptor AXI signals removed - scheduler_group_array connects
    //       directly to top-level m_axi_desc_* ports (no intermediate skid buffer)
    logic [IW-1:0]               fub_rd_axi_arid;
    logic [AW-1:0]               fub_rd_axi_araddr;
    logic [7:0]                  fub_rd_axi_arlen;
    logic [2:0]                  fub_rd_axi_arsize;
    logic [1:0]                  fub_rd_axi_arburst;
    logic                        fub_rd_axi_arlock;
    logic [3:0]                  fub_rd_axi_arcache;
    logic [2:0]                  fub_rd_axi_arprot;
    logic [3:0]                  fub_rd_axi_arqos;
    logic [3:0]                  fub_rd_axi_arregion;
    logic [UW-1:0]               fub_rd_axi_aruser;
    logic                        fub_rd_axi_arvalid;
    logic                        fub_rd_axi_arready;

    logic [IW-1:0]               fub_rd_axi_rid;
    logic [DW-1:0]               fub_rd_axi_rdata;
    logic [1:0]                  fub_rd_axi_rresp;
    logic                        fub_rd_axi_rlast;
    logic [UW-1:0]               fub_rd_axi_ruser;
    logic                        fub_rd_axi_rvalid;
    logic                        fub_rd_axi_rready;

    //=========================================================================
    // Internal Signals - Data Write AXI (pre-skid)
    //=========================================================================
    logic [IW-1:0]               fub_wr_axi_awid;
    logic [AW-1:0]               fub_wr_axi_awaddr;
    logic [7:0]                  fub_wr_axi_awlen;
    logic [2:0]                  fub_wr_axi_awsize;
    logic [1:0]                  fub_wr_axi_awburst;
    logic                        fub_wr_axi_awlock;
    logic [3:0]                  fub_wr_axi_awcache;
    logic [2:0]                  fub_wr_axi_awprot;
    logic [3:0]                  fub_wr_axi_awqos;
    logic [3:0]                  fub_wr_axi_awregion;
    logic [UW-1:0]               fub_wr_axi_awuser;
    logic                        fub_wr_axi_awvalid;
    logic                        fub_wr_axi_awready;

    logic [DW-1:0]               fub_wr_axi_wdata;
    logic [(DW/8)-1:0]           fub_wr_axi_wstrb;
    logic                        fub_wr_axi_wlast;
    logic [UW-1:0]               fub_wr_axi_wuser;
    logic                        fub_wr_axi_wvalid;
    logic                        fub_wr_axi_wready;

    logic [IW-1:0]               fub_wr_axi_bid;
    logic [1:0]                  fub_wr_axi_bresp;
    logic [UW-1:0]               fub_wr_axi_buser;
    logic                        fub_wr_axi_bvalid;
    logic                        fub_wr_axi_bready;

    //=========================================================================
    // Internal Signals - Scheduler ↔ Engines
    //=========================================================================
    // Read requests from schedulers to read engine
    logic [NC-1:0]               sched_rd_valid;
    logic [NC-1:0][AW-1:0]       sched_rd_addr;
    logic [NC-1:0][31:0]         sched_rd_beats;

    // Write requests from schedulers to write engine
    logic [NC-1:0]               sched_wr_valid;
    logic [NC-1:0]               sched_wr_ready;
    logic [NC-1:0][AW-1:0]       sched_wr_addr;
    logic [NC-1:0][31:0]         sched_wr_beats;

    // Completion strobes from engines to schedulers
    logic [NC-1:0]               sched_rd_done_strobe;
    logic [NC-1:0][31:0]         sched_rd_beats_done;
    logic [NC-1:0]               sched_wr_done_strobe;
    logic [NC-1:0][31:0]         sched_wr_beats_done;

    // Error signals from engines to schedulers
    logic [NC-1:0]               sched_rd_error;
    // Per-channel sticky/timeout detail from scheduler_group_array (for OBS)
    logic [NC-1:0]               dbg_sched_desc_error;
    logic [NC-1:0]               dbg_sched_rd_sticky;
    logic [NC-1:0]               dbg_sched_wr_sticky;
    logic [NC-1:0]               dbg_sched_timeout;
    logic [NC-1:0]               sched_wr_error;

    //=========================================================================
    // Internal Signals - Engines ↔ SRAM Controller
    //=========================================================================
    // Read engine → SRAM (allocation and write)
    logic                        axi_rd_alloc_req;
    logic [7:0]                  axi_rd_alloc_size;
    logic [IW-1:0]               axi_rd_alloc_id;
    logic [NC-1:0][$clog2(FIFO_DEPTH)+1-1:0] axi_rd_space_free;  // SRAM → read engine

    logic                        axi_rd_sram_valid;
    logic                        axi_rd_sram_ready;
    logic [IW-1:0]               axi_rd_sram_id;
    logic [DW-1:0]               axi_rd_sram_data;

    // Write engine → SRAM (drain and read)
    // Direct connection - both use ID-based interface
    logic [NC-1:0]               axi_wr_drain_req;
    logic [NC-1:0][7:0]          axi_wr_drain_size;
    logic [NC-1:0][$clog2(FIFO_DEPTH)+1-1:0] axi_wr_drain_data_avail;  // SRAM → write engine

    logic [NC-1:0]               axi_wr_sram_valid;           // Per-channel valid from SRAM (registered)
    logic [NC-1:0]               axi_wr_sram_valid_comb;      // Per-channel valid from SRAM (combinational)
    logic                        axi_wr_sram_drain;           // Drain signal from write engine
    logic [CHAN_WIDTH-1:0]       axi_wr_sram_id;              // Channel ID from write engine
    logic [DW-1:0]               axi_wr_sram_data;            // Muxed data from SRAM

    //=========================================================================
    // Internal Signals - Scheduler Group Monitor Bus (from scheduler_group_array)
    //=========================================================================
    logic                                     schedgrp_mon_valid;
    logic                                     schedgrp_mon_ready;
    monitor_common_pkg::monitor_packet_t      schedgrp_mon_packet;
    monitor_common_pkg::monbus_timestamp_t    schedgrp_mon_timestamp;

    //=========================================================================
    // Internal Signals - Monitor Configuration (conditional based on USE_AXI_MONITORS)
    //=========================================================================
    // When USE_AXI_MONITORS=0, internal signals are tied off
    logic                        int_cfg_desc_mon_enable;
    logic                        int_cfg_desc_mon_err_enable;
    logic                        int_cfg_desc_mon_perf_enable;
    logic                        int_cfg_desc_mon_timeout_enable;
    logic [31:0]                 int_cfg_desc_mon_timeout_cycles;
    logic [31:0]                 int_cfg_desc_mon_latency_thresh;
    logic [15:0]                 int_cfg_desc_mon_pkt_mask;
    logic [3:0]                  int_cfg_desc_mon_err_select;
    logic [7:0]                  int_cfg_desc_mon_err_mask;
    logic [7:0]                  int_cfg_desc_mon_timeout_mask;
    logic [7:0]                  int_cfg_desc_mon_compl_mask;
    logic [7:0]                  int_cfg_desc_mon_thresh_mask;
    logic [7:0]                  int_cfg_desc_mon_perf_mask;
    logic [7:0]                  int_cfg_desc_mon_addr_mask;
    logic [7:0]                  int_cfg_desc_mon_debug_mask;

    logic                        int_cfg_rdeng_mon_enable;
    logic                        int_cfg_rdeng_mon_err_enable;
    logic                        int_cfg_rdeng_mon_perf_enable;
    logic                        int_cfg_rdeng_mon_timeout_enable;
    logic [31:0]                 int_cfg_rdeng_mon_timeout_cycles;
    logic [31:0]                 int_cfg_rdeng_mon_latency_thresh;
    logic [15:0]                 int_cfg_rdeng_mon_pkt_mask;
    logic [3:0]                  int_cfg_rdeng_mon_err_select;
    logic [7:0]                  int_cfg_rdeng_mon_err_mask;
    logic [7:0]                  int_cfg_rdeng_mon_timeout_mask;
    logic [7:0]                  int_cfg_rdeng_mon_compl_mask;
    logic [7:0]                  int_cfg_rdeng_mon_thresh_mask;
    logic [7:0]                  int_cfg_rdeng_mon_perf_mask;
    logic [7:0]                  int_cfg_rdeng_mon_addr_mask;
    logic [7:0]                  int_cfg_rdeng_mon_debug_mask;

    logic                        int_cfg_wreng_mon_enable;
    logic                        int_cfg_wreng_mon_err_enable;
    logic                        int_cfg_wreng_mon_perf_enable;
    logic                        int_cfg_wreng_mon_timeout_enable;
    logic [31:0]                 int_cfg_wreng_mon_timeout_cycles;
    logic [31:0]                 int_cfg_wreng_mon_latency_thresh;
    logic [15:0]                 int_cfg_wreng_mon_pkt_mask;
    logic [3:0]                  int_cfg_wreng_mon_err_select;
    logic [7:0]                  int_cfg_wreng_mon_err_mask;
    logic [7:0]                  int_cfg_wreng_mon_timeout_mask;
    logic [7:0]                  int_cfg_wreng_mon_compl_mask;
    logic [7:0]                  int_cfg_wreng_mon_thresh_mask;
    logic [7:0]                  int_cfg_wreng_mon_perf_mask;
    logic [7:0]                  int_cfg_wreng_mon_addr_mask;
    logic [7:0]                  int_cfg_wreng_mon_debug_mask;

    //=========================================================================
    // Generate Block - Monitor Configuration Assignment
    //=========================================================================
    generate
        if (USE_AXI_MONITORS == 1) begin : g_monitors_enabled
            // Connect input ports to internal signals
            assign int_cfg_desc_mon_enable = cfg_desc_mon_enable;
            assign int_cfg_desc_mon_err_enable = cfg_desc_mon_err_enable;
            assign int_cfg_desc_mon_perf_enable = cfg_desc_mon_perf_enable;
            assign int_cfg_desc_mon_timeout_enable = cfg_desc_mon_timeout_enable;
            assign int_cfg_desc_mon_timeout_cycles = cfg_desc_mon_timeout_cycles;
            assign int_cfg_desc_mon_latency_thresh = cfg_desc_mon_latency_thresh;
            assign int_cfg_desc_mon_pkt_mask = cfg_desc_mon_pkt_mask;
            assign int_cfg_desc_mon_err_select = cfg_desc_mon_err_select;
            assign int_cfg_desc_mon_err_mask = cfg_desc_mon_err_mask;
            assign int_cfg_desc_mon_timeout_mask = cfg_desc_mon_timeout_mask;
            assign int_cfg_desc_mon_compl_mask = cfg_desc_mon_compl_mask;
            assign int_cfg_desc_mon_thresh_mask = cfg_desc_mon_thresh_mask;
            assign int_cfg_desc_mon_perf_mask = cfg_desc_mon_perf_mask;
            assign int_cfg_desc_mon_addr_mask = cfg_desc_mon_addr_mask;
            assign int_cfg_desc_mon_debug_mask = cfg_desc_mon_debug_mask;

            assign int_cfg_rdeng_mon_enable = cfg_rdeng_mon_enable;
            assign int_cfg_rdeng_mon_err_enable = cfg_rdeng_mon_err_enable;
            assign int_cfg_rdeng_mon_perf_enable = cfg_rdeng_mon_perf_enable;
            assign int_cfg_rdeng_mon_timeout_enable = cfg_rdeng_mon_timeout_enable;
            assign int_cfg_rdeng_mon_timeout_cycles = cfg_rdeng_mon_timeout_cycles;
            assign int_cfg_rdeng_mon_latency_thresh = cfg_rdeng_mon_latency_thresh;
            assign int_cfg_rdeng_mon_pkt_mask = cfg_rdeng_mon_pkt_mask;
            assign int_cfg_rdeng_mon_err_select = cfg_rdeng_mon_err_select;
            assign int_cfg_rdeng_mon_err_mask = cfg_rdeng_mon_err_mask;
            assign int_cfg_rdeng_mon_timeout_mask = cfg_rdeng_mon_timeout_mask;
            assign int_cfg_rdeng_mon_compl_mask = cfg_rdeng_mon_compl_mask;
            assign int_cfg_rdeng_mon_thresh_mask = cfg_rdeng_mon_thresh_mask;
            assign int_cfg_rdeng_mon_perf_mask = cfg_rdeng_mon_perf_mask;
            assign int_cfg_rdeng_mon_addr_mask = cfg_rdeng_mon_addr_mask;
            assign int_cfg_rdeng_mon_debug_mask = cfg_rdeng_mon_debug_mask;

            assign int_cfg_wreng_mon_enable = cfg_wreng_mon_enable;
            assign int_cfg_wreng_mon_err_enable = cfg_wreng_mon_err_enable;
            assign int_cfg_wreng_mon_perf_enable = cfg_wreng_mon_perf_enable;
            assign int_cfg_wreng_mon_timeout_enable = cfg_wreng_mon_timeout_enable;
            assign int_cfg_wreng_mon_timeout_cycles = cfg_wreng_mon_timeout_cycles;
            assign int_cfg_wreng_mon_latency_thresh = cfg_wreng_mon_latency_thresh;
            assign int_cfg_wreng_mon_pkt_mask = cfg_wreng_mon_pkt_mask;
            assign int_cfg_wreng_mon_err_select = cfg_wreng_mon_err_select;
            assign int_cfg_wreng_mon_err_mask = cfg_wreng_mon_err_mask;
            assign int_cfg_wreng_mon_timeout_mask = cfg_wreng_mon_timeout_mask;
            assign int_cfg_wreng_mon_compl_mask = cfg_wreng_mon_compl_mask;
            assign int_cfg_wreng_mon_thresh_mask = cfg_wreng_mon_thresh_mask;
            assign int_cfg_wreng_mon_perf_mask = cfg_wreng_mon_perf_mask;
            assign int_cfg_wreng_mon_addr_mask = cfg_wreng_mon_addr_mask;
            assign int_cfg_wreng_mon_debug_mask = cfg_wreng_mon_debug_mask;
        end else begin : g_monitors_disabled
            // Tie off all monitor configurations to 0
            assign int_cfg_desc_mon_enable = 1'b0;
            assign int_cfg_desc_mon_err_enable = 1'b0;
            assign int_cfg_desc_mon_perf_enable = 1'b0;
            assign int_cfg_desc_mon_timeout_enable = 1'b0;
            assign int_cfg_desc_mon_timeout_cycles = 32'h0;
            assign int_cfg_desc_mon_latency_thresh = 32'h0;
            assign int_cfg_desc_mon_pkt_mask = 16'h0;
            assign int_cfg_desc_mon_err_select = 4'h0;
            assign int_cfg_desc_mon_err_mask = 8'h0;
            assign int_cfg_desc_mon_timeout_mask = 8'h0;
            assign int_cfg_desc_mon_compl_mask = 8'h0;
            assign int_cfg_desc_mon_thresh_mask = 8'h0;
            assign int_cfg_desc_mon_perf_mask = 8'h0;
            assign int_cfg_desc_mon_addr_mask = 8'h0;
            assign int_cfg_desc_mon_debug_mask = 8'h0;

            assign int_cfg_rdeng_mon_enable = 1'b0;
            assign int_cfg_rdeng_mon_err_enable = 1'b0;
            assign int_cfg_rdeng_mon_perf_enable = 1'b0;
            assign int_cfg_rdeng_mon_timeout_enable = 1'b0;
            assign int_cfg_rdeng_mon_timeout_cycles = 32'h0;
            assign int_cfg_rdeng_mon_latency_thresh = 32'h0;
            assign int_cfg_rdeng_mon_pkt_mask = 16'h0;
            assign int_cfg_rdeng_mon_err_select = 4'h0;
            assign int_cfg_rdeng_mon_err_mask = 8'h0;
            assign int_cfg_rdeng_mon_timeout_mask = 8'h0;
            assign int_cfg_rdeng_mon_compl_mask = 8'h0;
            assign int_cfg_rdeng_mon_thresh_mask = 8'h0;
            assign int_cfg_rdeng_mon_perf_mask = 8'h0;
            assign int_cfg_rdeng_mon_addr_mask = 8'h0;
            assign int_cfg_rdeng_mon_debug_mask = 8'h0;

            assign int_cfg_wreng_mon_enable = 1'b0;
            assign int_cfg_wreng_mon_err_enable = 1'b0;
            assign int_cfg_wreng_mon_perf_enable = 1'b0;
            assign int_cfg_wreng_mon_timeout_enable = 1'b0;
            assign int_cfg_wreng_mon_timeout_cycles = 32'h0;
            assign int_cfg_wreng_mon_latency_thresh = 32'h0;
            assign int_cfg_wreng_mon_pkt_mask = 16'h0;
            assign int_cfg_wreng_mon_err_select = 4'h0;
            assign int_cfg_wreng_mon_err_mask = 8'h0;
            assign int_cfg_wreng_mon_timeout_mask = 8'h0;
            assign int_cfg_wreng_mon_compl_mask = 8'h0;
            assign int_cfg_wreng_mon_thresh_mask = 8'h0;
            assign int_cfg_wreng_mon_perf_mask = 8'h0;
            assign int_cfg_wreng_mon_addr_mask = 8'h0;
            assign int_cfg_wreng_mon_debug_mask = 8'h0;
        end
    endgenerate

    //=========================================================================
    // Component Instantiation - Scheduler Group Array
    //=========================================================================
    scheduler_group_array #(
        .NUM_CHANNELS           (NC),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (AW),
        .DATA_WIDTH             (DW),
        .AXI_ID_WIDTH           (IW),
        .DESC_MON_BASE_AGENT_ID (DESC_MON_BASE_AGENT_ID),
        .SCHED_MON_BASE_AGENT_ID(SCHED_MON_BASE_AGENT_ID),
        .DESC_AXI_MON_AGENT_ID  (DESC_AXI_MON_AGENT_ID),
        .MON_UNIT_ID            (MON_UNIT_ID),
        .DESC_MON_ENABLE_ERROR_LOGIC     (DESC_MON_ENABLE_ERROR_LOGIC),
        .DESC_MON_ENABLE_TIMEOUT_LOGIC   (DESC_MON_ENABLE_TIMEOUT_LOGIC),
        .DESC_MON_ENABLE_COMPL_LOGIC     (DESC_MON_ENABLE_COMPL_LOGIC),
        .DESC_MON_ENABLE_THRESHOLD_LOGIC (DESC_MON_ENABLE_THRESHOLD_LOGIC),
        .DESC_MON_ENABLE_PERF_LOGIC      (DESC_MON_ENABLE_PERF_LOGIC),
        .DESC_MON_ENABLE_DEBUG_LOGIC     (DESC_MON_ENABLE_DEBUG_LOGIC)
    ) u_scheduler_group_array (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // APB interface
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

        // Descriptor AXI Monitor Configuration (use internal signals)
        .cfg_desc_mon_enable        (int_cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (int_cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (int_cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable(int_cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles(int_cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh(int_cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask      (int_cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select    (int_cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask      (int_cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask  (int_cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask    (int_cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask   (int_cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask     (int_cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask     (int_cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask    (int_cfg_desc_mon_debug_mask),

        // Status
        .descriptor_engine_idle (descriptor_engine_idle),
        .scheduler_idle         (scheduler_idle),
        .scheduler_state        (scheduler_state),
        .sched_error            (sched_error),
        // Sticky/timeout detail for the channel-observation mux
        .dbg_descriptor_error   (dbg_sched_desc_error),
        .dbg_read_error_sticky  (dbg_sched_rd_sticky),
        .dbg_write_error_sticky (dbg_sched_wr_sticky),
        .dbg_timeout_expired    (dbg_sched_timeout),

        // Descriptor AXI Monitor Status
        .cfg_sts_desc_mon_busy          (cfg_sts_desc_mon_busy),
        .cfg_sts_desc_mon_active_txns   (cfg_sts_desc_mon_active_txns),
        .cfg_sts_desc_mon_error_count   (cfg_sts_desc_mon_error_count),
        .cfg_sts_desc_mon_txn_count     (cfg_sts_desc_mon_txn_count),
        .cfg_sts_desc_mon_conflict_error(cfg_sts_desc_mon_conflict_error),

        // Descriptor AXI master (connect directly to top-level ports)
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

        // Data read interface to read engine (per-channel arrays)
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),

        // Data write interface to write engine (per-channel arrays)
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),

        // Completion strobes from engines (per-channel arrays)
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),

        // Error signals (per-channel arrays from engines)
        .sched_rd_error         (sched_rd_error),
        .sched_wr_error         (sched_wr_error),

        // Free-running monitor-time broadcast
        .i_mon_time             (i_mon_time),

        // Monitor bus output (scheduler group monitor - directly to top-level)
        .mon_valid              (schedgrp_mon_valid),
        .mon_ready              (schedgrp_mon_ready),
        .mon_packet             (schedgrp_mon_packet),
        .mon_timestamp          (schedgrp_mon_timestamp)
    );

    //=========================================================================
    // Monitor Bus - Direct connection (no arbiter needed with single source)
    //=========================================================================
    assign mon_valid          = schedgrp_mon_valid;
    assign schedgrp_mon_ready = mon_ready;
    assign mon_packet         = schedgrp_mon_packet;
    assign mon_timestamp      = schedgrp_mon_timestamp;

    //=========================================================================
    // Component Instantiation - AXI Read Engine
    //=========================================================================

    axi_read_engine #(
        .NUM_CHANNELS           (NC),
        .ADDR_WIDTH             (AW),
        .DATA_WIDTH             (DW),
        .ID_WIDTH               (IW),
        .SEG_COUNT_WIDTH        ($clog2(FIFO_DEPTH)+1),  // Match SRAM controller width
        .PIPELINE               (1),
        .AR_MAX_OUTSTANDING     (AR_MAX_OUTSTANDING),
        .STROBE_EVERY_BEAT      (0)
    ) u_axi_read_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_rd_xfer_beats  (cfg_axi_rd_xfer_beats),

        // Scheduler interface
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),

        // AXI AR channel (pre-skid)
        .m_axi_arid             (fub_rd_axi_arid),
        .m_axi_araddr           (fub_rd_axi_araddr),
        .m_axi_arlen            (fub_rd_axi_arlen),
        .m_axi_arsize           (fub_rd_axi_arsize),
        .m_axi_arburst          (fub_rd_axi_arburst),
        .m_axi_arvalid          (fub_rd_axi_arvalid),
        .m_axi_arready          (fub_rd_axi_arready),

        // AXI R channel (pre-skid)
        .m_axi_rid              (fub_rd_axi_rid),
        .m_axi_rdata            (fub_rd_axi_rdata),
        .m_axi_rresp            (fub_rd_axi_rresp),
        .m_axi_rlast            (fub_rd_axi_rlast),
        .m_axi_rvalid           (fub_rd_axi_rvalid),
        .m_axi_rready           (fub_rd_axi_rready),

        // SRAM allocation interface
        .axi_rd_alloc_req       (axi_rd_alloc_req),
        .axi_rd_alloc_size      (axi_rd_alloc_size),
        .axi_rd_alloc_id        (axi_rd_alloc_id),
        .axi_rd_alloc_space_free(axi_rd_space_free),

        // SRAM write interface
        .axi_rd_sram_valid      (axi_rd_sram_valid),
        .axi_rd_sram_ready      (axi_rd_sram_ready),
        .axi_rd_sram_id         (axi_rd_sram_id),
        .axi_rd_sram_data       (axi_rd_sram_data),

        // Completion interface
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),

        // Debug interface
        .dbg_rd_all_complete    (axi_rd_all_complete),

        // Error signals
        .sched_rd_error         (sched_rd_error),

        // Debug
        .dbg_r_beats_rcvd       (),
        .dbg_sram_writes        (),
        .dbg_arb_request        ()
    );

    //=========================================================================
    // Component Instantiation - AXI Write Engine
    //=========================================================================

    axi_write_engine #(
        .NUM_CHANNELS           (NC),
        .ADDR_WIDTH             (AW),
        .DATA_WIDTH             (DW),
        .ID_WIDTH               (IW),
        .USER_WIDTH             (UW),
        .SEG_COUNT_WIDTH        ($clog2(FIFO_DEPTH)+1),  // Match SRAM controller width
        .PIPELINE               (1),
        .AW_MAX_OUTSTANDING     (AW_MAX_OUTSTANDING)
    ) u_axi_write_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_wr_xfer_beats  (cfg_axi_wr_xfer_beats),

        // Scheduler interface
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),
        .sched_wr_burst_len     ({NC{cfg_axi_wr_xfer_beats}}),  // All channels use same burst length

        // SRAM drain interface
        .axi_wr_drain_req       (axi_wr_drain_req),
        .axi_wr_drain_size      (axi_wr_drain_size),
        .axi_wr_drain_data_avail(axi_wr_drain_data_avail),

        // AXI AW channel (pre-skid)
        .m_axi_awid             (fub_wr_axi_awid),
        .m_axi_awaddr           (fub_wr_axi_awaddr),
        .m_axi_awlen            (fub_wr_axi_awlen),
        .m_axi_awsize           (fub_wr_axi_awsize),
        .m_axi_awburst          (fub_wr_axi_awburst),
        .m_axi_awvalid          (fub_wr_axi_awvalid),
        .m_axi_awready          (fub_wr_axi_awready),

        // AXI W channel (pre-skid)
        .m_axi_wdata            (fub_wr_axi_wdata),
        .m_axi_wstrb            (fub_wr_axi_wstrb),
        .m_axi_wlast            (fub_wr_axi_wlast),
        .m_axi_wuser            (fub_wr_axi_wuser),
        .m_axi_wvalid           (fub_wr_axi_wvalid),
        .m_axi_wready           (fub_wr_axi_wready),

        // AXI B channel (pre-skid)
        .m_axi_bid              (fub_wr_axi_bid),
        .m_axi_bresp            (fub_wr_axi_bresp),
        .m_axi_bvalid           (fub_wr_axi_bvalid),
        .m_axi_bready           (fub_wr_axi_bready),

        // SRAM read interface (ID-based - direct connection)
        .axi_wr_sram_valid      (axi_wr_sram_valid),
        .axi_wr_sram_valid_comb (axi_wr_sram_valid_comb),
        .axi_wr_sram_drain      (axi_wr_sram_drain),
        .axi_wr_sram_id         (axi_wr_sram_id),
        .axi_wr_sram_data       (axi_wr_sram_data),

        // Completion interface
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),
        .dbg_wr_all_complete    (axi_wr_all_complete),
        .sched_wr_error         (sched_wr_error),

        // Debug
        .dbg_aw_transactions    (),
        .dbg_w_beats            (),

        // Sideband to stream_core's external port surface so the FPGA
        // characterization harness can wire axi_bus_meter directly.
        .o_active_channel_id    (o_wr_active_channel_id),
        .o_active_channel_valid (o_wr_active_channel_valid)
    );

    //=========================================================================
    // Component Instantiation - SRAM Controller
    //=========================================================================
    sram_controller #(
        .NUM_CHANNELS           (NC),
        .DATA_WIDTH             (DW),
        .SRAM_DEPTH             (FIFO_DEPTH)
    ) u_sram_controller (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Write interface (from read engine)
        .axi_rd_sram_valid      (axi_rd_sram_valid),
        .axi_rd_sram_id         (axi_rd_sram_id[CHAN_WIDTH-1:0]),  // Extract channel ID from AXI ID
        .axi_rd_sram_ready      (axi_rd_sram_ready),
        .axi_rd_sram_data       (axi_rd_sram_data),

        // Allocation interface (for read engine)
        .axi_rd_alloc_req       (axi_rd_alloc_req),
        .axi_rd_alloc_size      (axi_rd_alloc_size),
        .axi_rd_alloc_id        (axi_rd_alloc_id[CHAN_WIDTH-1:0]),     // Extract channel ID from AXI ID
        .axi_rd_alloc_space_free(axi_rd_space_free),

        // Drain interface (for write engine flow control)
        .axi_wr_drain_req       (axi_wr_drain_req),
        .axi_wr_drain_size      (axi_wr_drain_size),
        .axi_wr_drain_data_avail(axi_wr_drain_data_avail),

        // Read interface (to write engine - direct connection)
        .axi_wr_sram_valid      (axi_wr_sram_valid),          // Per-channel valids (registered, arbitration use)
        .axi_wr_sram_valid_comb (axi_wr_sram_valid_comb),     // Per-channel valids (combinational, wvalid gate)
        .axi_wr_sram_drain      (axi_wr_sram_drain),          // Drain signal from write engine
        .axi_wr_sram_id         (axi_wr_sram_id),             // Channel ID from write engine
        .axi_wr_sram_data       (axi_wr_sram_data),           // Muxed data from SRAM

        // Debug
        .dbg_bridge_pending     (),
        .dbg_bridge_out_valid   ()
    );

    //=========================================================================
    // Component Instantiation - Performance Profiler
    //=========================================================================
    perf_profiler #(
        .NUM_CHANNELS           (NC),
        .CHANNEL_WIDTH          (CHAN_WIDTH),
        .TIMESTAMP_WIDTH        (32),
        .FIFO_DEPTH             (256)
    ) u_perf_profiler (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Channel idle signals (from scheduler_group_array)
        .channel_idle           (scheduler_idle),

        // Configuration
        .cfg_enable             (cfg_perf_enable),
        .cfg_mode               (cfg_perf_mode),
        .cfg_clear              (cfg_perf_clear),

        // FIFO read interface
        .perf_fifo_rd           (perf_fifo_rd),
        .perf_fifo_data_low     (perf_fifo_data_low),
        .perf_fifo_data_high    (perf_fifo_data_high),
        .perf_fifo_empty        (perf_fifo_empty),
        .perf_fifo_full         (perf_fifo_full),
        .perf_fifo_count        (perf_fifo_count)
    );

    //=========================================================================
    // Component Instantiation - AXI Skid Buffers
    //=========================================================================
    // NOTE: Descriptor AXI skid buffer removed - scheduler_group_array connects
    //       directly to top-level ports (descriptor fetch has built-in monitor)

    // Data read AXI skid buffer
    // Tie off unused AXI signals
    assign fub_rd_axi_arlock = 1'b0;
    assign fub_rd_axi_arcache = 4'h0;
    assign fub_rd_axi_arprot = 3'h0;
    assign fub_rd_axi_arqos = 4'h0;
    assign fub_rd_axi_arregion = 4'h0;
    // AXI USER fields carry channel ID for packet analysis/sorting.
    // ARUSER is request-side (FUB drives -> master forwards), so this assign
    // is a legitimate driver. RUSER is response-side (master drives FUB from
    // slave's R response), so we must NOT drive it here — doing so creates a
    // real multi-driver against axi4_master_rd's fub_axi_ruser output and
    // surfaces as DRC MDRV-1 in opt_design (and as Synth 8-6859 critical
    // warnings during synthesis). RUSER is unused downstream; leaving it
    // driven only by the master is correct.
    assign fub_rd_axi_aruser = UW'(fub_rd_axi_arid);  // Extract channel ID from transaction ID

    axi4_master_rd #(
        .SKID_DEPTH_AR          (SKID_DEPTH_AR),
        .SKID_DEPTH_R           (SKID_DEPTH_R),
        .AXI_ID_WIDTH           (IW),
        .AXI_ADDR_WIDTH         (AW),
        .AXI_DATA_WIDTH         (DW),
        .AXI_USER_WIDTH         (UW)
    ) u_rd_axi_skid (
        .aclk                   (clk),
        .aresetn                (rst_n),

        // FUB side (input from read engine)
        .fub_axi_arid           (fub_rd_axi_arid),
        .fub_axi_araddr         (fub_rd_axi_araddr),
        .fub_axi_arlen          (fub_rd_axi_arlen),
        .fub_axi_arsize         (fub_rd_axi_arsize),
        .fub_axi_arburst        (fub_rd_axi_arburst),
        .fub_axi_arlock         (fub_rd_axi_arlock),
        .fub_axi_arcache        (fub_rd_axi_arcache),
        .fub_axi_arprot         (fub_rd_axi_arprot),
        .fub_axi_arqos          (fub_rd_axi_arqos),
        .fub_axi_arregion       (fub_rd_axi_arregion),
        .fub_axi_aruser         (fub_rd_axi_aruser),
        .fub_axi_arvalid        (fub_rd_axi_arvalid),
        .fub_axi_arready        (fub_rd_axi_arready),

        .fub_axi_rid            (fub_rd_axi_rid),
        .fub_axi_rdata          (fub_rd_axi_rdata),
        .fub_axi_rresp          (fub_rd_axi_rresp),
        .fub_axi_rlast          (fub_rd_axi_rlast),
        .fub_axi_ruser          (fub_rd_axi_ruser),
        .fub_axi_rvalid         (fub_rd_axi_rvalid),
        .fub_axi_rready         (fub_rd_axi_rready),

        // Master side (output to external AXI)
        .m_axi_arid             (m_axi_rd_arid),
        .m_axi_araddr           (m_axi_rd_araddr),
        .m_axi_arlen            (m_axi_rd_arlen),
        .m_axi_arsize           (m_axi_rd_arsize),
        .m_axi_arburst          (m_axi_rd_arburst),
        .m_axi_arlock           (m_axi_rd_arlock),
        .m_axi_arcache          (m_axi_rd_arcache),
        .m_axi_arprot           (m_axi_rd_arprot),
        .m_axi_arqos            (m_axi_rd_arqos),
        .m_axi_arregion         (m_axi_rd_arregion),
        .m_axi_aruser           (m_axi_rd_aruser),
        .m_axi_arvalid          (m_axi_rd_arvalid),
        .m_axi_arready          (m_axi_rd_arready),

        .m_axi_rid              (m_axi_rd_rid),
        .m_axi_rdata            (m_axi_rd_rdata),
        .m_axi_rresp            (m_axi_rd_rresp),
        .m_axi_rlast            (m_axi_rd_rlast),
        .m_axi_ruser            (m_axi_rd_ruser),
        .m_axi_rvalid           (m_axi_rd_rvalid),
        .m_axi_rready           (m_axi_rd_rready),

        // Status
        .busy                   (cfg_sts_rdeng_skid_busy)
    );

    // Data write AXI skid buffer
    // Tie off unused AXI signals
    assign fub_wr_axi_awlock = 1'b0;
    assign fub_wr_axi_awcache = 4'h0;
    assign fub_wr_axi_awprot = 3'h0;
    assign fub_wr_axi_awqos = 4'h0;
    assign fub_wr_axi_awregion = 4'h0;
    // AXI USER fields carry channel ID for packet analysis/sorting.
    // AWUSER is request-side (legitimate driver). BUSER is response-side and
    // is driven by axi4_master_wr's fub_axi_buser output — so we must NOT
    // drive it here. See the equivalent comment on the read side above.
    assign fub_wr_axi_awuser = UW'(fub_wr_axi_awid);  // Extract channel ID from transaction ID
    // NOTE: fub_wr_axi_wuser already carries channel ID from write engine (passes through)

    axi4_master_wr #(
        .SKID_DEPTH_AW          (SKID_DEPTH_AW),
        .SKID_DEPTH_W           (SKID_DEPTH_W),
        .SKID_DEPTH_B           (SKID_DEPTH_B),
        .AXI_ID_WIDTH           (IW),
        .AXI_ADDR_WIDTH         (AW),
        .AXI_DATA_WIDTH         (DW),
        .AXI_USER_WIDTH         (UW)
    ) u_wr_axi_skid (
        .aclk                   (clk),
        .aresetn                (rst_n),

        // FUB side (input from write engine)
        .fub_axi_awid           (fub_wr_axi_awid),
        .fub_axi_awaddr         (fub_wr_axi_awaddr),
        .fub_axi_awlen          (fub_wr_axi_awlen),
        .fub_axi_awsize         (fub_wr_axi_awsize),
        .fub_axi_awburst        (fub_wr_axi_awburst),
        .fub_axi_awlock         (fub_wr_axi_awlock),
        .fub_axi_awcache        (fub_wr_axi_awcache),
        .fub_axi_awprot         (fub_wr_axi_awprot),
        .fub_axi_awqos          (fub_wr_axi_awqos),
        .fub_axi_awregion       (fub_wr_axi_awregion),
        .fub_axi_awuser         (fub_wr_axi_awuser),
        .fub_axi_awvalid        (fub_wr_axi_awvalid),
        .fub_axi_awready        (fub_wr_axi_awready),

        .fub_axi_wdata          (fub_wr_axi_wdata),
        .fub_axi_wstrb          (fub_wr_axi_wstrb),
        .fub_axi_wlast          (fub_wr_axi_wlast),
        .fub_axi_wuser          (fub_wr_axi_wuser),
        .fub_axi_wvalid         (fub_wr_axi_wvalid),
        .fub_axi_wready         (fub_wr_axi_wready),

        .fub_axi_bid            (fub_wr_axi_bid),
        .fub_axi_bresp          (fub_wr_axi_bresp),
        .fub_axi_buser          (fub_wr_axi_buser),
        .fub_axi_bvalid         (fub_wr_axi_bvalid),
        .fub_axi_bready         (fub_wr_axi_bready),

        // Master side (output to external AXI)
        .m_axi_awid             (m_axi_wr_awid),
        .m_axi_awaddr           (m_axi_wr_awaddr),
        .m_axi_awlen            (m_axi_wr_awlen),
        .m_axi_awsize           (m_axi_wr_awsize),
        .m_axi_awburst          (m_axi_wr_awburst),
        .m_axi_awlock           (m_axi_wr_awlock),
        .m_axi_awcache          (m_axi_wr_awcache),
        .m_axi_awprot           (m_axi_wr_awprot),
        .m_axi_awqos            (m_axi_wr_awqos),
        .m_axi_awregion         (m_axi_wr_awregion),
        .m_axi_awuser           (m_axi_wr_awuser),
        .m_axi_awvalid          (m_axi_wr_awvalid),
        .m_axi_awready          (m_axi_wr_awready),

        .m_axi_wdata            (m_axi_wr_wdata),
        .m_axi_wstrb            (m_axi_wr_wstrb),
        .m_axi_wlast            (m_axi_wr_wlast),
        .m_axi_wuser            (m_axi_wr_wuser),
        .m_axi_wvalid           (m_axi_wr_wvalid),
        .m_axi_wready           (m_axi_wr_wready),

        .m_axi_bid              (m_axi_wr_bid),
        .m_axi_bresp            (m_axi_wr_bresp),
        .m_axi_buser            (m_axi_wr_buser),
        .m_axi_bvalid           (m_axi_wr_bvalid),
        .m_axi_bready           (m_axi_wr_bready),

        // Status
        .busy                   (cfg_sts_wreng_skid_busy)
    );

    //=========================================================================
    // System-Level Status Logic
    //=========================================================================
    // System is idle when ALL schedulers are idle (AND reduction)
    assign system_idle = &scheduler_idle;

    //=========================================================================
    // Channel-Observation Mux
    //=========================================================================
    // obs_flags layout (always live for the selected channel):
    //   [6:0]  scheduler_state (one-hot)
    //   [7]    sched_rd_valid
    //   [8]    sched_wr_valid
    //   [9]    sched_wr_ready
    //   [10]   sched_rd_error                (live engine error → scheduler)
    //   [11]   sched_wr_error                (live engine error → scheduler)
    //   [12]   sched_error                   (state==CH_ERROR)
    //   [13]   descriptor_engine_idle
    //   [14]   scheduler_idle
    //   [15]   cfg_channel_enable
    //   [16]   axi_rd_all_complete
    //   [17]   axi_wr_all_complete
    //   [18]   dbg_descriptor_error          (sticky)
    //   [19]   dbg_read_error_sticky         (sticky)
    //   [20]   dbg_write_error_sticky        (sticky)
    //   [21]   dbg_timeout_expired           (live)
    //   [31:22] reserved (0)
    // Assumes NC <= 8; software just shouldn't probe channels >= NC.
    logic [2:0] w_obs_ch;
    assign w_obs_ch = cfg_obs_ch_sel;

    always_comb begin
        obs_flags = '0;
        obs_flags[6:0]   = scheduler_state[w_obs_ch];
        obs_flags[7]     = sched_rd_valid[w_obs_ch];
        obs_flags[8]     = sched_wr_valid[w_obs_ch];
        obs_flags[9]     = sched_wr_ready[w_obs_ch];
        obs_flags[10]    = sched_rd_error[w_obs_ch];
        obs_flags[11]    = sched_wr_error[w_obs_ch];
        obs_flags[12]    = sched_error[w_obs_ch];
        obs_flags[13]    = descriptor_engine_idle[w_obs_ch];
        obs_flags[14]    = scheduler_idle[w_obs_ch];
        obs_flags[15]    = cfg_channel_enable[w_obs_ch];
        obs_flags[16]    = axi_rd_all_complete[w_obs_ch];
        obs_flags[17]    = axi_wr_all_complete[w_obs_ch];
        obs_flags[18]    = dbg_sched_desc_error[w_obs_ch];
        obs_flags[19]    = dbg_sched_rd_sticky[w_obs_ch];
        obs_flags[20]    = dbg_sched_wr_sticky[w_obs_ch];
        obs_flags[21]    = dbg_sched_timeout[w_obs_ch];
    end

    always_comb begin
        obs_data0 = '0;
        obs_data1 = '0;
        case (cfg_obs_cat_sel)
            2'd0: begin  // status: beats remaining on rd / wr
                obs_data0 = sched_rd_beats[w_obs_ch];
                obs_data1 = sched_wr_beats[w_obs_ch];
            end
            2'd1: begin  // rd_addr: current 64-bit source address
                obs_data0 = sched_rd_addr[w_obs_ch][31:0];
                obs_data1 = (AW > 32) ? sched_rd_addr[w_obs_ch][AW-1:32] : 32'h0;
            end
            2'd2: begin  // wr_addr: current 64-bit destination address
                obs_data0 = sched_wr_addr[w_obs_ch][31:0];
                obs_data1 = (AW > 32) ? sched_wr_addr[w_obs_ch][AW-1:32] : 32'h0;
            end
            2'd3: begin  // sram: per-channel free / available beats
                obs_data0 = {{(32-($clog2(FIFO_DEPTH)+1)){1'b0}}, axi_rd_space_free[w_obs_ch]};
                obs_data1 = {{(32-($clog2(FIFO_DEPTH)+1)){1'b0}}, axi_wr_drain_data_avail[w_obs_ch]};
            end
        endcase
    end

endmodule : stream_core
