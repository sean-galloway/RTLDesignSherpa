// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_core_beats
// Purpose: RAPIDS Beats Core - Thin Wrapper over Independent Source/Sink Halves
//
// Description:
//   Thin structural wrapper that instantiates two WHOLLY INDEPENDENT half cores:
//   - rapids_src_beats (u_src): SOURCE, memory -> AXIS, read-only.
//   - rapids_snk_beats (u_snk): SINK,   AXIS -> memory, write-only.
//
//   The two halves share NO logic, no signals, and no monitor bus. Each half
//   contains its own scheduler_group_array_beats instance and its own data path.
//   This wrapper exists only to present a single boundary; every core port is
//   wired straight through to exactly one half instance. There is no logic here
//   beyond the two instantiations and their wiring.
//
//   Port-naming convention:
//   - Shared-infrastructure ports that BOTH halves have (APB, all cfg_*, all
//     status outputs, descriptor / control-read / control-write masters, and
//     the monitor bus) are exposed TWICE with src_ / snk_ prefixes. The two
//     monitor streams are kept separate (a later stage routes each to its own
//     monitor register block).
//   - Direction-unique ports (only one half has them) are exposed WITHOUT a
//     prefix, keeping the half's own port name: source-only m_axi_rd_*,
//     m_axis_*, cfg_axi_rd_xfer_beats, cfg_drain_size; sink-only m_axi_wr_*,
//     s_axis_*, cfg_axi_wr_xfer_beats, cfg_alloc_size.
//   - Debug outputs are exposed per half with src_dbg_ / snk_dbg_ prefixes.
//
//   The clk and rst_n are the single shared clock/reset for the whole wrapper
//   and are fanned out to both halves.
//
// Data Flows:
//   SINK PATH   (u_snk): AXIS Slave  -> SRAM Controller -> AXI Write Engine -> Memory
//   SOURCE PATH (u_src): Memory -> AXI Read Engine -> SRAM Controller -> AXIS Master
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

    // AXIS network-interface parameters (tid carries the channel id)
    parameter int AXIS_ID_WIDTH   = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,

    // Monitor Bus Base IDs
    parameter int DESC_MON_BASE_AGENT_ID = 16,   // 0x10 - Descriptor Engines (16-23)
    parameter int SCHED_MON_BASE_AGENT_ID = 48,  // 0x30 - Schedulers (48-55)
    parameter int DESC_AXI_MON_AGENT_ID = 8,     // 0x08 - Descriptor AXI Master Monitor
    parameter int MON_UNIT_ID = 1,               // 0x1
    parameter int MON_MAX_TRANSACTIONS = 16,
    // Monitor synthesis gates (default 1 = production unchanged); see
    // scheduler_group_array_beats. Threaded to both halves.
    parameter int USE_AXI_MONITORS = 1,
    parameter bit GEN_MON          = 1'b1,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SW  = DW / 8
) (
    // Clock and Reset (shared - single clock/reset for the whole wrapper)
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // SOURCE HALF (u_src) - shared-infrastructure ports (src_ prefixed)
    //=========================================================================
    // APB Programming Interface
    input  logic [NC-1:0]                       src_apb_valid,
    output logic [NC-1:0]                       src_apb_ready,
    input  logic [NC-1:0][AW-1:0]               src_apb_addr,

    // Per-channel configuration
    input  logic [NC-1:0]                       src_cfg_channel_enable,
    input  logic [NC-1:0]                       src_cfg_channel_reset,

    // Scheduler Configuration (global)
    input  logic                                src_cfg_sched_enable,
    input  logic [31:0]                         src_cfg_sched_timeout_cycles,
    input  logic [7:0]                          src_cfg_sched_timeout_limit,
    input  logic                                src_cfg_sched_timeout_enable,
    input  logic                                src_cfg_sched_err_enable,
    input  logic                                src_cfg_sched_compl_enable,
    input  logic                                src_cfg_sched_perf_enable,

    // Descriptor Engine Configuration (global)
    input  logic                                src_cfg_desceng_enable,
    input  logic                                src_cfg_desceng_prefetch,
    input  logic [3:0]                          src_cfg_desceng_fifo_thresh,
    input  logic [AW-1:0]                       src_cfg_desceng_addr0_base,
    input  logic [AW-1:0]                       src_cfg_desceng_addr0_limit,
    input  logic [AW-1:0]                       src_cfg_desceng_addr1_base,
    input  logic [AW-1:0]                       src_cfg_desceng_addr1_limit,

    // Control Engine Configuration (Phase 2, global)
    input  logic [8:0]                          src_cfg_ctrlrd_max_try,
    input  logic                                src_tick_1us,

    // Descriptor AXI Monitor Configuration
    input  logic                                src_cfg_desc_mon_enable,
    input  logic                                src_cfg_desc_mon_err_enable,
    input  logic                                src_cfg_desc_mon_perf_enable,
    input  logic                                src_cfg_desc_mon_timeout_enable,
    input  logic [31:0]                         src_cfg_desc_mon_timeout_cycles,
    input  logic [31:0]                         src_cfg_desc_mon_latency_thresh,
    input  logic [15:0]                         src_cfg_desc_mon_pkt_mask,
    input  logic [3:0]                          src_cfg_desc_mon_err_select,
    input  logic [7:0]                          src_cfg_desc_mon_err_mask,
    input  logic [7:0]                          src_cfg_desc_mon_timeout_mask,
    input  logic [7:0]                          src_cfg_desc_mon_compl_mask,
    input  logic [7:0]                          src_cfg_desc_mon_thresh_mask,
    input  logic [7:0]                          src_cfg_desc_mon_perf_mask,
    input  logic [7:0]                          src_cfg_desc_mon_addr_mask,
    input  logic [7:0]                          src_cfg_desc_mon_debug_mask,

    // Status
    output logic                                src_system_idle,
    output logic [NC-1:0]                       src_descriptor_engine_idle,
    output logic [NC-1:0]                       src_scheduler_idle,
    output logic [NC-1:0][6:0]                  src_scheduler_state,
    output logic [NC-1:0]                       src_sched_error,

    // Descriptor AXI Monitor Status
    output logic                                src_cfg_sts_desc_mon_busy,
    output logic [7:0]                          src_cfg_sts_desc_mon_active_txns,
    output logic [15:0]                         src_cfg_sts_desc_mon_error_count,
    output logic [31:0]                         src_cfg_sts_desc_mon_txn_count,
    output logic                                src_cfg_sts_desc_mon_conflict_error,

    // Descriptor Fetch AXI Master
    output logic                        src_m_axi_desc_arvalid,
    input  logic                        src_m_axi_desc_arready,
    output logic [AW-1:0]               src_m_axi_desc_araddr,
    output logic [7:0]                  src_m_axi_desc_arlen,
    output logic [2:0]                  src_m_axi_desc_arsize,
    output logic [1:0]                  src_m_axi_desc_arburst,
    output logic [IW-1:0]               src_m_axi_desc_arid,
    output logic                        src_m_axi_desc_arlock,
    output logic [3:0]                  src_m_axi_desc_arcache,
    output logic [2:0]                  src_m_axi_desc_arprot,
    output logic [3:0]                  src_m_axi_desc_arqos,
    output logic [3:0]                  src_m_axi_desc_arregion,
    input  logic                        src_m_axi_desc_rvalid,
    output logic                        src_m_axi_desc_rready,
    input  logic [255:0]                src_m_axi_desc_rdata,
    input  logic [1:0]                  src_m_axi_desc_rresp,
    input  logic                        src_m_axi_desc_rlast,
    input  logic [IW-1:0]               src_m_axi_desc_rid,

    // Control Read AXI Master (32-bit) [Phase 2]
    output logic                        src_m_axi_ctrlrd_arvalid,
    input  logic                        src_m_axi_ctrlrd_arready,
    output logic [AW-1:0]               src_m_axi_ctrlrd_araddr,
    output logic [7:0]                  src_m_axi_ctrlrd_arlen,
    output logic [2:0]                  src_m_axi_ctrlrd_arsize,
    output logic [1:0]                  src_m_axi_ctrlrd_arburst,
    output logic [IW-1:0]               src_m_axi_ctrlrd_arid,
    output logic                        src_m_axi_ctrlrd_arlock,
    output logic [3:0]                  src_m_axi_ctrlrd_arcache,
    output logic [2:0]                  src_m_axi_ctrlrd_arprot,
    output logic [3:0]                  src_m_axi_ctrlrd_arqos,
    output logic [3:0]                  src_m_axi_ctrlrd_arregion,
    input  logic                        src_m_axi_ctrlrd_rvalid,
    output logic                        src_m_axi_ctrlrd_rready,
    input  logic [31:0]                 src_m_axi_ctrlrd_rdata,
    input  logic [1:0]                  src_m_axi_ctrlrd_rresp,
    input  logic                        src_m_axi_ctrlrd_rlast,
    input  logic [IW-1:0]               src_m_axi_ctrlrd_rid,

    // Control Write AXI Master (32-bit) [Phase 2]
    output logic                        src_m_axi_ctrlwr_awvalid,
    input  logic                        src_m_axi_ctrlwr_awready,
    output logic [AW-1:0]               src_m_axi_ctrlwr_awaddr,
    output logic [7:0]                  src_m_axi_ctrlwr_awlen,
    output logic [2:0]                  src_m_axi_ctrlwr_awsize,
    output logic [1:0]                  src_m_axi_ctrlwr_awburst,
    output logic [IW-1:0]               src_m_axi_ctrlwr_awid,
    output logic                        src_m_axi_ctrlwr_awlock,
    output logic [3:0]                  src_m_axi_ctrlwr_awcache,
    output logic [2:0]                  src_m_axi_ctrlwr_awprot,
    output logic [3:0]                  src_m_axi_ctrlwr_awqos,
    output logic [3:0]                  src_m_axi_ctrlwr_awregion,
    output logic                        src_m_axi_ctrlwr_wvalid,
    input  logic                        src_m_axi_ctrlwr_wready,
    output logic [31:0]                 src_m_axi_ctrlwr_wdata,
    output logic [3:0]                  src_m_axi_ctrlwr_wstrb,
    output logic                        src_m_axi_ctrlwr_wlast,
    input  logic                        src_m_axi_ctrlwr_bvalid,
    output logic                        src_m_axi_ctrlwr_bready,
    input  logic [IW-1:0]               src_m_axi_ctrlwr_bid,
    input  logic [1:0]                  src_m_axi_ctrlwr_bresp,

    //=========================================================================
    // SOURCE HALF (u_src) - direction-unique ports (no prefix)
    //=========================================================================
    // AXI Transfer Configuration (source-only)
    input  logic [7:0]                          cfg_axi_rd_xfer_beats,
    input  logic [7:0]                          cfg_drain_size,   // source: beats drained per AXIS packet

    // Source Path - AXIS Master Interface (SRAM -> Network); tid = channel id
    output logic [DW-1:0]               m_axis_tdata,
    output logic [SW-1:0]               m_axis_tstrb,
    output logic                        m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]    m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]  m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]  m_axis_tuser,
    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,

    // AXI4 Master - Data Read (Memory -> Source SRAM)
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
    // SINK HALF (u_snk) - shared-infrastructure ports (snk_ prefixed)
    //=========================================================================
    // APB Programming Interface
    input  logic [NC-1:0]                       snk_apb_valid,
    output logic [NC-1:0]                       snk_apb_ready,
    input  logic [NC-1:0][AW-1:0]               snk_apb_addr,

    // Per-channel configuration
    input  logic [NC-1:0]                       snk_cfg_channel_enable,
    input  logic [NC-1:0]                       snk_cfg_channel_reset,

    // Scheduler Configuration (global)
    input  logic                                snk_cfg_sched_enable,
    input  logic [31:0]                         snk_cfg_sched_timeout_cycles,
    input  logic [7:0]                          snk_cfg_sched_timeout_limit,
    input  logic                                snk_cfg_sched_timeout_enable,
    input  logic                                snk_cfg_sched_err_enable,
    input  logic                                snk_cfg_sched_compl_enable,
    input  logic                                snk_cfg_sched_perf_enable,

    // Descriptor Engine Configuration (global)
    input  logic                                snk_cfg_desceng_enable,
    input  logic                                snk_cfg_desceng_prefetch,
    input  logic [3:0]                          snk_cfg_desceng_fifo_thresh,
    input  logic [AW-1:0]                       snk_cfg_desceng_addr0_base,
    input  logic [AW-1:0]                       snk_cfg_desceng_addr0_limit,
    input  logic [AW-1:0]                       snk_cfg_desceng_addr1_base,
    input  logic [AW-1:0]                       snk_cfg_desceng_addr1_limit,

    // Control Engine Configuration (Phase 2, global)
    input  logic [8:0]                          snk_cfg_ctrlrd_max_try,
    input  logic                                snk_tick_1us,

    // Descriptor AXI Monitor Configuration
    input  logic                                snk_cfg_desc_mon_enable,
    input  logic                                snk_cfg_desc_mon_err_enable,
    input  logic                                snk_cfg_desc_mon_perf_enable,
    input  logic                                snk_cfg_desc_mon_timeout_enable,
    input  logic [31:0]                         snk_cfg_desc_mon_timeout_cycles,
    input  logic [31:0]                         snk_cfg_desc_mon_latency_thresh,
    input  logic [15:0]                         snk_cfg_desc_mon_pkt_mask,
    input  logic [3:0]                          snk_cfg_desc_mon_err_select,
    input  logic [7:0]                          snk_cfg_desc_mon_err_mask,
    input  logic [7:0]                          snk_cfg_desc_mon_timeout_mask,
    input  logic [7:0]                          snk_cfg_desc_mon_compl_mask,
    input  logic [7:0]                          snk_cfg_desc_mon_thresh_mask,
    input  logic [7:0]                          snk_cfg_desc_mon_perf_mask,
    input  logic [7:0]                          snk_cfg_desc_mon_addr_mask,
    input  logic [7:0]                          snk_cfg_desc_mon_debug_mask,

    // Status
    output logic                                snk_system_idle,
    output logic [NC-1:0]                       snk_descriptor_engine_idle,
    output logic [NC-1:0]                       snk_scheduler_idle,
    output logic [NC-1:0][6:0]                  snk_scheduler_state,
    output logic [NC-1:0]                       snk_sched_error,

    // Descriptor AXI Monitor Status
    output logic                                snk_cfg_sts_desc_mon_busy,
    output logic [7:0]                          snk_cfg_sts_desc_mon_active_txns,
    output logic [15:0]                         snk_cfg_sts_desc_mon_error_count,
    output logic [31:0]                         snk_cfg_sts_desc_mon_txn_count,
    output logic                                snk_cfg_sts_desc_mon_conflict_error,

    // Descriptor Fetch AXI Master
    output logic                        snk_m_axi_desc_arvalid,
    input  logic                        snk_m_axi_desc_arready,
    output logic [AW-1:0]               snk_m_axi_desc_araddr,
    output logic [7:0]                  snk_m_axi_desc_arlen,
    output logic [2:0]                  snk_m_axi_desc_arsize,
    output logic [1:0]                  snk_m_axi_desc_arburst,
    output logic [IW-1:0]               snk_m_axi_desc_arid,
    output logic                        snk_m_axi_desc_arlock,
    output logic [3:0]                  snk_m_axi_desc_arcache,
    output logic [2:0]                  snk_m_axi_desc_arprot,
    output logic [3:0]                  snk_m_axi_desc_arqos,
    output logic [3:0]                  snk_m_axi_desc_arregion,
    input  logic                        snk_m_axi_desc_rvalid,
    output logic                        snk_m_axi_desc_rready,
    input  logic [255:0]                snk_m_axi_desc_rdata,
    input  logic [1:0]                  snk_m_axi_desc_rresp,
    input  logic                        snk_m_axi_desc_rlast,
    input  logic [IW-1:0]               snk_m_axi_desc_rid,

    // Control Read AXI Master (32-bit) [Phase 2]
    output logic                        snk_m_axi_ctrlrd_arvalid,
    input  logic                        snk_m_axi_ctrlrd_arready,
    output logic [AW-1:0]               snk_m_axi_ctrlrd_araddr,
    output logic [7:0]                  snk_m_axi_ctrlrd_arlen,
    output logic [2:0]                  snk_m_axi_ctrlrd_arsize,
    output logic [1:0]                  snk_m_axi_ctrlrd_arburst,
    output logic [IW-1:0]               snk_m_axi_ctrlrd_arid,
    output logic                        snk_m_axi_ctrlrd_arlock,
    output logic [3:0]                  snk_m_axi_ctrlrd_arcache,
    output logic [2:0]                  snk_m_axi_ctrlrd_arprot,
    output logic [3:0]                  snk_m_axi_ctrlrd_arqos,
    output logic [3:0]                  snk_m_axi_ctrlrd_arregion,
    input  logic                        snk_m_axi_ctrlrd_rvalid,
    output logic                        snk_m_axi_ctrlrd_rready,
    input  logic [31:0]                 snk_m_axi_ctrlrd_rdata,
    input  logic [1:0]                  snk_m_axi_ctrlrd_rresp,
    input  logic                        snk_m_axi_ctrlrd_rlast,
    input  logic [IW-1:0]               snk_m_axi_ctrlrd_rid,

    // Control Write AXI Master (32-bit) [Phase 2]
    output logic                        snk_m_axi_ctrlwr_awvalid,
    input  logic                        snk_m_axi_ctrlwr_awready,
    output logic [AW-1:0]               snk_m_axi_ctrlwr_awaddr,
    output logic [7:0]                  snk_m_axi_ctrlwr_awlen,
    output logic [2:0]                  snk_m_axi_ctrlwr_awsize,
    output logic [1:0]                  snk_m_axi_ctrlwr_awburst,
    output logic [IW-1:0]               snk_m_axi_ctrlwr_awid,
    output logic                        snk_m_axi_ctrlwr_awlock,
    output logic [3:0]                  snk_m_axi_ctrlwr_awcache,
    output logic [2:0]                  snk_m_axi_ctrlwr_awprot,
    output logic [3:0]                  snk_m_axi_ctrlwr_awqos,
    output logic [3:0]                  snk_m_axi_ctrlwr_awregion,
    output logic                        snk_m_axi_ctrlwr_wvalid,
    input  logic                        snk_m_axi_ctrlwr_wready,
    output logic [31:0]                 snk_m_axi_ctrlwr_wdata,
    output logic [3:0]                  snk_m_axi_ctrlwr_wstrb,
    output logic                        snk_m_axi_ctrlwr_wlast,
    input  logic                        snk_m_axi_ctrlwr_bvalid,
    output logic                        snk_m_axi_ctrlwr_bready,
    input  logic [IW-1:0]               snk_m_axi_ctrlwr_bid,
    input  logic [1:0]                  snk_m_axi_ctrlwr_bresp,

    //=========================================================================
    // Monitor Bus (SINGLE aggregated stream for the whole core)
    //   The two halves' monitor outputs are merged through a top-level
    //   monbus_arbiter, so the core exposes exactly one monitor stream.
    //=========================================================================
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output monitor_common_pkg::monitor_packet_t     mon_packet,
    output monitor_common_pkg::monbus_timestamp_t   mon_timestamp,

    //=========================================================================
    // SINK HALF (u_snk) - direction-unique ports (no prefix)
    //=========================================================================
    // AXI Transfer Configuration (sink-only)
    input  logic [7:0]                          cfg_axi_wr_xfer_beats,
    input  logic [7:0]                          cfg_alloc_size,   // sink: SRAM alloc size per AXIS fill

    // Sink Path - AXIS Slave Interface (Network -> SRAM); tid = channel id
    input  logic [DW-1:0]               s_axis_tdata,
    input  logic [SW-1:0]               s_axis_tstrb,
    input  logic                        s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]    s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]  s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]  s_axis_tuser,
    input  logic                        s_axis_tvalid,
    output logic                        s_axis_tready,

    // AXI4 Master - Data Write (Sink SRAM -> Memory)
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
    // Debug Interface (per half, src_dbg_ / snk_dbg_ prefixed)
    //=========================================================================
    // Source half debug
    output logic [NC-1:0]               src_dbg_rd_all_complete,
    output logic [31:0]                 src_dbg_r_beats_rcvd,
    output logic [31:0]                 src_dbg_sram_writes,
    output logic [NC-1:0]               src_dbg_arb_request,
    output logic [NC-1:0]               src_dbg_src_sram_bridge_pending,
    output logic [NC-1:0]               src_dbg_src_sram_bridge_out_valid,
    output logic [31:0]                 src_dbg_axis_beats_sent,
    output logic [31:0]                 src_dbg_axis_packets_sent,

    // Sink half debug
    output logic [NC-1:0]               snk_dbg_snk_sram_bridge_pending,
    output logic [NC-1:0]               snk_dbg_snk_sram_bridge_out_valid,
    output logic [31:0]                 snk_dbg_axis_beats_received,
    output logic [31:0]                 snk_dbg_axis_packets_received
);

    //=========================================================================
    // Per-half Monitor Bus (each half already arbitrates its own sources)
    //=========================================================================
    logic                                    src_mon_valid;
    logic                                    src_mon_ready;
    monitor_common_pkg::monitor_packet_t     src_mon_packet;
    monitor_common_pkg::monbus_timestamp_t   src_mon_timestamp;

    logic                                    snk_mon_valid;
    logic                                    snk_mon_ready;
    monitor_common_pkg::monitor_packet_t     snk_mon_packet;
    monitor_common_pkg::monbus_timestamp_t   snk_mon_timestamp;

    //=========================================================================
    // Source Half (memory -> AXIS, read-only)
    //=========================================================================
    rapids_src_beats #(
        .NUM_CHANNELS           (NUM_CHANNELS),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (ADDR_WIDTH),
        .DATA_WIDTH             (DATA_WIDTH),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .SRAM_DEPTH             (SRAM_DEPTH),
        .SEG_COUNT_WIDTH        (SEG_COUNT_WIDTH),
        .PIPELINE               (PIPELINE),
        .AR_MAX_OUTSTANDING     (AR_MAX_OUTSTANDING),
        .AXIS_ID_WIDTH          (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH        (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH        (AXIS_USER_WIDTH),
        .DESC_MON_BASE_AGENT_ID (DESC_MON_BASE_AGENT_ID),
        .SCHED_MON_BASE_AGENT_ID(SCHED_MON_BASE_AGENT_ID),
        .DESC_AXI_MON_AGENT_ID  (DESC_AXI_MON_AGENT_ID),
        .MON_UNIT_ID            (MON_UNIT_ID),
        .MON_MAX_TRANSACTIONS   (MON_MAX_TRANSACTIONS),
        .USE_AXI_MONITORS       (USE_AXI_MONITORS),
        .GEN_MON                (GEN_MON)
    ) u_src (
        .clk                        (clk),
        .rst_n                      (rst_n),

        // APB
        .apb_valid                  (src_apb_valid),
        .apb_ready                  (src_apb_ready),
        .apb_addr                   (src_apb_addr),

        // Configuration
        .cfg_channel_enable         (src_cfg_channel_enable),
        .cfg_channel_reset          (src_cfg_channel_reset),
        .cfg_sched_enable           (src_cfg_sched_enable),
        .cfg_sched_timeout_cycles   (src_cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit    (src_cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable   (src_cfg_sched_timeout_enable),
        .cfg_sched_err_enable       (src_cfg_sched_err_enable),
        .cfg_sched_compl_enable     (src_cfg_sched_compl_enable),
        .cfg_sched_perf_enable      (src_cfg_sched_perf_enable),
        .cfg_desceng_enable         (src_cfg_desceng_enable),
        .cfg_desceng_prefetch       (src_cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh    (src_cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base     (src_cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit    (src_cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base     (src_cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit    (src_cfg_desceng_addr1_limit),
        .cfg_ctrlrd_max_try         (src_cfg_ctrlrd_max_try),
        .tick_1us                   (src_tick_1us),

        // Descriptor AXI Monitor Configuration
        .cfg_desc_mon_enable        (src_cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (src_cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (src_cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable(src_cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles(src_cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh(src_cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask      (src_cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select    (src_cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask      (src_cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask  (src_cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask    (src_cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask   (src_cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask     (src_cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask     (src_cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask    (src_cfg_desc_mon_debug_mask),

        // AXI Transfer Configuration (source-only)
        .cfg_axi_rd_xfer_beats      (cfg_axi_rd_xfer_beats),
        .cfg_drain_size             (cfg_drain_size),

        // Status
        .system_idle                (src_system_idle),
        .descriptor_engine_idle     (src_descriptor_engine_idle),
        .scheduler_idle             (src_scheduler_idle),
        .scheduler_state            (src_scheduler_state),
        .sched_error                (src_sched_error),
        .cfg_sts_desc_mon_busy          (src_cfg_sts_desc_mon_busy),
        .cfg_sts_desc_mon_active_txns   (src_cfg_sts_desc_mon_active_txns),
        .cfg_sts_desc_mon_error_count   (src_cfg_sts_desc_mon_error_count),
        .cfg_sts_desc_mon_txn_count     (src_cfg_sts_desc_mon_txn_count),
        .cfg_sts_desc_mon_conflict_error(src_cfg_sts_desc_mon_conflict_error),

        // AXIS Master (source egress)
        .m_axis_tdata               (m_axis_tdata),
        .m_axis_tstrb               (m_axis_tstrb),
        .m_axis_tlast               (m_axis_tlast),
        .m_axis_tid                 (m_axis_tid),
        .m_axis_tdest               (m_axis_tdest),
        .m_axis_tuser               (m_axis_tuser),
        .m_axis_tvalid              (m_axis_tvalid),
        .m_axis_tready              (m_axis_tready),

        // Descriptor Fetch AXI Master
        .m_axi_desc_arvalid         (src_m_axi_desc_arvalid),
        .m_axi_desc_arready         (src_m_axi_desc_arready),
        .m_axi_desc_araddr          (src_m_axi_desc_araddr),
        .m_axi_desc_arlen           (src_m_axi_desc_arlen),
        .m_axi_desc_arsize          (src_m_axi_desc_arsize),
        .m_axi_desc_arburst         (src_m_axi_desc_arburst),
        .m_axi_desc_arid            (src_m_axi_desc_arid),
        .m_axi_desc_arlock          (src_m_axi_desc_arlock),
        .m_axi_desc_arcache         (src_m_axi_desc_arcache),
        .m_axi_desc_arprot          (src_m_axi_desc_arprot),
        .m_axi_desc_arqos           (src_m_axi_desc_arqos),
        .m_axi_desc_arregion        (src_m_axi_desc_arregion),
        .m_axi_desc_rvalid          (src_m_axi_desc_rvalid),
        .m_axi_desc_rready          (src_m_axi_desc_rready),
        .m_axi_desc_rdata           (src_m_axi_desc_rdata),
        .m_axi_desc_rresp           (src_m_axi_desc_rresp),
        .m_axi_desc_rlast           (src_m_axi_desc_rlast),
        .m_axi_desc_rid             (src_m_axi_desc_rid),

        // Control Read AXI Master
        .m_axi_ctrlrd_arvalid       (src_m_axi_ctrlrd_arvalid),
        .m_axi_ctrlrd_arready       (src_m_axi_ctrlrd_arready),
        .m_axi_ctrlrd_araddr        (src_m_axi_ctrlrd_araddr),
        .m_axi_ctrlrd_arlen         (src_m_axi_ctrlrd_arlen),
        .m_axi_ctrlrd_arsize        (src_m_axi_ctrlrd_arsize),
        .m_axi_ctrlrd_arburst       (src_m_axi_ctrlrd_arburst),
        .m_axi_ctrlrd_arid          (src_m_axi_ctrlrd_arid),
        .m_axi_ctrlrd_arlock        (src_m_axi_ctrlrd_arlock),
        .m_axi_ctrlrd_arcache       (src_m_axi_ctrlrd_arcache),
        .m_axi_ctrlrd_arprot        (src_m_axi_ctrlrd_arprot),
        .m_axi_ctrlrd_arqos         (src_m_axi_ctrlrd_arqos),
        .m_axi_ctrlrd_arregion      (src_m_axi_ctrlrd_arregion),
        .m_axi_ctrlrd_rvalid        (src_m_axi_ctrlrd_rvalid),
        .m_axi_ctrlrd_rready        (src_m_axi_ctrlrd_rready),
        .m_axi_ctrlrd_rdata         (src_m_axi_ctrlrd_rdata),
        .m_axi_ctrlrd_rresp         (src_m_axi_ctrlrd_rresp),
        .m_axi_ctrlrd_rlast         (src_m_axi_ctrlrd_rlast),
        .m_axi_ctrlrd_rid           (src_m_axi_ctrlrd_rid),

        // Control Write AXI Master
        .m_axi_ctrlwr_awvalid       (src_m_axi_ctrlwr_awvalid),
        .m_axi_ctrlwr_awready       (src_m_axi_ctrlwr_awready),
        .m_axi_ctrlwr_awaddr        (src_m_axi_ctrlwr_awaddr),
        .m_axi_ctrlwr_awlen         (src_m_axi_ctrlwr_awlen),
        .m_axi_ctrlwr_awsize        (src_m_axi_ctrlwr_awsize),
        .m_axi_ctrlwr_awburst       (src_m_axi_ctrlwr_awburst),
        .m_axi_ctrlwr_awid          (src_m_axi_ctrlwr_awid),
        .m_axi_ctrlwr_awlock        (src_m_axi_ctrlwr_awlock),
        .m_axi_ctrlwr_awcache       (src_m_axi_ctrlwr_awcache),
        .m_axi_ctrlwr_awprot        (src_m_axi_ctrlwr_awprot),
        .m_axi_ctrlwr_awqos         (src_m_axi_ctrlwr_awqos),
        .m_axi_ctrlwr_awregion      (src_m_axi_ctrlwr_awregion),
        .m_axi_ctrlwr_wvalid        (src_m_axi_ctrlwr_wvalid),
        .m_axi_ctrlwr_wready        (src_m_axi_ctrlwr_wready),
        .m_axi_ctrlwr_wdata         (src_m_axi_ctrlwr_wdata),
        .m_axi_ctrlwr_wstrb         (src_m_axi_ctrlwr_wstrb),
        .m_axi_ctrlwr_wlast         (src_m_axi_ctrlwr_wlast),
        .m_axi_ctrlwr_bvalid        (src_m_axi_ctrlwr_bvalid),
        .m_axi_ctrlwr_bready        (src_m_axi_ctrlwr_bready),
        .m_axi_ctrlwr_bid           (src_m_axi_ctrlwr_bid),
        .m_axi_ctrlwr_bresp         (src_m_axi_ctrlwr_bresp),

        // Data Read AXI Master (memory -> source SRAM)
        .m_axi_rd_arid              (m_axi_rd_arid),
        .m_axi_rd_araddr            (m_axi_rd_araddr),
        .m_axi_rd_arlen             (m_axi_rd_arlen),
        .m_axi_rd_arsize            (m_axi_rd_arsize),
        .m_axi_rd_arburst           (m_axi_rd_arburst),
        .m_axi_rd_arvalid           (m_axi_rd_arvalid),
        .m_axi_rd_arready           (m_axi_rd_arready),
        .m_axi_rd_rid               (m_axi_rd_rid),
        .m_axi_rd_rdata             (m_axi_rd_rdata),
        .m_axi_rd_rresp             (m_axi_rd_rresp),
        .m_axi_rd_rlast             (m_axi_rd_rlast),
        .m_axi_rd_rvalid            (m_axi_rd_rvalid),
        .m_axi_rd_rready            (m_axi_rd_rready),

        // Monitor Bus (source half - full monitor bus into top arbiter)
        .mon_valid                  (src_mon_valid),
        .mon_ready                  (src_mon_ready),
        .mon_packet                 (src_mon_packet),
        .mon_timestamp              (src_mon_timestamp),

        // Debug (source)
        .dbg_rd_all_complete           (src_dbg_rd_all_complete),
        .dbg_r_beats_rcvd              (src_dbg_r_beats_rcvd),
        .dbg_sram_writes               (src_dbg_sram_writes),
        .dbg_arb_request               (src_dbg_arb_request),
        .dbg_src_sram_bridge_pending   (src_dbg_src_sram_bridge_pending),
        .dbg_src_sram_bridge_out_valid (src_dbg_src_sram_bridge_out_valid),
        .dbg_axis_beats_sent           (src_dbg_axis_beats_sent),
        .dbg_axis_packets_sent         (src_dbg_axis_packets_sent)
    );

    //=========================================================================
    // Sink Half (AXIS -> memory, write-only)
    //=========================================================================
    rapids_snk_beats #(
        .NUM_CHANNELS           (NUM_CHANNELS),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (ADDR_WIDTH),
        .DATA_WIDTH             (DATA_WIDTH),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .SRAM_DEPTH             (SRAM_DEPTH),
        .SEG_COUNT_WIDTH        (SEG_COUNT_WIDTH),
        .PIPELINE               (PIPELINE),
        .AW_MAX_OUTSTANDING     (AW_MAX_OUTSTANDING),
        .W_PHASE_FIFO_DEPTH     (W_PHASE_FIFO_DEPTH),
        .B_PHASE_FIFO_DEPTH     (B_PHASE_FIFO_DEPTH),
        .AXIS_ID_WIDTH          (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH        (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH        (AXIS_USER_WIDTH),
        .DESC_MON_BASE_AGENT_ID (DESC_MON_BASE_AGENT_ID),
        .SCHED_MON_BASE_AGENT_ID(SCHED_MON_BASE_AGENT_ID),
        .DESC_AXI_MON_AGENT_ID  (DESC_AXI_MON_AGENT_ID),
        .MON_UNIT_ID            (MON_UNIT_ID),
        .MON_MAX_TRANSACTIONS   (MON_MAX_TRANSACTIONS),
        .USE_AXI_MONITORS       (USE_AXI_MONITORS),
        .GEN_MON                (GEN_MON)
    ) u_snk (
        .clk                        (clk),
        .rst_n                      (rst_n),

        // APB
        .apb_valid                  (snk_apb_valid),
        .apb_ready                  (snk_apb_ready),
        .apb_addr                   (snk_apb_addr),

        // Configuration
        .cfg_channel_enable         (snk_cfg_channel_enable),
        .cfg_channel_reset          (snk_cfg_channel_reset),
        .cfg_sched_enable           (snk_cfg_sched_enable),
        .cfg_sched_timeout_cycles   (snk_cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit    (snk_cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable   (snk_cfg_sched_timeout_enable),
        .cfg_sched_err_enable       (snk_cfg_sched_err_enable),
        .cfg_sched_compl_enable     (snk_cfg_sched_compl_enable),
        .cfg_sched_perf_enable      (snk_cfg_sched_perf_enable),
        .cfg_desceng_enable         (snk_cfg_desceng_enable),
        .cfg_desceng_prefetch       (snk_cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh    (snk_cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base     (snk_cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit    (snk_cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base     (snk_cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit    (snk_cfg_desceng_addr1_limit),
        .cfg_ctrlrd_max_try         (snk_cfg_ctrlrd_max_try),
        .tick_1us                   (snk_tick_1us),

        // Descriptor AXI Monitor Configuration
        .cfg_desc_mon_enable        (snk_cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (snk_cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (snk_cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable(snk_cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles(snk_cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh(snk_cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask      (snk_cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select    (snk_cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask      (snk_cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask  (snk_cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask    (snk_cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask   (snk_cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask     (snk_cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask     (snk_cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask    (snk_cfg_desc_mon_debug_mask),

        // AXI Transfer Configuration (sink-only)
        .cfg_axi_wr_xfer_beats      (cfg_axi_wr_xfer_beats),
        .cfg_alloc_size             (cfg_alloc_size),

        // Status
        .system_idle                (snk_system_idle),
        .descriptor_engine_idle     (snk_descriptor_engine_idle),
        .scheduler_idle             (snk_scheduler_idle),
        .scheduler_state            (snk_scheduler_state),
        .sched_error                (snk_sched_error),
        .cfg_sts_desc_mon_busy          (snk_cfg_sts_desc_mon_busy),
        .cfg_sts_desc_mon_active_txns   (snk_cfg_sts_desc_mon_active_txns),
        .cfg_sts_desc_mon_error_count   (snk_cfg_sts_desc_mon_error_count),
        .cfg_sts_desc_mon_txn_count     (snk_cfg_sts_desc_mon_txn_count),
        .cfg_sts_desc_mon_conflict_error(snk_cfg_sts_desc_mon_conflict_error),

        // AXIS Slave (sink ingress)
        .s_axis_tdata               (s_axis_tdata),
        .s_axis_tstrb               (s_axis_tstrb),
        .s_axis_tlast               (s_axis_tlast),
        .s_axis_tid                 (s_axis_tid),
        .s_axis_tdest               (s_axis_tdest),
        .s_axis_tuser               (s_axis_tuser),
        .s_axis_tvalid              (s_axis_tvalid),
        .s_axis_tready              (s_axis_tready),

        // Descriptor Fetch AXI Master
        .m_axi_desc_arvalid         (snk_m_axi_desc_arvalid),
        .m_axi_desc_arready         (snk_m_axi_desc_arready),
        .m_axi_desc_araddr          (snk_m_axi_desc_araddr),
        .m_axi_desc_arlen           (snk_m_axi_desc_arlen),
        .m_axi_desc_arsize          (snk_m_axi_desc_arsize),
        .m_axi_desc_arburst         (snk_m_axi_desc_arburst),
        .m_axi_desc_arid            (snk_m_axi_desc_arid),
        .m_axi_desc_arlock          (snk_m_axi_desc_arlock),
        .m_axi_desc_arcache         (snk_m_axi_desc_arcache),
        .m_axi_desc_arprot          (snk_m_axi_desc_arprot),
        .m_axi_desc_arqos           (snk_m_axi_desc_arqos),
        .m_axi_desc_arregion        (snk_m_axi_desc_arregion),
        .m_axi_desc_rvalid          (snk_m_axi_desc_rvalid),
        .m_axi_desc_rready          (snk_m_axi_desc_rready),
        .m_axi_desc_rdata           (snk_m_axi_desc_rdata),
        .m_axi_desc_rresp           (snk_m_axi_desc_rresp),
        .m_axi_desc_rlast           (snk_m_axi_desc_rlast),
        .m_axi_desc_rid             (snk_m_axi_desc_rid),

        // Control Read AXI Master
        .m_axi_ctrlrd_arvalid       (snk_m_axi_ctrlrd_arvalid),
        .m_axi_ctrlrd_arready       (snk_m_axi_ctrlrd_arready),
        .m_axi_ctrlrd_araddr        (snk_m_axi_ctrlrd_araddr),
        .m_axi_ctrlrd_arlen         (snk_m_axi_ctrlrd_arlen),
        .m_axi_ctrlrd_arsize        (snk_m_axi_ctrlrd_arsize),
        .m_axi_ctrlrd_arburst       (snk_m_axi_ctrlrd_arburst),
        .m_axi_ctrlrd_arid          (snk_m_axi_ctrlrd_arid),
        .m_axi_ctrlrd_arlock        (snk_m_axi_ctrlrd_arlock),
        .m_axi_ctrlrd_arcache       (snk_m_axi_ctrlrd_arcache),
        .m_axi_ctrlrd_arprot        (snk_m_axi_ctrlrd_arprot),
        .m_axi_ctrlrd_arqos         (snk_m_axi_ctrlrd_arqos),
        .m_axi_ctrlrd_arregion      (snk_m_axi_ctrlrd_arregion),
        .m_axi_ctrlrd_rvalid        (snk_m_axi_ctrlrd_rvalid),
        .m_axi_ctrlrd_rready        (snk_m_axi_ctrlrd_rready),
        .m_axi_ctrlrd_rdata         (snk_m_axi_ctrlrd_rdata),
        .m_axi_ctrlrd_rresp         (snk_m_axi_ctrlrd_rresp),
        .m_axi_ctrlrd_rlast         (snk_m_axi_ctrlrd_rlast),
        .m_axi_ctrlrd_rid           (snk_m_axi_ctrlrd_rid),

        // Control Write AXI Master
        .m_axi_ctrlwr_awvalid       (snk_m_axi_ctrlwr_awvalid),
        .m_axi_ctrlwr_awready       (snk_m_axi_ctrlwr_awready),
        .m_axi_ctrlwr_awaddr        (snk_m_axi_ctrlwr_awaddr),
        .m_axi_ctrlwr_awlen         (snk_m_axi_ctrlwr_awlen),
        .m_axi_ctrlwr_awsize        (snk_m_axi_ctrlwr_awsize),
        .m_axi_ctrlwr_awburst       (snk_m_axi_ctrlwr_awburst),
        .m_axi_ctrlwr_awid          (snk_m_axi_ctrlwr_awid),
        .m_axi_ctrlwr_awlock        (snk_m_axi_ctrlwr_awlock),
        .m_axi_ctrlwr_awcache       (snk_m_axi_ctrlwr_awcache),
        .m_axi_ctrlwr_awprot        (snk_m_axi_ctrlwr_awprot),
        .m_axi_ctrlwr_awqos         (snk_m_axi_ctrlwr_awqos),
        .m_axi_ctrlwr_awregion      (snk_m_axi_ctrlwr_awregion),
        .m_axi_ctrlwr_wvalid        (snk_m_axi_ctrlwr_wvalid),
        .m_axi_ctrlwr_wready        (snk_m_axi_ctrlwr_wready),
        .m_axi_ctrlwr_wdata         (snk_m_axi_ctrlwr_wdata),
        .m_axi_ctrlwr_wstrb         (snk_m_axi_ctrlwr_wstrb),
        .m_axi_ctrlwr_wlast         (snk_m_axi_ctrlwr_wlast),
        .m_axi_ctrlwr_bvalid        (snk_m_axi_ctrlwr_bvalid),
        .m_axi_ctrlwr_bready        (snk_m_axi_ctrlwr_bready),
        .m_axi_ctrlwr_bid           (snk_m_axi_ctrlwr_bid),
        .m_axi_ctrlwr_bresp         (snk_m_axi_ctrlwr_bresp),

        // Data Write AXI Master (sink SRAM -> memory)
        .m_axi_wr_awid              (m_axi_wr_awid),
        .m_axi_wr_awaddr            (m_axi_wr_awaddr),
        .m_axi_wr_awlen             (m_axi_wr_awlen),
        .m_axi_wr_awsize            (m_axi_wr_awsize),
        .m_axi_wr_awburst           (m_axi_wr_awburst),
        .m_axi_wr_awlock            (m_axi_wr_awlock),
        .m_axi_wr_awcache           (m_axi_wr_awcache),
        .m_axi_wr_awprot            (m_axi_wr_awprot),
        .m_axi_wr_awqos             (m_axi_wr_awqos),
        .m_axi_wr_awregion          (m_axi_wr_awregion),
        .m_axi_wr_awvalid           (m_axi_wr_awvalid),
        .m_axi_wr_awready           (m_axi_wr_awready),
        .m_axi_wr_wdata             (m_axi_wr_wdata),
        .m_axi_wr_wstrb             (m_axi_wr_wstrb),
        .m_axi_wr_wlast             (m_axi_wr_wlast),
        .m_axi_wr_wvalid            (m_axi_wr_wvalid),
        .m_axi_wr_wready            (m_axi_wr_wready),
        .m_axi_wr_bid               (m_axi_wr_bid),
        .m_axi_wr_bresp             (m_axi_wr_bresp),
        .m_axi_wr_bvalid            (m_axi_wr_bvalid),
        .m_axi_wr_bready            (m_axi_wr_bready),

        // Monitor Bus (sink half - full monitor bus into top arbiter)
        .mon_valid                  (snk_mon_valid),
        .mon_ready                  (snk_mon_ready),
        .mon_packet                 (snk_mon_packet),
        .mon_timestamp              (snk_mon_timestamp),

        // Debug (sink)
        .dbg_snk_sram_bridge_pending   (snk_dbg_snk_sram_bridge_pending),
        .dbg_snk_sram_bridge_out_valid (snk_dbg_snk_sram_bridge_out_valid),
        .dbg_axis_beats_received       (snk_dbg_axis_beats_received),
        .dbg_axis_packets_received     (snk_dbg_axis_packets_received)
    );

    //=========================================================================
    // Top-level MonBus Arbiter (merges the two half monitor streams)
    //
    // client[0] = source half monbus
    // client[1] = sink   half monbus
    //
    // Each half already aggregates its own monitor sources through its own
    // internal monbus_arbiter, so this is the third arbiter in the 3-level
    // hierarchy and produces the single core-level monitor stream.
    //=========================================================================
    logic                                    core_mon_valid_in    [2];
    logic                                    core_mon_ready_in    [2];
    monitor_common_pkg::monitor_packet_t     core_mon_packet_in   [2];
    monitor_common_pkg::monbus_timestamp_t   core_mon_timestamp_in[2];

    // Client 0: source half
    assign core_mon_valid_in[0]     = src_mon_valid;
    assign core_mon_packet_in[0]    = src_mon_packet;
    assign core_mon_timestamp_in[0] = src_mon_timestamp;
    assign src_mon_ready            = core_mon_ready_in[0];

    // Client 1: sink half
    assign core_mon_valid_in[1]     = snk_mon_valid;
    assign core_mon_packet_in[1]    = snk_mon_packet;
    assign core_mon_timestamp_in[1] = snk_mon_timestamp;
    assign snk_mon_ready            = core_mon_ready_in[1];

    monbus_arbiter #(
        .CLIENTS (2)
    ) u_mon_arbiter (
        .axi_aclk            (clk),
        .axi_aresetn         (rst_n),
        .block_arb           (1'b0),
        .monbus_valid_in     (core_mon_valid_in),
        .monbus_ready_in     (core_mon_ready_in),
        .monbus_packet_in    (core_mon_packet_in),
        .monbus_timestamp_in (core_mon_timestamp_in),
        .monbus_valid        (mon_valid),
        .monbus_ready        (mon_ready),
        .monbus_packet       (mon_packet),
        .monbus_timestamp    (mon_timestamp),
        /* verilator lint_off PINCONNECTEMPTY */
        .grant_valid         (),
        .grant               (),
        .grant_id            (),
        .last_grant          ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : rapids_core_beats
