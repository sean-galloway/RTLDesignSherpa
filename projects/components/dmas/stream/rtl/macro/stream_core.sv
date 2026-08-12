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
// Documentation: projects/components/dmas/stream/PRD.md
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
    parameter int CHAN_WIDTH = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 0,  // TASK-101 STREAM Extended
    parameter int AXI_ID_WIDTH = 8,
    parameter int FIFO_DEPTH = 512,
    parameter int AR_MAX_OUTSTANDING = 8,
    parameter int AW_MAX_OUTSTANDING = 8,
    // Monitor transaction-table depth. AR/AW_MAX_OUTSTANDING are PER-CHANNEL
    // limits on a SHARED master, so the no-backpressure bound is
    // NUM_CHANNELS * MAX_OUTSTANDING (the original hardwired 16 compared
    // against the per-channel limit and stalled the datapath at >=2 channels).
    // The default sizes for zero backpressure, per the design rule "monitors
    // are sized so backpressure does not normally happen". Deliberately
    // OVERRIDABLE downward: the saturation-recovery contract
    // (monitor_common_pkg::cmd_entry_reserve) guarantees an undersized
    // monitor throttles and RECOVERS rather than deadlocking, and the
    // mon_small test config pins this small on purpose to keep that
    // guarantee exercised end-to-end. +4 covers in-flight skid/handshake
    // overlap beyond the engines' own counters.
    // NOTE: Verilator 5.020's default --unroll-count is 64; monitor tables
    // deeper than that (8ch default = 68) need --unroll-count raised in the
    // sim build or the per-entry loops fail BLKLOOPINIT. The stream tests
    // pass --unroll-count 256. Synthesis tools are unaffected.
    //
    // SIZING: concurrency + REPORTING BACKLOG, floored at 16.
    //
    // A table slot is NOT freed when the AXI transaction completes -- it is
    // freed when the entry's packet has been REPORTED (axi_monitor_trans_mgr:
    // w_can_cleanup = event_reported, for COMPLETE/ERROR/ORPHANED alike). So
    // the table must hold
    //
    //     (transactions in flight)  +  (completed, packet not yet drained)
    //
    // The first term is NUM_CHANNELS*Ax_MAX_OUTSTANDING. The old `+ 4` was the
    // ENTIRE allowance for the second, and it was set when a build compiled one
    // packet cone. The unified harness compiles FIVE (timeout, compl,
    // threshold, perf, debug), each of which can owe a packet per transaction,
    // against a reporter that sustains ~1 packet / 2 cycles.
    //
    // MEASURED: at 4 channels x AR=2 the old formula gave 12 slots. A response
    // delay pins occupancy at the 8-transaction ceiling, leaving 4 slots of
    // reporting slack -- and 12 < 16 means cmd_entry_reserve() grants NO
    // recovery reservation, so the first overrun of those 4 is a permanent
    // wedge rather than a throttle. desc_perf hung there; the same test at 20
    // slots passed. This is the configuration the monitor BITSTREAM ships, so
    // it was a live silicon hazard, not a sim artifact.
    //
    // The floor of 16 is not cosmetic: cmd_entry_reserve() returns 2 only at
    // >= 16, and that reservation is what makes saturation recoverable.
    // MEASURED, not guessed. obs_equiv compares the external observer against
    // the in-core monitor over identical traffic:
    //     16 slots -> in-core tracked 3073 of 4096 bursts (75%)
    //     40 slots -> 4096 of 4096 (exact)
    // The shortfall is capping, not a counting bug: while the table is full the
    // upstream handshake throttles, but commands that slip through are never
    // tracked. A dropped burst is a dropped MATCH, which on a coverage run reads
    // as "this tuple never occurred" -- a confident false negative, the worst
    // failure mode for a board campaign whose purpose is observing matches.
    // 32 gives 40 slots at the board's 4ch x AR=2.
    // 8 -> 16 slots at 4ch x AR=2. NOT larger, and the reason is timing, not area:
    //
    //   slots   WNS        LUTs            in-core tracking
    //     16    +1.018 ns  81393 (39.9%)   3073/4096  (75%)
    //     40   -25.183 ns  131663 (64.6%)  4096/4096  (100%)
    //
    // trans_mgr's CAM does three combinational ID lookups plus a free-slot
    // priority encode across EVERY entry, so the cone scales with depth; at 40
    // the path is >3x the 10 ns period and 64% utilisation adds routing
    // congestion on top. Depth buys tracking completeness and spends timing,
    // steeply and nonlinearly.
    //
    // 16 is therefore the floor that makes saturation RECOVERABLE
    // (cmd_entry_reserve()==2 only at >=16) while still closing timing. It does
    // NOT make tracking complete -- see [[AMBA-MONTRACK]]. Closing that gap
    // needs a pipelined CAM or fewer cones per bitstream, not more slots.
    parameter int MON_TRANS_MARGIN = 8,     // reporting backlog, not concurrency
    parameter int RD_MON_MAX_TRANS = ((NUM_CHANNELS * AR_MAX_OUTSTANDING + MON_TRANS_MARGIN) < 16)
                                     ? 16 : (NUM_CHANNELS * AR_MAX_OUTSTANDING + MON_TRANS_MARGIN),
    parameter int WR_MON_MAX_TRANS = ((NUM_CHANNELS * AW_MAX_OUTSTANDING + MON_TRANS_MARGIN) < 16)
                                     ? 16 : (NUM_CHANNELS * AW_MAX_OUTSTANDING + MON_TRANS_MARGIN),

    // Monitor Control
    parameter int USE_AXI_MONITORS = 1,      // 1 = Enable monitors, 0 = Disable monitors
    // 0 = omit the per-channel descriptor-engine/scheduler completion/error
    // MonBus emitters (the cluster trace). Independent of USE_AXI_MONITORS (the
    // datapath perf monitors); set 0 on the area-tight FPGA char build where
    // only the datapath perf buckets are needed. Default on for back-compat.
    parameter bit GEN_MON = 1'b1,

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
    parameter RD_AXI_MON_AGENT_ID = 9,       // 0x09 - Data-read datapath monitor
    parameter WR_AXI_MON_AGENT_ID = 10,      // 0x0A - Data-write datapath monitor
    parameter MON_UNIT_ID = 1,               // 0x1

    // Desc-bus monitor reporter sub-block enables. Pass-through to
    // scheduler_group_array → axi4_master_rd_mon. Defaults match the
    // unit-level wrapper (5 cones on, debug on for stream's
    // compression dataset use).
    // Descriptor-fetch AXI monitor: perf-only, matching the data-read/-write
    // datapath monitors below (ENABLE_PERF_LOGIC only). The error/timeout/
    // compl/threshold/debug cones each pull in a CAM + reporter and were the
    // bulk of the descriptor monitor's LUTs; the characterization only needs
    // the perf buckets, so drop them (recovers FPGA fit on the xc7a100t).
    parameter bit DESC_MON_ENABLE_ERROR_LOGIC     = 1'b0,
    parameter bit DESC_MON_ENABLE_TIMEOUT_LOGIC   = 1'b0,
    parameter bit DESC_MON_ENABLE_COMPL_LOGIC     = 1'b0,
    parameter bit DESC_MON_ENABLE_THRESHOLD_LOGIC = 1'b0,
    parameter bit DESC_MON_ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit DESC_MON_ENABLE_DEBUG_LOGIC     = 1'b0,

    // Data-read/-write datapath monitor logic cones. Same area tradeoff as the
    // descriptor monitor above (perf-only by default for FPGA fit on the
    // xc7a100t); the monitor-validation flow (Genesys2 xc7k325t) overrides these
    // to 1'b1 to exercise every packet class (error/timeout/compl/threshold/...).
    parameter bit DATA_MON_ENABLE_ERROR_LOGIC     = 1'b0,
    parameter bit DATA_MON_ENABLE_TIMEOUT_LOGIC   = 1'b0,
    parameter bit DATA_MON_ENABLE_COMPL_LOGIC     = 1'b0,
    parameter bit DATA_MON_ENABLE_THRESHOLD_LOGIC = 1'b0,
    parameter bit DATA_MON_ENABLE_PERF_LOGIC      = 1'b1,
    parameter bit DATA_MON_ENABLE_DEBUG_LOGIC     = 1'b0,

    // Address-range (allowlist) checker on the in-core rd/wr datapath monitors.
    // N_ADDR_RANGES=0 (default) leaves the checker un-synthesised -> OFF on the
    // perf harness. The monitor-validation harness sets it to 4. The per-range
    // DEBUG/ERROR flavor is a build param (default all-0; the harness sets e.g.
    // 4'b1100 = ranges 2,3 error / 0,1 debug). Range VALUES + enables come at
    // runtime from the RDMON_/WRMON_ADDR_RANGE* CSRs.
    parameter int N_ADDR_RANGES = 0,
    parameter logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0] MON_ADDR_RANGE_IS_ERROR = '0,

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
    input  logic                        cam_clear,  // sync clear of monitor trans CAMs

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
    input  logic [7:0]                          cfg_sched_timeout_limit,
    input  logic                                cfg_sched_timeout_enable,
    input  logic                                cfg_sched_err_enable,
    input  logic                                cfg_sched_compl_enable,
    input  logic                                cfg_sched_perf_enable,

    // Descriptor engine configuration
    input  logic                                cfg_desceng_enable,
    input  logic                                cfg_desceng_prefetch,
    input  logic                                cfg_rd_prefetch_enable,   // scheduler read-ahead prefetch
    input  logic [3:0]                          cfg_desceng_fifo_thresh,
    input  logic [AW-1:0]                       cfg_desceng_addr0_base,
    input  logic [AW-1:0]                       cfg_desceng_addr0_limit,
    input  logic [AW-1:0]                       cfg_desceng_addr1_base,
    input  logic [AW-1:0]                       cfg_desceng_addr1_limit,

    // Descriptor AXI monitor configuration (expanded with filtering)
    input  logic                                cfg_desc_mon_enable,
    input  logic                                cfg_desc_mon_err_enable,
    input  logic                                cfg_desc_mon_perf_enable,
    input  logic                                cfg_desc_mon_compl_enable,
    input  logic                                cfg_desc_mon_thresh_enable,
    input  logic                                cfg_desc_mon_timeout_enable,
    input  logic [31:0]                         cfg_desc_mon_timeout_cycles,
    input  logic [31:0]                         cfg_desc_mon_latency_thresh,
    input  logic [15:0]                         cfg_desc_mon_pkt_mask,
    input  logic [15:0]                          cfg_desc_mon_err_select,
    input  logic [15:0]                          cfg_desc_mon_err_mask,
    input  logic [15:0]                          cfg_desc_mon_timeout_mask,
    input  logic [15:0]                          cfg_desc_mon_compl_mask,
    input  logic [15:0]                          cfg_desc_mon_thresh_mask,
    input  logic [15:0]                          cfg_desc_mon_perf_mask,
    input  logic [15:0]                          cfg_desc_mon_addr_mask,
    input  logic [15:0]                          cfg_desc_mon_debug_mask,

    // RFC Stage E perf-window run control (see DAXMON_PERF_CTRL @ 0x2D0)
    input  logic                                cfg_desc_mon_perf_run,

    // Read Engine AXI monitor configuration
    input  logic                                cfg_rdeng_mon_enable,
    input  logic                                cfg_rdeng_mon_err_enable,
    input  logic                                cfg_rdeng_mon_perf_enable,
    input  logic                                cfg_rdeng_mon_compl_enable,
    input  logic                                cfg_rdeng_mon_thresh_enable,
    input  logic                                cfg_rdeng_mon_timeout_enable,
    input  logic [31:0]                         cfg_rdeng_mon_timeout_cycles,
    input  logic [31:0]                         cfg_rdeng_mon_latency_thresh,
    input  logic [15:0]                         cfg_rdeng_mon_pkt_mask,
    input  logic [15:0]                          cfg_rdeng_mon_err_select,
    input  logic [15:0]                          cfg_rdeng_mon_err_mask,
    input  logic [15:0]                          cfg_rdeng_mon_timeout_mask,
    input  logic [15:0]                          cfg_rdeng_mon_compl_mask,
    input  logic [15:0]                          cfg_rdeng_mon_thresh_mask,
    input  logic [15:0]                          cfg_rdeng_mon_perf_mask,
    input  logic [15:0]                          cfg_rdeng_mon_addr_mask,
    input  logic [15:0]                          cfg_rdeng_mon_debug_mask,

    // Write Engine AXI monitor configuration
    input  logic                                cfg_wreng_mon_enable,
    input  logic                                cfg_wreng_mon_err_enable,
    input  logic                                cfg_wreng_mon_perf_enable,
    input  logic                                cfg_wreng_mon_compl_enable,
    input  logic                                cfg_wreng_mon_thresh_enable,
    input  logic                                cfg_wreng_mon_timeout_enable,
    input  logic [31:0]                         cfg_wreng_mon_timeout_cycles,
    input  logic [31:0]                         cfg_wreng_mon_latency_thresh,
    input  logic [15:0]                         cfg_wreng_mon_pkt_mask,
    input  logic [15:0]                          cfg_wreng_mon_err_select,
    input  logic [15:0]                          cfg_wreng_mon_err_mask,
    input  logic [15:0]                          cfg_wreng_mon_timeout_mask,
    input  logic [15:0]                          cfg_wreng_mon_compl_mask,
    input  logic [15:0]                          cfg_wreng_mon_thresh_mask,
    input  logic [15:0]                          cfg_wreng_mon_perf_mask,
    input  logic [15:0]                          cfg_wreng_mon_addr_mask,
    input  logic [15:0]                          cfg_wreng_mon_debug_mask,

    // RFC Stage E perf-window run control for the datapath monitors
    // (decoupled from cfg_*eng_mon_perf_enable, which only gates legacy
    // PktTypePerf emission). Level signal: 1=open the monitor's perf window
    // and accumulate cycle buckets; 0=close/freeze. Rising edge clears the
    // counters. See RDMON_PERF_CTRL @ 0x300 / WRMON_PERF_CTRL @ 0x330.
    input  logic                                cfg_rdeng_mon_perf_run,
    input  logic                                cfg_wreng_mon_perf_run,

    // Address-range checker CSR inputs (RDMON_/WRMON_ADDR_RANGE*). Bounds are
    // 32-bit, zero-extended to the AW-bit compare inside. Consumed only when
    // N_ADDR_RANGES > 0 (otherwise the in-core checker is not synthesised).
    input  logic [3:0][31:0]                    cfg_rdeng_mon_addr_range_low,
    input  logic [3:0][31:0]                    cfg_rdeng_mon_addr_range_high,
    input  logic [3:0]                          cfg_rdeng_mon_addr_range_en,
    input  logic                                cfg_rdeng_mon_addr_check_en,
    input  logic                                cfg_rdeng_mon_addr_match_en,
    input  logic                                cfg_rdeng_mon_addr_miss_en,
    input  logic [3:0][31:0]                    cfg_wreng_mon_addr_range_low,
    input  logic [3:0][31:0]                    cfg_wreng_mon_addr_range_high,
    input  logic [3:0]                          cfg_wreng_mon_addr_range_en,
    input  logic                                cfg_wreng_mon_addr_check_en,
    input  logic                                cfg_wreng_mon_addr_match_en,
    input  logic                                cfg_wreng_mon_addr_miss_en,

    // RFC Stage E option 2 / RFC Stage C: per-channel perf-bucket readout
    // select. Picks which channel's 4 buckets appear on the rdmon/wrmon_ch_*
    // outputs (indexed-readout pattern; see PERF_CH_SEL @ 0x35C).
    input  logic [CHAN_WIDTH-1:0]               cfg_perf_ch_sel,

    // RFC Stage D: latency-histogram indexed readout select (see HIST_SEL @
    // 0x378). bus 0=read R bus, 1=write W bus; metric 0=AR->firstR / AW->B,
    // 1=AR->RLAST (reads only); bin selects one of 16 log2 latency bins.
    input  logic                                cfg_perf_hist_bus,
    input  logic                                cfg_perf_hist_metric,
    input  logic [3:0]                          cfg_perf_hist_bin,
    output logic [31:0]                         perf_hist_data,
    output logic [31:0]                         perf_hist_total,

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

    // Descriptor monitor perf-window readback (RFC Stage E CSR route)
    output logic                                perf_window_active,
    output logic [31:0]                         perf_window_cycles,
    output logic [31:0]                         perf_prod_cycles,
    output logic [31:0]                         perf_bp_cycles,
    output logic [31:0]                         perf_starv_cycles,
    output logic [31:0]                         perf_idle_cycles,
    output logic [31:0]                         perf_beat_count,
    output logic [63:0]                         perf_byte_count,
    output logic [31:0]                         perf_burst_count,

    // Data Read Engine AXI Monitor Status
    output logic                                cfg_sts_rdeng_skid_busy,
    output logic [7:0]                          cfg_sts_rdeng_mon_active_txns,
    output logic [15:0]                         cfg_sts_rdeng_mon_error_count,
    output logic [31:0]                         cfg_sts_rdeng_mon_txn_count,
    output logic                                cfg_sts_rdeng_mon_conflict_error,

    // Read-engine datapath monitor perf-window readback (RFC Stage E CSR route).
    // Buckets PROD+BP+STARV+IDLE sum to the closed-window length; these measure
    // the data-read R bus (the same bus the FPGA-char axi_bus_meter snoops).
    output logic                                rdmon_perf_window_active,
    output logic [31:0]                         rdmon_perf_window_cycles,
    output logic [31:0]                         rdmon_perf_prod_cycles,
    output logic [31:0]                         rdmon_perf_bp_cycles,
    output logic [31:0]                         rdmon_perf_starv_cycles,
    output logic [31:0]                         rdmon_perf_idle_cycles,
    output logic [31:0]                         rdmon_perf_beat_count,
    output logic [63:0]                         rdmon_perf_byte_count,
    output logic [31:0]                         rdmon_perf_burst_count,

    // Data Write Engine AXI Monitor Status
    output logic                                cfg_sts_wreng_skid_busy,
    output logic [7:0]                          cfg_sts_wreng_mon_active_txns,
    output logic [15:0]                         cfg_sts_wreng_mon_error_count,
    output logic [31:0]                         cfg_sts_wreng_mon_txn_count,
    output logic                                cfg_sts_wreng_mon_conflict_error,

    // Write-engine datapath monitor perf-window readback (RFC Stage E CSR route).
    // Buckets PROD+BP+STARV+IDLE sum to the closed-window length; these measure
    // the data-write W bus (the same bus the FPGA-char axi_bus_meter snoops).
    output logic                                wrmon_perf_window_active,
    output logic [31:0]                         wrmon_perf_window_cycles,
    output logic [31:0]                         wrmon_perf_prod_cycles,
    output logic [31:0]                         wrmon_perf_bp_cycles,
    output logic [31:0]                         wrmon_perf_starv_cycles,
    output logic [31:0]                         wrmon_perf_idle_cycles,
    output logic [31:0]                         wrmon_perf_beat_count,
    output logic [63:0]                         wrmon_perf_byte_count,
    output logic [31:0]                         wrmon_perf_burst_count,

    // Per-channel perf buckets (RFC Stage C, via in-core axi_bus_meter). The
    // four 16-bit buckets are for the channel selected by cfg_perf_ch_sel; the
    // overflow masks expose all channels at once ({prod,bp,starv,idle} per
    // channel). Window-aligned with the aggregate monitor windows (same RUN).
    output logic [15:0]                         rdmon_ch_prod_cycles,
    output logic [15:0]                         rdmon_ch_bp_cycles,
    output logic [15:0]                         rdmon_ch_starv_cycles,
    output logic [15:0]                         rdmon_ch_idle_cycles,
    output logic [NC*4-1:0]                     rdmon_ch_overflow,
    output logic [15:0]                         wrmon_ch_prod_cycles,
    output logic [15:0]                         wrmon_ch_bp_cycles,
    output logic [15:0]                         wrmon_ch_starv_cycles,
    output logic [15:0]                         wrmon_ch_idle_cycles,
    output logic [NC*4-1:0]                     wrmon_ch_overflow,

    //=========================================================================
    // Unified Monitor Bus Interface (128-bit packet + 64-bit side-band ts)
    //=========================================================================
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output monitor_common_pkg::monitor_packet_t     mon_packet,
    output monitor_common_pkg::monbus_timestamp_t   mon_timestamp
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

    // Write-engine active-channel sideband (the W bus has no wid; this mirrors
    // the engine's r_w_channel_id / r_w_active). Consumed internally by the
    // in-core per-channel axi_bus_meter -- formerly a top-level output for the
    // harness meter, which was retired in RFC Stage E.4.
    logic [CHAN_WIDTH-1:0]       wr_active_channel_id;
    logic                        wr_active_channel_valid;

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
    logic [NC-1:0]               sched_wr_commit_strobe;
    logic [NC-1:0][31:0]         sched_wr_commit_beats;

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

    // Data-read and data-write datapath monitor bus (from u_rd_axi_skid /
    // u_wr_axi_skid). These carry AddrMatch/Error/Perf packets tagged with
    // RD_AXI_MON_AGENT_ID / WR_AXI_MON_AGENT_ID and are aggregated with the
    // scheduler-group stream by the monbus arbiter below.
    logic                                     rdmon_mon_valid;
    logic                                     rdmon_mon_ready;
    monitor_common_pkg::monitor_packet_t      rdmon_mon_packet;
    monitor_common_pkg::monbus_timestamp_t    rdmon_mon_timestamp;

    logic                                     wrmon_mon_valid;
    logic                                     wrmon_mon_ready;
    monitor_common_pkg::monitor_packet_t      wrmon_mon_packet;
    monitor_common_pkg::monbus_timestamp_t    wrmon_mon_timestamp;

    //=========================================================================
    // Internal Signals - Monitor Configuration (conditional based on USE_AXI_MONITORS)
    //=========================================================================
    // When USE_AXI_MONITORS=0, internal signals are tied off
    logic                        int_cfg_desc_mon_enable;
    logic                        int_cfg_desc_mon_err_enable;
    logic                        int_cfg_desc_mon_perf_enable;
    logic                        int_cfg_desc_mon_compl_enable;
    logic                        int_cfg_desc_mon_thresh_enable;
    logic                        int_cfg_desc_mon_timeout_enable;
    logic [31:0]                 int_cfg_desc_mon_timeout_cycles;
    logic [31:0]                 int_cfg_desc_mon_latency_thresh;
    logic [15:0]                 int_cfg_desc_mon_pkt_mask;
    logic [15:0]                  int_cfg_desc_mon_err_select;
    logic [15:0]                  int_cfg_desc_mon_err_mask;
    logic [15:0]                  int_cfg_desc_mon_timeout_mask;
    logic [15:0]                  int_cfg_desc_mon_compl_mask;
    logic [15:0]                  int_cfg_desc_mon_thresh_mask;
    logic [15:0]                  int_cfg_desc_mon_perf_mask;
    logic [15:0]                  int_cfg_desc_mon_addr_mask;
    logic [15:0]                  int_cfg_desc_mon_debug_mask;
    logic                        int_cfg_desc_mon_perf_run;

    logic                        int_cfg_rdeng_mon_enable;
    logic                        int_cfg_rdeng_mon_err_enable;
    logic                        int_cfg_rdeng_mon_perf_enable;
    logic                        int_cfg_rdeng_mon_compl_enable;
    logic                        int_cfg_rdeng_mon_thresh_enable;
    logic                        int_cfg_rdeng_mon_timeout_enable;
    logic [31:0]                 int_cfg_rdeng_mon_timeout_cycles;
    logic [31:0]                 int_cfg_rdeng_mon_latency_thresh;
    logic [15:0]                 int_cfg_rdeng_mon_pkt_mask;
    logic [15:0]                  int_cfg_rdeng_mon_err_select;
    logic [15:0]                  int_cfg_rdeng_mon_err_mask;
    logic [15:0]                  int_cfg_rdeng_mon_timeout_mask;
    logic [15:0]                  int_cfg_rdeng_mon_compl_mask;
    logic [15:0]                  int_cfg_rdeng_mon_thresh_mask;
    logic [15:0]                  int_cfg_rdeng_mon_perf_mask;
    logic [15:0]                  int_cfg_rdeng_mon_addr_mask;
    logic [15:0]                  int_cfg_rdeng_mon_debug_mask;
    logic                        int_cfg_rdeng_mon_perf_run;

    logic                        int_cfg_wreng_mon_enable;
    logic                        int_cfg_wreng_mon_err_enable;
    logic                        int_cfg_wreng_mon_perf_enable;
    logic                        int_cfg_wreng_mon_compl_enable;
    logic                        int_cfg_wreng_mon_thresh_enable;
    logic                        int_cfg_wreng_mon_timeout_enable;
    logic [31:0]                 int_cfg_wreng_mon_timeout_cycles;
    logic [31:0]                 int_cfg_wreng_mon_latency_thresh;
    logic [15:0]                 int_cfg_wreng_mon_pkt_mask;
    logic [15:0]                  int_cfg_wreng_mon_err_select;
    logic [15:0]                  int_cfg_wreng_mon_err_mask;
    logic [15:0]                  int_cfg_wreng_mon_timeout_mask;
    logic [15:0]                  int_cfg_wreng_mon_compl_mask;
    logic [15:0]                  int_cfg_wreng_mon_thresh_mask;
    logic [15:0]                  int_cfg_wreng_mon_perf_mask;
    logic [15:0]                  int_cfg_wreng_mon_addr_mask;
    logic [15:0]                  int_cfg_wreng_mon_debug_mask;
    logic                        int_cfg_wreng_mon_perf_run;

    //=========================================================================
    // Generate Block - Monitor Configuration Assignment
    //=========================================================================
    generate
        if (USE_AXI_MONITORS == 1) begin : g_monitors_enabled
            // Connect input ports to internal signals
            assign int_cfg_desc_mon_enable = cfg_desc_mon_enable;
            assign int_cfg_desc_mon_err_enable = cfg_desc_mon_err_enable;
            assign int_cfg_desc_mon_perf_enable = cfg_desc_mon_perf_enable;
            assign int_cfg_desc_mon_compl_enable = cfg_desc_mon_compl_enable;
            assign int_cfg_desc_mon_thresh_enable = cfg_desc_mon_thresh_enable;
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
            assign int_cfg_desc_mon_perf_run = cfg_desc_mon_perf_run;

            assign int_cfg_rdeng_mon_enable = cfg_rdeng_mon_enable;
            assign int_cfg_rdeng_mon_err_enable = cfg_rdeng_mon_err_enable;
            assign int_cfg_rdeng_mon_perf_enable = cfg_rdeng_mon_perf_enable;
            assign int_cfg_rdeng_mon_compl_enable = cfg_rdeng_mon_compl_enable;
            assign int_cfg_rdeng_mon_thresh_enable = cfg_rdeng_mon_thresh_enable;
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
            assign int_cfg_rdeng_mon_perf_run = cfg_rdeng_mon_perf_run;

            assign int_cfg_wreng_mon_enable = cfg_wreng_mon_enable;
            assign int_cfg_wreng_mon_err_enable = cfg_wreng_mon_err_enable;
            assign int_cfg_wreng_mon_perf_enable = cfg_wreng_mon_perf_enable;
            assign int_cfg_wreng_mon_compl_enable = cfg_wreng_mon_compl_enable;
            assign int_cfg_wreng_mon_thresh_enable = cfg_wreng_mon_thresh_enable;
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
            assign int_cfg_wreng_mon_perf_run = cfg_wreng_mon_perf_run;
        end else begin : g_monitors_disabled
            // Tie off the HEAVY monitor configs (CAM/reporter cones) to 0. The
            // perf-window RUN bits are the exception: they drive the always-on
            // datapath perf window/bus-meters below, which survive monitors-off,
            // so they pass through (see int_cfg_*_mon_perf_run assigns below).
            assign int_cfg_desc_mon_enable = 1'b0;
            assign int_cfg_desc_mon_err_enable = 1'b0;
            assign int_cfg_desc_mon_perf_enable = 1'b0;
            assign int_cfg_desc_mon_compl_enable = 1'b0;
            assign int_cfg_desc_mon_thresh_enable = 1'b0;
            assign int_cfg_desc_mon_timeout_enable = 1'b0;
            assign int_cfg_desc_mon_timeout_cycles = 32'h0;
            assign int_cfg_desc_mon_latency_thresh = 32'h0;
            assign int_cfg_desc_mon_pkt_mask = 16'h0;
            assign int_cfg_desc_mon_err_select = 16'h0;
            assign int_cfg_desc_mon_err_mask = 16'h0;
            assign int_cfg_desc_mon_timeout_mask = 16'h0;
            assign int_cfg_desc_mon_compl_mask = 16'h0;
            assign int_cfg_desc_mon_thresh_mask = 16'h0;
            assign int_cfg_desc_mon_perf_mask = 16'h0;
            assign int_cfg_desc_mon_addr_mask = 16'h0;
            assign int_cfg_desc_mon_debug_mask = 16'h0;
            assign int_cfg_desc_mon_perf_run = cfg_desc_mon_perf_run;  // always-on perf window

            assign int_cfg_rdeng_mon_enable = 1'b0;
            assign int_cfg_rdeng_mon_err_enable = 1'b0;
            assign int_cfg_rdeng_mon_perf_enable = 1'b0;
            assign int_cfg_rdeng_mon_compl_enable = 1'b0;
            assign int_cfg_rdeng_mon_thresh_enable = 1'b0;
            assign int_cfg_rdeng_mon_timeout_enable = 1'b0;
            assign int_cfg_rdeng_mon_timeout_cycles = 32'h0;
            assign int_cfg_rdeng_mon_latency_thresh = 32'h0;
            assign int_cfg_rdeng_mon_pkt_mask = 16'h0;
            assign int_cfg_rdeng_mon_err_select = 16'h0;
            assign int_cfg_rdeng_mon_err_mask = 16'h0;
            assign int_cfg_rdeng_mon_timeout_mask = 16'h0;
            assign int_cfg_rdeng_mon_compl_mask = 16'h0;
            assign int_cfg_rdeng_mon_thresh_mask = 16'h0;
            assign int_cfg_rdeng_mon_perf_mask = 16'h0;
            assign int_cfg_rdeng_mon_addr_mask = 16'h0;
            assign int_cfg_rdeng_mon_debug_mask = 16'h0;
            assign int_cfg_rdeng_mon_perf_run = cfg_rdeng_mon_perf_run;  // always-on perf window

            assign int_cfg_wreng_mon_enable = 1'b0;
            assign int_cfg_wreng_mon_err_enable = 1'b0;
            assign int_cfg_wreng_mon_perf_enable = 1'b0;
            assign int_cfg_wreng_mon_compl_enable = 1'b0;
            assign int_cfg_wreng_mon_thresh_enable = 1'b0;
            assign int_cfg_wreng_mon_timeout_enable = 1'b0;
            assign int_cfg_wreng_mon_timeout_cycles = 32'h0;
            assign int_cfg_wreng_mon_latency_thresh = 32'h0;
            assign int_cfg_wreng_mon_pkt_mask = 16'h0;
            assign int_cfg_wreng_mon_err_select = 16'h0;
            assign int_cfg_wreng_mon_err_mask = 16'h0;
            assign int_cfg_wreng_mon_timeout_mask = 16'h0;
            assign int_cfg_wreng_mon_compl_mask = 16'h0;
            assign int_cfg_wreng_mon_thresh_mask = 16'h0;
            assign int_cfg_wreng_mon_perf_mask = 16'h0;
            assign int_cfg_wreng_mon_addr_mask = 16'h0;
            assign int_cfg_wreng_mon_debug_mask = 16'h0;
            assign int_cfg_wreng_mon_perf_run = cfg_wreng_mon_perf_run;  // always-on perf window
        end
    endgenerate

    //=========================================================================
    // Component Instantiation - Scheduler Group Array
    //=========================================================================
    scheduler_group_array #(
        .GEN_MON                (GEN_MON),
        .USE_AXI_MONITORS       (USE_AXI_MONITORS),
        .NUM_CHANNELS           (NC),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (AW),
        .DATA_WIDTH             (DW),
        .USE_ROW_COL_MAJOR_ADDRESSING (USE_ROW_COL_MAJOR_ADDRESSING),
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
        .cam_clear              (cam_clear),

        // APB interface
        .apb_valid              (apb_valid),
        .apb_ready              (apb_ready),
        .apb_addr               (apb_addr),

        // Configuration
        .cfg_channel_enable     (cfg_channel_enable),
        .cfg_channel_reset      (cfg_channel_reset),
        .cfg_sched_enable       (cfg_sched_enable),
        .cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit(cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable(cfg_sched_timeout_enable),
        .cfg_sched_err_enable   (cfg_sched_err_enable),
        .cfg_sched_compl_enable (cfg_sched_compl_enable),
        .cfg_sched_perf_enable  (cfg_sched_perf_enable),
        .cfg_desceng_enable     (cfg_desceng_enable),
        .cfg_desceng_prefetch   (cfg_desceng_prefetch),
        .cfg_rd_prefetch_enable (cfg_rd_prefetch_enable),
        .cfg_desceng_fifo_thresh(cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base (cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit(cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base (cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit(cfg_desceng_addr1_limit),

        // Descriptor AXI Monitor Configuration (use internal signals)
        .cfg_desc_mon_enable        (int_cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (int_cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (int_cfg_desc_mon_perf_enable),
        .cfg_desc_mon_compl_enable(int_cfg_desc_mon_compl_enable),
        .cfg_desc_mon_thresh_enable(int_cfg_desc_mon_thresh_enable),
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
        .cfg_desc_mon_perf_run      (int_cfg_desc_mon_perf_run),

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

        // Descriptor monitor perf-window readback (RFC Stage E CSR route)
        .perf_window_active     (perf_window_active),
        .perf_window_cycles     (perf_window_cycles),
        .perf_prod_cycles       (perf_prod_cycles),
        .perf_bp_cycles         (perf_bp_cycles),
        .perf_starv_cycles      (perf_starv_cycles),
        .perf_idle_cycles       (perf_idle_cycles),
        .perf_beat_count        (perf_beat_count),
        .perf_byte_count        (perf_byte_count),
        .perf_burst_count       (perf_burst_count),

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
        .sched_wr_commit_strobe (sched_wr_commit_strobe),
        .sched_wr_commit_beats  (sched_wr_commit_beats),

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
    // Monitor Bus - Aggregate the three in-core monbus producers.
    //
    // Three sources ride the top-level monbus: the scheduler-group monitor and
    // the two AXI datapath monitors (read/write). A round-robin arbiter merges
    // them fairly onto the single mon_valid/mon_packet output; without it the
    // datapath monitors' AddrMatch/Error/Perf packets never reach a consumer.
    //=========================================================================
    localparam int MON_CLIENTS = 3;

    logic                                  mon_arb_valid_in [MON_CLIENTS];
    logic                                  mon_arb_ready_in [MON_CLIENTS];
    monitor_common_pkg::monitor_packet_t   mon_arb_packet_in[MON_CLIENTS];
    monitor_common_pkg::monbus_timestamp_t mon_arb_ts_in    [MON_CLIENTS];

    // Client 0: scheduler-group monitor
    assign mon_arb_valid_in [0] = schedgrp_mon_valid;
    assign mon_arb_packet_in[0] = schedgrp_mon_packet;
    assign mon_arb_ts_in    [0] = schedgrp_mon_timestamp;
    assign schedgrp_mon_ready   = mon_arb_ready_in[0];

    // Client 1: data-read datapath monitor
    assign mon_arb_valid_in [1] = rdmon_mon_valid;
    assign mon_arb_packet_in[1] = rdmon_mon_packet;
    assign mon_arb_ts_in    [1] = rdmon_mon_timestamp;
    assign rdmon_mon_ready      = mon_arb_ready_in[1];

    // Client 2: data-write datapath monitor
    assign mon_arb_valid_in [2] = wrmon_mon_valid;
    assign mon_arb_packet_in[2] = wrmon_mon_packet;
    assign mon_arb_ts_in    [2] = wrmon_mon_timestamp;
    assign wrmon_mon_ready      = mon_arb_ready_in[2];

    monbus_arbiter #(
        .CLIENTS            (MON_CLIENTS),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_mon_arbiter (
        .axi_aclk            (clk),
        .axi_aresetn         (rst_n),
        .block_arb           (1'b0),
        .monbus_valid_in     (mon_arb_valid_in),
        .monbus_ready_in     (mon_arb_ready_in),
        .monbus_packet_in    (mon_arb_packet_in),
        .monbus_timestamp_in (mon_arb_ts_in),
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

    //=========================================================================
    // RFC Stage E perf-window controller (HARDWARE close)
    //=========================================================================
    // The datapath perf windows (aggregate monitors, per-channel meters, latency
    // histograms) must bracket the ACTIVE transfer, exactly like the retired
    // harness axi_bus_meter (which froze on the harness timer 'done'). Software
    // writing RUN=1 opens the window (rising edge clears the counters), but
    // closing it in software lags by the host poll/UART latency -- on real
    // hardware that counts ~ms of post-transfer idle as starvation. So we close
    // the window IN HARDWARE: it opens on the RUN rising edge, latches "was
    // busy" once any scheduler is active, and closes a few cycles after all
    // schedulers go idle (the settle counter covers the final write-response
    // drain). Clearing RUN also closes it (software override). Shared by both
    // datapath buses; the host still toggles RUN to arm/disarm and read.
    // Datapath-activity signals (hoisted here so the perf-window busy gate can
    // bracket real data movement, not just scheduler FSM state). Also consumed
    // by the bubble-bucket gating further down. Pure functions of module ports.
    wire  w_rd_data_beat   = m_axi_rd_rvalid & m_axi_rd_rready;
    wire  w_wr_data_beat   = m_axi_wr_wvalid & m_axi_wr_wready;
    wire  w_rd_outstanding = |(~axi_rd_all_complete & cfg_channel_enable);
    wire  w_wr_outstanding = |(~axi_wr_all_complete & cfg_channel_enable);

    localparam int unsigned PERF_SETTLE = 16;
    logic        w_perf_run_any;
    logic        w_perf_dma_busy;
    logic        r_perf_armed;       // RUN is asserted (level), one window per arm
    logic        r_perf_started;     // a window has already begun this arm
    logic        r_perf_win_active;  // counting window currently open
    logic        w_perf_begin;
    logic [4:0]  r_perf_settle;
    logic        w_perf_close, w_perf_clear;

    assign w_perf_run_any   = int_cfg_rdeng_mon_perf_run | int_cfg_wreng_mon_perf_run;
    // Busy = any ENABLED channel's scheduler is not idle. Masking by
    // cfg_channel_enable is essential: disabled channels are held in
    // channel-reset, which forces their scheduler_idle low (idle && !reset), so
    // a plain &scheduler_idle would never assert and the window would never
    // close on "done" -- it would stay open until the host clears RUN.
    // Busy = the transfer is genuinely in flight. Keying on scheduler_idle
    // ALONE was the bug: with the descriptor engine + prefetch the scheduler
    // dispatches and returns to idle while the read/write engines are still
    // draining the transfer, so the window closed (settle) mid-flight -- or, if
    // the scheduler idled before the first beat, never opened -- and the in-core
    // perf buckets read all-zero even though the DMA moved every beat. Port the
    // RAPIDS deterministic-bracket principle (project_rapids_char_go_deterministic_close):
    // hold the window open while the scheduler is active OR the datapath still
    // has outstanding transactions / is transferring a beat this cycle. This
    // brackets real data movement and is robust to prefetch / transfer size /
    // channel count. (stream_core exposes axi_{rd,wr}_all_complete natively, so
    // no separate beat-count target CSR is needed -- outstanding IS the signal.)
    assign w_perf_dma_busy  = |(~scheduler_idle & cfg_channel_enable)
                            | w_rd_outstanding | w_wr_outstanding
                            | w_rd_data_beat   | w_wr_data_beat;

    // CRITICAL: the window must START on the first DMA activity AFTER RUN is
    // armed -- NOT on the RUN rising edge. The host arms RUN and then issues
    // several more slow 115200-baud UART transactions (kick-address shadow
    // loads + KICK_GO) before the DMA actually starts; that arm->kick gap is
    // millions of idle aclk cycles. Starting the counters on the RUN edge
    // bucketed all of those idle cycles into the window, so the board reported
    // ~0.1% utilisation while the datapath itself was fully busy. Holding the
    // meters frozen (i_freeze = ~r_perf_win_active) until w_perf_dma_busy first
    // rises excludes the entire arm->kick gap. (scheduler_idle was correct all
    // along -- it is idle because nothing has been kicked yet.)
    assign w_perf_begin     = w_perf_run_any & w_perf_dma_busy &
                              ~r_perf_win_active & ~r_perf_started;
    assign w_perf_clear     = w_perf_begin;               // clear+start counters on first activity
    assign w_perf_close     = r_perf_win_active &
                              ( (~w_perf_dma_busy & (r_perf_settle == PERF_SETTLE[4:0]))
                                | ~w_perf_run_any );        // done (idle+settle), or RUN cleared

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_perf_armed      <= 1'b0;
            r_perf_started    <= 1'b0;
            r_perf_win_active <= 1'b0;
            r_perf_settle     <= 5'd0;
        end else begin
            r_perf_armed <= w_perf_run_any;
            if (!w_perf_run_any) begin
                // RUN cleared: disarm and re-arm fresh on the next RUN edge.
                r_perf_started    <= 1'b0;
                r_perf_win_active <= 1'b0;
                r_perf_settle     <= 5'd0;
            end else if (w_perf_begin) begin
                // First DMA activity under this arm: open the window now.
                r_perf_win_active <= 1'b1;
                r_perf_started    <= 1'b1;
                r_perf_settle     <= 5'd0;
            end else if (r_perf_win_active) begin
                if (w_perf_dma_busy) begin
                    r_perf_settle <= 5'd0;
                end else if (r_perf_settle != PERF_SETTLE[4:0]) begin
                    r_perf_settle <= r_perf_settle + 5'd1;
                end
                if (w_perf_close) r_perf_win_active <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------------
    // Data-owed gating for the datapath BUBBLE buckets (prod/bp/starv/idle).
    //
    // True datapath utilisation is "of the cycles data was owed and flowing,
    // how many were productive". The shared window above opens on scheduler
    // activity (~one AR->firstR before any beat) and closes a settle period
    // after the datapath goes quiet, so it charges the one-time pipeline-fill
    // latency AND the trailing drain as starvation -- neither is a bubble.
    //
    // Gate the bubble meters to count only while, on each bus independently:
    //   (a) the bus has reached its first valid&&ready  (excludes the leading
    //       AR->firstR / first-SRAM-fill latency -- a latency, in the AR->firstR
    //       histogram, not a bubble), AND
    //   (b) the engine still has an outstanding transaction OR a beat is
    //       transferring this cycle  (excludes the trailing drain once the last
    //       beat dropped outstanding to 0).
    // Keyed to the engine's own outstanding state (axi_{rd,wr}_all_complete),
    // so it is robust across transfer size / descriptor count / channel count:
    // a real intra-transfer stall (data owed but not arriving) is still counted.
    // The beat/byte/burst counters stay on the full monitor window (below), so
    // the count invariants (beats==productive, bursts==hist-total) hold.
    logic r_rd_beat_seen, r_wr_beat_seen;
    // w_rd_data_beat / w_wr_data_beat / w_rd_outstanding / w_wr_outstanding are
    // declared above (hoisted for the perf-window busy gate).
    wire  w_rd_bucket_en   = r_perf_win_active & (r_rd_beat_seen | w_rd_data_beat)
                             & (w_rd_outstanding | w_rd_data_beat);
    wire  w_wr_bucket_en   = r_perf_win_active & (r_wr_beat_seen | w_wr_data_beat)
                             & (w_wr_outstanding | w_wr_data_beat);
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rd_beat_seen <= 1'b0;
            r_wr_beat_seen <= 1'b0;
        end else if (!r_perf_win_active) begin
            r_rd_beat_seen <= 1'b0;   // re-arm for the next window
            r_wr_beat_seen <= 1'b0;
        end else begin
            if (w_rd_data_beat) r_rd_beat_seen <= 1'b1;
            if (w_wr_data_beat) r_wr_beat_seen <= 1'b1;
        end
    )
    // Aggregate bubble buckets come from these gated per-channel meters (below),
    // not the monitor; the monitor's own bucket outputs are left unconnected.
    logic [31:0] w_rd_mon_prod_nc, w_rd_mon_bp_nc, w_rd_mon_starv_nc, w_rd_mon_idle_nc;
    logic [31:0] w_wr_mon_prod_nc, w_wr_mon_bp_nc, w_wr_mon_starv_nc, w_wr_mon_idle_nc;
    // The datapath perf-window readback (window/beat/byte/burst) is now sourced
    // from the always-on bus meters + counters below (survives USE_AXI_MONITORS=0),
    // NOT from the heavy axi4_master_*_mon. Its perf outputs are left unconnected.
    logic        w_rd_mon_winact_nc,  w_wr_mon_winact_nc;
    logic [31:0] w_rd_mon_wincyc_nc,  w_wr_mon_wincyc_nc;
    logic [31:0] w_rd_mon_beat_nc,    w_wr_mon_beat_nc;
    logic [63:0] w_rd_mon_byte_nc,    w_wr_mon_byte_nc;
    logic [31:0] w_rd_mon_burst_nc,   w_wr_mon_burst_nc;

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
        .sched_wr_commit_strobe (sched_wr_commit_strobe),
        .sched_wr_commit_beats  (sched_wr_commit_beats),
        .dbg_wr_all_complete    (axi_wr_all_complete),
        .sched_wr_error         (sched_wr_error),

        // Debug
        .dbg_aw_transactions    (),
        .dbg_w_beats            (),

        // Sideband to stream_core's external port surface so the FPGA
        // characterization harness can wire axi_bus_meter directly.
        .o_active_channel_id    (wr_active_channel_id),
        .o_active_channel_valid (wr_active_channel_valid)
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

    // Data read AXI skid buffer + integrated datapath perf monitor (RFC Stage E).
    // Upgraded from a bare axi4_master_rd to axi4_master_rd_mon: same skid core,
    // plus an axi_monitor snooping the master-side R bus. Perf-only build
    // (ENABLE_PERF_LOGIC) so it accumulates the four cycle buckets + beat/byte/
    // burst counts read back through RDMON_PERF_* CSRs (no MonBus packets).
    // Sized by RD_MON_MAX_TRANS (MAX(16, NUM_CHANNELS*AR_MAX_OUTSTANDING+MON_TRANS_MARGIN))
    // so block_ready stays deasserted in normal operation. The previous
    // hardwired 16 compared against the PER-CHANNEL outstanding limit and
    // claimed passivity it did not have: with >=2 channels the shared master
    // exceeded the block threshold and the monitor throttled the datapath.
    // USE_MONITOR follows USE_AXI_MONITORS so the production (monitors-off)
    // build keeps a bare skid with zero monitor area.

    // Zero-extend the 32-bit address-range CSR bounds to the AW-bit compare.
    // Sized to the checker's guarded range count so the widths match whether
    // N_ADDR_RANGES is 0 (unbuilt) or 4.
    localparam int NAR = (N_ADDR_RANGES > 0) ? N_ADDR_RANGES : 1;
    logic [NAR-1:0][AW-1:0] w_rdmon_range_low, w_rdmon_range_high;
    logic [NAR-1:0][AW-1:0] w_wrmon_range_low, w_wrmon_range_high;
    always_comb begin
        for (int gi = 0; gi < NAR; gi++) begin
            w_rdmon_range_low [gi] = {{(AW-32){1'b0}}, cfg_rdeng_mon_addr_range_low [gi]};
            w_rdmon_range_high[gi] = {{(AW-32){1'b0}}, cfg_rdeng_mon_addr_range_high[gi]};
            w_wrmon_range_low [gi] = {{(AW-32){1'b0}}, cfg_wreng_mon_addr_range_low [gi]};
            w_wrmon_range_high[gi] = {{(AW-32){1'b0}}, cfg_wreng_mon_addr_range_high[gi]};
        end
    end

    axi4_master_rd_mon #(
        .SKID_DEPTH_AR          (SKID_DEPTH_AR),
        .SKID_DEPTH_R           (SKID_DEPTH_R),
        .AXI_ID_WIDTH           (IW),
        .AXI_ADDR_WIDTH         (AW),
        .AXI_DATA_WIDTH         (DW),
        .AXI_USER_WIDTH         (UW),
        .USE_MONITOR            (USE_AXI_MONITORS == 1),
        .UNIT_ID                (MON_UNIT_ID),
        .AGENT_ID               (RD_AXI_MON_AGENT_ID),
        .MAX_TRANSACTIONS       (RD_MON_MAX_TRANS),
        .ENABLE_FILTERING       (1),
        .ENABLE_ERROR_LOGIC     (DATA_MON_ENABLE_ERROR_LOGIC),
        .ENABLE_TIMEOUT_LOGIC   (DATA_MON_ENABLE_TIMEOUT_LOGIC),
        .ENABLE_COMPL_LOGIC     (DATA_MON_ENABLE_COMPL_LOGIC),
        .ENABLE_THRESHOLD_LOGIC (DATA_MON_ENABLE_THRESHOLD_LOGIC),
        .ENABLE_PERF_LOGIC      (DATA_MON_ENABLE_PERF_LOGIC),
        .ENABLE_DEBUG_LOGIC     (DATA_MON_ENABLE_DEBUG_LOGIC),
        .N_ADDR_RANGES          (N_ADDR_RANGES),
        .ADDR_RANGE_IS_ERROR    (MON_ADDR_RANGE_IS_ERROR)
    ) u_rd_axi_skid (
        .aclk                   (clk),
        .aresetn                (rst_n),
        // Observability tap added with the port; unused here.
        .debug_block_ready      (),
        .cam_clear              (cam_clear),

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

        // Monitor configuration (driven by the now-live RDMON_* CSR hooks).
        // compl and threshold are REAL per-class controls (RDMON_ENABLE.COMPL_EN
        // / .THRESH_EN). They used to be aliased onto monitor-enable and perf,
        // which left COMPL_EN dead in the register map and made THRESHOLD
        // silently un-armable without PERF_EN.
        .cfg_monitor_enable     (int_cfg_rdeng_mon_enable),
        .cfg_error_enable       (int_cfg_rdeng_mon_err_enable | cfg_rdeng_mon_addr_miss_en),
        .cfg_perf_enable        (int_cfg_rdeng_mon_perf_enable),
        .cfg_compl_enable       (int_cfg_rdeng_mon_compl_enable),
        .cfg_threshold_enable   (int_cfg_rdeng_mon_thresh_enable),
        .cfg_debug_enable       (cfg_rdeng_mon_addr_match_en),
        .cfg_timeout_enable     (int_cfg_rdeng_mon_timeout_enable),
        .cfg_timeout_cycles     (16'(int_cfg_rdeng_mon_timeout_cycles)),
        .cfg_latency_threshold  (int_cfg_rdeng_mon_latency_thresh),

        .cfg_axi_pkt_mask       (int_cfg_rdeng_mon_pkt_mask),
        .cfg_axi_err_select     (int_cfg_rdeng_mon_err_select),
        .cfg_axi_error_mask     (int_cfg_rdeng_mon_err_mask),
        .cfg_axi_timeout_mask   (int_cfg_rdeng_mon_timeout_mask),
        .cfg_axi_compl_mask     (int_cfg_rdeng_mon_compl_mask),
        .cfg_axi_thresh_mask    (int_cfg_rdeng_mon_thresh_mask),
        .cfg_axi_perf_mask      (int_cfg_rdeng_mon_perf_mask),
        .cfg_axi_addr_mask      (int_cfg_rdeng_mon_addr_mask),
        .cfg_axi_debug_mask     (int_cfg_rdeng_mon_debug_mask),

        // Address-range checker (allowlist) driven by the RDMON_ADDR_RANGE* CSRs;
        // active only when N_ADDR_RANGES > 0 (else the checker is not built).
        .cfg_addr_check_enable  (cfg_rdeng_mon_addr_check_en),
        .cfg_addr_range_enable  (cfg_rdeng_mon_addr_range_en[NAR-1:0]),
        .cfg_addr_range_low     (w_rdmon_range_low),
        .cfg_addr_range_high    (w_rdmon_range_high),

        // Perf-window control (RFC Stage E CSR route). Trigger mode driven by
        // the RDMON_PERF_CTRL.RUN bit; decoupled from cfg_perf_enable so the
        // window accumulates without emitting PktTypePerf packets.
        // Hardware-closed window: open on the RUN rising edge, close when the
        // datapath goes idle after activity (see the perf-window controller).
        .cfg_start_event_sel    (3'b000),
        .cfg_end_event_sel      (3'b000),
        .cfg_start_trigger      (w_perf_clear),
        .cfg_end_trigger        (w_perf_close),
        .cfg_window_force_close (1'b0),

        .i_mon_time             (i_mon_time),

        // Monitor bus — aggregated with the scheduler-group stream by the
        // monbus arbiter (u_mon_arbiter) that drives the top-level mon_valid.
        .monbus_valid           (rdmon_mon_valid),
        .monbus_packet          (rdmon_mon_packet),
        .monbus_timestamp       (rdmon_mon_timestamp),
        .monbus_ready           (rdmon_mon_ready),

        // Status
        .busy                   (cfg_sts_rdeng_skid_busy),
        .active_transactions    (cfg_sts_rdeng_mon_active_txns),
        .error_count            (cfg_sts_rdeng_mon_error_count),
        .transaction_count      (cfg_sts_rdeng_mon_txn_count),

        // Perf-window readback is now sourced from the always-on bus meter +
        // counters (RDMON_PERF_*), so the heavy monitor's perf outputs are all
        // left unconnected here -- see the always-on perf block below.
        .window_active          (w_rd_mon_winact_nc),
        .window_cycles          (w_rd_mon_wincyc_nc),
        .perf_prod_cycles       (w_rd_mon_prod_nc),
        .perf_bp_cycles         (w_rd_mon_bp_nc),
        .perf_starv_cycles      (w_rd_mon_starv_nc),
        .perf_idle_cycles       (w_rd_mon_idle_nc),
        .perf_beat_count        (w_rd_mon_beat_nc),
        .perf_byte_count        (w_rd_mon_byte_nc),
        .perf_burst_count       (w_rd_mon_burst_nc),
        .cfg_conflict_error     (cfg_sts_rdeng_mon_conflict_error)
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

    // Data write AXI skid buffer + integrated datapath perf monitor (RFC Stage E).
    // See the read-side comment above: axi4_master_wr upgraded to
    // axi4_master_wr_mon, perf-only. Sized by WR_MON_MAX_TRANS -- see the
    // read-side comment: the bound is per-channel outstanding times channels,
    // read back through WRMON_PERF_* CSRs. W-channel cycle buckets match the
    // legacy write-side axi_bus_meter.
    axi4_master_wr_mon #(
        .SKID_DEPTH_AW          (SKID_DEPTH_AW),
        .SKID_DEPTH_W           (SKID_DEPTH_W),
        .SKID_DEPTH_B           (SKID_DEPTH_B),
        .AXI_ID_WIDTH           (IW),
        .AXI_ADDR_WIDTH         (AW),
        .AXI_DATA_WIDTH         (DW),
        .AXI_USER_WIDTH         (UW),
        .USE_MONITOR            (USE_AXI_MONITORS == 1),
        .UNIT_ID                (MON_UNIT_ID),
        .AGENT_ID               (WR_AXI_MON_AGENT_ID),
        .MAX_TRANSACTIONS       (WR_MON_MAX_TRANS),
        .ENABLE_FILTERING       (1),
        .ENABLE_ERROR_LOGIC     (DATA_MON_ENABLE_ERROR_LOGIC),
        .ENABLE_TIMEOUT_LOGIC   (DATA_MON_ENABLE_TIMEOUT_LOGIC),
        .ENABLE_COMPL_LOGIC     (DATA_MON_ENABLE_COMPL_LOGIC),
        .ENABLE_THRESHOLD_LOGIC (DATA_MON_ENABLE_THRESHOLD_LOGIC),
        .ENABLE_PERF_LOGIC      (DATA_MON_ENABLE_PERF_LOGIC),
        .ENABLE_DEBUG_LOGIC     (DATA_MON_ENABLE_DEBUG_LOGIC),
        .N_ADDR_RANGES          (N_ADDR_RANGES),
        .ADDR_RANGE_IS_ERROR    (MON_ADDR_RANGE_IS_ERROR)
    ) u_wr_axi_skid (
        .aclk                   (clk),
        .aresetn                (rst_n),
        // Observability tap added with the port; unused here.
        .debug_block_ready      (),
        .cam_clear              (cam_clear),

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

        // Monitor configuration (driven by the now-live WRMON_* CSR hooks)
        .cfg_monitor_enable     (int_cfg_wreng_mon_enable),
        .cfg_error_enable       (int_cfg_wreng_mon_err_enable | cfg_wreng_mon_addr_miss_en),
        .cfg_perf_enable        (int_cfg_wreng_mon_perf_enable),
        .cfg_compl_enable       (int_cfg_wreng_mon_compl_enable),
        .cfg_threshold_enable   (int_cfg_wreng_mon_thresh_enable),
        .cfg_debug_enable       (cfg_wreng_mon_addr_match_en),
        .cfg_timeout_enable     (int_cfg_wreng_mon_timeout_enable),
        .cfg_timeout_cycles     (16'(int_cfg_wreng_mon_timeout_cycles)),
        .cfg_latency_threshold  (int_cfg_wreng_mon_latency_thresh),

        .cfg_axi_pkt_mask       (int_cfg_wreng_mon_pkt_mask),
        .cfg_axi_err_select     (int_cfg_wreng_mon_err_select),
        .cfg_axi_error_mask     (int_cfg_wreng_mon_err_mask),
        .cfg_axi_timeout_mask   (int_cfg_wreng_mon_timeout_mask),
        .cfg_axi_compl_mask     (int_cfg_wreng_mon_compl_mask),
        .cfg_axi_thresh_mask    (int_cfg_wreng_mon_thresh_mask),
        .cfg_axi_perf_mask      (int_cfg_wreng_mon_perf_mask),
        .cfg_axi_addr_mask      (int_cfg_wreng_mon_addr_mask),
        .cfg_axi_debug_mask     (int_cfg_wreng_mon_debug_mask),

        // Address-range checker (allowlist) driven by the WRMON_ADDR_RANGE* CSRs.
        .cfg_addr_check_enable  (cfg_wreng_mon_addr_check_en),
        .cfg_addr_range_enable  (cfg_wreng_mon_addr_range_en[NAR-1:0]),
        .cfg_addr_range_low     (w_wrmon_range_low),
        .cfg_addr_range_high    (w_wrmon_range_high),

        // Perf-window control (RFC Stage E CSR route, WRMON_PERF_CTRL.RUN)
        // Hardware-closed window (shared controller; see the read monitor).
        .cfg_start_event_sel    (3'b000),
        .cfg_end_event_sel      (3'b000),
        .cfg_start_trigger      (w_perf_clear),
        .cfg_end_trigger        (w_perf_close),
        .cfg_window_force_close (1'b0),

        .i_mon_time             (i_mon_time),

        // Monitor bus — aggregated with the scheduler-group stream by the
        // monbus arbiter (u_mon_arbiter) that drives the top-level mon_valid.
        .monbus_valid           (wrmon_mon_valid),
        .monbus_packet          (wrmon_mon_packet),
        .monbus_timestamp       (wrmon_mon_timestamp),
        .monbus_ready           (wrmon_mon_ready),

        // Status
        .busy                   (cfg_sts_wreng_skid_busy),
        .active_transactions    (cfg_sts_wreng_mon_active_txns),
        .error_count            (cfg_sts_wreng_mon_error_count),
        .transaction_count      (cfg_sts_wreng_mon_txn_count),

        // Perf-window readback is now sourced from the always-on bus meter +
        // counters (WRMON_PERF_*); the heavy monitor's perf outputs are left
        // unconnected -- see the always-on perf block below.
        .window_active          (w_wr_mon_winact_nc),
        .window_cycles          (w_wr_mon_wincyc_nc),
        .perf_prod_cycles       (w_wr_mon_prod_nc),
        .perf_bp_cycles         (w_wr_mon_bp_nc),
        .perf_starv_cycles      (w_wr_mon_starv_nc),
        .perf_idle_cycles       (w_wr_mon_idle_nc),
        .perf_beat_count        (w_wr_mon_beat_nc),
        .perf_byte_count        (w_wr_mon_byte_nc),
        .perf_burst_count       (w_wr_mon_burst_nc),
        .cfg_conflict_error     (cfg_sts_wreng_mon_conflict_error)
    );

    //=========================================================================
    // RFC Stage C: per-channel perf buckets (in-core axi_bus_meter)
    //=========================================================================
    // Two axi_bus_meter blocks snoop the same R/W master buses as the aggregate
    // monitors above, attributing each productive/bp/starv/idle cycle to a
    // channel (read: m_axi_rd_rid[CHAN_WIDTH-1:0]; write: the write-engine
    // o_wr_active_channel_id sideband -- the W bus has no wid). They are
    // window-aligned with the aggregate monitor windows: i_freeze = ~RUN and a
    // one-cycle i_clear pulse on the RUN rising edge, so the per-channel buckets
    // summed over channels equal the aggregate buckets. This is the in-core
    // equivalent of the FPGA-char harness axi_bus_meter (RFC Stage E option 2);
    // the selected channel is muxed out via cfg_perf_ch_sel (indexed readout).
    // ==== Always-on datapath perf: bus meters + window/beat/byte/burst ========
    // Lightweight (a few counters/channel) and MUST survive USE_AXI_MONITORS=0 so
    // board (monitors-off) builds still measure datapath utilisation. Only the
    // heavy axi4_master_*_mon cones (USE_MONITOR) and the per-transaction latency
    // histograms (timestamp-FIFO area) stay gated. Window control = the shared
    // hardware-close controller: i_clear = w_perf_clear (RUN rising edge),
    // i_freeze = ~w_{rd,wr}_bucket_en.
            logic [15:0] rd_ch_prod  [NC];
            logic [15:0] rd_ch_bp    [NC];
            logic [15:0] rd_ch_starv [NC];
            logic [15:0] rd_ch_idle  [NC];
            logic [15:0] wr_ch_prod  [NC];
            logic [15:0] wr_ch_bp    [NC];
            logic [15:0] wr_ch_starv [NC];
            logic [15:0] wr_ch_idle  [NC];

            axi_bus_meter #(.NUM_CHANNELS(NC)) u_rd_bus_meter (
                .aclk            (clk),
                .aresetn         (rst_n),
                .i_clear         (w_perf_clear),
                .i_freeze        (~w_rd_bucket_en),  // data-owed gate (see above)
                .i_valid         (m_axi_rd_rvalid),
                .i_ready         (m_axi_rd_rready),
                .i_channel_id    (m_axi_rd_rid[CHAN_WIDTH-1:0]),
                .i_channel_valid (m_axi_rd_rvalid),
                // Aggregate buckets feed the RDMON_PERF CSRs (gated window);
                // beat/byte/burst stay on the monitor's full window.
                .o_agg_productive   (rdmon_perf_prod_cycles),
                .o_agg_backpressure (rdmon_perf_bp_cycles),
                .o_agg_starvation   (rdmon_perf_starv_cycles),
                .o_agg_idle         (rdmon_perf_idle_cycles),
                .o_ch_productive   (rd_ch_prod),
                .o_ch_backpressure (rd_ch_bp),
                .o_ch_starvation   (rd_ch_starv),
                .o_ch_idle         (rd_ch_idle),
                .o_ch_overflow     (rdmon_ch_overflow)
            );

            axi_bus_meter #(.NUM_CHANNELS(NC)) u_wr_bus_meter (
                .aclk            (clk),
                .aresetn         (rst_n),
                .i_clear         (w_perf_clear),
                .i_freeze        (~w_wr_bucket_en),  // data-owed gate (see above)
                .i_valid         (m_axi_wr_wvalid),
                .i_ready         (m_axi_wr_wready),
                .i_channel_id    (wr_active_channel_id),
                .i_channel_valid (wr_active_channel_valid),
                // Aggregate buckets feed the WRMON_PERF CSRs (gated window);
                // beat/byte/burst stay on the monitor's full window.
                .o_agg_productive   (wrmon_perf_prod_cycles),
                .o_agg_backpressure (wrmon_perf_bp_cycles),
                .o_agg_starvation   (wrmon_perf_starv_cycles),
                .o_agg_idle         (wrmon_perf_idle_cycles),
                .o_ch_productive   (wr_ch_prod),
                .o_ch_backpressure (wr_ch_bp),
                .o_ch_starvation   (wr_ch_starv),
                .o_ch_idle         (wr_ch_idle),
                .o_ch_overflow     (wrmon_ch_overflow)
            );

            // Indexed readout: present the cfg_perf_ch_sel-selected channel.
            always_comb begin
                rdmon_ch_prod_cycles  = rd_ch_prod [cfg_perf_ch_sel];
                rdmon_ch_bp_cycles    = rd_ch_bp   [cfg_perf_ch_sel];
                rdmon_ch_starv_cycles = rd_ch_starv[cfg_perf_ch_sel];
                rdmon_ch_idle_cycles  = rd_ch_idle [cfg_perf_ch_sel];
                wrmon_ch_prod_cycles  = wr_ch_prod [cfg_perf_ch_sel];
                wrmon_ch_bp_cycles    = wr_ch_bp   [cfg_perf_ch_sel];
                wrmon_ch_starv_cycles = wr_ch_starv[cfg_perf_ch_sel];
                wrmon_ch_idle_cycles  = wr_ch_idle [cfg_perf_ch_sel];
            end

            // ---- Always-on window / beat / byte / burst counters -------------
            // window_active reflects the shared hardware-close controller; the
            // live cycle + burst counters bracket the same span. beats ==
            // productive cycles by construction; bytes = beats * (DATA_WIDTH/8).
            logic [31:0] r_rd_win_cycles, r_wr_win_cycles;
            logic [31:0] r_rd_burst_cnt,  r_wr_burst_cnt;
            assign rdmon_perf_window_active = r_perf_win_active;
            assign wrmon_perf_window_active = r_perf_win_active;
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_rd_win_cycles <= 32'h0; r_wr_win_cycles <= 32'h0;
                    r_rd_burst_cnt  <= 32'h0; r_wr_burst_cnt  <= 32'h0;
                end else if (w_perf_clear) begin
                    r_rd_win_cycles <= 32'h0; r_wr_win_cycles <= 32'h0;
                    r_rd_burst_cnt  <= 32'h0; r_wr_burst_cnt  <= 32'h0;
                end else if (r_perf_win_active) begin
                    r_rd_win_cycles <= r_rd_win_cycles + 32'h1;
                    r_wr_win_cycles <= r_wr_win_cycles + 32'h1;
                    if (m_axi_rd_arvalid & m_axi_rd_arready)
                        r_rd_burst_cnt <= r_rd_burst_cnt + 32'h1;
                    if (m_axi_wr_awvalid & m_axi_wr_awready)
                        r_wr_burst_cnt <= r_wr_burst_cnt + 32'h1;
                end
            )
            assign rdmon_perf_window_cycles = r_rd_win_cycles;
            assign wrmon_perf_window_cycles = r_wr_win_cycles;
            assign rdmon_perf_burst_count   = r_rd_burst_cnt;
            assign wrmon_perf_burst_count   = r_wr_burst_cnt;
            assign rdmon_perf_beat_count    = rdmon_perf_prod_cycles;  // beats==productive
            assign wrmon_perf_beat_count    = wrmon_perf_prod_cycles;
            assign rdmon_perf_byte_count    = 64'(rdmon_perf_beat_count) * (DW/8);
            assign wrmon_perf_byte_count    = 64'(wrmon_perf_beat_count) * (DW/8);

            //=================================================================
            // RFC Stage D: per-transaction latency histograms (GATED)
            //=================================================================
            // Kept gated by USE_AXI_MONITORS (per-channel timestamp-FIFO area).
            // Read block: AR->first-R + AR->RLAST; write block: AW->B.
    generate
        if (USE_AXI_MONITORS == 1) begin : g_perf_hist
            logic [31:0] rd_hist_count, rd_hist_total;
            logic [31:0] wr_hist_count, wr_hist_total;

            axi_perf_latency_hist #(
                .ID_WIDTH        (IW),
                .NUM_CHANNELS    (NC),
                .MAX_OUTSTANDING (AR_MAX_OUTSTANDING),
                .NUM_BINS        (16),
                .IS_READ         (1'b1)
            ) u_rd_lat_hist (
                .aclk         (clk),
                .aresetn      (rst_n),
                // Backpressure request; not consumed here.
                .o_cmd_block  (),
                .i_clear      (w_perf_clear),
                .i_freeze     (~r_perf_win_active),
                .cmd_valid    (m_axi_rd_arvalid),
                .cmd_ready    (m_axi_rd_arready),
                .cmd_id       (m_axi_rd_arid),
                .data_valid   (m_axi_rd_rvalid),
                .data_ready   (m_axi_rd_rready),
                .data_last    (m_axi_rd_rlast),
                .data_id      (m_axi_rd_rid),
                .resp_valid   (1'b0),
                .resp_ready   (1'b0),
                .resp_id      ('0),
                .i_hist_metric(cfg_perf_hist_metric),
                .i_hist_bin   (cfg_perf_hist_bin),
                .o_hist_count (rd_hist_count),
                .o_hist_total (rd_hist_total)
            );

            axi_perf_latency_hist #(
                .ID_WIDTH        (IW),
                .NUM_CHANNELS    (NC),
                .MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
                .NUM_BINS        (16),
                .IS_READ         (1'b0)
            ) u_wr_lat_hist (
                .aclk         (clk),
                .aresetn      (rst_n),
                // Backpressure request; not consumed here.
                .o_cmd_block  (),
                .i_clear      (w_perf_clear),
                .i_freeze     (~r_perf_win_active),
                .cmd_valid    (m_axi_wr_awvalid),
                .cmd_ready    (m_axi_wr_awready),
                .cmd_id       (m_axi_wr_awid),
                .data_valid   (1'b0),
                .data_ready   (1'b0),
                .data_last    (1'b0),
                .data_id      ('0),
                .resp_valid   (m_axi_wr_bvalid),
                .resp_ready   (m_axi_wr_bready),
                .resp_id      (m_axi_wr_bid),
                .i_hist_metric(cfg_perf_hist_metric),
                .i_hist_bin   (cfg_perf_hist_bin),
                .o_hist_count (wr_hist_count),
                .o_hist_total (wr_hist_total)
            );

            assign perf_hist_data  = cfg_perf_hist_bus ? wr_hist_count : rd_hist_count;
            assign perf_hist_total = cfg_perf_hist_bus ? wr_hist_total : rd_hist_total;
        end else begin : g_no_perf_hist
            // Histograms disabled (monitors-off build): tie the hist readback
            // off. The bus meters, per-channel buckets, and window/beat/byte/
            // burst counters above are ALWAYS-ON, so RDMON/WRMON_PERF still count.
            assign perf_hist_data  = 32'h0;
            assign perf_hist_total = 32'h0;
        end
    endgenerate

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
