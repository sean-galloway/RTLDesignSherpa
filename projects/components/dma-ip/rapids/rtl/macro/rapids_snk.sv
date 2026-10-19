// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_snk
// Purpose: RAPIDS Beats SINK Core - Write-Only Data Engine (No Config/AXIL MonBus)
//
// Description:
//   Sink-only RAPIDS "beats" core combining:
//   - scheduler_group_array: 8 scheduler groups (write-only: EN_READ=0)
//   - snk_data_path_axis: AXIS -> SRAM -> AXI Write (network-to-memory)
//   - plane_mon_* in: the sink network plane's monitor packets (rtl/plane,
//     rapids TASK-024), client 1 of the half's monbus_arbiter; the plane and
//     its monitor-lite (agent 0x09) live in the top, not here
//
//   Derived from rapids_core by removing the source (read) data path and
//   configuring the scheduler array as write-only. This module contains
//   everything EXCEPT:
//   - Configuration registers (AXIL slave) - provided externally
//   - AXIL monitor bus converter - MonBus raw output provided
//
// Data Flow:
//   SINK PATH: AXIS Slave -> SRAM Controller -> AXI Write Engine -> Memory
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_spec/
// Subsystem: rapids_macro
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module rapids_snk #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int PIPELINE = 1,
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
    // Monitor synthesis gates (default 1 = production unchanged); see
    // scheduler_group_array.
    parameter int USE_AXI_MONITORS = 1,
    // Extended (row/col-major) addressing. Default ON, matching STREAM. Set 0
    // to compile the feature out entirely: the second-chunk fetch and the
    // run-base generators become unreachable and synthesize away, leaving
    // linear addressing verbatim.
    parameter int USE_ROW_COL_MAJOR_ADDRESSING = 1,
    parameter bit GEN_MON          = 1'b1,
    // Engine sharing (see scheduler_group_array): 1 = one descriptor / ctrlrd /
    // ctrlwr engine per half instead of one per channel.
    parameter int SHARED_ENGINES   = 1,
    // Tile packet header on the sink port (TILE_SPEC 11.5): rapids_tile_hdr_rx
    // strips each packet's header and passes cell-issued descriptors out on
    // desc_inj_* to the source half.
    parameter int TILE_HDR         = 0,
    // Straps toward RAPIDS (TILE_CREDITS = 1, needs TILE_HDR; TILE_SPEC 11.9,
    // rapids TASK-027): a TILE_LAND_FLITS landing space per cell between the
    // header decode and the data path, and credit returns for every beat this
    // half consumes (ret_*, to rapids_tile_credit_tx in rapids_core).
    parameter int TILE_CREDITS     = 0,
    parameter int TILE_LAND_FLITS  = 16,
    parameter int MON_MAX_TRANSACTIONS = 16,

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
    input  logic [31:0]                         cfg_sched_timeout_cycles,
    input  logic [7:0]                          cfg_sched_timeout_limit,
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

    // Control Engine Configuration (Phase 2, global)
    input  logic [8:0]                          cfg_ctrlrd_max_try,
    input  logic                                tick_1us,

    // Descriptor AXI Monitor Configuration
    input  logic                                cfg_desc_mon_enable,
    input  logic                                cfg_desc_mon_err_enable,
    input  logic                                cfg_desc_mon_perf_enable,
    input  logic                                cfg_desc_mon_perf_run,
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

    // Network plane monitor bus. The plane (rtl/plane: AXIS or CXS) owns
    // the network endpoint and its monitor-lite; its packets come back in
    // here as client 1 of this half's monbus_arbiter, exactly where the
    // in-module AXIS monitor used to sit (rapids TASK-015).
    input  logic                                plane_mon_valid,
    output logic                                plane_mon_ready,
    input  ocelus_common_pkg::monitor_packet_t   plane_mon_packet,
    input  ocelus_common_pkg::monbus_timestamp_t plane_mon_timestamp,

    // AXI Transfer Configuration
    input  logic [7:0]                          cfg_axi_wr_xfer_beats,
    input  logic [7:0]                          cfg_alloc_size,   // sink: SRAM alloc size per AXIS fill

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


    // Descriptor AXI Monitor perf window (DAXMON_PERF_* CSRs). The monitor
    // computes these; nothing collected them, so the CSRs read 0 in every
    // build.
    output logic                                 sts_desc_mon_win_active,
    output logic [31:0]                          sts_desc_mon_win_cycles,
    output logic [31:0]                          sts_desc_mon_prod_cycles,
    output logic [31:0]                          sts_desc_mon_bp_cycles,
    output logic [31:0]                          sts_desc_mon_starv_cycles,
    output logic [31:0]                          sts_desc_mon_idle_cycles,
    output logic [31:0]                          sts_desc_mon_beat_count,
    output logic [63:0]                          sts_desc_mon_byte_count,
    output logic [31:0]                          sts_desc_mon_burst_count,

    //=========================================================================
    // Sink Path - AXIS Slave Interface (Network -> SRAM); tid = channel id
    //=========================================================================
    input  logic [DW-1:0]               s_axis_tdata,
    input  logic [SW-1:0]               s_axis_tstrb,
    input  logic                        s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]    s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]  s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]  s_axis_tuser,
    input  logic                        s_axis_tvalid,
    output logic                        s_axis_tready,

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
    // AXI4 Master - Control Read (shared semaphore reads, 32-bit) [Phase 2]
    //=========================================================================
    output logic                        m_axi_ctrlrd_arvalid,
    input  logic                        m_axi_ctrlrd_arready,
    output logic [AW-1:0]               m_axi_ctrlrd_araddr,
    output logic [7:0]                  m_axi_ctrlrd_arlen,
    output logic [2:0]                  m_axi_ctrlrd_arsize,
    output logic [1:0]                  m_axi_ctrlrd_arburst,
    output logic [IW-1:0]               m_axi_ctrlrd_arid,
    output logic                        m_axi_ctrlrd_arlock,
    output logic [3:0]                  m_axi_ctrlrd_arcache,
    output logic [2:0]                  m_axi_ctrlrd_arprot,
    output logic [3:0]                  m_axi_ctrlrd_arqos,
    output logic [3:0]                  m_axi_ctrlrd_arregion,
    input  logic                        m_axi_ctrlrd_rvalid,
    output logic                        m_axi_ctrlrd_rready,
    input  logic [31:0]                 m_axi_ctrlrd_rdata,
    input  logic [1:0]                  m_axi_ctrlrd_rresp,
    input  logic                        m_axi_ctrlrd_rlast,
    input  logic [IW-1:0]               m_axi_ctrlrd_rid,

    //=========================================================================
    // AXI4 Master - Control Write (shared doorbell writes, 32-bit) [Phase 2]
    //=========================================================================
    output logic                        m_axi_ctrlwr_awvalid,
    input  logic                        m_axi_ctrlwr_awready,
    output logic [AW-1:0]               m_axi_ctrlwr_awaddr,
    output logic [7:0]                  m_axi_ctrlwr_awlen,
    output logic [2:0]                  m_axi_ctrlwr_awsize,
    output logic [1:0]                  m_axi_ctrlwr_awburst,
    output logic [IW-1:0]               m_axi_ctrlwr_awid,
    output logic                        m_axi_ctrlwr_awlock,
    output logic [3:0]                  m_axi_ctrlwr_awcache,
    output logic [2:0]                  m_axi_ctrlwr_awprot,
    output logic [3:0]                  m_axi_ctrlwr_awqos,
    output logic [3:0]                  m_axi_ctrlwr_awregion,
    output logic                        m_axi_ctrlwr_wvalid,
    input  logic                        m_axi_ctrlwr_wready,
    output logic [31:0]                 m_axi_ctrlwr_wdata,
    output logic [3:0]                  m_axi_ctrlwr_wstrb,
    output logic                        m_axi_ctrlwr_wlast,
    input  logic                        m_axi_ctrlwr_bvalid,
    output logic                        m_axi_ctrlwr_bready,
    input  logic [IW-1:0]               m_axi_ctrlwr_bid,
    input  logic [1:0]                  m_axi_ctrlwr_bresp,

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
    //   Full monitor bus (packet + side-band timestamp). The half aggregates
    //   its monitor sources through an internal monbus_arbiter so a single
    //   monitor stream leaves the half.
    //=========================================================================
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output ocelus_common_pkg::monitor_packet_t     mon_packet,
    output ocelus_common_pkg::monbus_timestamp_t   mon_timestamp,

    //=========================================================================
    // Debug Interface (Sink only)
    //=========================================================================
    output logic [NC-1:0]               dbg_snk_sram_bridge_pending,
    output logic [NC-1:0]               dbg_snk_sram_bridge_out_valid,
    output logic [31:0]                 dbg_axis_beats_received,
    output logic [31:0]                 dbg_axis_packets_received,

    // Active-channel sideband for per-channel bus instrumentation
    // (axi_bus_meter). The W bus carries no wid, so the write engine's
    // channel index must travel out of band to reach the meter at the top.
    output logic [CIW-1:0]              o_active_channel_id,
    output logic                        o_active_channel_valid,

    //=========================================================================
    // Tile header (TILE_HDR): cell-issued descriptors and sink-port status
    //=========================================================================
    output logic                        desc_inj_valid,
    output logic [CIW-1:0]              desc_inj_ch,
    output logic [255:0]                desc_inj_data,
    output logic [rapids_pkg::TILE_EXT_W:0] desc_inj_slot,   // TILE_CREDITS: {ok, sender slot}
    // Straps (TILE_CREDITS): credits this half returns -- [0] the header
    // decode (headers, dropped beats, refused desc packets), [1] the landing
    // space (each beat drained) -- and the senders' coordinates
    output logic [1:0]                  tile_ret_valid,
    output logic [1:0][rapids_pkg::TILE_EXT_W-1:0] tile_ret_slot,
    output logic [1:0]                  tile_ret_class,
    output logic                        tile_seen_valid,
    output logic [rapids_pkg::TILE_EXT_W-1:0] tile_seen_slot,
    output logic [rapids_pkg::TILE_COORD_W-1:0] tile_seen_coord,
    output logic                        sts_tile_land_overrun,    // sticky: a cell overran its strap
    // Stalled-data check (TILE_CREDITS): sink SRAM data that has not moved
    // for cfg_tile_stall_cycles (0 = off) is a MonBus error
    input  logic [31:0]                 cfg_tile_stall_cycles,
    output logic [NC-1:0]               sts_tile_stalled,
    // Credit packets to the source half's counters (TILE_SPEC 11.9)
    output logic                        credit_valid,
    output logic [rapids_pkg::TILE_COORD_W-1:0] credit_src,
    output logic                        credit_op,
    output logic [31:0]                 credit_count,
    output logic [1:0]                  credit_class,
    output logic                        sts_tile_unsupported,
    output logic                        sts_tile_tag_mismatch,
    output logic [15:0]                 sts_tile_desc_count,
    output logic [15:0]                 sts_tile_credit_count,
    input  logic                        tile_clr_unsupported,      // CSR write-1-to-clear pulses
    input  logic                        tile_clr_tag_mismatch
);

    //=========================================================================
    // Internal Signals - Scheduler Array ↔ Sink Data Path
    //=========================================================================

    // Scheduler → Sink Data Path (Write Requests)
    logic [NC-1:0]               sched_wr_valid;
    logic [NC-1:0]               sched_wr_ready;
    logic [NC-1:0][AW-1:0]       sched_wr_addr;
    logic [NC-1:0][31:0]         sched_wr_beats;
    // Packet records (TASK-019): scheduler array -> sink ingress
    logic [NC-1:0]               sched_wr_pkt_valid;
    logic [NC-1:0]               sched_wr_pkt_ready;
    logic [NC-1:0][31:0]         sched_wr_pkt_bytes;
    logic [NC-1:0][$clog2(DW/8)-1:0] sched_wr_pkt_offset;

    // Scheduler → Source Data Path (Read Requests) - UNUSED (write-only sink).
    // The array's read-request outputs are left unconnected; these wires exist
    // only to give the scheduler-array read outputs a landing pad if needed.
    logic [NC-1:0]               sched_rd_valid_unused;
    logic [NC-1:0][AW-1:0]       sched_rd_addr_unused;
    logic [NC-1:0][31:0]         sched_rd_beats_unused;

    // Sink Data Path → Scheduler (Write Completion)
    logic [NC-1:0]               sched_wr_done_strobe;
    logic [NC-1:0][31:0]         sched_wr_beats_done;
    logic [NC-1:0]               sched_wr_commit_strobe;
    logic [NC-1:0][31:0]         sched_wr_commit_beats;

    // Data Path → Scheduler (Error Signals)
    logic [NC-1:0]               sched_wr_error;

    //=========================================================================
    // Internal Monitor Bus - Scheduler Array -> Half MonBus Arbiter
    //=========================================================================
    logic                                    arr_mon_valid;
    logic                                    arr_mon_ready;
    ocelus_common_pkg::monitor_packet_t     arr_mon_packet;
    ocelus_common_pkg::monbus_timestamp_t   arr_mon_timestamp;

    //=========================================================================
    // Beats Scheduler Group Array (write-only: EN_READ=0, EN_WRITE=1)
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
        .MON_MAX_TRANSACTIONS   (MON_MAX_TRANSACTIONS),
        .EN_READ                (1'b0),
        .EN_WRITE               (1'b1),
        .USE_ROW_COL_MAJOR_ADDRESSING (USE_ROW_COL_MAJOR_ADDRESSING),
        .USE_AXI_MONITORS       (USE_AXI_MONITORS),
        .GEN_MON                (GEN_MON),
        .SHARED_ENGINES         (SHARED_ENGINES)
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
        .cfg_sched_timeout_limit(cfg_sched_timeout_limit),
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

        // Control Engine Configuration (Phase 2)
        .cfg_ctrlrd_max_try     (cfg_ctrlrd_max_try),
        .tick_1us               (tick_1us),

        // Descriptor AXI Monitor Configuration
        .cfg_desc_mon_enable        (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_perf_run      (cfg_desc_mon_perf_run),
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
        .sts_desc_mon_win_active   (sts_desc_mon_win_active),
        .sts_desc_mon_win_cycles   (sts_desc_mon_win_cycles),
        .sts_desc_mon_prod_cycles  (sts_desc_mon_prod_cycles),
        .sts_desc_mon_bp_cycles    (sts_desc_mon_bp_cycles),
        .sts_desc_mon_starv_cycles (sts_desc_mon_starv_cycles),
        .sts_desc_mon_idle_cycles  (sts_desc_mon_idle_cycles),
        .sts_desc_mon_beat_count   (sts_desc_mon_beat_count),
        .sts_desc_mon_byte_count   (sts_desc_mon_byte_count),
        .sts_desc_mon_burst_count  (sts_desc_mon_burst_count),

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

        // Shared Control Read AXI Master (Phase 2) -> core boundary
        .ctrlrd_axi_arvalid     (m_axi_ctrlrd_arvalid),
        .ctrlrd_axi_arready     (m_axi_ctrlrd_arready),
        .ctrlrd_axi_araddr      (m_axi_ctrlrd_araddr),
        .ctrlrd_axi_arlen       (m_axi_ctrlrd_arlen),
        .ctrlrd_axi_arsize      (m_axi_ctrlrd_arsize),
        .ctrlrd_axi_arburst     (m_axi_ctrlrd_arburst),
        .ctrlrd_axi_arid        (m_axi_ctrlrd_arid),
        .ctrlrd_axi_arlock      (m_axi_ctrlrd_arlock),
        .ctrlrd_axi_arcache     (m_axi_ctrlrd_arcache),
        .ctrlrd_axi_arprot      (m_axi_ctrlrd_arprot),
        .ctrlrd_axi_arqos       (m_axi_ctrlrd_arqos),
        .ctrlrd_axi_arregion    (m_axi_ctrlrd_arregion),
        .ctrlrd_axi_rvalid      (m_axi_ctrlrd_rvalid),
        .ctrlrd_axi_rready      (m_axi_ctrlrd_rready),
        .ctrlrd_axi_rdata       (m_axi_ctrlrd_rdata),
        .ctrlrd_axi_rresp       (m_axi_ctrlrd_rresp),
        .ctrlrd_axi_rlast       (m_axi_ctrlrd_rlast),
        .ctrlrd_axi_rid         (m_axi_ctrlrd_rid),

        // Shared Control Write AXI Master (Phase 2) -> core boundary
        .ctrlwr_axi_awvalid     (m_axi_ctrlwr_awvalid),
        .ctrlwr_axi_awready     (m_axi_ctrlwr_awready),
        .ctrlwr_axi_awaddr      (m_axi_ctrlwr_awaddr),
        .ctrlwr_axi_awlen       (m_axi_ctrlwr_awlen),
        .ctrlwr_axi_awsize      (m_axi_ctrlwr_awsize),
        .ctrlwr_axi_awburst     (m_axi_ctrlwr_awburst),
        .ctrlwr_axi_awid        (m_axi_ctrlwr_awid),
        .ctrlwr_axi_awlock      (m_axi_ctrlwr_awlock),
        .ctrlwr_axi_awcache     (m_axi_ctrlwr_awcache),
        .ctrlwr_axi_awprot      (m_axi_ctrlwr_awprot),
        .ctrlwr_axi_awqos       (m_axi_ctrlwr_awqos),
        .ctrlwr_axi_awregion    (m_axi_ctrlwr_awregion),
        .ctrlwr_axi_wvalid      (m_axi_ctrlwr_wvalid),
        .ctrlwr_axi_wready      (m_axi_ctrlwr_wready),
        .ctrlwr_axi_wdata       (m_axi_ctrlwr_wdata),
        .ctrlwr_axi_wstrb       (m_axi_ctrlwr_wstrb),
        .ctrlwr_axi_wlast       (m_axi_ctrlwr_wlast),
        .ctrlwr_axi_bvalid      (m_axi_ctrlwr_bvalid),
        .ctrlwr_axi_bready      (m_axi_ctrlwr_bready),
        .ctrlwr_axi_bid         (m_axi_ctrlwr_bid),
        .ctrlwr_axi_bresp       (m_axi_ctrlwr_bresp),

        // Data Read Interface (unused - write-only sink, no source data path)
        .sched_rd_valid         (sched_rd_valid_unused),
        .sched_rd_addr          (sched_rd_addr_unused),
        .sched_rd_beats         (sched_rd_beats_unused),
        /* verilator lint_off PINCONNECTEMPTY */
        .sched_rd_pkt_valid     (),
        .sched_rd_pkt_bytes     (),
        .sched_rd_pkt_offset    (),
        .sched_rd_pkt_tile      (),
        /* verilator lint_on PINCONNECTEMPTY */
        .sched_rd_pkt_ready     ({NC{1'b1}}),
        // Sink channels take no injected descriptors
        .desc_inj_valid         (1'b0),
        .desc_inj_ch            ('0),
        .desc_inj_data          ('0),
        /* verilator lint_off PINCONNECTEMPTY */
        .desc_inj_ready         (),
        /* verilator lint_on PINCONNECTEMPTY */
        /* verilator lint_off PINCONNECTEMPTY */
        .desc_inj_dropped       (),
        .desc_inj_dropped_clr   ('0),
        /* verilator lint_on PINCONNECTEMPTY */
        .tile_adv_done          (1'b0),         // tile credits live in the source half
        .tile_dest_legal        ('0),

        // Data Write Interface (to Sink Data Path)
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),
        .sched_wr_pkt_valid     (sched_wr_pkt_valid),
        .sched_wr_pkt_ready     (sched_wr_pkt_ready),
        .sched_wr_pkt_bytes     (sched_wr_pkt_bytes),
        .sched_wr_pkt_offset    (sched_wr_pkt_offset),

        // Completion Strobes
        // Read-completion inputs tied off (no source read engine present)
        .sched_rd_done_strobe   ('0),
        .sched_rd_beats_done    ('0),
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),
        .sched_wr_commit_strobe (sched_wr_commit_strobe),
        .sched_wr_commit_beats  (sched_wr_commit_beats),

        // Error Signals
        .sched_rd_error         ('0),
        .sched_wr_error         (sched_wr_error),

        // Monitor Bus -> internal half arbiter (client 0)
        .mon_valid              (arr_mon_valid),
        .mon_ready              (arr_mon_ready),
        .mon_packet             (arr_mon_packet),
        // No global monitor time source at core level: tie input to 0.
        .i_mon_time             ('0),
        .mon_timestamp          (arr_mon_timestamp)
    );

    //=========================================================================
    // Half MonBus Arbiter (aggregates the half's monitor sources)
    //
    // client[0] = scheduler group array monbus
    // client[1] = TIED-OFF placeholder reserved for the future data-path AXI
    //             monitor tap. CLIENTS=2 is used (CLIENTS=1 would make
    //             N=$clog2(1)=0 and produce illegal [N-1:0] ranges inside the
    //             arbiter). The unused client presents valid=0/packet=0/ts=0
    //             so it never wins a grant.
    //=========================================================================
    logic                                    mon_arb_valid_in    [3];
    logic                                    mon_arb_ready_in    [3];
    ocelus_common_pkg::monitor_packet_t     mon_arb_packet_in   [3];
    ocelus_common_pkg::monbus_timestamp_t   mon_arb_timestamp_in[3];

    // Client 0: scheduler group array
    assign mon_arb_valid_in[0]     = arr_mon_valid;
    assign mon_arb_packet_in[0]    = arr_mon_packet;
    assign mon_arb_timestamp_in[0] = arr_mon_timestamp;
    assign arr_mon_ready           = mon_arb_ready_in[0];

    // Client 1: the network plane's monitor-lite (AXIS or CXS)
    assign mon_arb_valid_in[1]     = plane_mon_valid;
    assign mon_arb_packet_in[1]    = plane_mon_packet;
    assign mon_arb_timestamp_in[1] = plane_mon_timestamp;
    assign plane_mon_ready         = mon_arb_ready_in[1];

    // Per-channel "data waiting in the sink SRAM", from snk_data_path_axis
    // below; read here by the stall check
    logic [NC-1:0]              w_chan_has_data;

    // Client 2: the stalled-data check when TILE_CREDITS, else tied off
    generate
    if (TILE_CREDITS != 0) begin : g_stall_mon
        // Client 2: the stalled-data check (TILE_SPEC 11.9). A channel's data
        // moves when a W beat of it is accepted.
        logic [NC-1:0] w_w_moved;
        always_comb begin
            for (int ch = 0; ch < NC; ch++)
                w_w_moved[ch] = m_axi_wr_wvalid && m_axi_wr_wready && o_active_channel_valid &&
                                (o_active_channel_id == CIW'(ch));
        end
        rapids_tile_stall_mon #(
            .NUM_CHANNELS (NC),
            .KIND         (1'b0),
            .MON_AGENT_ID (16'h000B),
            .MON_UNIT_ID  (8'(MON_UNIT_ID))
        ) u_stall_mon (
            .clk              (clk),
            .rst_n            (rst_n),
            .cfg_stall_cycles (cfg_tile_stall_cycles),
            .pending          (w_chan_has_data),
            .moved            (w_w_moved),
            .i_mon_time       ('0),
            .mon_valid        (mon_arb_valid_in[2]),
            .mon_ready        (mon_arb_ready_in[2]),
            .mon_packet       (mon_arb_packet_in[2]),
            .mon_timestamp    (mon_arb_timestamp_in[2]),
            .sts_stalled      (sts_tile_stalled)
        );
    end else begin : g_no_stall_mon
        assign mon_arb_valid_in[2]     = 1'b0;
        assign mon_arb_packet_in[2]    = '0;
        assign mon_arb_timestamp_in[2] = '0;
        assign sts_tile_stalled        = '0;
        logic unused_stall;
        assign unused_stall = &{1'b0, cfg_tile_stall_cycles, w_chan_has_data};
    end
    endgenerate
    // mon_arb_ready_in[2] intentionally unused

    monbus_arbiter #(
        .CLIENTS (3)
    ) u_mon_arbiter (
        .axi_aclk            (clk),
        .axi_aresetn         (rst_n),
        .block_arb           (1'b0),
        .monbus_valid_in     (mon_arb_valid_in),
        .monbus_ready_in     (mon_arb_ready_in),
        .monbus_packet_in    (mon_arb_packet_in),
        .monbus_timestamp_in (mon_arb_timestamp_in),
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
    // Sink Data Path (AXIS -> SRAM -> AXI Write -> Memory)
    //=========================================================================

    // Note: axi_write_engine expects burst_len per channel
    // Derive from cfg_axi_wr_xfer_beats (same for all channels in simplified flow)
    logic [NC-1:0][7:0] sched_wr_burst_len;
    always_comb begin
        for (int i = 0; i < NC; i++) begin
            sched_wr_burst_len[i] = cfg_axi_wr_xfer_beats;
        end
    end

    // AXI write-master AW sideband constants (the sink data path does not
    // produce these; drive standard AXI defaults so the m_axi_wr master is a
    // complete AXI4 interface).
    assign m_axi_wr_awlock   = 1'b0;
    assign m_axi_wr_awcache  = 4'b0011;
    assign m_axi_wr_awprot   = 3'b000;
    assign m_axi_wr_awqos    = 4'b0000;
    assign m_axi_wr_awregion = 4'b0000;

    //=========================================================================
    // The network endpoint lives in the plane (rtl/plane/rapids_plane_*), one
    // level up: the s_axis_* ports of this module are the plane-facing
    // AXIS stream, driven straight from the data path.
    //=========================================================================

    initial begin
        if ((TILE_CREDITS != 0) && (TILE_HDR == 0))
            $fatal(1, "rapids_snk: TILE_CREDITS = 1 needs TILE_HDR = 1");
        // the drain admits a landed packet only with TILE_LAND_FLITS + 4 beats free
        if ((TILE_CREDITS != 0) && (SD < TILE_LAND_FLITS + 4))
            $fatal(1, "rapids_snk: SRAM_DEPTH (per channel) must be >= TILE_LAND_FLITS + 4");
    end

    //=========================================================================
    // Tile header decode (TILE_HDR): between the plane and the data path
    //=========================================================================
    logic [DW-1:0]              w_dp_tdata;
    logic [SW-1:0]              w_dp_tstrb;
    logic                       w_dp_tlast;
    logic [AXIS_ID_WIDTH-1:0]   w_dp_tid;
    logic [AXIS_DEST_WIDTH-1:0] w_dp_tdest;
    logic [AXIS_USER_WIDTH-1:0] w_dp_tuser;
    logic                       w_dp_tvalid;
    logic                       w_dp_tready;
    // Header decode output (before the landing space, TILE_CREDITS)
    logic [DW-1:0]              w_hx_tdata;
    logic [SW-1:0]              w_hx_tstrb;
    logic                       w_hx_tlast;
    logic [AXIS_ID_WIDTH-1:0]   w_hx_tid;
    logic [AXIS_DEST_WIDTH-1:0] w_hx_tdest;
    logic [AXIS_USER_WIDTH-1:0] w_hx_tuser;
    logic                       w_hx_tvalid;
    logic                       w_hx_tready;
    logic [rapids_pkg::TILE_EXT_W-2:0] w_hx_tsender;
    logic [rapids_pkg::TILE_EXT_W-2:0] w_land_ret_slot;
    logic [NC-1:0]              w_chan_can_take;

    generate
    if (TILE_HDR != 0) begin : g_tile_hdr
        rapids_tile_hdr_rx #(
            .NUM_CHANNELS    (NC),
            .DATA_WIDTH      (DW),
            .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
            .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
            .AXIS_USER_WIDTH (AXIS_USER_WIDTH),
            .STRAPS          (TILE_CREDITS != 0)
        ) u_tile_hdr_rx (
            .clk              (clk),
            .rst_n            (rst_n),
            .s_axis_tdata     (s_axis_tdata),
            .s_axis_tstrb     (s_axis_tstrb),
            .s_axis_tlast     (s_axis_tlast),
            .s_axis_tid       (s_axis_tid),
            .s_axis_tdest     (s_axis_tdest),
            .s_axis_tuser     (s_axis_tuser),
            .s_axis_tvalid    (s_axis_tvalid),
            .s_axis_tready    (s_axis_tready),
            .m_axis_tdata     (w_hx_tdata),
            .m_axis_tstrb     (w_hx_tstrb),
            .m_axis_tlast     (w_hx_tlast),
            .m_axis_tid       (w_hx_tid),
            .m_axis_tdest     (w_hx_tdest),
            .m_axis_tuser     (w_hx_tuser),
            .m_axis_tvalid    (w_hx_tvalid),
            .m_axis_tready    (w_hx_tready),
            .m_axis_tsender   (w_hx_tsender),
            .desc_inj_valid   (desc_inj_valid),
            .desc_inj_ch      (desc_inj_ch),
            .desc_inj_data    (desc_inj_data),
            .desc_inj_slot    (desc_inj_slot),
            .ret_valid        (tile_ret_valid[0]),
            .ret_slot         (tile_ret_slot[0]),
            .ret_class        (tile_ret_class[0]),
            .seen_valid       (tile_seen_valid),
            .seen_slot        (tile_seen_slot),
            .seen_coord       (tile_seen_coord),
            .credit_valid     (credit_valid),
            .credit_src       (credit_src),
            .credit_op        (credit_op),
            .credit_count     (credit_count),
            .credit_class     (credit_class),
            .clr_unsupported  (tile_clr_unsupported),
            .clr_tag_mismatch (tile_clr_tag_mismatch),
            .sts_unsupported  (sts_tile_unsupported),
            .sts_tag_mismatch (sts_tile_tag_mismatch),
            .sts_desc_count   (sts_tile_desc_count),
            .sts_credit_count (sts_tile_credit_count)
        );

        if (TILE_CREDITS != 0) begin : g_landing
            // Landing space per cell; the header decode has taken the headers
            rapids_tile_landing #(
                .NUM_CHANNELS    (NC),
                .DATA_WIDTH      (DW),
                .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
                .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
                .AXIS_USER_WIDTH (AXIS_USER_WIDTH),
                .LAND_FLITS      (TILE_LAND_FLITS)
            ) u_tile_landing (
                .clk                (clk),
                .rst_n              (rst_n),
                .cfg_channel_enable (cfg_channel_enable),
                .s_axis_tdata       (w_hx_tdata),
                .s_axis_tstrb       (w_hx_tstrb),
                .s_axis_tlast       (w_hx_tlast),
                .s_axis_tid         (w_hx_tid),
                .s_axis_tdest       (w_hx_tdest),
                .s_axis_tuser       (w_hx_tuser),
                .s_axis_tsender     (w_hx_tsender),
                .s_axis_tvalid      (w_hx_tvalid),
                .s_axis_tready      (w_hx_tready),
                .m_axis_tdata       (w_dp_tdata),
                .m_axis_tstrb       (w_dp_tstrb),
                .m_axis_tlast       (w_dp_tlast),
                .m_axis_tid         (w_dp_tid),
                .m_axis_tdest       (w_dp_tdest),
                .m_axis_tuser       (w_dp_tuser),
                .m_axis_tvalid      (w_dp_tvalid),
                .m_axis_tready      (w_dp_tready),
                .chan_can_take      (w_chan_can_take),
                .ret_valid          (tile_ret_valid[1]),
                .ret_slot           (w_land_ret_slot),
                .sts_overrun        (sts_tile_land_overrun)
            );
            assign tile_ret_slot[1]  = rapids_pkg::TILE_EXT_W'(w_land_ret_slot);
            assign tile_ret_class[1] = 1'b0;
        end else begin : g_no_landing
            assign w_dp_tdata     = w_hx_tdata;
            assign w_dp_tstrb     = w_hx_tstrb;
            assign w_dp_tlast     = w_hx_tlast;
            assign w_dp_tid       = w_hx_tid;
            assign w_dp_tdest     = w_hx_tdest;
            assign w_dp_tuser     = w_hx_tuser;
            assign w_dp_tvalid    = w_hx_tvalid;
            assign w_hx_tready    = w_dp_tready;
            assign tile_ret_valid[1] = 1'b0;
            assign tile_ret_slot[1]  = '0;
            assign tile_ret_class[1] = 1'b0;
            assign sts_tile_land_overrun = 1'b0;
            logic unused_land;
            assign unused_land = &{1'b0, w_hx_tsender, w_chan_can_take, w_land_ret_slot};
            assign w_land_ret_slot = '0;
        end
    end else begin : g_no_tile_hdr
        assign w_dp_tdata     = s_axis_tdata;
        assign w_dp_tstrb     = s_axis_tstrb;
        assign w_dp_tlast     = s_axis_tlast;
        assign w_dp_tid       = s_axis_tid;
        assign w_dp_tdest     = s_axis_tdest;
        assign w_dp_tuser     = s_axis_tuser;
        assign w_dp_tvalid    = s_axis_tvalid;
        assign s_axis_tready  = w_dp_tready;
        assign desc_inj_valid = 1'b0;
        assign desc_inj_ch    = '0;
        assign desc_inj_data  = '0;
        assign desc_inj_slot  = '0;
        assign tile_ret_valid = '0;
        assign tile_ret_slot  = '0;
        assign tile_ret_class = '0;
        assign tile_seen_valid = 1'b0;
        assign tile_seen_slot  = '0;
        assign tile_seen_coord = '0;
        assign sts_tile_land_overrun = 1'b0;
        assign w_land_ret_slot = '0;
        assign w_hx_tsender    = '0;
        assign w_hx_tdata  = '0;
        assign w_hx_tstrb  = '0;
        assign w_hx_tlast  = 1'b0;
        assign w_hx_tid    = '0;
        assign w_hx_tdest  = '0;
        assign w_hx_tuser  = '0;
        assign w_hx_tvalid = 1'b0;
        assign w_hx_tready = 1'b0;
        logic unused_hx;
        assign unused_hx = &{1'b0, w_hx_tdata, w_hx_tstrb, w_hx_tlast, w_hx_tid, w_hx_tdest,
                             w_hx_tuser, w_hx_tvalid, w_hx_tready, w_hx_tsender, w_land_ret_slot,
                             w_chan_can_take};
        assign credit_valid   = 1'b0;
        assign credit_src     = '0;
        assign credit_op      = 1'b0;
        assign credit_count   = '0;
        assign credit_class   = '0;
        assign sts_tile_unsupported  = 1'b0;
        assign sts_tile_tag_mismatch = 1'b0;
        assign sts_tile_desc_count   = '0;
        assign sts_tile_credit_count = '0;
        logic unused_tile_clr;
        assign unused_tile_clr = &{1'b0, tile_clr_unsupported, tile_clr_tag_mismatch};
    end
    endgenerate

    snk_data_path_axis #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
        .W_PHASE_FIFO_DEPTH (W_PHASE_FIFO_DEPTH),
        .B_PHASE_FIFO_DEPTH (B_PHASE_FIFO_DEPTH),
        .AXIS_ID_WIDTH      (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH    (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH    (AXIS_USER_WIDTH),
        // a landed packet (at most TILE_LAND_FLITS beats, plus a spill) and
        // what the previous one may still hold in the shifter
        .TAKE_ROOM          ((TILE_CREDITS != 0) ? TILE_LAND_FLITS + 4 : 0)
    ) u_sink_data_path (
        .clk                (clk),
        .rst_n              (rst_n),

        // Configuration
        .cfg_axi_wr_xfer_beats(cfg_axi_wr_xfer_beats),
        .cfg_alloc_size     (cfg_alloc_size),
        .cfg_channel_reset  (cfg_channel_reset),

        // AXIS Slave Interface (Network ingress; tid = channel id)
        .s_axis_tdata       (w_dp_tdata),
        .s_axis_tstrb       (w_dp_tstrb),
        .s_axis_tlast       (w_dp_tlast),
        .s_axis_tid         (w_dp_tid),
        .s_axis_tdest       (w_dp_tdest),
        .s_axis_tuser       (w_dp_tuser),
        .s_axis_tvalid      (w_dp_tvalid),
        .s_axis_tready      (w_dp_tready),
        .chan_can_take      (w_chan_can_take),
        .chan_has_data      (w_chan_has_data),

        // Scheduler Interface
        .sched_wr_valid     (sched_wr_valid),
        .sched_wr_ready     (sched_wr_ready),
        .sched_wr_addr      (sched_wr_addr),
        .sched_wr_beats     (sched_wr_beats),
        .sched_wr_pkt_valid (sched_wr_pkt_valid),
        .sched_wr_pkt_ready (sched_wr_pkt_ready),
        .sched_wr_pkt_bytes (sched_wr_pkt_bytes),
        .sched_wr_pkt_offset(sched_wr_pkt_offset),
        .sched_wr_burst_len (sched_wr_burst_len),

        // Completion Interface
        .sched_wr_done_strobe(sched_wr_done_strobe),
        .sched_wr_beats_done (sched_wr_beats_done),
        .sched_wr_commit_strobe(sched_wr_commit_strobe),
        .sched_wr_commit_beats (sched_wr_commit_beats),
        .sched_wr_error     (sched_wr_error),

        // AXI Write Master
        .m_axi_awid         (m_axi_wr_awid),
        .m_axi_awaddr       (m_axi_wr_awaddr),
        .m_axi_awlen        (m_axi_wr_awlen),
        .m_axi_awsize       (m_axi_wr_awsize),
        .m_axi_awburst      (m_axi_wr_awburst),
        // AW sideband (awlock/awcache/awprot/awqos/awregion) not produced by the
        // sink data path; tied to standard AXI constants below.
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
        .dbg_sram_bridge_out_valid(dbg_snk_sram_bridge_out_valid),
        .dbg_axis_beats_received  (dbg_axis_beats_received),
        .dbg_axis_packets_received(dbg_axis_packets_received),

        // Active-channel sideband (RAPIDS TASK-001)
        .o_active_channel_id      (o_active_channel_id),
        .o_active_channel_valid   (o_active_channel_valid)
    );

    //=========================================================================
    // System-Level Status Logic
    //=========================================================================

    // System is idle when ALL schedulers are idle
    assign system_idle = &scheduler_idle;

endmodule : rapids_snk
