// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_src_beats
// Purpose: RAPIDS Beats Source (READ-ONLY) - Memory -> AXIS Out
//
// Description:
//   Source-only variant of rapids_core_beats. Combines:
//   - scheduler_group_array_beats: 8 scheduler groups (read-only, EN_WRITE=0)
//   - source_data_path: AXI Read -> SRAM -> AXIS Master (memory-to-network)
//
//   The sink (network-to-memory) data path is intentionally absent. The
//   scheduler array's sink-facing (write) scheduler inputs are tied off and its
//   sink-facing (write) outputs are left unconnected.
//
//   This module contains everything EXCEPT:
//   - Configuration registers (AXIL slave) - provided externally
//   - AXIL monitor bus converter - MonBus raw output provided
//
// Data Flow:
//   SOURCE PATH: Memory -> AXI Read Engine -> SRAM Controller -> AXIS Master
//
// Documentation: projects/components/dmas/rapids/docs/rapids_spec/
// Subsystem: rapids_macro_beats
//
// Author: sean galloway
// Created: 2026-07-03

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module rapids_src_beats #(
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
    // scheduler_group_array_beats.
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
    input  logic [7:0]                          cfg_drain_size,   // source: beats drained per AXIS packet

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
    // Source Path - AXIS Master Interface (SRAM -> Network); tid = channel id
    //=========================================================================
    output logic [DW-1:0]               m_axis_tdata,
    output logic [SW-1:0]               m_axis_tstrb,
    output logic                        m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]    m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]  m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]  m_axis_tuser,
    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,

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
    // Monitor Bus Interface (Raw Output - No AXIL Conversion)
    //   Full monitor bus (packet + side-band timestamp). The half aggregates
    //   its monitor sources through an internal monbus_arbiter so a single
    //   monitor stream leaves the half.
    //=========================================================================
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output monitor_common_pkg::monitor_packet_t     mon_packet,
    output monitor_common_pkg::monbus_timestamp_t   mon_timestamp,

    //=========================================================================
    // Debug Interface (Source Path)
    //=========================================================================
    output logic [NC-1:0]               dbg_rd_all_complete,
    output logic [31:0]                 dbg_r_beats_rcvd,
    output logic [31:0]                 dbg_sram_writes,
    output logic [NC-1:0]               dbg_arb_request,
    output logic [NC-1:0]               dbg_src_sram_bridge_pending,
    output logic [NC-1:0]               dbg_src_sram_bridge_out_valid,
    output logic [31:0]                 dbg_axis_beats_sent,
    output logic [31:0]                 dbg_axis_packets_sent
);

    //=========================================================================
    // Internal Signals - Scheduler Array <-> Source Data Path
    //=========================================================================

    // Scheduler -> Source Data Path (Read Requests)
    logic [NC-1:0]               sched_rd_valid;
    logic [NC-1:0][AW-1:0]       sched_rd_addr;
    logic [NC-1:0][31:0]         sched_rd_beats;

    // Source Data Path -> Scheduler (Read Completion)
    logic [NC-1:0]               sched_rd_done_strobe;
    logic [NC-1:0][31:0]         sched_rd_beats_done;

    // Source Data Path -> Scheduler (Error Signals)
    logic [NC-1:0]               sched_rd_error;

    //=========================================================================
    // Internal Monitor Bus - Scheduler Array -> Half MonBus Arbiter
    //=========================================================================
    logic                                    arr_mon_valid;
    logic                                    arr_mon_ready;
    monitor_common_pkg::monitor_packet_t     arr_mon_packet;
    monitor_common_pkg::monbus_timestamp_t   arr_mon_timestamp;

    //=========================================================================
    // Beats Scheduler Group Array (READ-ONLY: EN_WRITE=0)
    //=========================================================================

    scheduler_group_array_beats #(
        .NUM_CHANNELS           (NC),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (AW),
        .DATA_WIDTH             (DW),
        .AXI_ID_WIDTH           (IW),
        .EN_WRITE               (1'b0),  // Source-only: no sink write engine
        .DESC_MON_BASE_AGENT_ID (DESC_MON_BASE_AGENT_ID),
        .SCHED_MON_BASE_AGENT_ID(SCHED_MON_BASE_AGENT_ID),
        .DESC_AXI_MON_AGENT_ID  (DESC_AXI_MON_AGENT_ID),
        .MON_UNIT_ID            (MON_UNIT_ID),
        .MON_MAX_TRANSACTIONS   (MON_MAX_TRANSACTIONS),
        .USE_AXI_MONITORS       (USE_AXI_MONITORS),
        .GEN_MON                (GEN_MON)
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

        // Data Read Interface (to Source Data Path)
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),

        // Data Write Interface (Sink) - UNUSED in source-only build
        //   Outputs left unconnected; inputs tied off (no write engine present)
        .sched_wr_valid         (),
        .sched_wr_ready         ('0),
        .sched_wr_addr          (),
        .sched_wr_beats         (),

        // Completion Strobes
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),
        .sched_wr_done_strobe   ('0),
        .sched_wr_beats_done    ('0),
        .sched_wr_commit_strobe ('0),
        .sched_wr_commit_beats  ('0),

        // Error Signals
        .sched_rd_error         (sched_rd_error),
        .sched_wr_error         ('0),

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
    logic                                    mon_arb_valid_in    [2];
    logic                                    mon_arb_ready_in    [2];
    monitor_common_pkg::monitor_packet_t     mon_arb_packet_in   [2];
    monitor_common_pkg::monbus_timestamp_t   mon_arb_timestamp_in[2];

    // Client 0: scheduler group array
    assign mon_arb_valid_in[0]     = arr_mon_valid;
    assign mon_arb_packet_in[0]    = arr_mon_packet;
    assign mon_arb_timestamp_in[0] = arr_mon_timestamp;
    assign arr_mon_ready           = mon_arb_ready_in[0];

    // Client 1: tied-off placeholder (future data-path AXI monitor tap)
    assign mon_arb_valid_in[1]     = 1'b0;
    assign mon_arb_packet_in[1]    = '0;
    assign mon_arb_timestamp_in[1] = '0;
    // mon_arb_ready_in[1] intentionally unused

    monbus_arbiter #(
        .CLIENTS (2)
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
    // Source Data Path (Memory -> AXI Read -> SRAM -> AXIS Master)
    //=========================================================================

    src_data_path_axis_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING),
        .AXIS_ID_WIDTH      (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH    (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH    (AXIS_USER_WIDTH)
    ) u_source_data_path (
        .clk                (clk),
        .rst_n              (rst_n),

        // Configuration
        .cfg_axi_rd_xfer_beats(cfg_axi_rd_xfer_beats),
        .cfg_drain_size     (cfg_drain_size),

        // Scheduler Interface
        .sched_rd_valid     (sched_rd_valid),
        .sched_rd_addr      (sched_rd_addr),
        .sched_rd_beats     (sched_rd_beats),

        // Completion Interface
        .sched_rd_done_strobe(sched_rd_done_strobe),
        .sched_rd_beats_done (sched_rd_beats_done),
        .sched_rd_error      (sched_rd_error),

        // AXIS Master Interface (Network egress; tid = channel id)
        .m_axis_tdata       (m_axis_tdata),
        .m_axis_tstrb       (m_axis_tstrb),
        .m_axis_tlast       (m_axis_tlast),
        .m_axis_tid         (m_axis_tid),
        .m_axis_tdest       (m_axis_tdest),
        .m_axis_tuser       (m_axis_tuser),
        .m_axis_tvalid      (m_axis_tvalid),
        .m_axis_tready      (m_axis_tready),

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
        .dbg_sram_bridge_out_valid(dbg_src_sram_bridge_out_valid),
        .dbg_axis_beats_sent     (dbg_axis_beats_sent),
        .dbg_axis_packets_sent   (dbg_axis_packets_sent)
    );

    //=========================================================================
    // System-Level Status Logic
    //=========================================================================

    // System is idle when ALL schedulers are idle
    assign system_idle = &scheduler_idle;

endmodule : rapids_src_beats
