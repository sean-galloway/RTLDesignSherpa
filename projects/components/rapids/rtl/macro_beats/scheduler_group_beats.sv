// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: beats_scheduler_group
// Purpose: RAPIDS Beats Scheduler Group - Wrapper combining scheduler + descriptor engine
//
// Description:
//   Wrapper module combining scheduler and descriptor engine for a single channel.
//   Part of the RAPIDS Phase 1 "beats" architecture:
//   - Simplified from full RAPIDS for initial bring-up
//   - No program engine (using direct APB config)
//   - No control read/write engines
//   - MonBus aggregation from 2 sources (scheduler, descriptor_engine)
//
// Documentation: projects/components/rapids/docs/rapids_spec/
// Subsystem: rapids_macro_beats
//
// Author: sean galloway
// Created: 2025-01-10

`timescale 1ns / 1ps

// Import RAPIDS and monitor packages
`include "rapids_imports.svh"

module scheduler_group_beats #(
    parameter int CHANNEL_ID = 0,
    parameter int NUM_CHANNELS = 8,
    parameter int CHAN_WIDTH = $clog2(NUM_CHANNELS),
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    // Monitor Bus Parameters - Base IDs for each component
    parameter DESC_MON_AGENT_ID = 16,       // 0x10 - Descriptor Engine
    parameter SCHED_MON_AGENT_ID = 48,      // 0x30 - Scheduler
    parameter CTRLRD_MON_AGENT_ID = 32,     // 0x20 - Control Read Engine
    parameter CTRLWR_MON_AGENT_ID = 33,     // 0x21 - Control Write Engine
    parameter MON_UNIT_ID = 1,              // 0x1
    parameter MON_CHANNEL_ID = 0,           // Base channel ID
    // Direction enables (see scheduler_beats): SOURCE half = read-only (EN_WRITE=0),
    // SINK half = write-only (EN_READ=0); default both preserves mem-to-mem behavior.
    parameter bit EN_READ  = 1'b1,
    parameter bit EN_WRITE = 1'b1,
    // GEN_MON=0 gates this group's per-channel MonBus emitters (descriptor,
    // scheduler, ctrl-rd, ctrl-wr) to 0 so synthesis prunes the emitter cones.
    // Default 1 preserves production behavior.
    parameter bit GEN_MON = 1'b1
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    // APB Programming Interface (for initial descriptor fetch kick-off)
    input  logic                        apb_valid,
    output logic                        apb_ready,
    input  logic [ADDR_WIDTH-1:0]       apb_addr,

    // Configuration Interface
    input  logic                        cfg_channel_enable,
    input  logic                        cfg_channel_reset,

    // Scheduler Configuration
    input  logic [31:0]                 cfg_sched_timeout_cycles,
    input  logic [7:0]                  cfg_sched_timeout_limit,
    input  logic                        cfg_sched_timeout_enable,
    input  logic                        cfg_sched_err_enable,
    input  logic                        cfg_sched_compl_enable,
    input  logic                        cfg_sched_perf_enable,

    // Control Engine Configuration (Phase 2)
    input  logic [8:0]                  cfg_ctrlrd_max_try,     // ctrlrd poll retry budget (0-511)
    input  logic                        tick_1us,               // 1us tick for ctrlrd retry spacing

    // Descriptor Engine Configuration
    input  logic                        cfg_desceng_prefetch,
    input  logic [3:0]                  cfg_desceng_fifo_thresh,
    input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr0_base,
    input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr0_limit,
    input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr1_base,
    input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr1_limit,

    // Status Interface
    output logic                        descriptor_engine_idle,
    output logic                        scheduler_idle,
    output logic [6:0]                  scheduler_state,  // ONE-HOT encoding (7 bits)
    output logic                        sched_error,       // Scheduler error (sticky)

    // Descriptor Engine AXI4 Master Read Interface (256-bit descriptor fetch)
    output logic                        desc_ar_valid,
    input  logic                        desc_ar_ready,
    output logic [ADDR_WIDTH-1:0]       desc_ar_addr,
    output logic [7:0]                  desc_ar_len,
    output logic [2:0]                  desc_ar_size,
    output logic [1:0]                  desc_ar_burst,
    output logic [AXI_ID_WIDTH-1:0]     desc_ar_id,
    output logic                        desc_ar_lock,
    output logic [3:0]                  desc_ar_cache,
    output logic [2:0]                  desc_ar_prot,
    output logic [3:0]                  desc_ar_qos,
    output logic [3:0]                  desc_ar_region,

    // Descriptor Engine AXI Read Data Channel
    input  logic                        desc_r_valid,
    output logic                        desc_r_ready,
    input  logic [255:0]                desc_r_data,  // FIXED 256-bit descriptor width
    input  logic [1:0]                  desc_r_resp,
    input  logic                        desc_r_last,
    input  logic [AXI_ID_WIDTH-1:0]     desc_r_id,

    // Control Read Engine AXI4 Master (32-bit single-beat semaphore reads).
    // Arbitrated onto a single shared m_axi_ctrlrd master at the array level.
    output logic                        ctrlrd_ar_valid,
    input  logic                        ctrlrd_ar_ready,
    output logic [ADDR_WIDTH-1:0]       ctrlrd_ar_addr,
    output logic [7:0]                  ctrlrd_ar_len,
    output logic [2:0]                  ctrlrd_ar_size,
    output logic [1:0]                  ctrlrd_ar_burst,
    output logic [AXI_ID_WIDTH-1:0]     ctrlrd_ar_id,
    output logic                        ctrlrd_ar_lock,
    output logic [3:0]                  ctrlrd_ar_cache,
    output logic [2:0]                  ctrlrd_ar_prot,
    output logic [3:0]                  ctrlrd_ar_qos,
    output logic [3:0]                  ctrlrd_ar_region,
    input  logic                        ctrlrd_r_valid,
    output logic                        ctrlrd_r_ready,
    input  logic [31:0]                 ctrlrd_r_data,
    input  logic [AXI_ID_WIDTH-1:0]     ctrlrd_r_id,
    input  logic [1:0]                  ctrlrd_r_resp,
    input  logic                        ctrlrd_r_last,

    // Control Write Engine AXI4 Master (32-bit single-beat doorbell writes).
    // Arbitrated onto a single shared m_axi_ctrlwr master at the array level.
    output logic                        ctrlwr_aw_valid,
    input  logic                        ctrlwr_aw_ready,
    output logic [ADDR_WIDTH-1:0]       ctrlwr_aw_addr,
    output logic [7:0]                  ctrlwr_aw_len,
    output logic [2:0]                  ctrlwr_aw_size,
    output logic [1:0]                  ctrlwr_aw_burst,
    output logic [AXI_ID_WIDTH-1:0]     ctrlwr_aw_id,
    output logic                        ctrlwr_aw_lock,
    output logic [3:0]                  ctrlwr_aw_cache,
    output logic [2:0]                  ctrlwr_aw_prot,
    output logic [3:0]                  ctrlwr_aw_qos,
    output logic [3:0]                  ctrlwr_aw_region,
    output logic                        ctrlwr_w_valid,
    input  logic                        ctrlwr_w_ready,
    output logic [31:0]                 ctrlwr_w_data,
    output logic [3:0]                  ctrlwr_w_strb,
    output logic                        ctrlwr_w_last,
    input  logic                        ctrlwr_b_valid,
    output logic                        ctrlwr_b_ready,
    input  logic [AXI_ID_WIDTH-1:0]     ctrlwr_b_id,
    input  logic [1:0]                  ctrlwr_b_resp,

    // Data Read Interface (to AXI Read Engine)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        sched_rd_valid,
    output logic [ADDR_WIDTH-1:0]       sched_rd_addr,
    output logic [31:0]                 sched_rd_beats,

    // Data Write Interface (to AXI Write Engine)
    // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
    output logic                        sched_wr_valid,
    input  logic                        sched_wr_ready,
    output logic [ADDR_WIDTH-1:0]       sched_wr_addr,
    output logic [31:0]                 sched_wr_beats,

    // Data Path Completion Strobes
    input  logic                        sched_rd_done_strobe,
    input  logic [31:0]                 sched_rd_beats_done,
    input  logic                        sched_wr_done_strobe,
    input  logic [31:0]                 sched_wr_beats_done,
    input  logic                        sched_wr_commit_strobe,
    input  logic [31:0]                 sched_wr_commit_beats,

    // Error Signals (from AXI engines)
    input  logic                        sched_rd_error,
    input  logic                        sched_wr_error,

    // Free-running monitor-time broadcast (forwarded to all sub-reporters
    // and to the monbus arbiter timestamp side-band).
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Unified Monitor Bus Interface (128-bit packet + 64-bit side-band timestamp)
    output logic                                    mon_valid,
    input  logic                                    mon_ready,
    output monitor_common_pkg::monitor_packet_t     mon_packet,
    output monitor_common_pkg::monbus_timestamp_t   mon_timestamp
);

    //=========================================================================
    // Internal Signals - Component Interconnect
    //=========================================================================

    // Descriptor Engine to Scheduler Interface
    // Use component-based naming to avoid conflicts with external AXI signals
    // NOTE: Descriptor packet is FIXED at 256-bit width
    logic                        desceng_to_sched_valid;
    logic                        desceng_to_sched_ready;
    logic [255:0]                desceng_to_sched_packet;  // 256-bit descriptors
    logic                        desceng_to_sched_error;
    logic                        desceng_to_sched_eos;
    logic                        desceng_to_sched_eol;
    logic                        desceng_to_sched_eod;
    logic [1:0]                  desceng_to_sched_type;

    // Scheduler idle signal
    logic                        sched_channel_idle;

    //=========================================================================
    // Internal Signals - Monitor Bus Aggregation
    //=========================================================================
    // Use component-specific names to avoid conflicts with external AXI signals

    // Underlying *_beats reporters now emit native 128-bit packets and
    // expose per-packet side-band timestamps. Direct connection — no bridge.
    logic                                       desceng_mon_valid;
    logic                                       desceng_mon_ready;
    monitor_common_pkg::monitor_packet_t        desceng_mon_packet;
    monitor_common_pkg::monbus_timestamp_t      desceng_mon_timestamp;

    logic                                       sched_mon_valid;
    logic                                       sched_mon_ready;
    monitor_common_pkg::monitor_packet_t        sched_mon_packet;
    monitor_common_pkg::monbus_timestamp_t      sched_mon_timestamp;

    // Scheduler <-> Control Engine handshakes (Phase 2)
    logic                        sched_ctrlrd_valid, sched_ctrlrd_ready;
    logic [ADDR_WIDTH-1:0]       sched_ctrlrd_addr;
    logic [31:0]                 sched_ctrlrd_data, sched_ctrlrd_mask;
    logic                        sched_ctrlrd_error, sched_ctrlrd_idle;
    logic                        sched_ctrlwr_valid, sched_ctrlwr_ready;
    logic [ADDR_WIDTH-1:0]       sched_ctrlwr_addr;
    logic [31:0]                 sched_ctrlwr_data;
    logic                        sched_ctrlwr_error, sched_ctrlwr_idle;

    // Control engine MonBus (native 128-bit packet + side-band timestamp)
    logic                                       ctrlrd_mon_valid, ctrlrd_mon_ready;
    monitor_common_pkg::monitor_packet_t        ctrlrd_mon_packet;
    monitor_common_pkg::monbus_timestamp_t      ctrlrd_mon_timestamp;
    logic                                       ctrlwr_mon_valid, ctrlwr_mon_ready;
    monitor_common_pkg::monitor_packet_t        ctrlwr_mon_packet;
    monitor_common_pkg::monbus_timestamp_t      ctrlwr_mon_timestamp;

    //=========================================================================
    // Component Instantiations
    //=========================================================================

    // Single Descriptor Engine Instance
    // Note: descriptor_engine uses FIXED 256-bit descriptors (no DATA_WIDTH parameter)
    // NOTE: descriptor_engine_beats still has the legacy 4/8/6-bit MON_*
    // parameter widths and emits a 64-bit packet. Parameter casts are kept
    // narrow to match its declared widths; the bridge above widens the
    // packet output to 128 bits for the arbiter.
    descriptor_engine_beats #(
        .CHANNEL_ID             (CHANNEL_ID),
        .NUM_CHANNELS           (NUM_CHANNELS),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (ADDR_WIDTH),
        .AXI_ID_WIDTH           (AXI_ID_WIDTH),
        .MON_AGENT_ID           (16'(DESC_MON_AGENT_ID)),
        .MON_UNIT_ID            (8'(MON_UNIT_ID)),
        .MON_CHANNEL_ID         (9'(MON_CHANNEL_ID))
    ) u_descriptor_engine (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // APB interface (initial kick-off)
        .apb_valid              (apb_valid),
        .apb_ready              (apb_ready),
        .apb_addr               (apb_addr),

        // Scheduler interface
        .channel_idle           (sched_channel_idle),
        .descriptor_valid       (desceng_to_sched_valid),
        .descriptor_ready       (desceng_to_sched_ready),
        .descriptor_packet      (desceng_to_sched_packet),
        .descriptor_error       (desceng_to_sched_error),
        .descriptor_eos         (desceng_to_sched_eos),
        .descriptor_eol         (desceng_to_sched_eol),
        .descriptor_eod         (desceng_to_sched_eod),
        .descriptor_type        (desceng_to_sched_type),

        // AXI4 master read interface (descriptor fetch)
        .ar_valid               (desc_ar_valid),
        .ar_ready               (desc_ar_ready),
        .ar_addr                (desc_ar_addr),
        .ar_len                 (desc_ar_len),
        .ar_size                (desc_ar_size),
        .ar_burst               (desc_ar_burst),
        .ar_id                  (desc_ar_id),
        .ar_lock                (desc_ar_lock),
        .ar_cache               (desc_ar_cache),
        .ar_prot                (desc_ar_prot),
        .ar_qos                 (desc_ar_qos),
        .ar_region              (desc_ar_region),

        // AXI read data channel
        .r_valid                (desc_r_valid),
        .r_ready                (desc_r_ready),
        .r_data                 (desc_r_data),
        .r_resp                 (desc_r_resp),
        .r_last                 (desc_r_last),
        .r_id                   (desc_r_id),

        // Configuration
        .cfg_prefetch_enable    (cfg_desceng_prefetch),
        .cfg_fifo_threshold     (cfg_desceng_fifo_thresh),
        .cfg_addr0_base         (cfg_desceng_addr0_base),
        .cfg_addr0_limit        (cfg_desceng_addr0_limit),
        .cfg_addr1_base         (cfg_desceng_addr1_base),
        .cfg_addr1_limit        (cfg_desceng_addr1_limit),
        .cfg_channel_reset      (cfg_channel_reset),

        // Status
        .descriptor_engine_idle (descriptor_engine_idle),

        // Monitor bus (native 128-bit packet + side-band timestamp)
        .i_mon_time             (i_mon_time),
        .mon_valid              (desceng_mon_valid),
        .mon_ready              (desceng_mon_ready),
        .mon_packet             (desceng_mon_packet),
        .mon_timestamp          (desceng_mon_timestamp)
    );

    // Single Scheduler Instance (Simplified for RAPIDS Beats Phase 1)
    // NOTE: Scheduler module currently does NOT support runtime configuration for:
    //       - cfg_sched_err_enable (always enabled)
    //       - cfg_sched_compl_enable (always enabled)
    //       - cfg_sched_perf_enable (not implemented)
    //       These config inputs are defined for future enhancement.
    //
    //       Timeout configuration now uses runtime inputs:
    //       - cfg_sched_timeout_cycles (replaces TIMEOUT_CYCLES parameter)
    //       - cfg_sched_timeout_enable (can disable timeout detection)
    scheduler_beats #(
        .CHANNEL_ID             (CHANNEL_ID),
        .NUM_CHANNELS           (NUM_CHANNELS),
        .CHAN_WIDTH             (CHAN_WIDTH),
        .ADDR_WIDTH             (ADDR_WIDTH),
        .DATA_WIDTH             (DATA_WIDTH),
        .MON_AGENT_ID           (16'(SCHED_MON_AGENT_ID)),
        .MON_UNIT_ID            (8'(MON_UNIT_ID)),
        .MON_CHANNEL_ID         (9'(MON_CHANNEL_ID)),
        .EN_READ                (EN_READ),
        .EN_WRITE               (EN_WRITE)
    ) u_scheduler (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_channel_enable     (cfg_channel_enable),
        .cfg_channel_reset      (cfg_channel_reset),
        .cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit(cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable(cfg_sched_timeout_enable),

        // Status
        .scheduler_idle         (scheduler_idle),
        .scheduler_state        (scheduler_state),
        .sched_error            (sched_error),

        // Debug/observability taps (unused at this level)
        /* verilator lint_off PINCONNECTEMPTY */
        .dbg_descriptor_error   (),
        .dbg_read_error_sticky  (),
        .dbg_write_error_sticky (),
        .dbg_timeout_expired    (),
        /* verilator lint_on PINCONNECTEMPTY */

        // Descriptor engine interface
        .descriptor_valid       (desceng_to_sched_valid),
        .descriptor_ready       (desceng_to_sched_ready),
        .descriptor_packet      (desceng_to_sched_packet),
        .descriptor_error       (desceng_to_sched_error),

        // Data read interface (to AXI read engine)
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),

        // Data write interface (to AXI write engine)
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),

        // Data path completion strobes
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),
        .sched_wr_commit_strobe (sched_wr_commit_strobe),
        .sched_wr_commit_beats  (sched_wr_commit_beats),

        // Error signals
        .sched_rd_error         (sched_rd_error),
        .sched_wr_error         (sched_wr_error),

        // Control Read Engine handshake (CTRL_READ gate)
        .ctrlrd_valid           (sched_ctrlrd_valid),
        .ctrlrd_ready           (sched_ctrlrd_ready),
        .ctrlrd_addr            (sched_ctrlrd_addr),
        .ctrlrd_data            (sched_ctrlrd_data),
        .ctrlrd_mask            (sched_ctrlrd_mask),
        .ctrlrd_error           (sched_ctrlrd_error),
        .ctrlrd_idle            (sched_ctrlrd_idle),

        // Control Write Engine handshake (CTRL_WRITE doorbell)
        .ctrlwr_valid           (sched_ctrlwr_valid),
        .ctrlwr_ready           (sched_ctrlwr_ready),
        .ctrlwr_addr            (sched_ctrlwr_addr),
        .ctrlwr_data            (sched_ctrlwr_data),
        .ctrlwr_error           (sched_ctrlwr_error),
        .ctrlwr_idle            (sched_ctrlwr_idle),

        // Monitor bus (native 128-bit packet + side-band timestamp)
        .i_mon_time             (i_mon_time),
        .mon_valid              (sched_mon_valid),
        .mon_ready              (sched_mon_ready),
        .mon_packet             (sched_mon_packet),
        .mon_timestamp          (sched_mon_timestamp)
    );

    // Connect scheduler idle to descriptor engine channel_idle input
    assign sched_channel_idle = scheduler_idle;

    //=========================================================================
    // Control Read Engine (CTRL_READ gate) - shared 32-bit semaphore reads
    //=========================================================================
    ctrlrd_engine #(
        .CHANNEL_ID         (CHANNEL_ID),
        .NUM_CHANNELS       (NUM_CHANNELS),
        .CHAN_WIDTH         (CHAN_WIDTH),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .AXI_DATA_WIDTH     (32),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .MON_AGENT_ID       (16'(CTRLRD_MON_AGENT_ID)),
        .MON_UNIT_ID        (8'(MON_UNIT_ID)),
        .MON_CHANNEL_ID     (9'(MON_CHANNEL_ID))
    ) u_ctrlrd_engine (
        .clk                (clk),
        .rst_n              (rst_n),
        // Scheduler handshake
        .ctrlrd_valid       (sched_ctrlrd_valid),
        .ctrlrd_ready       (sched_ctrlrd_ready),
        .ctrlrd_pkt_addr    (sched_ctrlrd_addr),
        .ctrlrd_pkt_data    (sched_ctrlrd_data),
        .ctrlrd_pkt_mask    (sched_ctrlrd_mask),
        .ctrlrd_error       (sched_ctrlrd_error),
        /* verilator lint_off PINCONNECTEMPTY */
        .ctrlrd_result      (),  // scheduler gates on match/error, not the raw value
        /* verilator lint_on PINCONNECTEMPTY */
        // Config
        .cfg_ctrlrd_max_try (cfg_ctrlrd_max_try),
        .cfg_channel_reset  (cfg_channel_reset),
        .tick_1us           (tick_1us),
        .ctrlrd_engine_idle (sched_ctrlrd_idle),
        // AXI AR/R -> shared ctrlrd master (arbitrated at array level)
        .ar_valid           (ctrlrd_ar_valid),
        .ar_ready           (ctrlrd_ar_ready),
        .ar_addr            (ctrlrd_ar_addr),
        .ar_len             (ctrlrd_ar_len),
        .ar_size            (ctrlrd_ar_size),
        .ar_burst           (ctrlrd_ar_burst),
        .ar_id              (ctrlrd_ar_id),
        .ar_lock            (ctrlrd_ar_lock),
        .ar_cache           (ctrlrd_ar_cache),
        .ar_prot            (ctrlrd_ar_prot),
        .ar_qos             (ctrlrd_ar_qos),
        .ar_region          (ctrlrd_ar_region),
        .r_valid            (ctrlrd_r_valid),
        .r_ready            (ctrlrd_r_ready),
        .r_data             (ctrlrd_r_data),
        .r_id               (ctrlrd_r_id),
        .r_resp             (ctrlrd_r_resp),
        .r_last             (ctrlrd_r_last),
        // Monitor bus
        .i_mon_time         (i_mon_time),
        .mon_valid          (ctrlrd_mon_valid),
        .mon_ready          (ctrlrd_mon_ready),
        .mon_packet         (ctrlrd_mon_packet),
        .mon_timestamp      (ctrlrd_mon_timestamp)
    );

    //=========================================================================
    // Control Write Engine (CTRL_WRITE doorbell) - shared 32-bit writes
    //=========================================================================
    ctrlwr_engine #(
        .CHANNEL_ID         (CHANNEL_ID),
        .NUM_CHANNELS       (NUM_CHANNELS),
        .CHAN_WIDTH         (CHAN_WIDTH),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .MON_AGENT_ID       (16'(CTRLWR_MON_AGENT_ID)),
        .MON_UNIT_ID        (8'(MON_UNIT_ID)),
        .MON_CHANNEL_ID     (9'(MON_CHANNEL_ID))
    ) u_ctrlwr_engine (
        .clk                (clk),
        .rst_n              (rst_n),
        // Scheduler handshake
        .ctrlwr_valid       (sched_ctrlwr_valid),
        .ctrlwr_ready       (sched_ctrlwr_ready),
        .ctrlwr_pkt_addr    (sched_ctrlwr_addr),
        .ctrlwr_pkt_data    (sched_ctrlwr_data),
        .ctrlwr_error       (sched_ctrlwr_error),
        // Config
        .cfg_channel_reset  (cfg_channel_reset),
        .ctrlwr_engine_idle (sched_ctrlwr_idle),
        // AXI AW/W/B -> shared ctrlwr master (arbitrated at array level)
        .aw_valid           (ctrlwr_aw_valid),
        .aw_ready           (ctrlwr_aw_ready),
        .aw_addr            (ctrlwr_aw_addr),
        .aw_len             (ctrlwr_aw_len),
        .aw_size            (ctrlwr_aw_size),
        .aw_burst           (ctrlwr_aw_burst),
        .aw_id              (ctrlwr_aw_id),
        .aw_lock            (ctrlwr_aw_lock),
        .aw_cache           (ctrlwr_aw_cache),
        .aw_prot            (ctrlwr_aw_prot),
        .aw_qos             (ctrlwr_aw_qos),
        .aw_region          (ctrlwr_aw_region),
        .w_valid            (ctrlwr_w_valid),
        .w_ready            (ctrlwr_w_ready),
        .w_data             (ctrlwr_w_data),
        .w_strb             (ctrlwr_w_strb),
        .w_last             (ctrlwr_w_last),
        .b_valid            (ctrlwr_b_valid),
        .b_ready            (ctrlwr_b_ready),
        .b_id               (ctrlwr_b_id),
        .b_resp             (ctrlwr_b_resp),
        // Monitor bus
        .i_mon_time         (i_mon_time),
        .mon_valid          (ctrlwr_mon_valid),
        .mon_ready          (ctrlwr_mon_ready),
        .mon_packet         (ctrlwr_mon_packet),
        .mon_timestamp      (ctrlwr_mon_timestamp)
    );

    //=========================================================================
    // Monitor Bus Arbiter Instance (4 sources: descriptor_engine, scheduler,
    // ctrlrd_engine, ctrlwr_engine)
    //=========================================================================

    monbus_arbiter #(
        .CLIENTS                (4),
        .INPUT_SKID_ENABLE      (1),
        .OUTPUT_SKID_ENABLE     (1),
        .INPUT_SKID_DEPTH       (2),
        .OUTPUT_SKID_DEPTH      (2)
    ) u_monbus_aggregator (
        .axi_aclk               (clk),
        .axi_aresetn            (rst_n),
        .block_arb              (1'b0),
        // 4 sources: descriptor_engine, scheduler, ctrlrd_engine, ctrlwr_engine.
        // Each client carries packet + side-band timestamp atomically.
        // GEN_MON gates all four emitter valids to 0 -> the arbiter emits
        // valid=0 and synthesis prunes the upstream emitter register cones.
        .monbus_valid_in        ('{desceng_mon_valid & GEN_MON, sched_mon_valid & GEN_MON, ctrlrd_mon_valid & GEN_MON, ctrlwr_mon_valid & GEN_MON}),
        .monbus_ready_in        ('{desceng_mon_ready,     sched_mon_ready,     ctrlrd_mon_ready,     ctrlwr_mon_ready}),
        .monbus_packet_in       ('{desceng_mon_packet,    sched_mon_packet,    ctrlrd_mon_packet,    ctrlwr_mon_packet}),
        .monbus_timestamp_in    ('{desceng_mon_timestamp, sched_mon_timestamp, ctrlrd_mon_timestamp, ctrlwr_mon_timestamp}),
        .monbus_valid           (mon_valid),
        .monbus_ready           (mon_ready),
        .monbus_packet          (mon_packet),
        .monbus_timestamp       (mon_timestamp),
        .grant_valid            (/* UNUSED */),
        .grant                  (/* UNUSED */),
        .grant_id               (/* UNUSED */),
        .last_grant             (/* UNUSED */)
    );

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Monitor bus connectivity
    property monitor_bus_connected;
        @(posedge clk) disable iff (!rst_n)
        (desceng_mon_valid || sched_mon_valid) |-> ##[1:10] mon_valid;
    endproperty
    assert property (monitor_bus_connected);

    // Component integration
    property descriptor_scheduler_handshake;
        @(posedge clk) disable iff (!rst_n)
        (desceng_to_sched_valid && desceng_to_sched_ready) |-> ##[1:5] (scheduler_state != rapids_pkg::CH_IDLE);
    endproperty
    assert property (descriptor_scheduler_handshake);

    // Channel reset properties
    property channel_reset_propagation;
        @(posedge clk) disable iff (!rst_n)
        cfg_channel_reset |-> ##[1:100] (descriptor_engine_idle && scheduler_idle);
    endproperty
    assert property (channel_reset_propagation);

    property idle_signals_consistency;
        @(posedge clk) disable iff (!rst_n)
        (descriptor_engine_idle && scheduler_idle) |-> !cfg_channel_reset;
    endproperty
    assert property (idle_signals_consistency);
    `endif

endmodule : scheduler_group_beats
