//      // verilator_coverage annotation
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
            parameter MON_UNIT_ID = 1,              // 0x1
            parameter MON_CHANNEL_ID = 0            // Base channel ID
        ) (
            // Clock and Reset
 003696     input  logic                        clk,
 000012     input  logic                        rst_n,
        
            // APB Programming Interface (for initial descriptor fetch kick-off)
 000012     input  logic                        apb_valid,
 000020     output logic                        apb_ready,
%000000     input  logic [ADDR_WIDTH-1:0]       apb_addr,
        
            // Configuration Interface
 000012     input  logic                        cfg_channel_enable,
%000000     input  logic                        cfg_channel_reset,
        
            // Scheduler Configuration
%000000     input  logic [15:0]                 cfg_sched_timeout_cycles,
 000012     input  logic                        cfg_sched_timeout_enable,
 000012     input  logic                        cfg_sched_err_enable,
 000012     input  logic                        cfg_sched_compl_enable,
%000000     input  logic                        cfg_sched_perf_enable,
        
            // Descriptor Engine Configuration
 000012     input  logic                        cfg_desceng_prefetch,
%000000     input  logic [3:0]                  cfg_desceng_fifo_thresh,
%000000     input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr0_base,
%000000     input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr0_limit,
%000000     input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr1_base,
%000000     input  logic [ADDR_WIDTH-1:0]       cfg_desceng_addr1_limit,
        
            // Status Interface
 000024     output logic                        descriptor_engine_idle,
 000020     output logic                        scheduler_idle,
%000000     output logic [6:0]                  scheduler_state,  // ONE-HOT encoding (7 bits)
%000000     output logic                        sched_error,       // Scheduler error (sticky)
        
            // Descriptor Engine AXI4 Master Read Interface (256-bit descriptor fetch)
 000012     output logic                        desc_ar_valid,
 000012     input  logic                        desc_ar_ready,
%000000     output logic [ADDR_WIDTH-1:0]       desc_ar_addr,
%000000     output logic [7:0]                  desc_ar_len,
%000000     output logic [2:0]                  desc_ar_size,
%000000     output logic [1:0]                  desc_ar_burst,
%000000     output logic [AXI_ID_WIDTH-1:0]     desc_ar_id,
%000000     output logic                        desc_ar_lock,
%000000     output logic [3:0]                  desc_ar_cache,
%000000     output logic [2:0]                  desc_ar_prot,
%000000     output logic [3:0]                  desc_ar_qos,
%000000     output logic [3:0]                  desc_ar_region,
        
            // Descriptor Engine AXI Read Data Channel
 000012     input  logic                        desc_r_valid,
 000012     output logic                        desc_r_ready,
%000000     input  logic [255:0]                desc_r_data,  // FIXED 256-bit descriptor width
%000000     input  logic [1:0]                  desc_r_resp,
%000003     input  logic                        desc_r_last,
%000000     input  logic [AXI_ID_WIDTH-1:0]     desc_r_id,
        
            // Data Read Interface (to AXI Read Engine)
            // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
%000008     output logic                        sched_rd_valid,
%000000     output logic [ADDR_WIDTH-1:0]       sched_rd_addr,
%000000     output logic [31:0]                 sched_rd_beats,
        
            // Data Write Interface (to AXI Write Engine)
            // NOTE: Engine decides burst length internally, scheduler just tracks beats remaining
%000008     output logic                        sched_wr_valid,
 000012     input  logic                        sched_wr_ready,
%000000     output logic [ADDR_WIDTH-1:0]       sched_wr_addr,
%000000     output logic [31:0]                 sched_wr_beats,
        
            // Data Path Completion Strobes
%000004     input  logic                        sched_rd_done_strobe,
%000000     input  logic [31:0]                 sched_rd_beats_done,
%000004     input  logic                        sched_wr_done_strobe,
%000000     input  logic [31:0]                 sched_wr_beats_done,
        
            // Error Signals (from AXI engines)
%000000     input  logic                        sched_rd_error,
%000000     input  logic                        sched_wr_error,
        
            // Unified Monitor Bus Interface
 000028     output logic                        mon_valid,
 000012     input  logic                        mon_ready,
%000000     output logic [63:0]                 mon_packet
        );
        
            //=========================================================================
            // Internal Signals - Component Interconnect
            //=========================================================================
        
            // Descriptor Engine to Scheduler Interface
            // Use component-based naming to avoid conflicts with external AXI signals
            // NOTE: Descriptor packet is FIXED at 256-bit width
 000036     logic                        desceng_to_sched_valid;
 000020     logic                        desceng_to_sched_ready;
%000000     logic [255:0]                desceng_to_sched_packet;  // 256-bit descriptors
%000000     logic                        desceng_to_sched_error;
%000000     logic                        desceng_to_sched_eos;
%000000     logic                        desceng_to_sched_eol;
%000000     logic                        desceng_to_sched_eod;
%000000     logic [1:0]                  desceng_to_sched_type;
        
            // Scheduler idle signal
 000020     logic                        sched_channel_idle;
        
            //=========================================================================
            // Internal Signals - Monitor Bus Aggregation
            //=========================================================================
            // Use component-specific names to avoid conflicts with external AXI signals
        
 000012     logic                        desceng_mon_valid;
 000012     logic                        desceng_mon_ready;
%000000     logic [63:0]                 desceng_mon_packet;
        
 000016     logic                        sched_mon_valid;
 000012     logic                        sched_mon_ready;
%000000     logic [63:0]                 sched_mon_packet;
        
            //=========================================================================
            // Component Instantiations
            //=========================================================================
        
            // Single Descriptor Engine Instance
            // Note: descriptor_engine uses FIXED 256-bit descriptors (no DATA_WIDTH parameter)
            descriptor_engine_beats #(
                .CHANNEL_ID             (CHANNEL_ID),
                .NUM_CHANNELS           (NUM_CHANNELS),
                .CHAN_WIDTH             (CHAN_WIDTH),
                .ADDR_WIDTH             (ADDR_WIDTH),
                .AXI_ID_WIDTH           (AXI_ID_WIDTH),
                .MON_AGENT_ID           (8'(DESC_MON_AGENT_ID)),
                .MON_UNIT_ID            (4'(MON_UNIT_ID)),
                .MON_CHANNEL_ID         (6'(MON_CHANNEL_ID))
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
        
                // Monitor bus
                .mon_valid              (desceng_mon_valid),
                .mon_ready              (desceng_mon_ready),
                .mon_packet             (desceng_mon_packet)
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
                .MON_AGENT_ID           (8'(SCHED_MON_AGENT_ID)),
                .MON_UNIT_ID            (4'(MON_UNIT_ID)),
                .MON_CHANNEL_ID         (6'(MON_CHANNEL_ID))
            ) u_scheduler (
                .clk                    (clk),
                .rst_n                  (rst_n),
        
                // Configuration
                .cfg_channel_enable     (cfg_channel_enable),
                .cfg_channel_reset      (cfg_channel_reset),
                .cfg_sched_timeout_cycles(cfg_sched_timeout_cycles),
                .cfg_sched_timeout_enable(cfg_sched_timeout_enable),
        
                // Status
                .scheduler_idle         (scheduler_idle),
                .scheduler_state        (scheduler_state),
                .sched_error            (sched_error),
        
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
        
                // Error signals
                .sched_rd_error         (sched_rd_error),
                .sched_wr_error         (sched_wr_error),
        
                // Monitor bus
                .mon_valid              (sched_mon_valid),
                .mon_ready              (sched_mon_ready),
                .mon_packet             (sched_mon_packet)
            );
        
            // Connect scheduler idle to descriptor engine channel_idle input
            assign sched_channel_idle = scheduler_idle;
        
            //=========================================================================
            // Monitor Bus Arbiter Instance (2 sources: descriptor_engine, scheduler)
            //=========================================================================
        
            monbus_arbiter #(
                .CLIENTS                (2),
                .INPUT_SKID_ENABLE      (1),
                .OUTPUT_SKID_ENABLE     (1),
                .INPUT_SKID_DEPTH       (2),
                .OUTPUT_SKID_DEPTH      (2)
            ) u_monbus_aggregator (
                .axi_aclk               (clk),
                .axi_aresetn            (rst_n),
                .block_arb              (1'b0),
                // Direct connection to individual signals (2 sources only)
                .monbus_valid_in        ('{desceng_mon_valid, sched_mon_valid}),
                .monbus_ready_in        ('{desceng_mon_ready, sched_mon_ready}),
                .monbus_packet_in       ('{desceng_mon_packet, sched_mon_packet}),
                .monbus_valid           (mon_valid),
                .monbus_ready           (mon_ready),
                .monbus_packet          (mon_packet),
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
                (desceng_to_sched_valid && desceng_to_sched_ready) |-> ##[1:5] (scheduler_state != CH_IDLE);
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
        
