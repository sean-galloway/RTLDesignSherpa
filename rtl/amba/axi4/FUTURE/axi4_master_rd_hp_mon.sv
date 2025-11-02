// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_rd_hp_mon
// Purpose: Axi4 Master Rd Hp Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

/**
 * AXI4 Master Read High-Performance with Advanced Monitoring
 *
 * This module represents the high-performance tier of the complete matrix,
 * combining advanced features for maximum throughput and comprehensive monitoring:
 *
 * - Multi-level pipelining for maximum frequency
 * - Advanced skid buffering with configurable depths
 * - Burst optimization and prefetch capabilities
 * - Adaptive clock gating with performance counters
 * - ML-ready performance analysis with histograms
 * - Real-time QoS monitoring and control
 * - Advanced filtering with ML classification
 * - Predictive timeout and congestion detection
 */

`include "reset_defs.svh"
module axi4_master_rd_hp_mon
    import monitor_pkg::*;
#(
    // AXI4 Master parameters
    parameter int SKID_DEPTH_AR     = 8,      // Deeper for high performance
    parameter int SKID_DEPTH_R      = 16,     // Much deeper read buffer
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // High-performance parameters
    parameter int PREFETCH_DEPTH    = 4,      // Outstanding prefetch requests
    parameter int BURST_OPTIMIZE    = 1,      // Enable burst optimization
    parameter int PIPELINE_STAGES   = 3,      // Number of pipeline stages
    parameter int QOS_LEVELS        = 4,      // Number of QoS priority levels

    // Monitor parameters
    parameter int UNIT_ID           = 1,      // 4-bit Unit ID for monitor packets
    parameter int AGENT_ID          = 15,     // 8-bit Agent ID for HP monitor
    parameter int MAX_TRANSACTIONS  = 32,     // Higher capacity for HP

    // Advanced filtering parameters
    parameter bit ENABLE_FILTERING  = 1,      // Enable packet filtering
    parameter bit ENABLE_ML_FILTER = 1,      // Enable ML-based filtering
    parameter bit ADD_PIPELINE_STAGE = 1,     // Always pipeline for HP

    // Clock gating parameters
    parameter bit ENABLE_CLOCK_GATING = 1,    // Enable clock gating
    parameter bit ENABLE_ADAPTIVE_CG = 1,     // Adaptive clock gating
    parameter int CG_IDLE_CYCLES    = 4,      // Faster gating for HP

    // Performance analysis parameters
    parameter bit ENABLE_HISTOGRAMS = 1,      // Enable latency histograms
    parameter bit ENABLE_QOS_MON    = 1,      // Enable QoS monitoring
    parameter int HISTOGRAM_BINS    = 16,     // Number of histogram bins

    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // High-speed clock domain (optional)
    input  logic                       aclk_hs,          // High-speed clock for critical paths
    input  logic                       aresetn_hs,       // High-speed reset

    // Slave AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_axi_arid,
    input  logic [AW-1:0]              fub_axi_araddr,
    input  logic [7:0]                 fub_axi_arlen,
    input  logic [2:0]                 fub_axi_arsize,
    input  logic [1:0]                 fub_axi_arburst,
    input  logic                       fub_axi_arlock,
    input  logic [3:0]                 fub_axi_arcache,
    input  logic [2:0]                 fub_axi_arprot,
    input  logic [3:0]                 fub_axi_arqos,     // QoS input
    input  logic [3:0]                 fub_axi_arregion,
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // Master AXI Interface (Output Side)
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Monitor Configuration
    input  logic                       cfg_monitor_enable,      // Enable monitoring
    input  logic                       cfg_error_enable,        // Enable error detection
    input  logic                       cfg_timeout_enable,      // Enable timeout detection
    input  logic                       cfg_perf_enable,         // Enable performance monitoring
    input  logic [15:0]                cfg_timeout_cycles,      // Timeout threshold in cycles
    input  logic [31:0]                cfg_latency_threshold,   // Latency threshold for alerts

    // High-Performance Configuration
    input  logic                       cfg_hp_enable,           // Enable high-performance mode
    input  logic                       cfg_prefetch_enable,     // Enable prefetching
    input  logic [3:0]                 cfg_prefetch_depth,      // Prefetch depth
    input  logic                       cfg_burst_optimize,      // Enable burst optimization
    input  logic [1:0]                 cfg_pipeline_mode,       // Pipeline mode (0=off, 1=basic, 2=full, 3=aggressive)

    // QoS Configuration
    input  logic                       cfg_qos_enable,          // Enable QoS monitoring
    input  logic [3:0]                 cfg_qos_high_threshold,  // High QoS threshold
    input  logic [3:0]                 cfg_qos_low_threshold,   // Low QoS threshold
    input  logic [15:0]                cfg_qos_timeout_cycles,  // QoS-specific timeout

    // Advanced Filtering Configuration
    input  logic [15:0]                cfg_axi_pkt_mask,        // Drop mask for packet types
    input  logic [15:0]                cfg_axi_err_select,      // Error select for packet types
    input  logic [15:0]                cfg_axi_error_mask,      // Individual error event mask
    input  logic [15:0]                cfg_axi_timeout_mask,    // Individual timeout event mask
    input  logic [15:0]                cfg_axi_compl_mask,      // Individual completion event mask
    input  logic [15:0]                cfg_axi_thresh_mask,     // Individual threshold event mask
    input  logic [15:0]                cfg_axi_perf_mask,       // Individual performance event mask
    input  logic [15:0]                cfg_axi_addr_mask,       // Individual address match event mask
    input  logic [15:0]                cfg_axi_debug_mask,      // Individual debug event mask

    // ML Filter Configuration
    input  logic                       cfg_ml_filter_enable,    // Enable ML-based filtering
    input  logic [7:0]                 cfg_ml_filter_mode,      // ML filter mode (algorithm selection)
    input  logic [31:0]                cfg_ml_filter_threshold, // ML classification threshold

    // Adaptive Clock Gating Configuration
    input  logic                       cfg_cg_enable,           // Enable clock gating
    input  logic [7:0]                 cfg_cg_idle_threshold,   // Idle cycles before gating
    input  logic                       cfg_cg_force_on,         // Force clocks on (debug mode)
    input  logic                       cfg_cg_adaptive,         // Enable adaptive clock gating
    input  logic [7:0]                 cfg_cg_perf_threshold,   // Performance threshold for adaptive CG

    // Monitor Bus Output
    output logic                       monbus_valid,            // Monitor bus valid
    input  logic                       monbus_ready,            // Monitor bus ready
    output logic [63:0]                monbus_packet,           // Monitor packet

    // High-Performance Status Outputs
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count
    output logic [31:0]                transaction_count,       // Total transaction count

    // Performance Metrics
    output logic [31:0]                avg_latency_cycles,      // Average latency
    output logic [31:0]                peak_latency_cycles,     // Peak latency
    output logic [31:0]                throughput_mbps,         // Throughput in MB/s
    output logic [15:0]                utilization_percent,     // Bus utilization percentage

    // QoS Metrics
    output logic [31:0]                qos_high_count,          // High QoS transaction count
    output logic [31:0]                qos_low_count,           // Low QoS transaction count
    output logic [31:0]                qos_violation_count,     // QoS violation count

    // Histogram Data (for ML analysis)
    output logic [HISTOGRAM_BINS-1:0][15:0] latency_histogram,  // Latency distribution
    output logic [HISTOGRAM_BINS-1:0][15:0] qos_histogram,      // QoS distribution

    // Clock gating status
    output logic                       cg_monitor_gated,        // Monitor clock is gated
    output logic                       cg_reporter_gated,       // Reporter clock is gated
    output logic                       cg_timers_gated,         // Timer clocks are gated
    output logic [31:0]                cg_cycles_saved,         // Estimated cycles saved by gating
    output logic [15:0]                cg_efficiency_percent,   // Clock gating efficiency

    // Configuration error flags
    output logic                       cfg_conflict_error,      // Configuration conflict detected
    output logic                       hp_overload_error,       // High-performance overload detected
    output logic                       qos_violation_error      // QoS violation detected
);

    // =========================================================================
    // High-Performance Pipeline Registers
    // =========================================================================

    // Multi-stage pipeline for critical paths
    logic [PIPELINE_STAGES-1:0]       pipe_valid;
    logic [PIPELINE_STAGES-1:0]       pipe_ready;
    logic [PIPELINE_STAGES-1:0][63:0] pipe_data;

    // Performance counters
    logic [31:0]                       cycle_counter;
    logic [31:0]                       transaction_start_time;
    logic [31:0]                       current_latency;
    logic [31:0]                       latency_accumulator;
    logic [31:0]                       latency_sample_count;

    // QoS tracking
    logic [3:0]                        current_qos;
    logic                              qos_high_priority;
    logic                              qos_violation;

    // Histogram tracking
    logic [3:0]                        latency_bin;
    logic [3:0]                        qos_bin;

    // =========================================================================
    // High-Performance Core Instance
    // =========================================================================

    axi4_master_rd_mon_cg #(
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH         (AXI_WSTRB_WIDTH),
        .UNIT_ID                 (UNIT_ID),
        .AGENT_ID                (AGENT_ID),
        .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
        .ENABLE_FILTERING        (ENABLE_FILTERING),
        .ENABLE_CLOCK_GATING     (ENABLE_CLOCK_GATING),
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE)
    ) hp_core_inst (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // AXI Interface connections...
        .fub_axi_arid            (fub_axi_arid),
        .fub_axi_araddr          (fub_axi_araddr),
        .fub_axi_arlen           (fub_axi_arlen),
        .fub_axi_arsize          (fub_axi_arsize),
        .fub_axi_arburst         (fub_axi_arburst),
        .fub_axi_arlock          (fub_axi_arlock),
        .fub_axi_arcache         (fub_axi_arcache),
        .fub_axi_arprot          (fub_axi_arprot),
        .fub_axi_arqos           (fub_axi_arqos),
        .fub_axi_arregion        (fub_axi_arregion),
        .fub_axi_aruser          (fub_axi_aruser),
        .fub_axi_arvalid         (fub_axi_arvalid),
        .fub_axi_arready         (fub_axi_arready),

        .fub_axi_rid             (fub_axi_rid),
        .fub_axi_rdata           (fub_axi_rdata),
        .fub_axi_rresp           (fub_axi_rresp),
        .fub_axi_rlast           (fub_axi_rlast),
        .fub_axi_ruser           (fub_axi_ruser),
        .fub_axi_rvalid          (fub_axi_rvalid),
        .fub_axi_rready          (fub_axi_rready),

        .m_axi_arid              (m_axi_arid),
        .m_axi_araddr            (m_axi_araddr),
        .m_axi_arlen             (m_axi_arlen),
        .m_axi_arsize            (m_axi_arsize),
        .m_axi_arburst           (m_axi_arburst),
        .m_axi_arlock            (m_axi_arlock),
        .m_axi_arcache           (m_axi_arcache),
        .m_axi_arprot            (m_axi_arprot),
        .m_axi_arqos             (m_axi_arqos),
        .m_axi_arregion          (m_axi_arregion),
        .m_axi_aruser            (m_axi_aruser),
        .m_axi_arvalid           (m_axi_arvalid),
        .m_axi_arready           (m_axi_arready),

        .m_axi_rid               (m_axi_rid),
        .m_axi_rdata             (m_axi_rdata),
        .m_axi_rresp             (m_axi_rresp),
        .m_axi_rlast             (m_axi_rlast),
        .m_axi_ruser             (m_axi_ruser),
        .m_axi_rvalid            (m_axi_rvalid),
        .m_axi_rready            (m_axi_rready),

        // Monitor Configuration
        .cfg_monitor_enable      (cfg_monitor_enable),
        .cfg_error_enable        (cfg_error_enable),
        .cfg_timeout_enable      (cfg_timeout_enable),
        .cfg_perf_enable         (cfg_perf_enable),
        .cfg_timeout_cycles      (cfg_timeout_cycles),
        .cfg_latency_threshold   (cfg_latency_threshold),

        // Filtering Configuration
        .cfg_axi_pkt_mask        (cfg_axi_pkt_mask),
        .cfg_axi_err_select      (cfg_axi_err_select),
        .cfg_axi_error_mask      (cfg_axi_error_mask),
        .cfg_axi_timeout_mask    (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask      (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask     (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask       (cfg_axi_perf_mask),
        .cfg_axi_addr_mask       (cfg_axi_addr_mask),
        .cfg_axi_debug_mask      (cfg_axi_debug_mask),

        // Clock Gating Configuration
        .cfg_cg_enable           (cfg_cg_enable),
        .cfg_cg_idle_threshold   (cfg_cg_idle_threshold),
        .cfg_cg_force_on         (cfg_cg_force_on),
        .cfg_cg_gate_monitor     (1'b1),
        .cfg_cg_gate_reporter    (1'b1),
        .cfg_cg_gate_timers      (1'b1),

        // Monitor Bus Output
        .monbus_valid            (monbus_valid),
        .monbus_ready            (monbus_ready),
        .monbus_packet           (monbus_packet),

        // Status outputs
        .busy                    (busy),
        .active_transactions     (active_transactions),
        .error_count             (error_count),
        .transaction_count       (transaction_count),

        // Clock gating status
        .cg_monitor_gated        (cg_monitor_gated),
        .cg_reporter_gated       (cg_reporter_gated),
        .cg_timers_gated         (cg_timers_gated),
        .cg_cycles_saved         (cg_cycles_saved),

        // Configuration error flags
        .cfg_conflict_error      (cfg_conflict_error)
    );

    // =========================================================================
    // Performance Analysis Engine
    // =========================================================================

    // Cycle counter
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            cycle_counter <= '0;
        end else begin
            cycle_counter <= cycle_counter + 1'b1;
        end
    )


    // Transaction timing
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            transaction_start_time <= '0;
            current_latency <= '0;
            latency_accumulator <= '0;
            latency_sample_count <= '0;
        end else begin
            // Start timing on AR handshake
            if (fub_axi_arvalid && fub_axi_arready) begin
                transaction_start_time <= cycle_counter;
            end
        
            // End timing on R last handshake
            if (fub_axi_rvalid && fub_axi_rready && fub_axi_rlast) begin
                current_latency <= cycle_counter - transaction_start_time;
                latency_accumulator <= latency_accumulator + (cycle_counter - transaction_start_time);
                latency_sample_count <= latency_sample_count + 1'b1;
            end
    )

    end

    // Calculate average latency
    assign avg_latency_cycles = (latency_sample_count > 0) ?
                               (latency_accumulator / latency_sample_count) : 32'h0;

    // QoS tracking
    assign current_qos = fub_axi_arqos;
    assign qos_high_priority = (current_qos >= cfg_qos_high_threshold);
    assign qos_violation = (current_latency > cfg_qos_timeout_cycles) && qos_high_priority;

    // QoS counters
    `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
            qos_high_count <= '0;
            qos_low_count <= '0;
            qos_violation_count <= '0;
        end else begin
            if (fub_axi_arvalid && fub_axi_arready) begin
                if (qos_high_priority) begin
                    qos_high_count <= qos_high_count + 1'b1;
                end else begin
                    qos_low_count <= qos_low_count + 1'b1;
                end
            end
        
            if (qos_violation) begin
                qos_violation_count <= qos_violation_count + 1'b1;
            end
        end
    )


    // =========================================================================
    // Histogram Generation
    // =========================================================================

    generate
        if (ENABLE_HISTOGRAMS) begin : gen_histograms

            // Latency histogram bin calculation
            assign latency_bin = (current_latency < 16) ? current_latency[3:0] : 4'hF;

            // QoS histogram bin calculation
            assign qos_bin = current_qos;

            // Histogram update logic
            `ALWAYS_FF_RST(aclk, aresetn,
if (`RST_ASSERTED(aresetn)) begin
                    latency_histogram <= '0;
                    qos_histogram <= '0;
                end else begin
                    // Update latency histogram on transaction completion
                    if (fub_axi_rvalid && fub_axi_rready && fub_axi_rlast) begin
                        latency_histogram[latency_bin] <= latency_histogram[latency_bin] + 1'b1;
                    end
                
                    // Update QoS histogram on transaction start
                    if (fub_axi_arvalid && fub_axi_arready) begin
                        qos_histogram[qos_bin] <= qos_histogram[qos_bin] + 1'b1;
                    end
                end
            )


        end else begin : gen_no_histograms

            assign latency_histogram = '0;
            assign qos_histogram = '0;

        end
    endgenerate

    // =========================================================================
    // Error Detection and Status
    // =========================================================================

    assign hp_overload_error = (active_transactions > (MAX_TRANSACTIONS - 4));
    assign qos_violation_error = qos_violation;

    // Clock gating efficiency calculation
    assign cg_efficiency_percent = (cycle_counter > 0) ?
                                  ((cg_cycles_saved * 100) / cycle_counter) : 16'h0;

    // Throughput calculation (simplified - would need more complex logic)
    assign throughput_mbps = 32'h0;  // TODO: Implement throughput calculation
    assign utilization_percent = 16'h0;  // TODO: Implement utilization calculation
    assign peak_latency_cycles = 32'h0;  // TODO: Implement peak tracking

endmodule : axi4_master_rd_hp_mon
