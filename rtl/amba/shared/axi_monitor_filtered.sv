// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_filtered
// Purpose: Axi Monitor Filtered module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI Monitor with Integrated Filtering
 *
 * This module wraps the standard axi_monitor_base with configurable packet filtering
 * based on the filtering architecture from monbus_axil_group. Provides 3-level
 * filtering hierarchy:
 *
 * Level 1: Packet type masking (pkt_mask) - drop entire packet types
 * Level 2: Error routing (err_select) - route specific packet types to error handling
 * Level 3: Event code masking - fine-grained filtering within packet types
 *
 * Features:
 * - AXI protocol specific filtering (protocol 3'b000)
 * - Static configuration (no dynamic changes expected)
 * - Configuration validation with error flagging
 * - Optional pipeline stage for timing closure
 * - Pass-through interface compatibility with axi_monitor_base
 */

`include "reset_defs.svh"
module axi_monitor_filtered
    import monitor_pkg::*;
#(
    // Monitor parameters (passed through to axi_monitor_base)
    parameter int UNIT_ID                = 1,
    parameter int AGENT_ID               = 10,
    parameter int MAX_TRANSACTIONS       = 16,
    parameter int ADDR_WIDTH             = 32,
    parameter int ID_WIDTH               = 8,
    parameter bit IS_READ                = 1,
    parameter bit IS_AXI                 = 1,
    parameter bit ENABLE_PERF_PACKETS    = 1,
    parameter bit ENABLE_DEBUG_MODULE    = 0,

    // Filtering parameters
    parameter bit ENABLE_FILTERING       = 1,     // Enable filtering logic
    parameter bit ADD_PIPELINE_STAGE     = 0      // Add register stage for timing
)
(
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    // Command interface
    input  logic [ADDR_WIDTH-1:0]       cmd_addr,
    input  logic [ID_WIDTH-1:0]         cmd_id,
    input  logic [7:0]                  cmd_len,
    input  logic [2:0]                  cmd_size,
    input  logic [1:0]                  cmd_burst,
    input  logic                        cmd_valid,
    input  logic                        cmd_ready,

    // Data interface
    input  logic [ID_WIDTH-1:0]         data_id,
    input  logic                        data_last,
    input  logic [1:0]                  data_resp,
    input  logic                        data_valid,
    input  logic                        data_ready,

    // Response interface
    input  logic [ID_WIDTH-1:0]         resp_id,
    input  logic [1:0]                  resp_code,
    input  logic                        resp_valid,
    input  logic                        resp_ready,

    // Configuration (passed through to base monitor)
    input  logic [3:0]                  cfg_freq_sel,
    input  logic [3:0]                  cfg_addr_cnt,
    input  logic [3:0]                  cfg_data_cnt,
    input  logic [3:0]                  cfg_resp_cnt,
    input  logic                        cfg_error_enable,
    input  logic                        cfg_compl_enable,
    input  logic                        cfg_threshold_enable,
    input  logic                        cfg_timeout_enable,
    input  logic                        cfg_perf_enable,
    input  logic                        cfg_debug_enable,
    input  logic [3:0]                  cfg_debug_level,
    input  logic [15:0]                 cfg_debug_mask,
    input  logic [15:0]                 cfg_active_trans_threshold,
    input  logic [31:0]                 cfg_latency_threshold,

    // AXI Protocol Filtering Configuration
    input  logic [15:0]                 cfg_axi_pkt_mask,      // Drop mask for packet types
    input  logic [15:0]                 cfg_axi_err_select,    // Error select for packet types (unused in this context)
    input  logic [15:0]                 cfg_axi_error_mask,    // Individual error event mask
    input  logic [15:0]                 cfg_axi_timeout_mask,  // Individual timeout event mask
    input  logic [15:0]                 cfg_axi_compl_mask,    // Individual completion event mask
    input  logic [15:0]                 cfg_axi_thresh_mask,   // Individual threshold event mask
    input  logic [15:0]                 cfg_axi_perf_mask,     // Individual performance event mask
    input  logic [15:0]                 cfg_axi_addr_mask,     // Individual address match event mask
    input  logic [15:0]                 cfg_axi_debug_mask,    // Individual debug event mask

    // Monitor bus output (filtered)
    output logic                        monbus_valid,
    input  logic                        monbus_ready,
    output logic [63:0]                 monbus_packet,

    // Status outputs
    output logic                        block_ready,
    output logic                        busy,
    output logic [7:0]                  active_count,

    // Configuration error flags
    output logic                        cfg_conflict_error     // Configuration conflict detected
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // Unfiltered monitor bus from base monitor
    logic                    base_monbus_valid;
    logic                    base_monbus_ready;
    logic [63:0]             base_monbus_packet;

    // Packet analysis
    logic [3:0]              pkt_type;
    logic [2:0]              pkt_protocol;
    logic [3:0]              pkt_event_code;
    logic [35:0]             pkt_event_data;

    // Filter decisions
    logic                    pkt_drop;
    logic                    pkt_event_masked;

    // Pipeline stage (optional)
    logic                    pipe_valid;
    logic                    pipe_ready;
    logic [63:0]             pipe_packet;

    // =========================================================================
    // Configuration Validation
    // =========================================================================

    // Check for conflicting configurations
    // Note: err_select not used in this context but checked for completeness
    assign cfg_conflict_error = |(cfg_axi_pkt_mask & cfg_axi_err_select);

    // =========================================================================
    // AXI Monitor Base Instance
    // =========================================================================

    axi_monitor_base #(
        .UNIT_ID                 (UNIT_ID),
        .AGENT_ID                (AGENT_ID),
        .MAX_TRANSACTIONS        (MAX_TRANSACTIONS),
        .ADDR_WIDTH              (ADDR_WIDTH),
        .ID_WIDTH                (ID_WIDTH),
        .IS_READ                 (IS_READ),
        .IS_AXI                  (IS_AXI),
        .ENABLE_PERF_PACKETS     (ENABLE_PERF_PACKETS),
        .ENABLE_DEBUG_MODULE     (ENABLE_DEBUG_MODULE)
    ) u_axi_monitor_base (
        .aclk                    (aclk),
        .aresetn                 (aresetn),

        // Command interface
        .cmd_addr                (cmd_addr),
        .cmd_id                  (cmd_id),
        .cmd_len                 (cmd_len),
        .cmd_size                (cmd_size),
        .cmd_burst               (cmd_burst),
        .cmd_valid               (cmd_valid),
        .cmd_ready               (cmd_ready),

        // Data interface
        .data_id                 (data_id),
        .data_last               (data_last),
        .data_resp               (data_resp),
        .data_valid              (data_valid),
        .data_ready              (data_ready),

        // Response interface
        .resp_id                 (resp_id),
        .resp_code               (resp_code),
        .resp_valid              (resp_valid),
        .resp_ready              (resp_ready),

        // Configuration
        .cfg_freq_sel            (cfg_freq_sel),
        .cfg_addr_cnt            (cfg_addr_cnt),
        .cfg_data_cnt            (cfg_data_cnt),
        .cfg_resp_cnt            (cfg_resp_cnt),
        .cfg_error_enable        (cfg_error_enable),
        .cfg_compl_enable        (cfg_compl_enable),
        .cfg_threshold_enable    (cfg_threshold_enable),
        .cfg_timeout_enable      (cfg_timeout_enable),
        .cfg_perf_enable         (cfg_perf_enable),
        .cfg_debug_enable        (cfg_debug_enable),
        .cfg_debug_level         (cfg_debug_level),
        .cfg_debug_mask          (cfg_debug_mask),
        .cfg_active_trans_threshold(cfg_active_trans_threshold),
        .cfg_latency_threshold   (cfg_latency_threshold),

        // Monitor bus output (unfiltered)
        .monbus_valid            (base_monbus_valid),
        .monbus_ready            (base_monbus_ready),
        .monbus_packet           (base_monbus_packet),

        // Status outputs
        .block_ready             (block_ready),
        .busy                    (busy),
        .active_count            (active_count)
    );

    // =========================================================================
    // Packet Analysis and Filtering Logic
    // =========================================================================

    // Extract packet fields using monitor_pkg functions
    assign pkt_type = get_packet_type(base_monbus_packet);
    assign pkt_protocol = base_monbus_packet[59:57]; // 3-bit protocol field
    assign pkt_event_code = get_event_code(base_monbus_packet);
    assign pkt_event_data = get_event_data(base_monbus_packet);

    // Filter logic
    always_comb begin
        pkt_drop = 1'b0;
        pkt_event_masked = 1'b0;

        // Only apply filtering if enabled and packet is valid
        if (ENABLE_FILTERING && base_monbus_valid) begin

            // Verify this is an AXI protocol packet (3'b000)
            if (pkt_protocol == 3'b000) begin

                // Level 1: Check if packet type is dropped
                pkt_drop = cfg_axi_pkt_mask[pkt_type];

                // Level 3: Check individual event masking (only if not already dropped)
                if (!pkt_drop) begin
                    case (pkt_type)
                        monitor_pkg::PktTypeError:     pkt_event_masked = cfg_axi_error_mask[pkt_event_code];
                        monitor_pkg::PktTypeTimeout:   pkt_event_masked = cfg_axi_timeout_mask[pkt_event_code];
                        monitor_pkg::PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask[pkt_event_code];
                        monitor_pkg::PktTypeThreshold: pkt_event_masked = cfg_axi_thresh_mask[pkt_event_code];
                        monitor_pkg::PktTypePerf:      pkt_event_masked = cfg_axi_perf_mask[pkt_event_code];
                        monitor_pkg::PktTypeAddrMatch: pkt_event_masked = cfg_axi_addr_mask[pkt_event_code];
                        monitor_pkg::PktTypeDebug:     pkt_event_masked = cfg_axi_debug_mask[pkt_event_code];
                        default:                       pkt_event_masked = 1'b0;
                    endcase

                    // Final decision: drop if event is masked
                    if (pkt_event_masked) begin
                        pkt_drop = 1'b1;
                    end
                end

            end else begin
                // Drop non-AXI protocol packets (should not happen in AXI monitor)
                pkt_drop = 1'b1;
            end
        end
    end

    // Base monitor ready control - always ready if packet will be dropped,
    // otherwise depends on downstream ready
    assign base_monbus_ready = pkt_drop ||
                              (ADD_PIPELINE_STAGE ? pipe_ready : monbus_ready);

    // =========================================================================
    // Optional Pipeline Stage
    // =========================================================================

    generate
        if (ADD_PIPELINE_STAGE) begin : gen_pipeline

            logic pipe_valid_reg;
            logic [63:0] pipe_packet_reg;

            `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
                    pipe_valid_reg <= 1'b0;
                    pipe_packet_reg <= '0;
                end else begin
                    if (pipe_ready) begin
                        pipe_valid_reg <= base_monbus_valid && !pkt_drop;
                        pipe_packet_reg <= base_monbus_packet;
                    end
                end
            )


            assign pipe_valid = pipe_valid_reg;
            assign pipe_packet = pipe_packet_reg;
            assign pipe_ready = !pipe_valid || monbus_ready;

            // Output from pipeline
            assign monbus_valid = pipe_valid;
            assign monbus_packet = pipe_packet;

        end else begin : gen_no_pipeline

            // Direct connection (combinatorial)
            assign monbus_valid = base_monbus_valid && !pkt_drop;
            assign monbus_packet = base_monbus_packet;

        end
    endgenerate

endmodule : axi_monitor_filtered
