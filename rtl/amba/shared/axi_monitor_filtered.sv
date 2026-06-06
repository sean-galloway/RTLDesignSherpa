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
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    // NOTE: `import monitor_pkg::*;` intentionally omitted — its helper
    // functions (get_packet_type etc.) duplicate monitor_common_pkg's, and
    // Vivado flags the duplicates as ambiguous under wildcard imports.
#(
    // Monitor parameters (passed through to axi_monitor_base)
    parameter logic [7:0]  UNIT_ID       = 8'h01,
    parameter logic [15:0] AGENT_ID      = 16'h000A,
    parameter int MAX_TRANSACTIONS       = 16,
    parameter int ADDR_WIDTH             = 32,
    parameter int ID_WIDTH               = 8,
    parameter bit IS_READ                = 1'b1,
    parameter bit IS_AXI                 = 1'b1,
    parameter bit ENABLE_PERF_PACKETS    = 1'b1,
    parameter bit ENABLE_DEBUG_MODULE    = 1'b0,

    // Reporter sub-block enables (passed through to axi_monitor_base).
    // ENABLE_PERF_LOGIC defaults to ENABLE_PERF_PACKETS for back-compat.
    parameter bit ENABLE_ERROR_LOGIC     = 1'b1,
    parameter bit ENABLE_TIMEOUT_LOGIC   = 1'b1,
    parameter bit ENABLE_COMPL_LOGIC     = 1'b1,
    parameter bit ENABLE_THRESHOLD_LOGIC = 1'b1,
    parameter bit ENABLE_PERF_LOGIC      = ENABLE_PERF_PACKETS,
    parameter bit ENABLE_DEBUG_LOGIC     = 1'b0,

    // Filtering parameters
    parameter bit ENABLE_FILTERING       = 1,     // Enable filtering logic
    parameter bit ADD_PIPELINE_STAGE     = 0,     // Add register stage for timing

    // Address-range check (0 = disabled, no comparator synthesised)
    parameter int N_ADDR_RANGES          = 0
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

    // Address-range check configuration (active when N_ADDR_RANGES > 0)
    input  logic                                                   cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]     cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][ADDR_WIDTH-1:0] cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][ADDR_WIDTH-1:0] cfg_addr_range_high,

    // Performance window control (Stage A of perfmon RFC). Wire to the
    // integrating block's perfmon CSR; tie 3'b111 + 1'b0 if perfmon is
    // unused at this instance.
    input  logic [2:0]                  cfg_start_event_sel,
    input  logic [2:0]                  cfg_end_event_sel,
    input  logic                        cfg_start_trigger,
    input  logic                        cfg_end_trigger,
    input  logic                        cfg_window_force_close,

    // Free-running monitor-time broadcast from monbus_axil_group
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor bus output (filtered, 128-bit packet)
    output logic                                    monbus_valid,
    input  logic                                    monbus_ready,
    output monitor_common_pkg::monitor_packet_t     monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t   monbus_timestamp,

    // Status outputs
    output logic                        block_ready,
    output logic                        busy,
    output logic [7:0]                  active_count,

    // Performance window status (Stage A of perfmon RFC).
    output logic                        window_active,
    output logic [31:0]                 window_cycles,

    // Performance cycle buckets + counters (Stage B of perfmon RFC).
    output logic [31:0]                 perf_prod_cycles,
    output logic [31:0]                 perf_bp_cycles,
    output logic [31:0]                 perf_starv_cycles,
    output logic [31:0]                 perf_idle_cycles,
    output logic [31:0]                 perf_beat_count,
    output logic [63:0]                 perf_byte_count,
    output logic [31:0]                 perf_burst_count,

    // Configuration error flags
    output logic                        cfg_conflict_error     // Configuration conflict detected
);

    // =========================================================================
    // Internal Signals
    // =========================================================================

    // Unfiltered monitor bus from base monitor (128-bit packet + 64-bit ts)
    logic                                            base_monbus_valid;
    logic                                            base_monbus_ready;
    monitor_common_pkg::monitor_packet_t             base_monbus_packet;
    monitor_common_pkg::monbus_timestamp_t           base_monbus_timestamp;

    // Packet analysis (widened to the new 128-bit field layout)
    logic [3:0]              pkt_type;
    logic [3:0]              pkt_protocol;     // 4-bit protocol field
    logic [7:0]              pkt_event_code;   // 8-bit event_code
    logic [63:0]             pkt_event_data;   // 64-bit event_data

    // Filter decisions
    logic                    pkt_drop;
    logic                    pkt_event_masked;

    // Pipeline stage (optional)
    logic                                            pipe_valid;
    logic                                            pipe_ready;
    monitor_common_pkg::monitor_packet_t             pipe_packet;
    monitor_common_pkg::monbus_timestamp_t           pipe_timestamp;

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
        .ENABLE_DEBUG_MODULE     (ENABLE_DEBUG_MODULE),
        .ENABLE_ERROR_LOGIC      (ENABLE_ERROR_LOGIC),
        .ENABLE_TIMEOUT_LOGIC    (ENABLE_TIMEOUT_LOGIC),
        .ENABLE_COMPL_LOGIC      (ENABLE_COMPL_LOGIC),
        .ENABLE_THRESHOLD_LOGIC  (ENABLE_THRESHOLD_LOGIC),
        .ENABLE_PERF_LOGIC       (ENABLE_PERF_LOGIC),
        .ENABLE_DEBUG_LOGIC      (ENABLE_DEBUG_LOGIC),
        .N_ADDR_RANGES           (N_ADDR_RANGES)
    ) u_axi_monitor_base (
        .aclk                    (aclk),
        .aresetn                 (aresetn),
        .i_mon_time              (i_mon_time),

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

        // Address-range checker
        .cfg_addr_check_enable   (cfg_addr_check_enable),
        .cfg_addr_range_enable   (cfg_addr_range_enable),
        .cfg_addr_range_low      (cfg_addr_range_low),
        .cfg_addr_range_high     (cfg_addr_range_high),

        // Performance window control (Stage A of perfmon RFC)
        .cfg_start_event_sel     (cfg_start_event_sel),
        .cfg_end_event_sel       (cfg_end_event_sel),
        .cfg_start_trigger       (cfg_start_trigger),
        .cfg_end_trigger         (cfg_end_trigger),
        .cfg_window_force_close  (cfg_window_force_close),

        // Monitor bus output (unfiltered, 128-bit + side-band ts)
        .monbus_valid            (base_monbus_valid),
        .monbus_ready            (base_monbus_ready),
        .monbus_packet           (base_monbus_packet),
        .monbus_timestamp        (base_monbus_timestamp),

        // Status outputs
        .block_ready             (block_ready),
        .busy                    (busy),
        .active_count            (active_count),

        // Performance window status
        .window_active           (window_active),
        .window_cycles           (window_cycles),

        // Performance counters (Stage B)
        .perf_prod_cycles        (perf_prod_cycles),
        .perf_bp_cycles          (perf_bp_cycles),
        .perf_starv_cycles       (perf_starv_cycles),
        .perf_idle_cycles        (perf_idle_cycles),
        .perf_beat_count         (perf_beat_count),
        .perf_byte_count         (perf_byte_count),
        .perf_burst_count        (perf_burst_count)
    );

    // =========================================================================
    // Packet Analysis and Filtering Logic
    // =========================================================================

    // Extract packet fields using monitor_pkg functions.
    // 128-bit layout: protocol lives at [108:105].
    assign pkt_type = get_packet_type(base_monbus_packet);
    assign pkt_protocol = base_monbus_packet[108:105]; // 4-bit protocol field
    assign pkt_event_code = get_event_code(base_monbus_packet);
    assign pkt_event_data = get_event_data(base_monbus_packet);

    // Masks are 16-bit (4-bit event-code index space). The 128-bit packet
    // widens event_code to 8 bits but all currently-defined codes still
    // fit in the low nibble — slice [3:0] for mask indexing.
    logic [3:0] ec_idx;
    assign ec_idx = pkt_event_code[3:0];

    // Filter logic
    always_comb begin
        pkt_drop = 1'b0;
        pkt_event_masked = 1'b0;

        // Only apply filtering if enabled and packet is valid
        if (ENABLE_FILTERING && base_monbus_valid) begin

            // Verify this is an AXI protocol packet (PROTOCOL_AXI = 4'h0)
            if (pkt_protocol == 4'h0) begin

                // Level 1: Check if packet type is dropped
                pkt_drop = cfg_axi_pkt_mask[pkt_type];

                // Level 3: Check individual event masking (only if not already dropped).
                if (!pkt_drop) begin
                    case (pkt_type)
                        monitor_common_pkg::PktTypeError:     pkt_event_masked = cfg_axi_error_mask[ec_idx];
                        monitor_common_pkg::PktTypeTimeout:   pkt_event_masked = cfg_axi_timeout_mask[ec_idx];
                        monitor_common_pkg::PktTypeCompletion: pkt_event_masked = cfg_axi_compl_mask[ec_idx];
                        monitor_common_pkg::PktTypeThreshold: pkt_event_masked = cfg_axi_thresh_mask[ec_idx];
                        monitor_common_pkg::PktTypePerf:      pkt_event_masked = cfg_axi_perf_mask[ec_idx];
                        monitor_common_pkg::PktTypeAddrMatch: pkt_event_masked = cfg_axi_addr_mask[ec_idx];
                        monitor_common_pkg::PktTypeDebug:     pkt_event_masked = cfg_axi_debug_mask[ec_idx];
                        default:                              pkt_event_masked = 1'b0;
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

            logic                                            pipe_valid_reg;
            monitor_common_pkg::monitor_packet_t             pipe_packet_reg;
            monitor_common_pkg::monbus_timestamp_t           pipe_timestamp_reg;

            `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
                    pipe_valid_reg     <= 1'b0;
                    pipe_packet_reg    <= '0;
                    pipe_timestamp_reg <= '0;
                end else begin
                    if (pipe_ready) begin
                        pipe_valid_reg     <= base_monbus_valid && !pkt_drop;
                        pipe_packet_reg    <= base_monbus_packet;
                        pipe_timestamp_reg <= base_monbus_timestamp;
                    end
                end
            )


            assign pipe_valid     = pipe_valid_reg;
            assign pipe_packet    = pipe_packet_reg;
            assign pipe_timestamp = pipe_timestamp_reg;
            assign pipe_ready     = !pipe_valid || monbus_ready;

            // Output from pipeline
            assign monbus_valid     = pipe_valid;
            assign monbus_packet    = pipe_packet;
            assign monbus_timestamp = pipe_timestamp;

        end else begin : gen_no_pipeline

            // Direct connection (combinatorial pass-through for both packet
            // and side-band timestamp)
            assign monbus_valid     = base_monbus_valid && !pkt_drop;
            assign monbus_packet    = base_monbus_packet;
            assign monbus_timestamp = base_monbus_timestamp;

        end
    endgenerate

endmodule : axi_monitor_filtered
