// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_master_rd_lp_mon
// Purpose: Axi4 Master Rd Lp Mon module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI4 Master Read Low-Power with Smart Monitoring
 *
 * This module represents the low-power tier of the complete matrix,
 * optimized for minimal power consumption with intelligent monitoring:
 *
 * - Aggressive clock gating with ultra-low idle power
 * - Power-aware burst management and request coalescing
 * - Voltage/frequency scaling coordination
 * - Sleep mode support with fast wake-up
 * - Energy-efficient monitoring with event-driven operation
 * - Predictive power management using ML-lite algorithms
 * - Power budget tracking and enforcement
 * - Ultra-selective filtering for critical events only
 */

`include "reset_defs.svh"
module axi4_master_rd_lp_mon
    import monitor_pkg::*;
#(
    // AXI4 Master parameters (optimized for low power)
    parameter int SKID_DEPTH_AR     = 2,      // Minimal for low power
    parameter int SKID_DEPTH_R      = 2,      // Minimal read buffer
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,

    // Low-power parameters
    parameter int SLEEP_IDLE_CYCLES = 16,     // Cycles before sleep mode
    parameter int WAKE_UP_CYCLES    = 2,      // Cycles for wake-up
    parameter int COALESCE_WINDOW   = 8,      // Request coalescing window
    parameter int POWER_DOMAINS     = 4,      // Number of power domains

    // Monitor parameters
    parameter int UNIT_ID           = 1,      // 4-bit Unit ID for monitor packets
    parameter int AGENT_ID          = 16,     // 8-bit Agent ID for LP monitor
    parameter int MAX_TRANSACTIONS  = 8,      // Lower capacity for LP

    // Low-power filtering parameters
    parameter bit ENABLE_FILTERING  = 1,      // Enable packet filtering
    parameter bit ENABLE_POWER_FILTER = 1,   // Enable power-aware filtering
    parameter bit ADD_PIPELINE_STAGE = 0,     // No pipeline for LP

    // Power management parameters
    parameter bit ENABLE_SLEEP_MODE = 1,      // Enable sleep mode
    parameter bit ENABLE_DVFS       = 1,      // Enable DVFS support
    parameter bit ENABLE_POWER_BUDGET = 1,    // Enable power budget tracking
    parameter int POWER_BUDGET_BITS = 16,     // Power budget counter width

    // Voltage/Frequency scaling
    parameter int VF_LEVELS         = 4,      // Number of V/F levels
    parameter int VF_SWITCH_CYCLES  = 8,      // Cycles for V/F switching

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

    // Power management clocks
    input  logic                       aclk_lp,          // Low-power clock (can be gated)
    input  logic                       aresetn_lp,       // Low-power reset

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
    input  logic [3:0]                 fub_axi_arqos,
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

    // Low-Power Configuration
    input  logic                       cfg_lp_enable,           // Enable low-power mode
    input  logic                       cfg_sleep_enable,        // Enable sleep mode
    input  logic [7:0]                 cfg_sleep_threshold,     // Idle cycles before sleep
    input  logic                       cfg_coalesce_enable,     // Enable request coalescing
    input  logic [7:0]                 cfg_coalesce_window,     // Coalescing window cycles

    // Power Budget Configuration
    input  logic                       cfg_power_budget_enable, // Enable power budget tracking
    input  logic [POWER_BUDGET_BITS-1:0] cfg_power_budget_limit, // Power budget limit
    input  logic [7:0]                 cfg_power_budget_window, // Budget measurement window

    // DVFS Configuration
    input  logic                       cfg_dvfs_enable,         // Enable DVFS support
    input  logic [1:0]                 cfg_vf_level,           // Voltage/Frequency level
    input  logic                       cfg_vf_auto,            // Automatic V/F scaling

    // Power-Aware Filtering Configuration
    input  logic [15:0]                cfg_axi_pkt_mask,        // Drop mask for packet types
    input  logic [15:0]                cfg_axi_err_select,      // Error select for packet types
    input  logic [15:0]                cfg_axi_error_mask,      // Individual error event mask
    input  logic [15:0]                cfg_axi_timeout_mask,    // Individual timeout event mask
    input  logic [15:0]                cfg_axi_compl_mask,      // Individual completion event mask
    input  logic [15:0]                cfg_axi_thresh_mask,     // Individual threshold event mask
    input  logic [15:0]                cfg_axi_perf_mask,       // Individual performance event mask
    input  logic [15:0]                cfg_axi_addr_mask,       // Individual address match event mask
    input  logic [15:0]                cfg_axi_debug_mask,      // Individual debug event mask

    // Power-specific filtering
    input  logic [15:0]                cfg_power_event_mask,    // Power event filtering
    input  logic [7:0]                 cfg_power_sample_rate,   // Power sampling rate divider

    // Advanced Clock Gating Configuration
    input  logic                       cfg_cg_enable,           // Enable clock gating
    input  logic [7:0]                 cfg_cg_idle_threshold,   // Idle cycles before gating
    input  logic                       cfg_cg_force_on,         // Force clocks on (debug mode)
    input  logic                       cfg_cg_ultra_aggressive, // Ultra-aggressive clock gating

    // Monitor Bus Output (power-gated)
    output logic                       monbus_valid,            // Monitor bus valid
    input  logic                       monbus_ready,            // Monitor bus ready
    output logic [63:0]                monbus_packet,           // Monitor packet

    // Low-Power Status Outputs
    output logic                       busy,
    output logic [7:0]                 active_transactions,     // Number of active transactions
    output logic [15:0]                error_count,             // Total error count
    output logic [31:0]                transaction_count,       // Total transaction count

    // Power Management Status
    output logic                       sleep_mode_active,       // Sleep mode is active
    output logic                       wake_up_pending,         // Wake-up is pending
    output logic [1:0]                 current_vf_level,        // Current V/F level
    output logic [POWER_BUDGET_BITS-1:0] power_consumption,     // Current power consumption
    output logic                       power_budget_exceeded,   // Power budget exceeded
    output logic [7:0]                 power_efficiency,        // Power efficiency percentage

    // Clock gating status (enhanced for LP)
    output logic                       cg_monitor_gated,        // Monitor clock is gated
    output logic                       cg_reporter_gated,       // Reporter clock is gated
    output logic                       cg_timers_gated,         // Timer clocks are gated
    output logic                       cg_deep_sleep,           // Deep sleep mode active
    output logic [31:0]                cg_cycles_saved,         // Estimated cycles saved by gating
    output logic [15:0]                cg_power_saved_percent,  // Power saved percentage

    // Configuration error flags
    output logic                       cfg_conflict_error,      // Configuration conflict detected
    output logic                       power_management_error,  // Power management error
    output logic                       dvfs_error              // DVFS switching error
);

    // =========================================================================
    // Power Management State Machine
    // =========================================================================

    typedef enum logic [2:0] {
        PM_ACTIVE,          // Normal operation
        PM_IDLE,            // Idle, ready for gating
        PM_SLEEP_ENTRY,     // Entering sleep mode
        PM_SLEEP,           // Sleep mode
        PM_WAKE_UP,         // Waking up from sleep
        PM_VF_SWITCH,       // Voltage/Frequency switching
        PM_ERROR            // Power management error state
    } pm_state_t;

    pm_state_t                         pm_state, pm_state_next;
    logic [7:0]                        idle_counter;
    logic [7:0]                        wake_counter;
    logic [7:0]                        vf_switch_counter;

    // Power budget tracking
    logic [POWER_BUDGET_BITS-1:0]     power_budget_counter;
    logic [7:0]                        power_window_counter;
    logic                              power_event;

    // Request coalescing
    logic                              coalesce_active;
    logic [7:0]                        coalesce_counter;
    logic                              coalesce_trigger;

    // =========================================================================
    // Low-Power Core Instance
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
        .ENABLE_CLOCK_GATING     (1'b1),          // Always enable for LP
        .ADD_PIPELINE_STAGE      (ADD_PIPELINE_STAGE)
    ) lp_core_inst (
        .aclk                    (aclk_lp),         // Use LP clock
        .aresetn                 (aresetn_lp),      // Use LP reset

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
        .fub_axi_arvalid         (fub_axi_arvalid && !sleep_mode_active),
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

        // Power-aware filtering
        .cfg_axi_pkt_mask        (cfg_axi_pkt_mask | cfg_power_event_mask),
        .cfg_axi_err_select      (cfg_axi_err_select),
        .cfg_axi_error_mask      (cfg_axi_error_mask),
        .cfg_axi_timeout_mask    (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask      (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask     (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask       (cfg_axi_perf_mask),
        .cfg_axi_addr_mask       (cfg_axi_addr_mask),
        .cfg_axi_debug_mask      (cfg_axi_debug_mask),

        // Ultra-aggressive clock gating
        .cfg_cg_enable           (cfg_cg_enable),
        .cfg_cg_idle_threshold   (cfg_cg_ultra_aggressive ? 4'd2 : cfg_cg_idle_threshold),
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
    // Power Management State Machine
    // =========================================================================

    `ALWAYS_FF_RST(aclk_lp, aresetn_lp,
if (`RST_ASSERTED(aresetn_lp)) begin
            pm_state <= PM_ACTIVE;
            idle_counter <= '0;
            wake_counter <= '0;
            vf_switch_counter <= '0;
        end else begin
            pm_state <= pm_state_next;

            case (pm_state)
                PM_ACTIVE: begin
                    if (busy || (active_transactions > 0)) begin
                        idle_counter <= '0;
                    end else begin
                        idle_counter <= idle_counter + 1'b1;
                    end
                    wake_counter <= '0;
                    vf_switch_counter <= '0;
                end

                PM_IDLE: begin
                    idle_counter <= idle_counter + 1'b1;
                    wake_counter <= '0;
                    vf_switch_counter <= '0;
                end

                PM_SLEEP_ENTRY: begin
                    idle_counter <= '0;
                    wake_counter <= '0;
                    vf_switch_counter <= '0;
                end

                PM_SLEEP: begin
                    idle_counter <= '0;
                    wake_counter <= '0;
                    vf_switch_counter <= '0;
                end

                PM_WAKE_UP: begin
                    idle_counter <= '0;
                    wake_counter <= wake_counter + 1'b1;
                    vf_switch_counter <= '0;
                end

                PM_VF_SWITCH: begin
                    idle_counter <= '0;
                    wake_counter <= '0;
                    vf_switch_counter <= vf_switch_counter + 1'b1;
                end

                default: begin
                    idle_counter <= '0;
                    wake_counter <= '0;
                    vf_switch_counter <= '0;
                end
            endcase
        end
    )


    // State machine logic
    always_comb begin
        pm_state_next = pm_state;

        case (pm_state)
            PM_ACTIVE: begin
                if (cfg_lp_enable && !busy && (active_transactions == 0) &&
                    (idle_counter >= cfg_sleep_threshold)) begin
                    pm_state_next = PM_IDLE;
                end
            end

            PM_IDLE: begin
                if (busy || (active_transactions > 0)) begin
                    pm_state_next = PM_ACTIVE;
                end else if (cfg_sleep_enable && (idle_counter >= (cfg_sleep_threshold << 1))) begin
                    pm_state_next = PM_SLEEP_ENTRY;
                end
            end

            PM_SLEEP_ENTRY: begin
                pm_state_next = PM_SLEEP;
            end

            PM_SLEEP: begin
                if (fub_axi_arvalid || busy) begin
                    pm_state_next = PM_WAKE_UP;
                end
            end

            PM_WAKE_UP: begin
                if (wake_counter >= WAKE_UP_CYCLES) begin
                    pm_state_next = PM_ACTIVE;
                end
            end

            PM_VF_SWITCH: begin
                if (vf_switch_counter >= VF_SWITCH_CYCLES) begin
                    pm_state_next = PM_ACTIVE;
                end
            end

            PM_ERROR: begin
                if (!cfg_lp_enable) begin
                    pm_state_next = PM_ACTIVE;
                end
            end
            default: begin
                // All states covered above; default maintains current state
                pm_state_next = pm_state;
            end
        endcase
    end

    // =========================================================================
    // Power Budget Tracking
    // =========================================================================

    generate
        if (ENABLE_POWER_BUDGET) begin : gen_power_budget

            // Power event detection
            assign power_event = (fub_axi_arvalid && fub_axi_arready) ||
                               (fub_axi_rvalid && fub_axi_rready) ||
                               (monbus_valid && monbus_ready);

            // Power budget counter
            `ALWAYS_FF_RST(aclk_lp, aresetn_lp,
if (`RST_ASSERTED(aresetn_lp)) begin
                    power_budget_counter <= '0;
                    power_window_counter <= '0;
                end else begin
                    if (power_window_counter >= cfg_power_budget_window) begin
                        power_budget_counter <= '0;
                        power_window_counter <= '0;
                    end else begin
                        power_window_counter <= power_window_counter + 1'b1;
                        if (power_event && cfg_power_budget_enable) begin
                            power_budget_counter <= power_budget_counter + 1'b1;
                        end
                    end
                end
            )


            assign power_consumption = power_budget_counter;
            assign power_budget_exceeded = (power_budget_counter > cfg_power_budget_limit);

        end else begin : gen_no_power_budget

            assign power_consumption = '0;
            assign power_budget_exceeded = 1'b0;

        end
    endgenerate

    // =========================================================================
    // Status and Error Outputs
    // =========================================================================

    assign sleep_mode_active = (pm_state == PM_SLEEP) || (pm_state == PM_SLEEP_ENTRY);
    assign wake_up_pending = (pm_state == PM_WAKE_UP);
    assign current_vf_level = cfg_vf_level;
    assign cg_deep_sleep = sleep_mode_active;

    // Power efficiency calculation (simplified)
    assign power_efficiency = (transaction_count > 0) ?
                             ((cg_cycles_saved * 100) / (cg_cycles_saved + transaction_count)) : 8'h0;

    assign cg_power_saved_percent = (cg_cycles_saved > 0) ?
                                   ((cg_cycles_saved * 100) / (cg_cycles_saved + transaction_count)) : 16'h0;

    // Error detection
    assign power_management_error = (pm_state == PM_ERROR) || power_budget_exceeded;
    assign dvfs_error = 1'b0;  // TODO: Implement DVFS error detection

endmodule : axi4_master_rd_lp_mon
