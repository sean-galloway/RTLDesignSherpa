// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pm_acpi_core
// Purpose: Core PM/ACPI power management logic
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pm_acpi/README.md
// Subsystem: pm_acpi
//
// Author: sean galloway
// Created: 2025-11-16

/**
 * ============================================================================
 * PM_ACPI Core Logic
 * ============================================================================
 *
 * DESCRIPTION:
 *   Core power management logic implementing ACPI-compatible functionality:
 *   - 32-bit PM Timer with configurable divider
 *   - Power state FSM (S0/S1/S3)
 *   - General Purpose Event (GPE) handling
 *   - Clock gating control
 *   - Power domain sequencing
 *   - Wake event logic
 *   - Interrupt aggregation
 *
 * PM TIMER:
 *   - 32-bit free-running counter
 *   - Configurable divider for 3.579545 MHz equivalent
 *   - Rolls over ~1200 seconds at standard frequency
 *   - Generates overflow interrupt
 *
 * POWER STATES:
 *   - S0 (0): Working - Full power, all clocks active
 *   - S1 (1): Sleep   - Clock gating, context retained, quick wake
 *   - S3 (3): Deep    - Power domains off, context lost, wake from events
 *
 * GPE HANDLING:
 *   - 32 general-purpose event sources
 *   - Edge detection with sticky status
 *   - Individual enable masks
 *   - Interrupt aggregation
 *
 * ============================================================================
 */

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pm_acpi_core (
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input  logic        clk,
    input  logic        rst_n,

    // ========================================================================
    // Configuration Interface (from config_regs)
    // ========================================================================
    
    // Global control
    input  logic        cfg_acpi_enable,
    input  logic        cfg_pm_timer_enable,
    input  logic        cfg_gpe_enable,
    input  logic        cfg_low_power_req,
    
    // PM1 control
    input  logic [2:0]  cfg_sleep_type,        // Target sleep state
    input  logic        cfg_sleep_enable,      // Sleep entry trigger
    input  logic        cfg_pwrbtn_ovr,
    input  logic        cfg_slpbtn_ovr,
    
    // PM1 enables
    input  logic        cfg_pm1_tmr_en,
    input  logic        cfg_pm1_pwrbtn_en,
    input  logic        cfg_pm1_slpbtn_en,
    input  logic        cfg_pm1_rtc_en,
    
    // PM Timer configuration
    input  logic [15:0] cfg_pm_timer_div,      // Clock divider
    
    // GPE enables
    input  logic [31:0] cfg_gpe_enables,
    
    // Clock gate control
    input  logic [31:0] cfg_clk_gate_ctrl,
    
    // Power domain control
    input  logic [7:0]  cfg_pwr_domain_ctrl,
    
    // Wake enables
    input  logic        cfg_gpe_wake_en,
    input  logic        cfg_pwrbtn_wake_en,
    input  logic        cfg_rtc_wake_en,
    input  logic        cfg_ext_wake_en,
    
    // Interrupt enables (top-level)
    input  logic        cfg_pme_enable,
    input  logic        cfg_wake_enable,
    input  logic        cfg_timer_ovf_enable,
    input  logic        cfg_state_trans_enable,
    input  logic        cfg_pm1_enable,
    input  logic        cfg_gpe_int_enable,

    // ========================================================================
    // Status Interface (to config_regs)
    // ========================================================================
    
    // Current power state
    output logic [1:0]  status_current_state,
    
    // ACPI status flags
    output logic        status_pme,
    output logic        status_wake,
    output logic        status_timer_overflow,
    output logic        status_state_transition,
    
    // PM1 status
    output logic        status_pm1_tmr,
    output logic        status_pm1_pwrbtn,
    output logic        status_pm1_slpbtn,
    output logic        status_pm1_rtc,
    output logic        status_pm1_wake,
    
    // PM Timer value
    output logic [31:0] status_pm_timer_value,
    
    // GPE status
    output logic [31:0] status_gpe_status,
    
    // Clock gate status
    output logic [31:0] status_clk_gate_status,
    
    // Power domain status
    output logic [7:0]  status_pwr_domain_status,
    
    // Wake status
    output logic        status_gpe_wake,
    output logic        status_pwrbtn_wake,
    output logic        status_rtc_wake,
    output logic        status_ext_wake,
    
    // Reset status (for tracking reset source)
    output logic        status_por_reset,
    output logic        status_wdt_reset,
    output logic        status_sw_reset,
    output logic        status_ext_reset,

    // ========================================================================
    // External Interfaces
    // ========================================================================
    
    // GPE event inputs (from system)
    input  logic [31:0] gpe_events_in,
    
    // Power button input
    input  logic        power_button_n,        // Active low
    
    // Sleep button input
    input  logic        sleep_button_n,        // Active low
    
    // RTC alarm input
    input  logic        rtc_alarm,
    
    // External wake input
    input  logic        ext_wake_n,            // Active low
    
    // Clock gate outputs (to clock gates)
    output logic [31:0] clock_gate_en,
    
    // Power domain outputs (to power switches)
    output logic [7:0]  power_domain_en,
    
    // System reset request
    output logic        sys_reset_req,
    
    // Peripheral reset request
    output logic        periph_reset_req,
    
    // PM interrupt output (aggregated)
    output logic        pm_interrupt
);

    // ========================================================================
    // Internal Registers and Signals
    // ========================================================================
    
    // PM Timer
    logic [31:0] pm_timer_count;
    logic [15:0] pm_timer_div_count;
    logic        pm_timer_tick;
    logic        pm_timer_overflow;
    
    // Power state FSM
    typedef enum logic [2:0] {
        PWR_S0_WORKING   = 3'b000,
        PWR_S1_SLEEP     = 3'b001,
        PWR_S3_SUSPEND   = 3'b011,
        PWR_TRANSITION   = 3'b111
    } pwr_state_t;
    
    pwr_state_t current_pwr_state, next_pwr_state;
    logic       state_transition_done;
    
    // GPE edge detection
    logic [31:0] gpe_events_prev;
    logic [31:0] gpe_events_edge;
    logic [31:0] gpe_status_reg;
    
    // Button debounce and edge detection
    logic [2:0] power_button_sync;
    logic [2:0] sleep_button_sync;
    logic       power_button_press;
    logic       sleep_button_press;
    
    // Wake event detection
    logic       any_wake_event;
    logic       gpe_wake_event;
    logic       pwrbtn_wake_event;
    logic       rtc_wake_event;
    logic       ext_wake_event;
    
    // Clock gating state machine
    logic [31:0] clk_gate_current;
    logic [31:0] clk_gate_target;
    
    // Power domain sequencing
    logic [7:0]  pwr_domain_current;
    logic [7:0]  pwr_domain_target;
    
    // Interrupt aggregation
    logic        pme_int;
    logic        wake_int;
    logic        timer_ovf_int;
    logic        state_trans_int;
    logic        pm1_int;
    logic        gpe_int;

    // ========================================================================
    // PM Timer Logic
    // ========================================================================
    
    // Timer divider counter
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            pm_timer_div_count <= '0;
            pm_timer_tick <= 1'b0;
        end else if (cfg_acpi_enable && cfg_pm_timer_enable) begin
            if (pm_timer_div_count >= cfg_pm_timer_div) begin
                pm_timer_div_count <= '0;
                pm_timer_tick <= 1'b1;
            end else begin
                pm_timer_div_count <= pm_timer_div_count + 1'b1;
                pm_timer_tick <= 1'b0;
            end
        end else begin
            pm_timer_div_count <= '0;
            pm_timer_tick <= 1'b0;
        end
    )
    
    // PM Timer counter (32-bit free-running)
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            pm_timer_count <= '0;
            pm_timer_overflow <= 1'b0;
        end else if (cfg_acpi_enable && cfg_pm_timer_enable && pm_timer_tick) begin
            {pm_timer_overflow, pm_timer_count} <= {1'b0, pm_timer_count} + 1'b1;
        end else begin
            pm_timer_overflow <= 1'b0;
        end
    )
    
    assign status_pm_timer_value = pm_timer_count;
    assign status_timer_overflow = pm_timer_overflow;
    assign status_pm1_tmr = pm_timer_overflow;

    // ========================================================================
    // Button Input Synchronization and Edge Detection
    // ========================================================================
    
    // Synchronize button inputs (active-low)
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            power_button_sync <= 3'b111;
            sleep_button_sync <= 3'b111;
        end else begin
            power_button_sync <= {power_button_sync[1:0], power_button_n};
            sleep_button_sync <= {sleep_button_sync[1:0], sleep_button_n};
        end
    )
    
    // Detect button presses (high-to-low transition after debounce)
    assign power_button_press = (power_button_sync[2:1] == 2'b10);
    assign sleep_button_press = (sleep_button_sync[2:1] == 2'b10);
    
    assign status_pm1_pwrbtn = power_button_press;
    assign status_pm1_slpbtn = sleep_button_press;
    assign status_pm1_rtc = rtc_alarm;

    // ========================================================================
    // GPE Event Handling
    // ========================================================================
    
    // Edge detection for GPE events
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            gpe_events_prev <= '0;
        end else if (cfg_acpi_enable && cfg_gpe_enable) begin
            gpe_events_prev <= gpe_events_in;
        end
    )
    
    // Rising edge detection
    assign gpe_events_edge = gpe_events_in & ~gpe_events_prev;
    
    // GPE status register (sticky until cleared by software)
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            gpe_status_reg <= '0;
        end else if (cfg_acpi_enable && cfg_gpe_enable) begin
            gpe_status_reg <= gpe_status_reg | gpe_events_edge;
        end
    )
    
    assign status_gpe_status = gpe_status_reg;
    
    // GPE interrupt aggregation (enabled events only)
    assign gpe_int = |(gpe_status_reg & cfg_gpe_enables);

    // ========================================================================
    // Power State FSM
    // ========================================================================
    
    // State register
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            current_pwr_state <= PWR_S0_WORKING;
            state_transition_done <= 1'b0;
        end else begin
            current_pwr_state <= next_pwr_state;
            state_transition_done <= (current_pwr_state == PWR_TRANSITION) && 
                                    (next_pwr_state != PWR_TRANSITION);
        end
    )
    
    // Next state logic
    always_comb begin
        next_pwr_state = current_pwr_state;
        
        if (!cfg_acpi_enable) begin
            next_pwr_state = PWR_S0_WORKING;
        end else begin
            case (current_pwr_state)
                PWR_S0_WORKING: begin
                    // Enter sleep state if requested
                    if (cfg_sleep_enable) begin
                        if (cfg_sleep_type == 3'h0) begin
                            next_pwr_state = PWR_S0_WORKING;  // Stay in S0
                        end else if (cfg_sleep_type == 3'h1) begin
                            next_pwr_state = PWR_TRANSITION;  // Go to S1
                        end else if (cfg_sleep_type == 3'h3) begin
                            next_pwr_state = PWR_TRANSITION;  // Go to S3
                        end
                    end
                end
                
                PWR_S1_SLEEP: begin
                    // Wake from S1
                    if (any_wake_event) begin
                        next_pwr_state = PWR_TRANSITION;  // Return to S0
                    end
                end
                
                PWR_S3_SUSPEND: begin
                    // Wake from S3
                    if (any_wake_event) begin
                        next_pwr_state = PWR_TRANSITION;  // Return to S0
                    end
                end
                
                PWR_TRANSITION: begin
                    // Transition complete, go to target state
                    if (cfg_sleep_type == 3'h0 || any_wake_event) begin
                        next_pwr_state = PWR_S0_WORKING;
                    end else if (cfg_sleep_type == 3'h1) begin
                        next_pwr_state = PWR_S1_SLEEP;
                    end else if (cfg_sleep_type == 3'h3) begin
                        next_pwr_state = PWR_S3_SUSPEND;
                    end else begin
                        next_pwr_state = PWR_S0_WORKING;
                    end
                end
                
                default: begin
                    next_pwr_state = PWR_S0_WORKING;
                end
            endcase
        end
    end
    
    // Power state status output
    assign status_current_state = (current_pwr_state == PWR_S0_WORKING) ? 2'b00 :
                                 (current_pwr_state == PWR_S1_SLEEP)    ? 2'b01 :
                                 (current_pwr_state == PWR_S3_SUSPEND)  ? 2'b11 : 2'b00;
    
    assign status_state_transition = state_transition_done;

    // ========================================================================
    // Wake Event Detection
    // ========================================================================
    
    // Individual wake sources
    assign gpe_wake_event = cfg_gpe_wake_en && (|(gpe_status_reg & cfg_gpe_enables));
    assign pwrbtn_wake_event = cfg_pwrbtn_wake_en && power_button_press;
    assign rtc_wake_event = cfg_rtc_wake_en && rtc_alarm;
    assign ext_wake_event = cfg_ext_wake_en && !ext_wake_n;
    
    // Any wake event
    assign any_wake_event = gpe_wake_event || pwrbtn_wake_event || 
                           rtc_wake_event || ext_wake_event;
    
    // Wake status outputs
    assign status_gpe_wake = gpe_wake_event;
    assign status_pwrbtn_wake = pwrbtn_wake_event;
    assign status_rtc_wake = rtc_wake_event;
    assign status_ext_wake = ext_wake_event;
    assign status_wake = any_wake_event;
    assign status_pm1_wake = any_wake_event;

    // ========================================================================
    // Clock Gating Control with Power State Awareness
    // ========================================================================
    
    // Determine target clock gating based on power state
    always_comb begin
        case (current_pwr_state)
            PWR_S0_WORKING: begin
                // S0: Use configuration directly
                clk_gate_target = cfg_clk_gate_ctrl;
            end
            PWR_S1_SLEEP: begin
                // S1: Gate all clocks except essential ones
                // Keep bits [1:0] for minimal functionality
                clk_gate_target = cfg_clk_gate_ctrl & 32'h00000003;
            end
            PWR_S3_SUSPEND: begin
                // S3: Gate all clocks
                clk_gate_target = 32'h00000000;
            end
            default: begin
                clk_gate_target = cfg_clk_gate_ctrl;
            end
        endcase
    end
    
    // Gradually transition clock gates
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            clk_gate_current <= 32'hFFFFFFFF;  // All enabled at reset
        end else begin
            clk_gate_current <= clk_gate_target;  // For simplicity, instant transition
        end
    )
    
    assign clock_gate_en = clk_gate_current;
    assign status_clk_gate_status = clk_gate_current;

    // ========================================================================
    // Power Domain Sequencing
    // ========================================================================
    
    // Determine target power domains based on power state
    always_comb begin
        case (current_pwr_state)
            PWR_S0_WORKING: begin
                // S0: Use configuration directly
                pwr_domain_target = cfg_pwr_domain_ctrl;
            end
            PWR_S1_SLEEP: begin
                // S1: Keep all domains powered (context retention)
                pwr_domain_target = cfg_pwr_domain_ctrl;
            end
            PWR_S3_SUSPEND: begin
                // S3: Power down all except domain 0 (always-on)
                pwr_domain_target = cfg_pwr_domain_ctrl & 8'h01;
            end
            default: begin
                pwr_domain_target = cfg_pwr_domain_ctrl;
            end
        endcase
    end
    
    // Power domain sequencing (instant for MVP)
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            pwr_domain_current <= 8'hFF;  // All powered at reset
        end else begin
            pwr_domain_current <= pwr_domain_target;
        end
    )
    
    assign power_domain_en = pwr_domain_current;
    assign status_pwr_domain_status = pwr_domain_current;

    // ========================================================================
    // PME (Power Management Event) Generation
    // ========================================================================
    
    // PME asserts on any significant power management event
    assign status_pme = power_button_press || sleep_button_press || 
                       any_wake_event || state_transition_done;

    // ========================================================================
    // Reset Status Tracking
    // ========================================================================
    
    // Simple reset source tracking (could be enhanced with external inputs)
    logic first_cycle;
    
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            first_cycle <= 1'b1;
        end else begin
            first_cycle <= 1'b0;
        end
    )
    
    assign status_por_reset = first_cycle;  // Power-on assumed at first reset
    assign status_wdt_reset = 1'b0;         // Would need watchdog input
    assign status_sw_reset = 1'b0;          // Would be set by SW reset mechanism
    assign status_ext_reset = 1'b0;         // Would need external reset pin input
    
    // Reset request outputs (placeholder for future enhancement)
    assign sys_reset_req = 1'b0;
    assign periph_reset_req = 1'b0;

    // ========================================================================
    // Interrupt Aggregation
    // ========================================================================
    
    // Individual interrupt sources
    assign pme_int = status_pme && cfg_pme_enable;
    assign wake_int = status_wake && cfg_wake_enable;
    assign timer_ovf_int = status_timer_overflow && cfg_timer_ovf_enable;
    assign state_trans_int = status_state_transition && cfg_state_trans_enable;
    assign pm1_int = (status_pm1_tmr || status_pm1_pwrbtn || status_pm1_slpbtn || 
                     status_pm1_rtc || status_pm1_wake) && cfg_pm1_enable;
    // gpe_int already calculated above
    
    // Aggregate interrupt output
    assign pm_interrupt = pme_int || wake_int || timer_ovf_int || 
                         state_trans_int || pm1_int || 
                         (gpe_int && cfg_gpe_int_enable);

endmodule : pm_acpi_core
