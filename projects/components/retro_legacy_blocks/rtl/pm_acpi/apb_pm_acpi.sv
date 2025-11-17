// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_pm_acpi
// Purpose: APB PM_ACPI Top Level Integration
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pm_acpi/README.md
// Subsystem: pm_acpi
//
// Author: sean galloway
// Created: 2025-11-16

/**
 * ============================================================================
 * APB PM_ACPI Top Level Integration
 * ============================================================================
 *
 * DESCRIPTION:
 *   Top-level module that integrates APB slave with CDC, configuration
 *   registers, and PM_ACPI core. Provides complete ACPI-compatible power
 *   management functionality with optional dual clock domain support.
 *
 * ARCHITECTURE:
 *   - APB Slave CDC: Handles low-frequency APB interface with optional clock crossing
 *   - Config Registers: Register bank for PM_ACPI configuration
 *   - PM_ACPI Core: Power management logic with PM timer, GPE, power states
 *
 * CLOCK DOMAINS:
 *   - pclk: APB interface clock
 *   - pm_clk: PM controller clock (can be async for always-on operation)
 *   - CDC_ENABLE=0: Single clock (pclk == pm_clk, no CDC)
 *   - CDC_ENABLE=1: Dual clock (pclk != pm_clk, CDC enabled)
 *
 * REGISTER MAP: (12-bit address space, 0x000-0xFFF)
 *   0x000-0x00F: ACPI control and status
 *   0x010-0x01F: PM1 registers
 *   0x020-0x02F: PM Timer
 *   0x030-0x04F: GPE registers
 *   0x050-0x06F: Clock gating and power domain control
 *   0x070-0xFFF: Reserved
 *
 * POWER MANAGEMENT FEATURES:
 *   - ACPI-compatible PM1 control/status
 *   - 32-bit PM Timer (3.579545 MHz equivalent)
 *   - 32 GPE event sources
 *   - 32 clock gate controls
 *   - 8 power domain controls
 *   - Wake event handling
 *   - Power state FSM (S0/S1/S3)
 *
 * ============================================================================
 */

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: presetn and pm_resetn connect to modules with different reset styles.
// pm_acpi_config_regs uses async reset, peakrdl_to_cmdrsp uses sync reset.
// This is intentional - both modules are in same clock domain.
module apb_pm_acpi #(
    parameter int CDC_ENABLE = 0  // 0=same clock (apb_slave), 1=different clocks (apb_slave_cdc)
)(
    // ========================================================================
    // Clock and Reset - Dual Domain
    // ========================================================================
    input  logic                    pclk,          // APB clock domain (always used for APB interface)
    input  logic                    presetn,       // APB reset (active low)
    input  logic                    pm_clk,        // PM clock domain (used for PM logic)
    input  logic                    pm_resetn,     // PM reset (active low)

    // ========================================================================
    // APB4 Slave Interface (APB Clock Domain)
    // ========================================================================
    input  logic                    s_apb_PSEL,
    input  logic                    s_apb_PENABLE,
    output logic                    s_apb_PREADY,
    input  logic [11:0]             s_apb_PADDR,   // Fixed 12-bit addressing
    input  logic                    s_apb_PWRITE,
    input  logic [31:0]             s_apb_PWDATA,
    input  logic [3:0]              s_apb_PSTRB,
    input  logic [2:0]              s_apb_PPROT,
    output logic [31:0]             s_apb_PRDATA,
    output logic                    s_apb_PSLVERR,

    // ========================================================================
    // External Power Management Interfaces (PM Clock Domain)
    // ========================================================================
    
    // GPE event inputs (from system peripherals)
    input  logic [31:0]             gpe_events,
    
    // Power/sleep buttons (active low)
    input  logic                    power_button_n,
    input  logic                    sleep_button_n,
    
    // RTC alarm input
    input  logic                    rtc_alarm,
    
    // External wake input (active low)
    input  logic                    ext_wake_n,
    
    // Clock gate outputs (to system clock gates)
    output logic [31:0]             clock_gate_en,
    
    // Power domain outputs (to power switches)
    output logic [7:0]              power_domain_en,
    
    // Reset request outputs
    output logic                    sys_reset_req,
    output logic                    periph_reset_req,
    
    // PM interrupt output (APB clock domain)
    output logic                    pm_interrupt
);

    // ========================================================================
    // CDC Command/Response Interface Signals
    // ========================================================================
    logic                    w_cmd_valid;
    logic                    w_cmd_ready;
    logic                    w_cmd_pwrite;
    logic [11:0]             w_cmd_paddr;
    logic [31:0]             w_cmd_pwdata;
    logic [3:0]              w_cmd_pstrb;
    logic [2:0]              w_cmd_pprot;

    logic                    w_rsp_valid;
    logic                    w_rsp_ready;
    logic [31:0]             w_rsp_prdata;
    logic                    w_rsp_pslverr;

    // ========================================================================
    // Configuration Register Interface Signals
    // ========================================================================
    logic        w_cfg_acpi_enable;
    logic        w_cfg_pm_timer_enable;
    logic        w_cfg_gpe_enable;
    logic        w_cfg_low_power_req;
    logic [2:0]  w_cfg_sleep_type;
    logic        w_cfg_sleep_enable;
    logic        w_cfg_pwrbtn_ovr;
    logic        w_cfg_slpbtn_ovr;
    logic        w_cfg_pm1_tmr_en;
    logic        w_cfg_pm1_pwrbtn_en;
    logic        w_cfg_pm1_slpbtn_en;
    logic        w_cfg_pm1_rtc_en;
    logic [15:0] w_cfg_pm_timer_div;
    logic [31:0] w_cfg_gpe_enables;
    logic [31:0] w_cfg_clk_gate_ctrl;
    logic [7:0]  w_cfg_pwr_domain_ctrl;
    logic        w_cfg_gpe_wake_en;
    logic        w_cfg_pwrbtn_wake_en;
    logic        w_cfg_rtc_wake_en;
    logic        w_cfg_ext_wake_en;
    logic        w_cfg_pme_enable;
    logic        w_cfg_wake_enable;
    logic        w_cfg_timer_ovf_enable;
    logic        w_cfg_state_trans_enable;
    logic        w_cfg_pm1_enable;
    logic        w_cfg_gpe_int_enable;

    // Status signals from core
    logic [1:0]  w_status_current_state;
    logic        w_status_pme;
    logic        w_status_wake;
    logic        w_status_timer_overflow;
    logic        w_status_state_transition;
    logic        w_status_pm1_tmr;
    logic        w_status_pm1_pwrbtn;
    logic        w_status_pm1_slpbtn;
    logic        w_status_pm1_rtc;
    logic        w_status_pm1_wake;
    logic [31:0] w_status_pm_timer_value;
    logic [31:0] w_status_gpe_status;
    logic [31:0] w_status_clk_gate_status;
    logic [7:0]  w_status_pwr_domain_status;
    logic        w_status_gpe_wake;
    logic        w_status_pwrbtn_wake;
    logic        w_status_rtc_wake;
    logic        w_status_ext_wake;
    logic        w_status_por_reset;
    logic        w_status_wdt_reset;
    logic        w_status_sw_reset;
    logic        w_status_ext_reset;

    // ========================================================================
    // APB Slave - CDC or Non-CDC based on parameter
    // ========================================================================
    generate
        if (CDC_ENABLE != 0) begin : g_apb_slave_cdc
            // Clock Domain Crossing version for async clocks
            apb_slave_cdc #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3),
                .DEPTH     (2)
            ) u_apb_slave_cdc (
                // APB Clock Domain
                .pclk                 (pclk),
                .presetn              (presetn),

                // PM Clock Domain
                .aclk                 (pm_clk),
                .aresetn              (pm_resetn),

                // APB Interface (pclk domain)
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (pm_clk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (w_cmd_pprot),

                // Response Interface (pm_clk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end else begin : g_apb_slave_no_cdc
            // Non-CDC version for same clock domain (pclk == pm_clk)
            apb_slave #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3)
            ) u_apb_slave (
                // Single clock domain (use pclk for both APB and cmd/rsp)
                .pclk                 (pclk),
                .presetn              (presetn),

                // APB Interface
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (same pclk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (w_cmd_pprot),

                // Response Interface (same pclk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end
    endgenerate

    // ========================================================================
    // PM_ACPI Configuration Registers
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses pm_clk (async clock)
    // ========================================================================
    pm_acpi_config_regs u_pm_acpi_config_regs (
        // Clock and Reset - conditional based on CDC_ENABLE
        .clk               (CDC_ENABLE[0] ? pm_clk : pclk),
        .rst_n             (CDC_ENABLE[0] ? pm_resetn : presetn),

        // Command/Response Interface
        .cmd_valid         (w_cmd_valid),
        .cmd_ready         (w_cmd_ready),
        .cmd_pwrite        (w_cmd_pwrite),
        .cmd_paddr         (w_cmd_paddr),
        .cmd_pwdata        (w_cmd_pwdata),
        .cmd_pstrb         (w_cmd_pstrb),

        .rsp_valid         (w_rsp_valid),
        .rsp_ready         (w_rsp_ready),
        .rsp_prdata        (w_rsp_prdata),
        .rsp_pslverr       (w_rsp_pslverr),

        // Configuration outputs to core
        .cfg_acpi_enable          (w_cfg_acpi_enable),
        .cfg_pm_timer_enable      (w_cfg_pm_timer_enable),
        .cfg_gpe_enable           (w_cfg_gpe_enable),
        .cfg_low_power_req        (w_cfg_low_power_req),
        .cfg_sleep_type           (w_cfg_sleep_type),
        .cfg_sleep_enable         (w_cfg_sleep_enable),
        .cfg_pwrbtn_ovr           (w_cfg_pwrbtn_ovr),
        .cfg_slpbtn_ovr           (w_cfg_slpbtn_ovr),
        .cfg_pm1_tmr_en           (w_cfg_pm1_tmr_en),
        .cfg_pm1_pwrbtn_en        (w_cfg_pm1_pwrbtn_en),
        .cfg_pm1_slpbtn_en        (w_cfg_pm1_slpbtn_en),
        .cfg_pm1_rtc_en           (w_cfg_pm1_rtc_en),
        .cfg_pm_timer_div         (w_cfg_pm_timer_div),
        .cfg_gpe_enables          (w_cfg_gpe_enables),
        .cfg_clk_gate_ctrl        (w_cfg_clk_gate_ctrl),
        .cfg_pwr_domain_ctrl      (w_cfg_pwr_domain_ctrl),
        .cfg_gpe_wake_en          (w_cfg_gpe_wake_en),
        .cfg_pwrbtn_wake_en       (w_cfg_pwrbtn_wake_en),
        .cfg_rtc_wake_en          (w_cfg_rtc_wake_en),
        .cfg_ext_wake_en          (w_cfg_ext_wake_en),
        .cfg_pme_enable           (w_cfg_pme_enable),
        .cfg_wake_enable          (w_cfg_wake_enable),
        .cfg_timer_ovf_enable     (w_cfg_timer_ovf_enable),
        .cfg_state_trans_enable   (w_cfg_state_trans_enable),
        .cfg_pm1_enable           (w_cfg_pm1_enable),
        .cfg_gpe_int_enable       (w_cfg_gpe_int_enable),

        // Status inputs from core
        .status_current_state     (w_status_current_state),
        .status_pme               (w_status_pme),
        .status_wake              (w_status_wake),
        .status_timer_overflow    (w_status_timer_overflow),
        .status_state_transition  (w_status_state_transition),
        .status_pm1_tmr           (w_status_pm1_tmr),
        .status_pm1_pwrbtn        (w_status_pm1_pwrbtn),
        .status_pm1_slpbtn        (w_status_pm1_slpbtn),
        .status_pm1_rtc           (w_status_pm1_rtc),
        .status_pm1_wake          (w_status_pm1_wake),
        .status_pm_timer_value    (w_status_pm_timer_value),
        .status_gpe_status        (w_status_gpe_status),
        .status_clk_gate_status   (w_status_clk_gate_status),
        .status_pwr_domain_status (w_status_pwr_domain_status),
        .status_gpe_wake          (w_status_gpe_wake),
        .status_pwrbtn_wake       (w_status_pwrbtn_wake),
        .status_rtc_wake          (w_status_rtc_wake),
        .status_ext_wake          (w_status_ext_wake),
        .status_por_reset         (w_status_por_reset),
        .status_wdt_reset         (w_status_wdt_reset),
        .status_sw_reset          (w_status_sw_reset),
        .status_ext_reset         (w_status_ext_reset)
    );

    // ========================================================================
    // PM_ACPI Core Logic
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses pm_clk (async clock, for always-on operation)
    // ========================================================================
    pm_acpi_core u_pm_acpi_core (
        // Clock and Reset - conditional based on CDC_ENABLE
        .clk                  (CDC_ENABLE[0] ? pm_clk : pclk),
        .rst_n                (CDC_ENABLE[0] ? pm_resetn : presetn),

        // Configuration inputs
        .cfg_acpi_enable          (w_cfg_acpi_enable),
        .cfg_pm_timer_enable      (w_cfg_pm_timer_enable),
        .cfg_gpe_enable           (w_cfg_gpe_enable),
        .cfg_low_power_req        (w_cfg_low_power_req),
        .cfg_sleep_type           (w_cfg_sleep_type),
        .cfg_sleep_enable         (w_cfg_sleep_enable),
        .cfg_pwrbtn_ovr           (w_cfg_pwrbtn_ovr),
        .cfg_slpbtn_ovr           (w_cfg_slpbtn_ovr),
        .cfg_pm1_tmr_en           (w_cfg_pm1_tmr_en),
        .cfg_pm1_pwrbtn_en        (w_cfg_pm1_pwrbtn_en),
        .cfg_pm1_slpbtn_en        (w_cfg_pm1_slpbtn_en),
        .cfg_pm1_rtc_en           (w_cfg_pm1_rtc_en),
        .cfg_pm_timer_div         (w_cfg_pm_timer_div),
        .cfg_gpe_enables          (w_cfg_gpe_enables),
        .cfg_clk_gate_ctrl        (w_cfg_clk_gate_ctrl),
        .cfg_pwr_domain_ctrl      (w_cfg_pwr_domain_ctrl),
        .cfg_gpe_wake_en          (w_cfg_gpe_wake_en),
        .cfg_pwrbtn_wake_en       (w_cfg_pwrbtn_wake_en),
        .cfg_rtc_wake_en          (w_cfg_rtc_wake_en),
        .cfg_ext_wake_en          (w_cfg_ext_wake_en),
        .cfg_pme_enable           (w_cfg_pme_enable),
        .cfg_wake_enable          (w_cfg_wake_enable),
        .cfg_timer_ovf_enable     (w_cfg_timer_ovf_enable),
        .cfg_state_trans_enable   (w_cfg_state_trans_enable),
        .cfg_pm1_enable           (w_cfg_pm1_enable),
        .cfg_gpe_int_enable       (w_cfg_gpe_int_enable),

        // Status outputs
        .status_current_state     (w_status_current_state),
        .status_pme               (w_status_pme),
        .status_wake              (w_status_wake),
        .status_timer_overflow    (w_status_timer_overflow),
        .status_state_transition  (w_status_state_transition),
        .status_pm1_tmr           (w_status_pm1_tmr),
        .status_pm1_pwrbtn        (w_status_pm1_pwrbtn),
        .status_pm1_slpbtn        (w_status_pm1_slpbtn),
        .status_pm1_rtc           (w_status_pm1_rtc),
        .status_pm1_wake          (w_status_pm1_wake),
        .status_pm_timer_value    (w_status_pm_timer_value),
        .status_gpe_status        (w_status_gpe_status),
        .status_clk_gate_status   (w_status_clk_gate_status),
        .status_pwr_domain_status (w_status_pwr_domain_status),
        .status_gpe_wake          (w_status_gpe_wake),
        .status_pwrbtn_wake       (w_status_pwrbtn_wake),
        .status_rtc_wake          (w_status_rtc_wake),
        .status_ext_wake          (w_status_ext_wake),
        .status_por_reset         (w_status_por_reset),
        .status_wdt_reset         (w_status_wdt_reset),
        .status_sw_reset          (w_status_sw_reset),
        .status_ext_reset         (w_status_ext_reset),

        // External interfaces
        .gpe_events_in        (gpe_events),
        .power_button_n       (power_button_n),
        .sleep_button_n       (sleep_button_n),
        .rtc_alarm            (rtc_alarm),
        .ext_wake_n           (ext_wake_n),
        .clock_gate_en        (clock_gate_en),
        .power_domain_en      (power_domain_en),
        .sys_reset_req        (sys_reset_req),
        .periph_reset_req     (periph_reset_req),
        .pm_interrupt         (pm_interrupt)
    );

/* verilator lint_on SYNCASYNCNET */
endmodule : apb_pm_acpi
