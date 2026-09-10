// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_pm_acpi
// Purpose: APB PM_ACPI Top Level Integration
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pm_acpi/README.md
// Subsystem: pm_acpi
//
// Author: sean galloway
// Created: 2025-11-16
// Updated: 2026-09-09 - GitHub #54: strict decode, sticky status vectors,
//          SYNC_STAGES parameter, reset-request outputs wired

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
 *   0x000-0x00C: ACPI control, status, interrupt enable/status
 *   0x010-0x018: PM1 control, status, enable
 *   0x020-0x024: PM Timer value and configuration
 *   0x030-0x03C: GPE0 status and enable, low and high halves
 *   0x050-0x05C: Clock gate and power domain control/status
 *   0x060-0x06C: Wake status/enable, reset control/status
 *   Only these twenty-one addresses decode. EVERY other address in the 4 KB
 *   window - the old 7-bit alias at 0x080 included - is dropped (write
 *   ignored, read 0) and answered with PSLVERR (see #54 round_2 item 4).
 *
 * POWER MANAGEMENT FEATURES:
 *   - ACPI-compatible PM1 control/status
 *   - 32-bit PM Timer (~3.571 MHz at default divider; ACPI target 3.579545 MHz)
 *   - 32 GPE event sources
 *   - 32 clock gate controls
 *   - 8 power domain controls
 *   - Wake event handling with a latched wake request
 *   - Power state FSM (S0/S1/S3)
 *
 * ASYNCHRONOUS DEVICE PINS:
 *   gpe_events, power_button_n, sleep_button_n, rtc_alarm and ext_wake_n are
 *   all synchronized inside pm_acpi_core, unconditionally, in both CDC_ENABLE
 *   settings. SYNC_STAGES sets the depth for the first, fourth and fifth of
 *   those; the two buttons keep a 3-flop chain that also feeds their press
 *   edge detect. Drive any of them for at least two PM-clock periods.
 *
 * ============================================================================
 */

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: presetn and pm_resetn connect to modules with different reset styles.
// pm_acpi_config_regs uses async reset, peakrdl_to_cmdrsp uses sync reset.
// This is intentional - both modules are in same clock domain.
module apb4_pm_acpi #(
    parameter int CDC_ENABLE = 0, // 0=same clock (apb4_slave), 1=different clocks (apb4_slave_cdc)
    // Async-FIFO pointer encoding, forwarded to the CDC block: 0 = Gray
    // (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit pointers).
    // Gray by default -- Johnson is opt-in.
    parameter int USE_JOHNSON = 0,
    // Depth of the rtc_alarm / ext_wake_n / gpe_events synchronizers in
    // pm_acpi_core. >= 2.
    parameter int SYNC_STAGES = 2
)(
    // ========================================================================
    // Clock and Reset - Dual Domain
    // ========================================================================
    input  logic                    pclk,          // APB clock domain (APB interface)
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

    // GPE event inputs (from system peripherals, asynchronous)
    input  logic [31:0]             gpe_events,

    // Power/sleep buttons (active low, asynchronous)
    input  logic                    power_button_n,
    input  logic                    sleep_button_n,

    // RTC alarm input (asynchronous)
    input  logic                    rtc_alarm,

    // External wake input (active low, asynchronous)
    input  logic                    ext_wake_n,

    // Reset-source inputs. RESET_STATUS.wdt_reset and .ext_reset used to read
    // 0 always because nothing carried the information into the block; these
    // are that information (RLB-009). Tie them high (inactive) if the system
    // has no watchdog or no external reset button.
    input  logic                    wdt_reset_n,
    input  logic                    ext_reset_n,

    // Clock gate outputs (to system clock gates)
    output logic [31:0]             clock_gate_en,

    // Power domain outputs (to power switches)
    output logic [7:0]              power_domain_en,

    // Reset request outputs (one pm_clk pulse per RESET_CTRL write)
    output logic                    sys_reset_req,
    output logic                    periph_reset_req,

    // PM interrupt output (pm_clk domain when CDC_ENABLE=1 -- driven by
    // the core; synchronize externally if consumed on another clock)
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
    logic        w_cfg_soft_reset;
    logic [2:0]  w_cfg_sleep_type;
    logic        w_cfg_sleep_enable;
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
    logic        w_cfg_sys_reset;
    logic        w_cfg_periph_reset;

    // Per-bit W1C clear pulses, config_regs -> core
    logic [3:0]  w_sw_clr_acpi_status;
    logic [5:0]  w_sw_clr_acpi_int_status;
    logic [4:0]  w_sw_clr_pm1_status;
    logic [3:0]  w_sw_clr_wake_status;
    logic [31:0] w_sw_clr_gpe_status;

    // Sticky status vectors, core -> config_regs
    logic [1:0]  w_status_current_state;
    logic [3:0]  w_status_acpi;
    logic [5:0]  w_status_acpi_int;
    logic [4:0]  w_status_pm1;
    logic [3:0]  w_status_wake_src;
    logic [31:0] w_status_gpe;
    logic [3:0]  w_status_reset_src;
    logic [31:0] w_status_pm_timer_value;
    logic [31:0] w_status_clk_gate_status;
    logic [7:0]  w_status_pwr_domain_status;

    // ========================================================================
    // APB Slave - CDC or Non-CDC based on parameter
    // ========================================================================
    generate
        if (CDC_ENABLE != 0) begin : g_apb4_slave_cdc
            // Clock Domain Crossing version for async clocks
            apb4_slave_cdc #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3),
                .DEPTH     (2),
                .USE_JOHNSON (USE_JOHNSON)
            ) u_apb4_slave_cdc (
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
        end else begin : g_apb4_slave_no_cdc
            // Non-CDC version for same clock domain (pclk == pm_clk)
            apb4_slave #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3)
            ) u_apb4_slave (
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
        .cfg_soft_reset           (w_cfg_soft_reset),
        .cfg_sleep_type           (w_cfg_sleep_type),
        .cfg_sleep_enable         (w_cfg_sleep_enable),
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
        .cfg_sys_reset            (w_cfg_sys_reset),
        .cfg_periph_reset         (w_cfg_periph_reset),

        // Per-bit W1C clear pulses to the core
        .sw_clr_acpi_status       (w_sw_clr_acpi_status),
        .sw_clr_acpi_int_status   (w_sw_clr_acpi_int_status),
        .sw_clr_pm1_status        (w_sw_clr_pm1_status),
        .sw_clr_wake_status       (w_sw_clr_wake_status),
        .sw_clr_gpe_status        (w_sw_clr_gpe_status),

        // Status inputs from core
        .status_current_state     (w_status_current_state),
        .status_acpi              (w_status_acpi),
        .status_acpi_int          (w_status_acpi_int),
        .status_pm1               (w_status_pm1),
        .status_wake_src          (w_status_wake_src),
        .status_gpe               (w_status_gpe),
        .status_reset_src         (w_status_reset_src),
        .status_pm_timer_value    (w_status_pm_timer_value),
        .status_clk_gate_status   (w_status_clk_gate_status),
        .status_pwr_domain_status (w_status_pwr_domain_status)
    );

    // ========================================================================
    // PM_ACPI Core Logic
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses pm_clk (async clock, for always-on operation)
    // ========================================================================
    pm_acpi_core #(
        .SYNC_STAGES (SYNC_STAGES)
    ) u_pm_acpi_core (
        // Clock and Reset - conditional based on CDC_ENABLE
        .clk                  (CDC_ENABLE[0] ? pm_clk : pclk),
        .rst_n                (CDC_ENABLE[0] ? pm_resetn : presetn),

        // Configuration inputs
        .cfg_acpi_enable          (w_cfg_acpi_enable),
        .cfg_pm_timer_enable      (w_cfg_pm_timer_enable),
        .cfg_gpe_enable           (w_cfg_gpe_enable),
        .cfg_soft_reset           (w_cfg_soft_reset),
        .cfg_sleep_type           (w_cfg_sleep_type),
        .cfg_sleep_enable         (w_cfg_sleep_enable),
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
        .cfg_sys_reset            (w_cfg_sys_reset),
        .cfg_periph_reset         (w_cfg_periph_reset),

        // Per-bit W1C clear pulses from the register wrapper
        .sw_clr_acpi_status       (w_sw_clr_acpi_status),
        .sw_clr_acpi_int_status   (w_sw_clr_acpi_int_status),
        .sw_clr_pm1_status        (w_sw_clr_pm1_status),
        .sw_clr_wake_status       (w_sw_clr_wake_status),
        .sw_clr_gpe_status        (w_sw_clr_gpe_status),

        // Status outputs
        .status_current_state     (w_status_current_state),
        .status_acpi              (w_status_acpi),
        .status_acpi_int          (w_status_acpi_int),
        .status_pm1               (w_status_pm1),
        .status_wake_src          (w_status_wake_src),
        .status_gpe               (w_status_gpe),
        .status_reset_src         (w_status_reset_src),
        .status_pm_timer_value    (w_status_pm_timer_value),
        .status_clk_gate_status   (w_status_clk_gate_status),
        .status_pwr_domain_status (w_status_pwr_domain_status),

        // External interfaces
        .gpe_events_in        (gpe_events),
        .power_button_n       (power_button_n),
        .sleep_button_n       (sleep_button_n),
        .rtc_alarm            (rtc_alarm),
        .ext_wake_n           (ext_wake_n),
        .wdt_reset_n          (wdt_reset_n),
        .ext_reset_n          (ext_reset_n),
        .clock_gate_en        (clock_gate_en),
        .power_domain_en      (power_domain_en),
        .sys_reset_req        (sys_reset_req),
        .periph_reset_req     (periph_reset_req),
        .pm_interrupt         (pm_interrupt)
    );

/* verilator lint_on SYNCASYNCNET */
endmodule : apb4_pm_acpi
