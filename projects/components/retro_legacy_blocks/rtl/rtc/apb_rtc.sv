// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_rtc
// Purpose: APB wrapper for Real-Time Clock (RTC)
//
// Top-level integration module providing:
// - APB4 slave interface
// - Time-of-day tracking (seconds, minutes, hours, day, month, year)
// - BCD and binary counting modes
// - 24-hour and 12-hour (AM/PM) modes
// - Programmable alarm with field masking
// - Leap year handling (2000-2099)
// - Second tick and alarm interrupts
// - Clock source selection (32.768 kHz or system clock for testing)
//
// Follows 3-layer architecture:
//   Layer 1: apb_rtc (this module) - APB interface
//   Layer 2: rtc_config_regs - Register wrapper with status feedback
//   Layer 3: rtc_core - Time counting logic
//
// Register Map (32-bit aligned):
//   0x000: RTC_CONFIG      - Global configuration and control
//   0x004: RTC_CONTROL     - Control (alarm, interrupt enables)
//   0x008: RTC_STATUS      - Status flags
//   0x00C: RTC_SECONDS     - Current seconds (0-59)
//   0x010: RTC_MINUTES     - Current minutes (0-59)
//   0x014: RTC_HOURS       - Current hours (0-23 or 1-12)
//   0x018: RTC_DAY         - Current day (1-31)
//   0x01C: RTC_MONTH       - Current month (1-12)
//   0x020: RTC_YEAR        - Current year (0-99, base 2000)
//   0x024: RTC_ALARM_SEC   - Alarm seconds match
//   0x028: RTC_ALARM_MIN   - Alarm minutes match
//   0x02C: RTC_ALARM_HOUR  - Alarm hours match
//   0x030: RTC_ALARM_MASK  - Alarm field enables

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_rtc (
    //========================================================================
    // Clock and Reset
    //========================================================================
    input  wire                    pclk,           // APB clock
    input  wire                    presetn,        // APB reset (active low)
    input  wire                    rtc_clk,        // RTC clock (32.768 kHz)
    input  wire                    rtc_resetn,     // RTC reset (active low)

    //========================================================================
    // APB4 Slave Interface
    //========================================================================
    input  wire                    s_apb_PSEL,
    input  wire                    s_apb_PENABLE,
    output wire                    s_apb_PREADY,
    input  wire [11:0]             s_apb_PADDR,    // Fixed 12-bit addressing
    input  wire                    s_apb_PWRITE,
    input  wire [31:0]             s_apb_PWDATA,
    input  wire [3:0]              s_apb_PSTRB,
    input  wire [2:0]              s_apb_PPROT,
    output wire [31:0]             s_apb_PRDATA,
    output wire                    s_apb_PSLVERR,

    //========================================================================
    // Interrupt Outputs
    //========================================================================
    output wire                    rtc_alarm_irq,  // Alarm interrupt
    output wire                    rtc_second_irq  // Second tick interrupt
);

    //========================================================================
    // CMD/RSP Interface Signals
    //========================================================================

    logic        w_cmd_valid;
    logic        w_cmd_ready;
    logic        w_cmd_pwrite;
    logic [11:0] w_cmd_paddr;
    logic [31:0] w_cmd_pwdata;
    logic [3:0]  w_cmd_pstrb;

    logic        w_rsp_valid;
    logic        w_rsp_ready;
    logic [31:0] w_rsp_prdata;
    logic        w_rsp_pslverr;

    //========================================================================
    // APB Slave - Convert APB to CMD/RSP Interface
    //========================================================================

    apb_slave #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32),
        .STRB_WIDTH(4),
        .PROT_WIDTH(3)
    ) u_apb_slave (
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

        // Command Interface
        .cmd_valid            (w_cmd_valid),
        .cmd_ready            (w_cmd_ready),
        .cmd_pwrite           (w_cmd_pwrite),
        .cmd_paddr            (w_cmd_paddr),
        .cmd_pwdata           (w_cmd_pwdata),
        .cmd_pstrb            (w_cmd_pstrb),
        .cmd_pprot            (),  // Unused

        // Response Interface
        .rsp_valid            (w_rsp_valid),
        .rsp_ready            (w_rsp_ready),
        .rsp_prdata           (w_rsp_prdata),
        .rsp_pslverr          (w_rsp_pslverr)
    );

    //========================================================================
    // Configuration Register Interface Signals
    //========================================================================

    wire        w_cfg_rtc_enable;
    wire        w_cfg_hour_mode_12;
    wire        w_cfg_bcd_mode;
    wire        w_cfg_clock_select;
    wire        w_cfg_time_set_mode;
    wire        w_cfg_alarm_enable;
    wire        w_cfg_alarm_int_enable;
    wire        w_cfg_second_int_enable;

    wire [7:0]  w_time_seconds_out;
    wire [7:0]  w_time_minutes_out;
    wire [7:0]  w_time_hours_out;
    wire [7:0]  w_time_day_out;
    wire [7:0]  w_time_month_out;
    wire [7:0]  w_time_year_out;
    wire        w_time_regs_wr;

    wire [7:0]  w_time_seconds_in;
    wire [7:0]  w_time_minutes_in;
    wire [7:0]  w_time_hours_in;
    wire [7:0]  w_time_day_in;
    wire [7:0]  w_time_month_in;
    wire [7:0]  w_time_year_in;

    wire [7:0]  w_alarm_seconds;
    wire [7:0]  w_alarm_minutes;
    wire [7:0]  w_alarm_hours;
    wire        w_alarm_sec_match_en;
    wire        w_alarm_min_match_en;
    wire        w_alarm_hour_match_en;

    wire        w_status_alarm_flag;
    wire        w_status_second_tick;
    wire        w_status_time_valid;
    wire        w_status_pm_indicator;

    wire        w_clear_alarm_flag;
    wire        w_clear_second_tick;

    //========================================================================
    // Configuration Registers Module
    //========================================================================

    rtc_config_regs u_config_regs (
        .clk                   (pclk),
        .rst_n                 (presetn),

        // CMD/RSP interface
        .cmd_valid             (w_cmd_valid),
        .cmd_ready             (w_cmd_ready),
        .cmd_pwrite            (w_cmd_pwrite),
        .cmd_paddr             (w_cmd_paddr),
        .cmd_pwdata            (w_cmd_pwdata),
        .cmd_pstrb             (w_cmd_pstrb),

        .rsp_valid             (w_rsp_valid),
        .rsp_ready             (w_rsp_ready),
        .rsp_prdata            (w_rsp_prdata),
        .rsp_pslverr           (w_rsp_pslverr),

        // Configuration outputs
        .cfg_rtc_enable        (w_cfg_rtc_enable),
        .cfg_hour_mode_12      (w_cfg_hour_mode_12),
        .cfg_bcd_mode          (w_cfg_bcd_mode),
        .cfg_clock_select      (w_cfg_clock_select),
        .cfg_time_set_mode     (w_cfg_time_set_mode),
        .cfg_alarm_enable      (w_cfg_alarm_enable),
        .cfg_alarm_int_enable  (w_cfg_alarm_int_enable),
        .cfg_second_int_enable (w_cfg_second_int_enable),

        // Time registers
        .time_seconds_out      (w_time_seconds_out),
        .time_minutes_out      (w_time_minutes_out),
        .time_hours_out        (w_time_hours_out),
        .time_day_out          (w_time_day_out),
        .time_month_out        (w_time_month_out),
        .time_year_out         (w_time_year_out),
        .time_regs_wr          (w_time_regs_wr),

        .time_seconds_in       (w_time_seconds_in),
        .time_minutes_in       (w_time_minutes_in),
        .time_hours_in         (w_time_hours_in),
        .time_day_in           (w_time_day_in),
        .time_month_in         (w_time_month_in),
        .time_year_in          (w_time_year_in),

        // Alarm configuration
        .alarm_seconds         (w_alarm_seconds),
        .alarm_minutes         (w_alarm_minutes),
        .alarm_hours           (w_alarm_hours),
        .alarm_sec_match_en    (w_alarm_sec_match_en),
        .alarm_min_match_en    (w_alarm_min_match_en),
        .alarm_hour_match_en   (w_alarm_hour_match_en),

        // Status signals
        .status_alarm_flag     (w_status_alarm_flag),
        .status_second_tick    (w_status_second_tick),
        .status_time_valid     (w_status_time_valid),
        .status_pm_indicator   (w_status_pm_indicator),

        .clear_alarm_flag      (w_clear_alarm_flag),
        .clear_second_tick     (w_clear_second_tick)
    );

    //========================================================================
    // RTC Core (Time Counting Logic)
    //========================================================================

    rtc_core u_rtc_core (
        .clk                   (pclk),
        .rst                   (~presetn),  // Convert active-low to active-high
        .rtc_clk               (rtc_clk),

        // Configuration
        .cfg_rtc_enable        (w_cfg_rtc_enable),
        .cfg_hour_mode_12      (w_cfg_hour_mode_12),
        .cfg_bcd_mode          (w_cfg_bcd_mode),
        .cfg_clock_select      (w_cfg_clock_select),
        .cfg_time_set_mode     (w_cfg_time_set_mode),
        .cfg_alarm_enable      (w_cfg_alarm_enable),
        .cfg_alarm_int_enable  (w_cfg_alarm_int_enable),
        .cfg_second_int_enable (w_cfg_second_int_enable),

        // Time register interfaces
        .time_seconds_in       (w_time_seconds_out),
        .time_minutes_in       (w_time_minutes_out),
        .time_hours_in         (w_time_hours_out),
        .time_day_in           (w_time_day_out),
        .time_month_in         (w_time_month_out),
        .time_year_in          (w_time_year_out),
        .time_regs_wr          (w_time_regs_wr),

        .time_seconds_out      (w_time_seconds_in),
        .time_minutes_out      (w_time_minutes_in),
        .time_hours_out        (w_time_hours_in),
        .time_day_out          (w_time_day_in),
        .time_month_out        (w_time_month_in),
        .time_year_out         (w_time_year_in),

        // Alarm configuration
        .alarm_seconds         (w_alarm_seconds),
        .alarm_minutes         (w_alarm_minutes),
        .alarm_hours           (w_alarm_hours),
        .alarm_sec_match_en    (w_alarm_sec_match_en),
        .alarm_min_match_en    (w_alarm_min_match_en),
        .alarm_hour_match_en   (w_alarm_hour_match_en),

        // Status outputs
        .status_alarm_flag     (w_status_alarm_flag),
        .status_second_tick    (w_status_second_tick),
        .status_time_valid     (w_status_time_valid),
        .status_pm_indicator   (w_status_pm_indicator),

        // Status flag clears
        .clear_alarm_flag      (w_clear_alarm_flag),
        .clear_second_tick     (w_clear_second_tick),

        // Interrupt outputs
        .rtc_alarm_irq         (rtc_alarm_irq),
        .rtc_second_irq        (rtc_second_irq)
    );

endmodule
