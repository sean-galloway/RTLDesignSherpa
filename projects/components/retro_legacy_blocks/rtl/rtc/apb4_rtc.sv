// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_rtc
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
//   Layer 1: apb4_rtc (this module) - APB interface
//   Layer 2: rtc_config_regs - Register wrapper, decode, time-set staging
//   Layer 3: rtc_core - Time counting logic and every clock crossing
//
// CLOCKS AND RESETS
//   pclk/presetn   - APB domain. Resets the register block, the decode, the
//                    read shadow and the ALARM and TICK status flags. It does
//                    NOT reset the time-set commit link, the bookkeeping that
//                    tracks it, the synchronizers that carry its completion
//                    evidence (snapshot pulse, load pulse, tick/alarm level),
//                    RTC_STATUS.commit_timeout - which follows the transfer
//                    it reports, not the register file - the held
//                    clock-source select with its settle one-shot, or the
//                    counter domain's applied configuration. Those take the counter domain's reset, so
//                    a bus reset cannot corrupt a commit, manufacture or lose
//                    a status flag, stop the clock or re-clock it.
//   rtc_clk        - 32.768 kHz counter clock. With
//                    RTC_CONFIG.clock_select=1 the counters run on pclk
//                    instead (test mode); the crossings are identical either
//                    way, they simply degenerate to a same-clock delay.
//   rtc_resetn     - counter-domain reset, passed to rtc_core, which
//                    synchronizes its release onto the selected counter
//                    clock. That release DEPENDS ON pclk: the clock-select
//                    settle one-shot runs on pclk and gates the reset
//                    synchronizer, so the counter domain leaves reset about
//                    7-9 pclk edges after rtc_resetn rises, and with pclk
//                    stopped it never leaves reset at all.
//                    (GitHub #56 round_2 item 5: this port used to be
//                    declared and connected to nothing, so the RTC domain was
//                    reset only by ~presetn and only asynchronously).
//   The two domains reset independently, and the time-set commit link takes
//   its side from that:
//     - presetn alone clears the register file and leaves timekeeping - and
//       any commit already in flight or queued - alone. The commit lands
//       intact; the bus reset does not corrupt it. The counter domain also
//       keeps the configuration it was last given (see cfg_valid), so the
//       register file's reset defaults cannot stop the clock or switch its
//       source. Software re-writes RTC_CONFIG afterwards to re-establish it.
//     - rtc_resetn alone clears the time counters AND both ends of the commit
//       link, including the pclk-side bookkeeping that tracks it (its source
//       side and that bookkeeping are reset through a synchronizer onto
//       pclk), so an unacknowledged commit is dropped and software must
//       re-issue it. A commit staged entirely while rtc_resetn is low never
//       sets busy and is never delivered on release.
//   See rtc_core.sv's RESET TABLE for the flop-by-flop statement.
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

module apb4_rtc #(
    // Watchdog on the time-set commit handshake, in pclk cycles - and on a
    // queued commit's own window, which is the same length. See rtc_core.sv
    // for the floor: it must exceed ~10 counter clocks expressed in pclk
    // cycles (~30500 at 100 MHz pclk against a 32.768 kHz crystal). 0
    // DISABLES both watchdogs: a stalled commit then hangs busy with no
    // report, which is only ever what a formal harness wants.
    parameter int COMMIT_TIMEOUT_CYCLES = 65535
) (
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

    apb4_slave #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32),
        .STRB_WIDTH(4),
        .PROT_WIDTH(3)
    ) u_apb4_slave (
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
    wire        w_cfg_valid;
    wire        w_cfg_alarm_enable;
    wire        w_cfg_alarm_int_enable;
    wire        w_cfg_second_int_enable;

    wire [7:0]  w_time_seconds_out;
    wire [7:0]  w_time_minutes_out;
    wire [7:0]  w_time_hours_out;
    wire [7:0]  w_time_day_out;
    wire [7:0]  w_time_month_out;
    wire [7:0]  w_time_year_out;
    wire        w_time_set_commit;
    wire        w_time_commit_busy;

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
    wire        w_status_commit_timeout;

    wire        w_clear_alarm_flag;
    wire        w_clear_second_tick;
    wire        w_clear_commit_timeout;

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
        .cfg_valid             (w_cfg_valid),
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
        .time_set_commit       (w_time_set_commit),
        .time_commit_busy      (w_time_commit_busy),

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
        .status_commit_timeout (w_status_commit_timeout),

        .clear_alarm_flag      (w_clear_alarm_flag),
        .clear_second_tick     (w_clear_second_tick),
        .clear_commit_timeout  (w_clear_commit_timeout)
    );

    //========================================================================
    // RTC Core (Time Counting Logic)
    //========================================================================

    rtc_core #(
        .COMMIT_TIMEOUT_CYCLES (COMMIT_TIMEOUT_CYCLES)
    ) u_rtc_core (
        .clk                   (pclk),
        .rst_n                 (presetn),
        .rtc_clk               (rtc_clk),
        .rtc_rst_n             (rtc_resetn),

        // Configuration
        .cfg_rtc_enable        (w_cfg_rtc_enable),
        .cfg_hour_mode_12      (w_cfg_hour_mode_12),
        .cfg_bcd_mode          (w_cfg_bcd_mode),
        .cfg_clock_select      (w_cfg_clock_select),
        .cfg_time_set_mode     (w_cfg_time_set_mode),
        .cfg_valid             (w_cfg_valid),
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
        .time_set_commit       (w_time_set_commit),
        .time_commit_busy      (w_time_commit_busy),

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
        .status_commit_timeout (w_status_commit_timeout),

        // Status flag clears
        .clear_alarm_flag      (w_clear_alarm_flag),
        .clear_second_tick     (w_clear_second_tick),
        .clear_commit_timeout  (w_clear_commit_timeout),

        // Interrupt outputs
        .rtc_alarm_irq         (rtc_alarm_irq),
        .rtc_second_irq        (rtc_second_irq)
    );

endmodule
