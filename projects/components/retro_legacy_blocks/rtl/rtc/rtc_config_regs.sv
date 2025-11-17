// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rtc_config_regs
// Purpose: Configuration register wrapper for RTC - PeakRDL Wrapper
//
// This module wraps the PeakRDL-generated rtc_regs module and adds:
// - CMD/RSP to PeakRDL adapter (peakrdl_to_cmdrsp)
// - Bidirectional time register handling
// - Write detection for time register updates
// - Status flag write-to-clear support
// - Status register feedback from rtc_core
//
// ARCHITECTURE:
//   cmd/rsp --> peakrdl_to_cmdrsp adapter --> rtc_regs (PeakRDL) --> hwif --> mapping --> RTC core
//
// Follows PIC/PIT pattern: separate generated registers from integration logic

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rtc_config_regs
    import rtc_regs_pkg::*;
(
    input wire clk,
    input wire rst_n,  // Active-low reset

    // Command/Response Interface (from apb_slave)
    input  wire        cmd_valid,
    output wire        cmd_ready,
    input  wire        cmd_pwrite,
    input  wire [11:0] cmd_paddr,
    input  wire [31:0] cmd_pwdata,
    input  wire [3:0]  cmd_pstrb,

    output wire        rsp_valid,
    input  wire        rsp_ready,
    output wire [31:0] rsp_prdata,
    output wire        rsp_pslverr,

    // RTC Core Interface - Configuration
    output wire        cfg_rtc_enable,
    output wire        cfg_hour_mode_12,
    output wire        cfg_bcd_mode,
    output wire        cfg_clock_select,
    output wire        cfg_time_set_mode,
    output wire        cfg_alarm_enable,
    output wire        cfg_alarm_int_enable,
    output wire        cfg_second_int_enable,

    // Time registers - bidirectional
    output wire [7:0]  time_seconds_out,
    output wire [7:0]  time_minutes_out,
    output wire [7:0]  time_hours_out,
    output wire [7:0]  time_day_out,
    output wire [7:0]  time_month_out,
    output wire [7:0]  time_year_out,
    output wire        time_regs_wr,

    input  wire [7:0]  time_seconds_in,
    input  wire [7:0]  time_minutes_in,
    input  wire [7:0]  time_hours_in,
    input  wire [7:0]  time_day_in,
    input  wire [7:0]  time_month_in,
    input  wire [7:0]  time_year_in,

    // Alarm configuration
    output wire [7:0]  alarm_seconds,
    output wire [7:0]  alarm_minutes,
    output wire [7:0]  alarm_hours,
    output wire        alarm_sec_match_en,
    output wire        alarm_min_match_en,
    output wire        alarm_hour_match_en,

    // Status inputs (from rtc_core)
    input  wire        status_alarm_flag,
    input  wire        status_second_tick,
    input  wire        status_time_valid,
    input  wire        status_pm_indicator,

    // Status flag clears
    output wire        clear_alarm_flag,
    output wire        clear_second_tick
);

    //========================================================================
    // Internal Signals for PeakRDL Passthrough Interface
    //========================================================================

    logic                regblk_req;
    logic                regblk_req_is_wr;
    logic [11:0]         regblk_addr;
    logic [31:0]         regblk_wr_data;
    logic [31:0]         regblk_wr_biten;
    logic                regblk_req_stall_wr;
    logic                regblk_req_stall_rd;
    logic                regblk_rd_ack;
    logic                regblk_rd_err;
    logic [31:0]         regblk_rd_data;
    logic                regblk_wr_ack;
    logic                regblk_wr_err;

    //========================================================================
    // Instantiate CMD/RSP to PeakRDL Adapter
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // CMD/RSP interface (external)
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),

        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),

        // PeakRDL passthrough interface (to register block)
        .regblk_req         (regblk_req),
        .regblk_req_is_wr   (regblk_req_is_wr),
        .regblk_addr        (regblk_addr),
        .regblk_wr_data     (regblk_wr_data),
        .regblk_wr_biten    (regblk_wr_biten),
        .regblk_req_stall_wr(regblk_req_stall_wr),
        .regblk_req_stall_rd(regblk_req_stall_rd),
        .regblk_rd_ack      (regblk_rd_ack),
        .regblk_rd_err      (regblk_rd_err),
        .regblk_rd_data     (regblk_rd_data),
        .regblk_wr_ack      (regblk_wr_ack),
        .regblk_wr_err      (regblk_wr_err)
    );

    //========================================================================
    // PeakRDL Register Interface Structures
    //========================================================================

    rtc_regs__in_t  hwif_in;
    rtc_regs__out_t hwif_out;

    //========================================================================
    // Time Register Write Detection
    //========================================================================

    logic r_time_regs_wr;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_time_regs_wr <= 1'b0;
        end else begin
            // Detect writes to any time register (0x00C-0x020)
            r_time_regs_wr <= regblk_wr_ack && regblk_req_is_wr && 
                              (regblk_addr[11:0] >= 12'h00C) && 
                              (regblk_addr[11:0] <= 12'h020);
        end
    )

    assign time_regs_wr = r_time_regs_wr;

    //========================================================================
    // Status Flag Write-to-Clear Detection
    //========================================================================

    logic r_clear_alarm_flag;
    logic r_clear_second_tick;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_clear_alarm_flag <= 1'b0;
            r_clear_second_tick <= 1'b0;
        end else begin
            // Detect write-1-to-clear on status register (0x008)
            if (regblk_wr_ack && regblk_req_is_wr && (regblk_addr[11:0] == 12'h008)) begin
                r_clear_alarm_flag <= regblk_wr_data[0];   // Bit 0: alarm_flag
                r_clear_second_tick <= regblk_wr_data[1];  // Bit 1: second_tick
            end else begin
                r_clear_alarm_flag <= 1'b0;
                r_clear_second_tick <= 1'b0;
            end
        end
    )

    assign clear_alarm_flag = r_clear_alarm_flag;
    assign clear_second_tick = r_clear_second_tick;

    //========================================================================
    // Time Register Inputs (from rtc_core)
    //========================================================================

    assign hwif_in.RTC_SECONDS.seconds.next = time_seconds_in;
    assign hwif_in.RTC_MINUTES.minutes.next = time_minutes_in;
    assign hwif_in.RTC_HOURS.hours.next = time_hours_in;
    assign hwif_in.RTC_DAY.day.next = time_day_in;
    assign hwif_in.RTC_MONTH.month.next = time_month_in;
    assign hwif_in.RTC_YEAR.year.next = time_year_in;

    //========================================================================
    // Status Register Inputs (from rtc_core)
    //========================================================================

    assign hwif_in.RTC_STATUS.alarm_flag.next = status_alarm_flag;
    assign hwif_in.RTC_STATUS.second_tick.next = status_second_tick;
    assign hwif_in.RTC_STATUS.time_valid.next = status_time_valid;
    assign hwif_in.RTC_STATUS.pm_indicator.next = status_pm_indicator;

    //========================================================================
    // PeakRDL Generated Register File
    //========================================================================

    rtc_regs u_rtc_regs (
        .clk                   (clk),
        .rst                   (~rst_n),  // Convert active-low to active-high
        .s_cpuif_req           (regblk_req),
        .s_cpuif_req_is_wr     (regblk_req_is_wr),
        .s_cpuif_addr          (regblk_addr[5:0]),  // Only lower 6 bits needed
        .s_cpuif_wr_data       (regblk_wr_data),
        .s_cpuif_wr_biten      (regblk_wr_biten),
        .s_cpuif_req_stall_wr  (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd  (regblk_req_stall_rd),
        .s_cpuif_rd_ack        (regblk_rd_ack),
        .s_cpuif_rd_err        (regblk_rd_err),
        .s_cpuif_rd_data       (regblk_rd_data),
        .s_cpuif_wr_ack        (regblk_wr_ack),
        .s_cpuif_wr_err        (regblk_wr_err),
        .hwif_in               (hwif_in),
        .hwif_out              (hwif_out)
    );

    //========================================================================
    // Output Assignments to RTC Core
    //========================================================================

    // Configuration signals
    assign cfg_rtc_enable        = hwif_out.RTC_CONFIG.rtc_enable.value;
    assign cfg_hour_mode_12      = hwif_out.RTC_CONFIG.hour_mode_12.value;
    assign cfg_bcd_mode          = hwif_out.RTC_CONFIG.bcd_mode.value;
    assign cfg_clock_select      = hwif_out.RTC_CONFIG.clock_select.value;
    assign cfg_time_set_mode     = hwif_out.RTC_CONFIG.time_set_mode.value;

    // Control signals
    assign cfg_alarm_enable      = hwif_out.RTC_CONTROL.alarm_enable.value;
    assign cfg_alarm_int_enable  = hwif_out.RTC_CONTROL.alarm_int_enable.value;
    assign cfg_second_int_enable = hwif_out.RTC_CONTROL.second_int_enable.value;

    // Time register outputs (to core for setting time)
    assign time_seconds_out = hwif_out.RTC_SECONDS.seconds.value;
    assign time_minutes_out = hwif_out.RTC_MINUTES.minutes.value;
    assign time_hours_out   = hwif_out.RTC_HOURS.hours.value;
    assign time_day_out     = hwif_out.RTC_DAY.day.value;
    assign time_month_out   = hwif_out.RTC_MONTH.month.value;
    assign time_year_out    = hwif_out.RTC_YEAR.year.value;

    // Alarm configuration
    assign alarm_seconds        = hwif_out.RTC_ALARM_SEC.alarm_seconds.value;
    assign alarm_minutes        = hwif_out.RTC_ALARM_MIN.alarm_minutes.value;
    assign alarm_hours          = hwif_out.RTC_ALARM_HOUR.alarm_hours.value;
    assign alarm_sec_match_en   = hwif_out.RTC_ALARM_MASK.sec_match_en.value;
    assign alarm_min_match_en   = hwif_out.RTC_ALARM_MASK.min_match_en.value;
    assign alarm_hour_match_en  = hwif_out.RTC_ALARM_MASK.hour_match_en.value;

endmodule
