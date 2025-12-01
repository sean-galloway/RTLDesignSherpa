// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rtc_core
// Purpose: Core logic for Real-Time Clock with alarm functionality
//
// Implements RTC functionality:
// - Time counting: seconds, minutes, hours, day, month, year
// - BCD and binary counting modes
// - 24-hour and 12-hour (AM/PM) modes
// - Leap year handling (2000-2099)
// - Alarm comparison with field masking
// - Second tick and alarm interrupts
// - Clock source selection (32.768 kHz or system clock for testing)
//
// Follows PIC/PIT pattern: separate core logic from register interface

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rtc_core (
    input wire clk,              // System clock
    input wire rst,              // Active-high reset
    input wire rtc_clk,          // RTC clock (32.768 kHz)

    // Configuration from registers
    input wire        cfg_rtc_enable,
    input wire        cfg_hour_mode_12,     // 0=24h, 1=12h
    input wire        cfg_bcd_mode,         // 0=binary, 1=BCD
    input wire        cfg_clock_select,     // 0=rtc_clk, 1=clk (for testing)
    input wire        cfg_time_set_mode,    // 1=allow setting time (stops counter)

    input wire        cfg_alarm_enable,
    input wire        cfg_alarm_int_enable,
    input wire        cfg_second_int_enable,

    // Time register interfaces (bidirectional)
    input  wire [7:0] time_seconds_in,
    input  wire [7:0] time_minutes_in,
    input  wire [7:0] time_hours_in,
    input  wire [7:0] time_day_in,
    input  wire [7:0] time_month_in,
    input  wire [7:0] time_year_in,
    input  wire       time_regs_wr,         // Write strobe for time registers

    output wire [7:0] time_seconds_out,
    output wire [7:0] time_minutes_out,
    output wire [7:0] time_hours_out,
    output wire [7:0] time_day_out,
    output wire [7:0] time_month_out,
    output wire [7:0] time_year_out,

    // Alarm configuration
    input  wire [7:0] alarm_seconds,
    input  wire [7:0] alarm_minutes,
    input  wire [7:0] alarm_hours,
    input  wire       alarm_sec_match_en,
    input  wire       alarm_min_match_en,
    input  wire       alarm_hour_match_en,

    // Status outputs
    output wire       status_alarm_flag,
    output wire       status_second_tick,
    output wire       status_time_valid,
    output wire       status_pm_indicator,

    // Status flag clears (write 1 to clear)
    input  wire       clear_alarm_flag,
    input  wire       clear_second_tick,

    // Interrupt outputs
    output wire       rtc_alarm_irq,
    output wire       rtc_second_irq
);

    //========================================================================
    // Clock Selection and Divider
    //========================================================================

    wire selected_clk;
    assign selected_clk = cfg_clock_select ? clk : rtc_clk;

    // Clock divider for generating 1 Hz tick
    // For 32.768 kHz: divide by 32768
    // For system clock: assume ~100MHz, divide accordingly (simplified for now)
    logic [15:0] r_clk_div_counter;
    logic        r_second_tick;
    
    wire [15:0]  clk_div_target;
    assign clk_div_target = cfg_clock_select ? 16'd99 : 16'd32767;  // Simplified

    always_ff @(posedge selected_clk) begin
        if (rst || !cfg_rtc_enable) begin
            r_clk_div_counter <= 16'h0;
            r_second_tick <= 1'b0;
        end else begin
            if (r_clk_div_counter >= clk_div_target) begin
                r_clk_div_counter <= 16'h0;
                r_second_tick <= 1'b1;
            end else begin
                r_clk_div_counter <= r_clk_div_counter + 16'h1;
                r_second_tick <= 1'b0;
            end
        end
    end

    //========================================================================
    // Time Registers
    //========================================================================

    logic [7:0] r_seconds;
    logic [7:0] r_minutes;
    logic [7:0] r_hours;
    logic [7:0] r_day;
    logic [7:0] r_month;
    logic [7:0] r_year;
    logic       r_time_valid;

    //========================================================================
    // BCD/Binary Conversion Helpers
    //========================================================================

    function automatic logic [7:0] bcd_increment(input logic [7:0] bcd_val, input logic [7:0] max_val);
        logic [3:0] ones, tens;
        ones = bcd_val[3:0];
        tens = bcd_val[7:4];
        
        if (ones == 4'd9) begin
            ones = 4'd0;
            if (tens == 4'd9) begin
                tens = 4'd0;
            end else begin
                tens = tens + 4'd1;
            end
        end else begin
            ones = ones + 4'd1;
        end
        
        bcd_increment = {tens, ones};
    endfunction

    function automatic logic [7:0] binary_increment(input logic [7:0] bin_val);
        binary_increment = bin_val + 8'd1;
    endfunction

    function automatic logic bcd_compare_ge(input logic [7:0] bcd_val, input logic [7:0] bcd_limit);
        logic [7:0] bin_val, bin_limit;
        bin_val = (bcd_val[7:4] * 8'd10) + bcd_val[3:0];
        bin_limit = (bcd_limit[7:4] * 8'd10) + bcd_limit[3:0];
        bcd_compare_ge = (bin_val >= bin_limit);
    endfunction

    function automatic logic binary_compare_ge(input logic [7:0] bin_val, input logic [7:0] bin_limit);
        binary_compare_ge = (bin_val >= bin_limit);
    endfunction

    //========================================================================
    // Leap Year Calculation
    //========================================================================

    function automatic logic is_leap_year(input logic [7:0] year_val, input logic is_bcd);
        logic [7:0] year_bin;
        logic [15:0] full_year;
        
        // Convert to binary if needed
        if (is_bcd) begin
            year_bin = (year_val[7:4] * 8'd10) + year_val[3:0];
        end else begin
            year_bin = year_val;
        end
        
        // Add base year 2000
        full_year = 16'd2000 + {8'h0, year_bin};
        
        // Leap year: divisible by 4, except centuries not divisible by 400
        // For 2000-2099: all years divisible by 4 are leap years (2000 is divisible by 400)
        is_leap_year = (year_bin[1:0] == 2'b00);
    endfunction

    //========================================================================
    // Days in Month Calculation
    //========================================================================

    function automatic logic [7:0] days_in_month(
        input logic [7:0] month_val,
        input logic [7:0] year_val,
        input logic is_bcd
    );
        logic [7:0] month_bin;
        logic [7:0] days;
        
        // Convert month to binary if needed
        if (is_bcd) begin
            month_bin = (month_val[7:4] * 8'd10) + month_val[3:0];
        end else begin
            month_bin = month_val;
        end
        
        // Determine days
        case (month_bin)
            8'd1, 8'd3, 8'd5, 8'd7, 8'd8, 8'd10, 8'd12: days = 8'd31;
            8'd4, 8'd6, 8'd9, 8'd11: days = 8'd30;
            8'd2: days = is_leap_year(year_val, is_bcd) ? 8'd29 : 8'd28;
            default: days = 8'd31;
        endcase
        
        // Convert to BCD if needed
        if (is_bcd) begin
            days = {4'd0, days / 8'd10, days % 8'd10};
        end
        
        days_in_month = days;
    endfunction

    //========================================================================
    // Time Counter Logic
    //========================================================================

    always_ff @(posedge selected_clk) begin
        if (rst) begin
            r_seconds <= 8'h00;
            r_minutes <= 8'h00;
            r_hours <= 8'h00;
            r_day <= 8'h01;
            r_month <= 8'h01;
            r_year <= 8'h00;
            r_time_valid <= 1'b0;
        end else if (!cfg_rtc_enable) begin
            // Keep current values when disabled
        end else if (cfg_time_set_mode && time_regs_wr) begin
            // Load new time values
            r_seconds <= time_seconds_in;
            r_minutes <= time_minutes_in;
            r_hours <= time_hours_in;
            r_day <= time_day_in;
            r_month <= time_month_in;
            r_year <= time_year_in;
            r_time_valid <= 1'b1;
        end else if (r_second_tick && !cfg_time_set_mode) begin
            // Increment time
            logic [7:0] next_seconds, next_minutes, next_hours, next_day, next_month, next_year;
            logic carry_minute, carry_hour, carry_day, carry_month, carry_year;
            logic [7:0] max_days;
            
            // Seconds increment
            if (cfg_bcd_mode) begin
                next_seconds = bcd_increment(r_seconds, 8'h59);
                carry_minute = bcd_compare_ge(next_seconds, 8'h60);
                if (carry_minute) next_seconds = 8'h00;
            end else begin
                next_seconds = binary_increment(r_seconds);
                carry_minute = binary_compare_ge(next_seconds, 8'd60);
                if (carry_minute) next_seconds = 8'd0;
            end
            
            // Minutes increment
            if (carry_minute) begin
                if (cfg_bcd_mode) begin
                    next_minutes = bcd_increment(r_minutes, 8'h59);
                    carry_hour = bcd_compare_ge(next_minutes, 8'h60);
                    if (carry_hour) next_minutes = 8'h00;
                end else begin
                    next_minutes = binary_increment(r_minutes);
                    carry_hour = binary_compare_ge(next_minutes, 8'd60);
                    if (carry_hour) next_minutes = 8'd0;
                end
            end else begin
                next_minutes = r_minutes;
                carry_hour = 1'b0;
            end
            
            // Hours increment
            if (carry_hour) begin
                if (cfg_hour_mode_12) begin
                    // 12-hour mode: 12, 1, 2, ..., 11, 12, 1, ...
                    if (cfg_bcd_mode) begin
                        if (r_hours[6:0] == 7'h12) begin
                            next_hours = {~r_hours[7], 7'h01};  // Toggle AM/PM, go to 1
                            carry_day = r_hours[7];  // Carry at 11:59:59 PM -> 12:00:00 AM
                        end else begin
                            next_hours = {r_hours[7], bcd_increment(r_hours[6:0], 7'h12)[6:0]};
                            carry_day = 1'b0;
                        end
                    end else begin
                        // Binary 12-hour is complex, simplified here
                        next_hours = binary_increment(r_hours) % 8'd13;
                        if (next_hours == 8'd0) next_hours = 8'd1;
                        carry_day = (r_hours == 8'd11);  // Simplified
                    end
                end else begin
                    // 24-hour mode
                    if (cfg_bcd_mode) begin
                        next_hours = bcd_increment(r_hours, 8'h23);
                        carry_day = bcd_compare_ge(next_hours, 8'h24);
                        if (carry_day) next_hours = 8'h00;
                    end else begin
                        next_hours = binary_increment(r_hours);
                        carry_day = binary_compare_ge(next_hours, 8'd24);
                        if (carry_day) next_hours = 8'd0;
                    end
                end
            end else begin
                next_hours = r_hours;
                carry_day = 1'b0;
            end
            
            // Day increment
            max_days = days_in_month(r_month, r_year, cfg_bcd_mode);
            if (carry_day) begin
                if (cfg_bcd_mode) begin
                    next_day = bcd_increment(r_day, max_days);
                    carry_month = bcd_compare_ge(next_day, max_days + 8'h01);
                    if (carry_month) next_day = 8'h01;
                end else begin
                    next_day = binary_increment(r_day);
                    carry_month = binary_compare_ge(next_day, max_days + 8'd1);
                    if (carry_month) next_day = 8'd1;
                end
            end else begin
                next_day = r_day;
                carry_month = 1'b0;
            end
            
            // Month increment
            if (carry_month) begin
                if (cfg_bcd_mode) begin
                    next_month = bcd_increment(r_month, 8'h12);
                    carry_year = bcd_compare_ge(next_month, 8'h13);
                    if (carry_year) next_month = 8'h01;
                end else begin
                    next_month = binary_increment(r_month);
                    carry_year = binary_compare_ge(next_month, 8'd13);
                    if (carry_year) next_month = 8'd1;
                end
            end else begin
                next_month = r_month;
                carry_year = 1'b0;
            end
            
            // Year increment
            // Note: Year is 2-digit (00-99), bcd_increment already wraps 99->00
            if (carry_year) begin
                if (cfg_bcd_mode) begin
                    next_year = bcd_increment(r_year, 8'h99);
                    // bcd_increment wraps 99->00 automatically
                end else begin
                    next_year = binary_increment(r_year);
                    if (binary_compare_ge(next_year, 8'd100)) next_year = 8'd0;
                end
            end else begin
                next_year = r_year;
            end
            
            // Update registers
            r_seconds <= next_seconds;
            r_minutes <= next_minutes;
            r_hours <= next_hours;
            r_day <= next_day;
            r_month <= next_month;
            r_year <= next_year;
            r_time_valid <= 1'b1;
        end
    end

    //========================================================================
    // Alarm Comparison
    //========================================================================

    logic r_alarm_match;

    always_ff @(posedge selected_clk) begin
        if (rst || !cfg_rtc_enable) begin
            r_alarm_match <= 1'b0;
        end else if (cfg_alarm_enable && r_second_tick) begin
            logic sec_match, min_match, hour_match;
            
            sec_match = !alarm_sec_match_en || (r_seconds == alarm_seconds);
            min_match = !alarm_min_match_en || (r_minutes == alarm_minutes);
            hour_match = !alarm_hour_match_en || (r_hours == alarm_hours);
            
            r_alarm_match <= sec_match && min_match && hour_match;
        end else begin
            r_alarm_match <= 1'b0;
        end
    end

    //========================================================================
    // Status Flags
    //========================================================================

    logic r_alarm_flag;
    logic r_second_tick_flag;

    always_ff @(posedge clk) begin
        if (rst) begin
            r_alarm_flag <= 1'b0;
            r_second_tick_flag <= 1'b0;
        end else begin
            // Alarm flag
            if (clear_alarm_flag) begin
                r_alarm_flag <= 1'b0;
            end else if (r_alarm_match) begin
                r_alarm_flag <= 1'b1;
            end
            
            // Second tick flag
            if (clear_second_tick) begin
                r_second_tick_flag <= 1'b0;
            end else if (r_second_tick) begin
                r_second_tick_flag <= 1'b1;
            end
        end
    end

    //========================================================================
    // Output Assignments
    //========================================================================

    assign time_seconds_out = r_seconds;
    assign time_minutes_out = r_minutes;
    assign time_hours_out = r_hours;
    assign time_day_out = r_day;
    assign time_month_out = r_month;
    assign time_year_out = r_year;

    assign status_alarm_flag = r_alarm_flag;
    assign status_second_tick = r_second_tick_flag;
    assign status_time_valid = r_time_valid;
    assign status_pm_indicator = cfg_hour_mode_12 && cfg_bcd_mode ? r_hours[7] : 1'b0;

    assign rtc_alarm_irq = r_alarm_flag && cfg_alarm_int_enable;
    assign rtc_second_irq = r_second_tick_flag && cfg_second_int_enable;

endmodule
