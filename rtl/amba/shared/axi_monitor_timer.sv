// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_timer
// Purpose: Axi Monitor Timer module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps
/**
 * AXI Monitor Bus Frequency Invariant Timer
 *
 * This module provides a configurable timer for timeout detection in the
 * AXI Error Monitor. It uses the counter_freq_invariant module to generate
 * timing ticks based on the frequency selection provided, allowing the
 * timeout thresholds to remain consistent across different clock frequencies.
 */

`include "reset_defs.svh"
module axi_monitor_timer (
    // Global Clock and Reset
    input  logic        aclk,
    input  logic        aresetn,

    // Timer configuration
    input  logic [3:0]  cfg_freq_sel,    // Frequency selection

    // Timer outputs
    output logic        timer_tick,      // Timer tick signal
    output logic [31:0] timestamp        // Global timestamp counter
);

    // Counter for timestamp generation (flopped)
    logic [31:0] r_timestamp;
    assign timestamp = r_timestamp;

    // Timer tick from frequency invariant counter (combinational)
    logic w_timer_tick;
    assign timer_tick = w_timer_tick;

    // Timestamp counter generation
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_timestamp <= '0;
        end else begin
            // Increment timestamp counter every clock cycle
            r_timestamp <= r_timestamp + 1'b1;
        end
    )


    // Use counter_freq_invariant for generating timer ticks
    counter_freq_invariant #(
        .COUNTER_WIDTH (1),        // Only need 1-bit counter
        .PRESCALER_MAX (65536)     // Maximum prescaler value
    ) timer_counter(
        .clk         (aclk),
        .rst_n       (aresetn),
        .sync_reset_n(1'b1),
        .freq_sel    (cfg_freq_sel),
        .tick        (w_timer_tick),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_counter   ()             // Not used
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi_monitor_timer
