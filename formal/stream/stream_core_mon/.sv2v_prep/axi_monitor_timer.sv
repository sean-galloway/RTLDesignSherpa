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
 * Provides a configurable timer for timeout detection in the AXI Error
 * Monitor. Uses counter_freq_invariant to generate timing ticks based on
 * the frequency selection provided, so timeout thresholds remain consistent
 * across different clock frequencies.
 *
 * cfg_freq_sel width matches the counter_freq_invariant NUM_FREQ_ENTRIES
 * parameter (default 16 entries → 4-bit select).
 */

`include "reset_defs.svh"

module axi_monitor_timer #(
    // Counter_freq_invariant configuration.
    // Override these to change the supported frequency range.
    parameter int CFI_MIN_FREQ_MHZ     = 5,
    parameter int CFI_MAX_FREQ_MHZ     = 220,
    parameter int CFI_NUM_FREQ_ENTRIES = 16,
    parameter int CFI_FREQ_STRATEGY    = 0,   // 0 = LINEAR, 1 = POW2

    // Derived
    parameter int SEL_WIDTH = (CFI_NUM_FREQ_ENTRIES > 1)
                            ? $clog2(CFI_NUM_FREQ_ENTRIES) : 1
) (
    // Global Clock and Reset
    input  logic                  aclk,
    input  logic                  aresetn,

    // Timer configuration
    input  logic [SEL_WIDTH-1:0]  cfg_freq_sel,    // Frequency selection

    // Timer outputs
    output logic                  timer_tick,      // Timer tick signal
    output logic [31:0]           timestamp        // Global timestamp counter
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

    // Frequency-invariant prescaler for 1 MHz tick generation.
    // The counter LUT is generated at elaboration from the CFI_*
    // parameters; no hardcoded frequency table.
    counter_freq_invariant #(
        .COUNTER_WIDTH    (1),                    // Only need tick output
        .MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ),
        .NUM_FREQ_ENTRIES (CFI_NUM_FREQ_ENTRIES),
        .FREQ_STRATEGY    (CFI_FREQ_STRATEGY)
    ) timer_counter (
        .clk         (aclk),
        .rst_n       (aresetn),
        .sync_reset_n(1'b1),
        .freq_sel    (cfg_freq_sel),
        .tick        (w_timer_tick),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_counter   ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : axi_monitor_timer
