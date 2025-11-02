// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hpet_core
// Purpose: Hpet Core module
//
// Documentation: projects/components/hpet_core.sv/PRD.md
// Subsystem: hpet_core.sv
//
// Author: sean galloway
// Created: 2025-10-18

/**
 * ============================================================================
 * HPET Timer Core (High Speed Domain)
 * ============================================================================
 *
 * DESCRIPTION:
 *   Core HPET timer logic implementing main counter, timer comparators,
 *   and interrupt generation. Operates in high-speed clock domain for
 *   precise timing resolution.
 *
 * FEATURES:
 *   - Configurable-width main counter with configurable enable
 *   - Multiple independent timer comparators
 *   - One-shot and periodic timer modes
 *   - Individual timer interrupt generation
 *   - 32-bit and full-width comparison modes
 * ============================================================================
 */

`timescale 1ns / 1ps

`include "reset_defs.svh"

module hpet_core #(
    parameter int NUM_TIMERS = 3
)(
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input  logic                    clk,
    input  logic                    rst_n,

    // ========================================================================
    // Configuration Interface
    // ========================================================================
    input  logic                    hpet_enable,

    // Main Counter Interface (64-bit fixed)
    input  logic                    counter_write,
    input  logic [63:0]             counter_wdata,
    output logic [63:0]             counter_rdata,

    // Timer Configuration
    input  logic [NUM_TIMERS-1:0]   timer_enable,
    input  logic [NUM_TIMERS-1:0]   timer_int_enable,
    input  logic [NUM_TIMERS-1:0]   timer_type,
    input  logic [NUM_TIMERS-1:0]   timer_size,

    // Timer Comparators (64-bit fixed)
    input  logic [NUM_TIMERS-1:0]   timer_comp_write,
    input  logic [63:0]             timer_comp_wdata [NUM_TIMERS],  // Per-timer data bus
    input  logic                    timer_comp_write_high,
    output logic [63:0]             timer_comp_rdata [NUM_TIMERS],

    // Interrupt Interface
    output logic [NUM_TIMERS-1:0]   timer_int_status,
    input  logic [NUM_TIMERS-1:0]   timer_int_clear,
    output logic [NUM_TIMERS-1:0]   timer_irq
);

    // ============================================================================
    // Main Counter Logic (64-bit fixed)
    // ============================================================================
    logic [63:0] r_main_counter;

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_main_counter <= '0;
        end else begin
            if (counter_write) begin
                // Software write to main counter
                r_main_counter <= counter_wdata;
            end else if (hpet_enable) begin
                // Increment counter when HPET is enabled
                r_main_counter <= r_main_counter + 1'b1;
            end
        end
    )


    assign counter_rdata = r_main_counter;

    // ============================================================================
    // Timer Comparator Registers (64-bit fixed)
    // ============================================================================
    // FPGA Synthesis Attributes: Use distributed RAM for low latency
    // (typically 2-8 timers, small array)
`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif INTEL
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [63:0] r_timer_comparator [NUM_TIMERS];

`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif INTEL
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [63:0] r_timer_period [NUM_TIMERS];  // Store original period for periodic mode

    genvar i;
    generate
        for (i = 0; i < NUM_TIMERS; i++) begin : gen_timer_comparators
            `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
                    r_timer_comparator[i] <= '0;
                    r_timer_period[i] <= '0;
                end else begin
                    if (timer_comp_write[i]) begin
                        // Handle partial writes from 32-bit APB interface
                        // Config_regs sends {32'h0, data} for low writes, {data, 32'h0} for high writes
                        // timer_comp_write_high indicates which half is being written

                        if (timer_comp_write_high) begin
                            // Writing to high 32 bits
                            r_timer_comparator[i][63:32] <= timer_comp_wdata[i][63:32];
                            r_timer_period[i][63:32] <= timer_comp_wdata[i][63:32];
                        end else begin
                            // Writing to low 32 bits
                            r_timer_comparator[i][31:0] <= timer_comp_wdata[i][31:0];
                            r_timer_period[i][31:0] <= timer_comp_wdata[i][31:0];
                        end
                    end else if (w_timer_fire[i] && timer_type[i]) begin
                        // Periodic mode: advance comparator by the original period
                        // This maintains a constant period between interrupts
                        r_timer_comparator[i] <= r_timer_comparator[i] + r_timer_period[i];
                    end
                end
            )


            assign timer_comp_rdata[i] = r_timer_comparator[i];
        end
    endgenerate

    // ============================================================================
    // Timer Comparison and Match Logic - FIXED: Handle different counter widths
    // ============================================================================
    logic [NUM_TIMERS-1:0] w_timer_match;
    logic [NUM_TIMERS-1:0] r_timer_match_prev;

    generate
        for (i = 0; i < NUM_TIMERS; i++) begin : gen_timer_comparison
            always_comb begin
                w_timer_match[i] = 1'b0;

                if (timer_enable[i] && hpet_enable) begin
                    if (timer_size[i]) begin
                        // Full-width comparison
                        w_timer_match[i] = (r_main_counter >= r_timer_comparator[i]);
                    end else begin
                        // 32-bit comparison mode
                        w_timer_match[i] = (r_main_counter[31:0] >= r_timer_comparator[i][31:0]);
                    end
                end
            end
        end
    endgenerate

    // Store previous match state for edge detection
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_timer_match_prev <= '0;
        end else begin
            r_timer_match_prev <= w_timer_match;
        end
    )


    // ============================================================================
    // Timer Mode Handling and Comparator Updates
    // ============================================================================
    logic [NUM_TIMERS-1:0] w_timer_fire;
    logic [NUM_TIMERS-1:0] r_timer_enable_int;

    // Timer fire detection (rising edge of match)
    assign w_timer_fire = w_timer_match & ~r_timer_match_prev;

    // Internal timer enable (can be disabled by one-shot completion)
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_timer_enable_int <= '0;
        end else begin
            r_timer_enable_int <= timer_enable;
        end
    )


    // Timer mode handling merged into comparator logic to avoid conflicts

    // ============================================================================
    // Interrupt Status and Generation
    // ============================================================================
    logic [NUM_TIMERS-1:0] r_interrupt_status;
    logic [NUM_TIMERS-1:0] r_interrupt_output;

    generate
        for (i = 0; i < NUM_TIMERS; i++) begin : gen_interrupt_logic
            // Interrupt status register (sticky)
            `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
                    r_interrupt_status[i] <= 1'b0;
                end else begin
                    if (timer_int_clear[i]) begin
                        // Software clear
                        r_interrupt_status[i] <= 1'b0;
                    end else if (w_timer_fire[i]) begin
                        // Timer fired, set interrupt status
                        r_interrupt_status[i] <= 1'b1;
                    end
                end
            )


            // Interrupt output generation
            `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
                    r_interrupt_output[i] <= 1'b0;
                end else begin
                    if (timer_int_clear[i]) begin
                        // Clear interrupt output
                        r_interrupt_output[i] <= 1'b0;
                    end else if (w_timer_fire[i] && timer_int_enable[i]) begin
                        // Generate interrupt if enabled
                        r_interrupt_output[i] <= 1'b1;
                    end else if (!r_interrupt_status[i]) begin
                        // Auto-clear when status is cleared
                        r_interrupt_output[i] <= 1'b0;
                    end
                end
            )

        end
    endgenerate

    // ============================================================================
    // Output Assignments
    // ============================================================================
    assign timer_int_status = r_interrupt_status;
    assign timer_irq = r_interrupt_output;

    // ============================================================================
    // Parameter Validation and Debug (Synthesis will optimize this away)
    // ============================================================================
    `ifdef SIMULATION
        initial begin
            $display("HPET Core instantiated with 64-bit counter, NUM_TIMERS=%0d", NUM_TIMERS);

            // Validate parameters
            if (NUM_TIMERS < 1 || NUM_TIMERS > 8) begin
                $warning("NUM_TIMERS=%0d is outside typical range (1-8)", NUM_TIMERS);
            end
        end

        // Monitor counter overflow
        always @(posedge clk) begin
            if (hpet_enable && &r_main_counter) begin
                $display("HPET main counter overflow at time %0t", $time);
            end
        end
    `endif

endmodule : hpet_core
