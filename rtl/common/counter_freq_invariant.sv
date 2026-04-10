// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: counter_freq_invariant
// Purpose:
//   Frequency-invariant time-based counter that generates consistent
//   microsecond ticks regardless of input clock frequency.
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18
// Updated: 2026-04-09 -- parametric LUT replaces hardcoded frequency table

`timescale 1ns / 1ps

//==============================================================================
// Module: counter_freq_invariant
//==============================================================================
// Description:
//   Divides an arbitrary clock to produce a 1 MHz tick rate for time-based
//   operations. The division factor is selected at run time via `freq_sel`
//   from a lookup table that is generated at elaboration time from the
//   MIN_FREQ_MHZ, MAX_FREQ_MHZ, NUM_FREQ_ENTRIES and FREQ_STRATEGY
//   parameters. This replaces the previous hardcoded 68-entry LUT.
//
// Parameters:
//   COUNTER_WIDTH    -- Width of the output microsecond counter (default 16)
//   MIN_FREQ_MHZ     -- Lowest clock frequency in the LUT, in MHz (default 5)
//   MAX_FREQ_MHZ     -- Highest clock frequency in the LUT, in MHz (default 220)
//   NUM_FREQ_ENTRIES -- Number of entries in the LUT (default 16)
//   FREQ_STRATEGY    -- LUT distribution strategy:
//                        0 = LINEAR (uniform spacing, default)
//                        1 = POW2   (doubling per step, capped at MAX)
//   DEBUG_LUT        -- Print the generated LUT at simulation time 0
//
// Ports:
//   clk              -- Input clock
//   rst_n            -- Active-low asynchronous reset
//   sync_reset_n     -- Synchronous run/reset (0 = reset counters, 1 = run)
//   freq_sel         -- LUT index ($clog2(NUM_FREQ_ENTRIES) bits wide)
//   o_counter        -- Microsecond counter (wraps at 2^COUNTER_WIDTH)
//   tick             -- Single-cycle pulse every microsecond
//
// Timing:
//   Latency          -- 2 cycles (prescaler + output counter)
//   Reconfiguration  -- Immediate (freq_sel change resets and reloads)
//
// LUT generation strategies:
//   LINEAR: freq[i] = MIN + (MAX - MIN) * i / (N - 1)
//           Uniform steps. Good for FPGA bring-up where you want
//           predictable coverage across the operating range.
//
//   POW2:   freq[i] = min(MIN * 2^i, MAX)
//           Doublings from MIN, clamped at MAX. Gives finer resolution
//           at the low end. Saturates once MAX is reached.
//
// Example (defaults: 5-220 MHz, 16 entries, LINEAR):
//   idx  0: 5 MHz    idx  4: 62 MHz   idx  8: 119 MHz  idx 12: 176 MHz
//   idx  1: 19 MHz   idx  5: 76 MHz   idx  9: 133 MHz  idx 13: 191 MHz
//   idx  2: 33 MHz   idx  6: 91 MHz   idx 10: 148 MHz  idx 14: 205 MHz
//   idx  3: 48 MHz   idx  7: 105 MHz  idx 11: 162 MHz  idx 15: 220 MHz
//
// Usage:
//   counter_freq_invariant #(
//       .COUNTER_WIDTH   (16),
//       .MIN_FREQ_MHZ    (100),      // ASIC: 100 MHz - 1 GHz
//       .MAX_FREQ_MHZ    (1000),
//       .NUM_FREQ_ENTRIES(32),
//       .FREQ_STRATEGY   (0)         // LINEAR
//   ) u_timer (
//       .clk         (sys_clk),
//       .rst_n       (sys_rst_n),
//       .sync_reset_n(1'b1),
//       .freq_sel    (cfg_freq_sel),
//       .o_counter   (usec_count),
//       .tick        (usec_tick)
//   );
//
// Related modules:
//   counter_bin.sv        -- basic binary counter
//   counter_load_clear.sv -- programmable counter (used internally)
//   clock_divider.sv      -- integer clock division
//   clock_pulse.sv        -- configurable pulse generator
//
// Test:
//   val/common/test_counter_freq_invariant.py
//
//==============================================================================

`include "reset_defs.svh"

module counter_freq_invariant #(
    // =========================================================================
    // User parameters
    // =========================================================================
    parameter int COUNTER_WIDTH    = 16,     // Width of output microsecond counter
    parameter int MIN_FREQ_MHZ     = 5,      // Lowest supported clock (MHz)
    parameter int MAX_FREQ_MHZ     = 220,    // Highest supported clock (MHz)
    parameter int NUM_FREQ_ENTRIES = 16,     // Number of LUT entries
    parameter int FREQ_STRATEGY    = 0,      // 0 = LINEAR, 1 = POW2
    parameter bit DEBUG_LUT        = 1'b0,   // Print LUT at time 0

    // =========================================================================
    // Derived parameters (do not override)
    // =========================================================================
    parameter int SEL_WIDTH     = (NUM_FREQ_ENTRIES > 1) ? $clog2(NUM_FREQ_ENTRIES) : 1,
    parameter int DIV_WIDTH     = $clog2(MAX_FREQ_MHZ + 1),
    parameter int PRESCALER_MAX = 2 ** DIV_WIDTH
) (
    input  logic                      clk,
    input  logic                      rst_n,
    input  logic                      sync_reset_n,
    input  logic [SEL_WIDTH-1:0]      freq_sel,
    output logic [COUNTER_WIDTH-1:0]  o_counter,
    output logic                      tick
);

    // =========================================================================
    // Elaboration-time parameter validation
    // =========================================================================
    initial begin : param_check
        if (MIN_FREQ_MHZ < 1)
            $error("counter_freq_invariant: MIN_FREQ_MHZ must be >= 1 (got %0d)", MIN_FREQ_MHZ);
        if (MAX_FREQ_MHZ < MIN_FREQ_MHZ)
            $error("counter_freq_invariant: MAX_FREQ_MHZ (%0d) < MIN_FREQ_MHZ (%0d)",
                   MAX_FREQ_MHZ, MIN_FREQ_MHZ);
        if (NUM_FREQ_ENTRIES < 1)
            $error("counter_freq_invariant: NUM_FREQ_ENTRIES must be >= 1 (got %0d)",
                   NUM_FREQ_ENTRIES);
    end

    // =========================================================================
    // LUT generation functions (pure integer, elaboration-time constant)
    //
    // Each function returns the clock frequency in MHz for a given LUT index.
    // Because the division factor == cycles per microsecond == clock MHz,
    // these values ARE the division factors directly.
    // =========================================================================

    // LINEAR: uniform spacing from MIN to MAX
    //   freq[i] = MIN + (MAX - MIN) * i / (N - 1)
    function automatic int linear_freq(
        input int idx, input int n, input int lo, input int hi
    );
        if (n <= 1) return lo;
        return lo + ((hi - lo) * idx) / (n - 1);
    endfunction

    // POW2: doubling per step, clamped at MAX
    //   freq[i] = min(MIN * 2^i, MAX)
    function automatic int pow2_freq(
        input int idx, input int n, input int lo, input int hi
    );
        int v;
        v = lo;
        for (int k = 0; k < idx; k++) begin
            if (v >= hi) return hi;
            v = v * 2;
        end
        if (v > hi) v = hi;
        return v;
    endfunction

    // Strategy selector
    function automatic int freq_mhz_at_idx(input int idx);
        case (FREQ_STRATEGY)
            1:       return pow2_freq  (idx, NUM_FREQ_ENTRIES, MIN_FREQ_MHZ, MAX_FREQ_MHZ);
            default: return linear_freq(idx, NUM_FREQ_ENTRIES, MIN_FREQ_MHZ, MAX_FREQ_MHZ);
        endcase
    endfunction

    // =========================================================================
    // LUT: unpacked array, each entry driven by a constant expression
    //
    // The generate block evaluates freq_mhz_at_idx(gi) at elaboration time
    // (gi is a genvar → constant). Synthesis infers a mux/ROM.
    // =========================================================================
    logic [DIV_WIDTH-1:0] w_div_table [NUM_FREQ_ENTRIES];

    generate
        for (genvar gi = 0; gi < NUM_FREQ_ENTRIES; gi++) begin : gen_div_entry
            assign w_div_table[gi] = DIV_WIDTH'(freq_mhz_at_idx(gi));
        end
    endgenerate

    // =========================================================================
    // Division factor lookup (combinational mux driven by freq_sel)
    // =========================================================================
    logic [DIV_WIDTH-1:0] w_division_factor;
    assign w_division_factor = w_div_table[freq_sel];

    // =========================================================================
    // Frequency change detection and clear pulse
    // =========================================================================
    logic [SEL_WIDTH-1:0] r_prev_freq_sel;
    logic                 r_clear_pulse;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_prev_freq_sel <= '0;
            r_clear_pulse   <= 1'b1;    // start in reset state
        end else begin
            r_prev_freq_sel <= freq_sel;
            r_clear_pulse   <= (freq_sel != r_prev_freq_sel) || !sync_reset_n;
        end
    )

    // =========================================================================
    // Prescaler: counts (division_factor - 1) clock cycles per microsecond
    // =========================================================================
    logic w_prescaler_done;

    counter_load_clear #(
        .MAX(PRESCALER_MAX)
    ) prescaler_counter (
        .clk       (clk),
        .rst_n     (rst_n),
        .clear     (r_clear_pulse),
        .increment (1'b1),
        .load      (1'b1),
        .loadval   (w_division_factor - DIV_WIDTH'(1)),
        .done      (w_prescaler_done),
        /* verilator lint_off PINCONNECTEMPTY */
        .count     ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // =========================================================================
    // Output counter and tick generation
    // =========================================================================
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            o_counter <= '0;
            tick      <= 1'b0;
        end else begin
            if (r_clear_pulse) begin
                o_counter <= '0;
                tick      <= 1'b0;
            end else if (w_prescaler_done && sync_reset_n) begin
                o_counter <= o_counter + 1'b1;
                tick      <= 1'b1;
            end else begin
                tick <= 1'b0;
            end
        end
    )

    // =========================================================================
    // Optional debug: print LUT at time 0
    // =========================================================================
    // synthesis translate_off
    initial begin : debug_print
        if (DEBUG_LUT) begin
            $display("counter_freq_invariant LUT (strategy=%0d, %0d entries, %0d-%0d MHz, DIV_WIDTH=%0d):",
                     FREQ_STRATEGY, NUM_FREQ_ENTRIES, MIN_FREQ_MHZ, MAX_FREQ_MHZ, DIV_WIDTH);
            for (int i = 0; i < NUM_FREQ_ENTRIES; i++) begin
                $display("  freq_sel[%2d] = %4d MHz  (%0d cycles/us)", i,
                         freq_mhz_at_idx(i), freq_mhz_at_idx(i));
            end
        end
    end
    // synthesis translate_on

endmodule : counter_freq_invariant
