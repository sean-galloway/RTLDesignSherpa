// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: counter_bin_load
// Purpose: //   Binary counter with FIFO-optimized wraparound, variable increment, and load
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: counter_bin_load
//==============================================================================
// Description:
//   Binary counter with FIFO-optimized wraparound, variable increment, and load
//   capability. Supports standard +1 increment, adding arbitrary values, and
//   direct load operations for FIFO pointer management with drop/flush.
//
// Features:
//   - Standard +1 increment (enable input)
//   - Variable increment (add_enable + add_value inputs)
//   - Load operation to directly set counter value
//   - FIFO-optimized wraparound (MSB toggle at 2*MAX)
//   - Priority: load > add > enable
//   - Single-cycle registered output
//   - Combinational next-value preview
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Bit width of counter
//     Type: int
//     Range: 2 to 64
//     Default: 5
//     Constraints: Must be at least 2 to support MSB inversion behavior
//
//   MAX:
//     Description: Maximum count value (counter wraps at MAX-1)
//     Type: int
//     Range: 2 to (2^(WIDTH-1))
//     Default: 10
//     Constraints: Must fit within WIDTH-1 bits (lower bits)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:              Clock input (rising edge active)
//     rst_n:            Asynchronous active-low reset
//     enable:           Count +1 enable (active-high)
//     add_enable:       Add variable amount enable (active-high)
//     add_value:        Value to add when add_enable=1 [WIDTH-1:0]
//     load:             Load enable (active-high, highest priority)
//     load_value:       Value to load when load=1 [WIDTH-1:0]
//
//   Outputs:
//     counter_bin_curr[WIDTH-1:0]:  Current counter value (registered)
//     counter_bin_next[WIDTH-1:0]:  Next counter value (combinational)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Priority (highest to lowest):
//   1. load=1:       counter_bin_next = load_value
//   2. add_enable=1: counter_bin_next = counter_bin_curr + add_value (with wrap)
//   3. enable=1:     counter_bin_next = counter_bin_curr + 1 (with wrap)
//   4. else:         counter_bin_next = counter_bin_curr (hold)
//
//   FIFO Wraparound at 2*MAX:
//   - For enable=1: MSB toggles at MAX-1, lower bits clear
//   - For add_enable=1: Full counter range 0 to 2*MAX-1, wraps at 2*MAX
//   - This allows MSB to indicate full/empty: MSB different = full/empty
//
//   Reset behavior (rst_n=0):
//   - counter_bin_curr = 0
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // FIFO read pointer with drop capability
//   counter_bin_load #(
//       .WIDTH(4),          // 3 bits for addresses (0-7) + 1 MSB for full detection
//       .MAX(8)             // Wrap at count 7
//   ) u_rd_ptr (
//       .clk              (clk),
//       .rst_n            (rst_n),
//       .enable           (rd_en & !fifo_empty),
//       .load             (drop_valid),
//       .load_value       (rd_ptr + drop_count),  // Jump ahead by drop_count
//       .counter_bin_curr (rd_ptr),
//       .counter_bin_next (rd_ptr_next)
//   );
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - counter_bin.sv - Base counter (no load)
//   - counter_load_clear.sv - Counter with load/clear (no FIFO wraparound)
//   - gaxi_drop_fifo_sync.sv - Uses this counter for drop operations
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_counter_bin_load.py
//   Run: pytest val/common/test_counter_bin_load.py -v
//
//==============================================================================

`include "reset_defs.svh"

module counter_bin_load #(
    parameter int WIDTH = 5,
    parameter int MAX   = 10
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    input  logic             add_enable,
    input  logic [WIDTH-1:0] add_value,
    input  logic             load,
    input  logic [WIDTH-1:0] load_value,
    output logic [WIDTH-1:0] counter_bin_curr,
    output logic [WIDTH-1:0] counter_bin_next
);

    // Wraparound boundary (2*MAX for FIFO pointer management)
    localparam int WRAP_BOUNDARY = 2 * MAX;

    // Maximum value for lower bits (excludes MSB)
    logic [WIDTH-2:0] w_max_val;
    assign w_max_val = (WIDTH-1)'(MAX - 1);

    // Extended sum for overflow detection
    logic [WIDTH:0] w_sum_ext;

    // Combinational next-value logic with priority
    always_comb begin
        counter_bin_next = counter_bin_curr;  // Default: hold
        w_sum_ext = '0;  // Default assignment to prevent latch

        if (load) begin
            // Highest priority: Load operation (for drop_all)
            counter_bin_next = load_value;

        end else if (add_enable) begin
            // Variable increment (for drop by count)
            // Add with wraparound at 2*MAX
            w_sum_ext = {1'b0, counter_bin_curr} + {1'b0, add_value};

            if (w_sum_ext >= (WIDTH+1)'(WRAP_BOUNDARY)) begin
                // Wraparound: subtract 2*MAX to bring back into range
                counter_bin_next = w_sum_ext[WIDTH-1:0] - WIDTH'(WRAP_BOUNDARY);
            end else begin
                // No wraparound: use sum directly
                counter_bin_next = w_sum_ext[WIDTH-1:0];
            end

        end else if (enable) begin
            // Standard +1 increment (for normal read/write)
            // Check if lower bits reached MAX-1
            if (counter_bin_curr[WIDTH-2:0] == w_max_val) begin
                // Wraparound: invert MSB, clear lower bits
                counter_bin_next = {~counter_bin_curr[WIDTH-1], {(WIDTH - 1){1'b0}}};
            end else begin
                // Normal increment
                counter_bin_next = counter_bin_curr + 1;
            end
        end
        // else: hold current value (already assigned as default)
    end

    // Registered counter output
    `ALWAYS_FF_RST(clk, rst_n,
        if (!rst_n)
            counter_bin_curr <= 'b0;
        else
            counter_bin_curr <= counter_bin_next;
    )


endmodule : counter_bin_load
