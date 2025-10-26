// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: shifter_lfsr_fibonacci
// Purpose: //   Fibonacci-configuration Linear Feedback Shift Register (LFSR) with configurable
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: shifter_lfsr_fibonacci
//==============================================================================
// Description:
//   Fibonacci-configuration Linear Feedback Shift Register (LFSR) with configurable
//   tap positions. Uses right-shift architecture with XOR feedback applied at the
//   MSB. Suitable for pseudo-random number generation, scrambling, and pattern
//   generation.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: LFSR register width in bits
//     Type: int
//     Range: 2 to 128
//     Default: 8
//     Constraints: Determines sequence length (2^WIDTH - 1 states for maximal taps)
//
//   TAP_INDEX_WIDTH:
//     Description: Bit width for tap position indices
//     Type: int
//     Range: $clog2(WIDTH) to 16
//     Default: 12
//     Constraints: Must be wide enough to represent WIDTH (TAP_INDEX_WIDTH >= $clog2(WIDTH))
//
//   TAP_COUNT:
//     Description: Number of feedback tap positions
//     Type: int
//     Range: 1 to 8
//     Default: 4
//     Constraints: Determines feedback complexity. Use maximal-length tap sets for full period.
//
//   Derived Parameters (localparam):
//     TIW: Alias for TAP_INDEX_WIDTH (used for array sizing)
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Fibonacci LFSRs apply feedback at the MSB only (external feedback)
//   - Right-shift operation: MSB=feedback, all bits shift right
//   - Maximal-length tap sets produce sequences of period (2^WIDTH - 1)
//   - lfsr_done pulses when LFSR returns to seed value
//   - Tap positions are 1-indexed (tap 1 = bit 0, tap WIDTH = bit WIDTH-1)
//   - Different feedback than Galois LFSR (see shifter_lfsr_galois.sv)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - shifter_lfsr_galois.sv - Galois LFSR (internal feedback)
//   - shifter_lfsr.sv - Generic LFSR wrapper
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_shifter_lfsr_fibonacci.py
//   Run: pytest val/common/test_shifter_lfsr_fibonacci.py -v
//
//==============================================================================

`include "reset_defs.svh"
module shifter_lfsr_fibonacci #(
    parameter int WIDTH           = 8,   // Width of the LFSR
    parameter int TAP_INDEX_WIDTH = 12,
    parameter int TAP_COUNT       = 4,   // Number of taps
    parameter int TIW = TAP_INDEX_WIDTH
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic                     enable,     // enable the lfsr
    input  logic                     seed_load,  // enable the seed for the lfsr
    input  logic [        WIDTH-1:0] seed_data,  // seed value
    input  logic [TAP_COUNT*TIW-1:0] taps,       // Concatenated tap positions
    output logic [        WIDTH-1:0] lfsr_out,   // LFSR output
    output logic                     lfsr_done  // the lfsr has wrapped around to the seed
);
    // Calculate feedback bit based on tap positions
    logic [WIDTH-1:0] w_taps;
    logic [WIDTH-1:0] r_lfsr;
    logic w_feedback;
    logic [TIW-1:0]   w_tap_positions [TAP_COUNT]; // verilog_lint: waive unpacked-dimensions-range-ordering

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    always_comb begin
        for (int i = 0; i < TAP_COUNT; i++) w_tap_positions[i] = taps[i*TIW+:TIW];
    end

    always_comb begin
        w_taps = 'b0;
        for (int i = 0; i < TAP_COUNT; i++)
            /* verilator lint_off WIDTHTRUNC */
            if (w_tap_positions[i] > 0) w_taps[w_tap_positions[i]-1'b1] = 1'b1;
            /* verilator lint_on WIDTHTRUNC */
    end

    ////////////////////////////////////////////////////////////////////////////
    // Calculate feedback by XORing tapped bits
    assign w_feedback = ^(r_lfsr & w_taps);

    ////////////////////////////////////////////////////////////////////////////
    // observe when the lfsr has looped back
    assign lfsr_done = (lfsr_out == seed_data) ? 1'b1 : 1'b0;

    // Output value immediately
    assign lfsr_out = r_lfsr;

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            r_lfsr <= 'b0;  // initialization to all 0's
        end else begin
            if (enable) begin
                if (seed_load) begin
                    r_lfsr <= seed_data;  // Load seed
                end else if (|r_lfsr) begin // Only shift if we have non-zero value
                    // Fibonacci LFSR: Shift right, feedback to MSB
                    r_lfsr <= {w_feedback, r_lfsr[WIDTH-1:1]};
                end
            end
        end
    )


endmodule : shifter_lfsr_fibonacci
