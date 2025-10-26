// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: shifter_lfsr_galois
// Purpose: //   Galois-configuration Linear Feedback Shift Register (LFSR) with configurable
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: shifter_lfsr_galois
//==============================================================================
// Description:
//   Galois-configuration Linear Feedback Shift Register (LFSR) with configurable
//   tap positions. Uses right-shift architecture with XOR feedback applied at
//   internal tap positions. Suitable for pseudo-random number generation, CRC
//   computation, and pattern generation.
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
//   - Galois LFSRs apply feedback at multiple internal positions
//   - Right-shift operation: MSB=0, tap XORs applied if LSB=1
//   - Maximal-length tap sets produce sequences of period (2^WIDTH - 1)
//   - lfsr_done pulses when LFSR returns to seed value
//   - Tap positions are 1-indexed (tap 1 = bit 0, tap WIDTH = bit WIDTH-1)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - shifter_lfsr_fibonacci.sv - Fibonacci LFSR (external feedback)
//   - shifter_lfsr.sv - Generic LFSR wrapper
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_shifter_lfsr_galois.py
//   Run: pytest val/common/test_shifter_lfsr_galois.py -v
//
//==============================================================================

`include "reset_defs.svh"
module shifter_lfsr_galois #(
    parameter int WIDTH = 8,           // Width of the LFSR
    parameter int TAP_INDEX_WIDTH = 12,
    parameter int TAP_COUNT = 4,        // Number of taps
    parameter int TIW = TAP_INDEX_WIDTH
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic                     enable,     // enable the lfsr
    input  logic                     seed_load,  // enable the seed for the lfsr
    input  logic [     WIDTH-1:0]    seed_data,  // seed value
    input  logic [TAP_COUNT*TIW-1:0] taps,       // Concatenated tap positions
    output logic [     WIDTH-1:0]    lfsr_out,   // LFSR output
    output logic                     lfsr_done  // the lfsr has wrapped around to the seed
);

    logic [WIDTH-1:0]  r_lfsr;
    logic [TIW-1:0]    w_tap_positions [TAP_COUNT];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic              w_feedback;
    logic [WIDTH-1:0]  next_lfsr;

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    always_comb begin
        for (int i = 0; i < TAP_COUNT; i++) begin
            w_tap_positions[i] = taps[i*TIW+:TIW];
        end
    end

    // Observe when the lfsr has looped back
    assign lfsr_done = (lfsr_out == seed_data) ? 1'b1 : 1'b0;

    // Get the LSB for feedback
    assign w_feedback = r_lfsr[0];

    // Calculate next LFSR state with proper Galois feedback
    always_comb begin
        // Start with right shift (include 0 in MSB)
        next_lfsr = {1'b0, r_lfsr[WIDTH-1:1]};

        // Apply Galois feedback taps if LSB is 1
        if (w_feedback) begin
            for (int j = 0; j < TAP_COUNT; j++) begin
                /* verilator lint_off WIDTHEXPAND */
                if (w_tap_positions[j] > 0 && w_tap_positions[j] <= WIDTH) begin
                    // Apply XOR to the tap positions
                    next_lfsr[w_tap_positions[j]-1] = next_lfsr[w_tap_positions[j]-1] ^ 1'b1;
                /* verilator lint_on WIDTHEXPAND */
                end
            end
        end
    end

    // Update LFSR state
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            // Reset LFSR to a non-zero value
            r_lfsr <= {WIDTH{1'b1}};  // initialization to all 1's
        end else if (enable) begin
            if (seed_load) begin
                r_lfsr <= seed_data;
            end else begin
                // Update with the next state calculated in combinational logic
                r_lfsr <= next_lfsr;
            end
        end
    )


    assign lfsr_out = r_lfsr[WIDTH-1:0];

endmodule : shifter_lfsr_galois
