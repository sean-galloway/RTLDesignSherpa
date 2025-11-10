// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: debounce
// Purpose: //   Multi-channel button/signal debouncer using shift register sampling. Samples
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: debounce
//==============================================================================
// Description:
//   Multi-channel button/signal debouncer using shift register sampling. Samples
//   input signals at regular tick intervals and outputs stable signal only when
//   input has been stable for the configured debounce delay. Supports both
//   normally-open (NO) and normally-closed (NC) button configurations.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   N:
//     Description: Number of input signals/buttons to debounce
//     Type: int
//     Range: 1 to 32
//     Default: 4
//     Constraints: Each signal gets independent shift register
//
//   DEBOUNCE_DELAY:
//     Description: Debounce delay in tick cycles
//     Type: int
//     Range: 2 to 16
//     Default: 4
//     Constraints: Number of consecutive stable samples required before output changes
//
//   PRESSED_STATE:
//     Description: Logic level when button is pressed
//     Type: bit
//     Range: 0 or 1
//     Default: 1
//     Constraints: 1 = Normally Open (NO), 0 = Normally Closed (NC)
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Requires external tick generator (typically ~10ms interval)
//   - Shift register samples input on each tick pulse
//   - Output asserts only when all samples match pressed state
//   - PRESSED_STATE=1: Button pressed = logic 1 (normally-open, pull-down)
//   - PRESSED_STATE=0: Button pressed = logic 0 (normally-closed, pull-up)
//   - Typical config: N=4, DEBOUNCE_DELAY=4, tick=10ms → 40ms debounce
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - counter_freq_invariant.sv - Can generate tick signal
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_debounce.py
//   Run: pytest val/common/test_debounce.py -v
//
//==============================================================================

`include "reset_defs.svh"
module debounce #(
    parameter int N              = 4,  // Number of buttons (input signals)
    parameter int DEBOUNCE_DELAY = 4,  // Debounce delay in tick cycles
    /* verilator lint_off WIDTHTRUNC */
    parameter bit PRESSED_STATE  = 1   // State when the button is pressed (1 for NO, 0 for NC)
    /* verilator lint_on WIDTHTRUNC */
) (
    input  logic         clk,           // Clock signal
    input  logic         rst_n,         // Active low reset signal
    input  logic         long_tick,     // A ~10ms tick to delay between sampling the buttons
    input  logic [N-1:0] button_in,     // Input button signals to be debounced
    output logic [N-1:0] button_out     // Debounced output signals
);

    logic [DEBOUNCE_DELAY-1:0] r_shift_regs        [N];  // Shift registers for each button
    logic [             N-1:0] w_debounced_signals;

    // Debounce logic for each button
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < N; i++) begin
                r_shift_regs[i] <= {DEBOUNCE_DELAY{1'b0}};
            end
        end else if (long_tick) begin
            for (int i = 0; i < N; i++) begin
                r_shift_regs[i] <= {
                    r_shift_regs[i][DEBOUNCE_DELAY-2:0], PRESSED_STATE ? button_in[i] : ~button_in[i]
                };
            end
        end
    )


    // Generate debounced output based on shift register state
    // For both NO and NC, all 1s in shift register means button is pressed
    always_comb begin
        for (int i = 0; i < N; i++) begin
            // Output 1 when shift register shows stable pressed state (all 1s)
            // This works for both NO and NC due to the inversion in the shift logic
            w_debounced_signals[i] = &r_shift_regs[i];
        end
    end

    // Update output signals
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            button_out <= {N{1'b0}};
        end else begin
            button_out <= w_debounced_signals;
        end
    )


endmodule : debounce
