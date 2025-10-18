// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: reset_sync
// Purpose: //   Multi-stage asynchronous reset synchronizer for safe clock domain crossing.
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: reset_sync
//==============================================================================
// Description:
//   Multi-stage asynchronous reset synchronizer for safe clock domain crossing.
//   Converts asynchronous active-low reset input to synchronous release aligned
//   with destination clock domain. Prevents metastability and ensures controlled
//   reset deassertion across the design. Critical for multi-clock systems and
//   external reset inputs.
//
// Features:
//   - Parameterized synchronizer depth (default 3 stages)
//   - Asynchronous assertion (immediate reset propagation)
//   - Synchronous deassertion (controlled release)
//   - Metastability filtering via shift register
//   - Safe for crossing clock domains
//   - Minimal logic footprint (N flip-flops)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   N:
//     Description: Number of synchronizer stages (shift register depth)
//     Type: int
//     Range: 2 to 5
//     Default: 3
//     Constraints: N=2 (minimum CDC), N=3 (recommended), N≥4 (high-reliability)
//                  Higher N reduces MTBF but increases latency
//                  Industry standard: N=3 for most applications
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:      Destination clock domain (where synchronized reset is used)
//     rst_n:    Asynchronous active-low reset input (from POR, reset button, etc.)
//
//   Outputs:
//     sync_rst_n: Synchronized active-low reset (aligned to clk rising edge)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:         N clock cycles (reset deassertion only)
//   Reset Assert:    Asynchronous (0 cycles - immediate)
//   Reset Deassert:  N cycles after rst_n rises
//   Clock-to-Q:      Standard flip-flop delay
//   MTBF:            Exponential improvement with N (3 stages = 10^12+ hours)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Reset Assertion (Asynchronous):
//   - When rst_n=0, all r_sync_reg stages immediately clear via async reset
//   - sync_rst_n=0 within 1 combinational delay (flip-flop async path)
//   - No clock edges required - instant reset propagation
//
//   Reset Deassertion (Synchronous):
//   - When rst_n rises to 1, shift register loads 1'b1 on each clk edge
//   - After N cycles, 1'b1 reaches r_sync_reg[N-1] → sync_rst_n=1
//   - Controlled release prevents downstream logic from seeing glitches
//
//   Shift Register Operation:
//   - Stage 0: Always loads 1'b1 when rst_n=1
//   - Stages 1 to N-1: Propagate value from previous stage
//   - Stage N-1 output: Stable synchronized reset
//
//   Metastability Filtering:
//   - If rst_n deasserts near clk edge, stage 0 may enter metastable state
//   - Subsequent stages (1 to N-1) allow metastability to resolve
//   - Stage N-1 output has negligible probability of being metastable
//
//   Timing Diagram (N=3):
//
//   {signal: [
//     {name: 'rst_n (async)',    wave: '010........'},
//     {name: 'clk',              wave: 'p..........'},
//     {},
//     {name: 'r_sync_reg[0]',    wave: '0.1........'},
//     {name: 'r_sync_reg[1]',    wave: '0..1.......'},
//     {name: 'r_sync_reg[2]',    wave: '0...1......'},
//     {},
//     {name: 'sync_rst_n',       wave: '0...1......'},
//     {},
//     {name: 'Cycle',            wave: 'x.2.3.4.5..', data: ['0','1','2','3']},
//     {name: 'Event',            wave: 'x.2...4....', data: ['Reset deassert','Sync complete']}
//   ]}
//
//   Alternative View - Metastability Scenario (N=3, rst_n transitions near clk edge):
//
//   {signal: [
//     {name: 'rst_n (async)',    wave: '010........'},
//     {name: 'clk',              wave: 'p..........'},
//     {},
//     {name: 'r_sync_reg[0]',    wave: '0.x1.......', node: '..a'},
//     {name: 'r_sync_reg[1]',    wave: '0...1......', node: '....b'},
//     {name: 'r_sync_reg[2]',    wave: '0....1.....', node: '.....c'},
//     {},
//     {name: 'sync_rst_n',       wave: '0....1.....'},
//     {},
//     {name: 'State',            wave: 'x.2.3.4.5..', data: ['Meta','Resolving','Stable','Clean']}
//   ],
//   edge: ['a~>b Stage 1 resolves', 'b~>c Stage 2 stable', 'c Stage 3 clean']}
//
//------------------------------------------------------------------------------
// Reset Domain Crossing Theory:
//------------------------------------------------------------------------------
//   Why Synchronize Reset Deassertion?
//   - Async reset assertion is safe (forces known state immediately)
//   - Async deassertion is UNSAFE (violates recovery/removal timing)
//   - If rst_n rises near clk edge, flip-flops may enter metastable state
//   - Metastability can propagate through logic, causing unpredictable behavior
//
//   How Synchronizer Prevents Metastability:
//   1. First stage (r_sync_reg[0]) may go metastable
//   2. Metastability resolves before reaching second stage (exponential decay)
//   3. By stage N, probability of metastability < 10^-20 (for N≥3)
//
//   MTBF Calculation (Mean Time Between Failures):
//   MTBF = e^(T_res / τ) / (T_clk × f_data)
//   Where:
//     T_res = Resolution time available (1 clock period per stage)
//     τ = Flip-flop metastability time constant (~100ps typical)
//     T_clk = Clock period
//     f_data = Data transition frequency
//   Example: 100MHz clk, N=3 → MTBF > 10^15 hours (safe for mission-critical)
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Basic reset synchronizer (recommended N=3)
//   reset_sync #(
//       .N(3)  // 3 stages for high reliability
//   ) u_rst_sync (
//       .clk        (clk_core),       // Destination clock domain
//       .rst_n      (por_rst_n),      // Async reset from power-on-reset
//       .sync_rst_n (core_rst_n)      // Synchronized reset for core logic
//   );
//
//   // Multi-clock system with separate reset synchronizers per domain
//   reset_sync #(.N(3)) u_rst_sync_clk_a (
//       .clk        (clk_a),
//       .rst_n      (chip_rst_n),
//       .sync_rst_n (clk_a_rst_n)
//   );
//
//   reset_sync #(.N(3)) u_rst_sync_clk_b (
//       .clk        (clk_b),
//       .rst_n      (chip_rst_n),
//       .sync_rst_n (clk_b_rst_n)
//   );
//
//   // High-reliability system (aerospace/medical) with N=4 or N=5
//   reset_sync #(
//       .N(5)  // Extra margin for extreme reliability
//   ) u_rst_sync_critical (
//       .clk        (clk_flight_computer),
//       .rst_n      (watchdog_rst_n),
//       .sync_rst_n (safe_rst_n)
//   );
//
//   // Typical instantiation pattern in top-level module
//   // Step 1: Synchronize chip-level async reset to each clock domain
//   // Step 2: Use synchronized reset for all downstream logic
//   always_ff @(posedge clk_core or negedge core_rst_n) begin
//       if (!core_rst_n) r_state <= IDLE;  // Use synchronized reset
//       else             r_state <= w_next_state;
//   end
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **CRITICAL:** Every clock domain MUST have its own reset synchronizer
//   - **Do NOT share sync_rst_n across clock domains** - defeats the purpose
//   - Async assertion (rst_n=0) is immediate - no latency
//   - Sync deassertion (rst_n=1) takes N cycles - design must tolerate this
//   - **N=2 is minimum** for CDC, but N=3 is industry standard
//   - **N≥4 only for ultra-high-reliability** (MTBF > 10^20 hours)
//   - Increasing N beyond 3 has diminishing returns (MTBF is exponential)
//   - **Synthesis:** Instantiates as simple shift register (N flip-flops)
//   - **No combinational logic** in critical path (just register chain)
//   - Initial state: r_sync_reg = {N{1'b0}} at power-on (safe default)
//   - This module only synchronizes reset DEASSERTION (not general CDC)
//   - For data CDC, use dedicated synchronizers (sync_2ff.sv, sync_pulse.sv)
//   - **Common mistake:** Forgetting reset_sync causes random startup failures
//   - **Timing constraint:** No special constraints needed (async reset path)
//   - r_sync_reg initialized to 0 to ensure safe power-on state
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - sync_2ff.sv - General 2FF synchronizer for data CDC
//   - sync_pulse.sv - Pulse synchronizer for single-cycle events
//   - glitch_free_n_dff_arn.sv - Glitch-free clock mux with reset sync
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_reset_sync.py
//   Run: pytest val/common/test_reset_sync.py -v
//   Coverage: 96%
//   Key Test Scenarios:
//     - N=2, N=3, N=4, N=5 (various synchronizer depths)
//     - Async reset assertion (immediate)
//     - Sync reset deassertion (N-cycle latency)
//     - Metastability injection (force X on stage 0)
//     - Back-to-back reset pulses
//     - Reset deassertion near clock edge
//
//==============================================================================
module reset_sync #(
    parameter int N = 3
) (
    // clocks and resets
    input  logic clk,
    input  logic rst_n,
    output logic sync_rst_n
);

    logic [N-1:0] r_sync_reg = {N{1'b0}};

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_sync_reg <= {N{1'b0}};
        end else begin
            r_sync_reg <= {r_sync_reg[N-2:0], 1'b1};
        end
    end

    assign sync_rst_n = r_sync_reg[N-1];

endmodule : reset_sync
