// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: counter_load_clear
// Purpose: //   Parameterizable up counter with load and clear functionality. Counts from
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: counter_load_clear
//==============================================================================
// Description:
//   Parameterizable up counter with load and clear functionality. Counts from
//   0 to a programmable match value, then wraps to 0. Supports runtime loading
//   of the match value and immediate clearing to 0. Useful for configurable
//   delays, loop iterations, and timeout generation.
//
// Features:
//   - Configurable maximum count value (compile-time parameter)
//   - Runtime-loadable match value for flexible counting
//   - Immediate clear to 0 (highest priority)
//   - Increment enable control
//   - Done flag when count reaches match value
//   - Automatic wraparound to 0 after reaching match
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   MAX:
//     Description: Maximum possible count value (compile-time upper bound)
//     Type: int
//     Range: 2 to 2^32-1
//     Default: 32
//     Constraints: Determines counter width = $clog2(MAX)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:        Clock input (rising edge active)
//     rst_n:      Asynchronous active-low reset
//     clear:      Immediate clear to 0 (active-high, highest priority)
//     increment:  Count enable (active-high)
//     load:       Load match value from loadval (active-high, pulsed)
//     loadval[$clog2(MAX)-1:0]: Runtime match value to load
//
//   Outputs:
//     count[$clog2(MAX)-1:0]: Current count value
//     done:       Count reached match value (combinational flag)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        1 cycle (count is registered)
//   Clock-to-Q:     Single flip-flop delay
//   Combinational:  done flag is combinational from count
//   Load Latency:   1 cycle (loadval captured into r_match_val)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Priority Order (highest to lowest):
//   1. Reset (rst_n = 0): count = 0, r_match_val = 0
//   2. Load (load = 1): r_match_val <= loadval (independent of count)
//   3. Clear (clear = 1): count = 0 (overrides increment)
//   4. Increment (increment = 1):
//      - If count == r_match_val: wrap to 0
//      - Else: count = count + 1
//   5. Hold (increment = 0): count unchanged
//
//   Match Value Loading:
//   - Load operation captures loadval into internal r_match_val register
//   - Load can occur independently of counting (same cycle as increment)
//   - Match value change takes effect immediately for comparison
//
//   Done Flag:
//   - Combinational output: done = (count == r_match_val)
//   - Asserts when count reaches match value
//   - Can be used for event detection or loop termination
//
//   Wraparound Behavior:
//   - When count == r_match_val and increment = 1:
//     * Next cycle: count = 0
//     * done remains high for 1 cycle at match value
//
//   Example Sequence (MAX=16, loadval=5):
//   1. Reset: count=0, r_match_val=0, done=1
//   2. Load 5: r_match_val=5, done=0 (count still 0)
//   3. Increment: count=0→1→2→3→4→5, done=1 at count=5
//   4. Next increment: count wraps to 0, done=0
//
//   Timing Diagram (MAX=8, loadval=3):
//
//   {signal: [
//     {name: 'clk',       wave: 'p...........'},
//     {name: 'rst_n',     wave: '01..........'},
//     {name: 'load',      wave: '0.10........'},
//     {name: 'loadval',   wave: 'x.3.x.......', data: ['3']},
//     {name: 'increment', wave: '0...1.......'},
//     {name: 'clear',     wave: '0.........10'},
//     {},
//     {name: 'count',     wave: 'x.=.======.=', data: ['0','0','1','2','3','0','1','0']},
//     {name: 'done',      wave: '0.1.0...1.0.'},
//     {name: 'r_match_val', wave: 'x.=.........', data: ['3']},
//     {},
//     {name: 'Event',     wave: 'x.2.4...6.8.', data: ['Load 3','Count','Wrap','Clear']}
//   ]}
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Fixed delay counter (count to 100)
//   counter_load_clear #(
//       .MAX(256)  // Width = 8 bits
//   ) u_delay_counter (
//       .clk       (clk),
//       .rst_n     (rst_n),
//       .clear     (1'b0),
//       .increment (timer_enable),
//       .load      (init_pulse),
//       .loadval   (8'd99),     // Count 0-99 (100 cycles)
//       .count     (timer_count),
//       .done      (timeout)
//   );
//
//   // Variable loop counter (runtime configurable)
//   counter_load_clear #(
//       .MAX(1024)  // Width = 10 bits
//   ) u_loop_counter (
//       .clk       (clk),
//       .rst_n     (rst_n),
//       .clear     (loop_restart),
//       .increment (loop_step),
//       .load      (cfg_write),
//       .loadval   (cfg_loop_count),  // Runtime programmable
//       .count     (iteration),
//       .done      (loop_done)
//   );
//
//   // Detect done edge for event trigger
//   logic r_done_prev;
//   always_ff @(posedge clk) r_done_prev <= done;
//   assign event_trigger = done & ~r_done_prev;  // Rising edge
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Clear has priority over increment** - Use for emergency stop
//   - **Load is independent** - Can load while counting
//   - Match value change takes effect immediately (same cycle)
//   - done flag is combinational (no register delay)
//   - Counter width automatically sized: $clog2(MAX) bits
//   - For standard modulo-N: set loadval = N-1, count will be 0 to N-1
//   - **Reset state:** count=0, r_match_val=0, done=1 (match at reset)
//   - Increment with done=1 causes immediate wrap to 0 next cycle
//   - **Synthesis:** Infers efficient up-counter with comparator
//   - **Timing:** Critical path is count + 1 through comparison
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - counter_bin.sv - FIFO-optimized counter with MSB inversion
//   - counter_freq_invariant.sv - Time-based counter (ms/us/ns)
//   - counter_bingray.sv - Gray code counter for CDC
//   - counter_ring.sv - Ring counter (one-hot shifting)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_counter_load_clear.py
//   Run: pytest val/common/test_counter_load_clear.py -v
//   Coverage: 95%
//   Key Test Scenarios:
//     - Basic counting to match value
//     - Clear functionality (priority over increment)
//     - Load new match values during counting
//     - Wraparound behavior
//     - done flag edge detection
//     - Hold state (increment = 0)
//
//==============================================================================

`include "reset_defs.svh"

module counter_load_clear #(
    parameter int MAX = 32'd32  // Maximum count value (determines width)
) (
    input logic                     clk,
    input logic                     rst_n,
    input logic                     clear,
    input logic                     increment,
    input logic                     load,
    input logic [$clog2(MAX)-1:0]   loadval,
    output logic [$clog2(MAX)-1:0]  count,
    output logic                    done
);
    // Match value register (runtime programmable)
    logic [$clog2(MAX)-1:0] r_match_val;

    // Main counter register and match value update
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            count <= 'b0;
            r_match_val <= 'b0;
        end else begin
            // Load match value (independent of counting)
            if (load)
                r_match_val <= loadval;

            // Count logic with priority: clear > increment
            if (clear) begin
                count <= 'b0;
            end else if (increment) begin
                count <= (count == r_match_val) ? 'b0 : count + 'b1;
            end
            // Else: hold current count
        end
    )


    // Done flag (combinational)
    assign done = (count == r_match_val);

endmodule : counter_load_clear
