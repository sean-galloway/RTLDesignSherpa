//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: counter_bin
        // Purpose: //   Binary counter with configurable maximum value and special FIFO-optimized
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: counter_bin
        //==============================================================================
        // Description:
        //   Binary counter with configurable maximum value and special FIFO-optimized
        //   wraparound behavior. Counts from 0 to MAX-1, then wraps by clearing lower
        //   bits and inverting the MSB. This behavior is specifically designed for
        //   efficient FIFO pointer management where the MSB indicates buffer fullness.
        //
        // Features:
        //   - Configurable bit width (1-64 bits)
        //   - Parameterizable maximum count value
        //   - FIFO-optimized wraparound (MSB inversion + lower bit clear)
        //   - Enable control for gating count operation
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
        //     clk:          Clock input (rising edge active)
        //     rst_n:        Asynchronous active-low reset
        //     enable:       Count enable (active-high)
        //
        //   Outputs:
        //     counter_bin_curr[WIDTH-1:0]:  Current counter value (registered)
        //     counter_bin_next[WIDTH-1:0]:  Next counter value (combinational)
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   Latency:        1 cycle (counter_bin_curr is registered)
        //   Clock-to-Q:     Single flip-flop delay
        //   Combinational:  counter_bin_next available same cycle as enable
        //   Pipeline:       No pipeline stages
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   On each rising clock edge (if enable=1):
        //   1. If counter_bin_curr[WIDTH-2:0] == MAX-1:
        //      - Set counter_bin_next[WIDTH-1] = ~counter_bin_curr[WIDTH-1]
        //      - Set counter_bin_next[WIDTH-2:0] = 0 (clear all lower bits)
        //   2. Else:
        //      - counter_bin_next = counter_bin_curr + 1
        //   3. If enable=0:
        //      - counter_bin_next = counter_bin_curr (hold)
        //
        //   Reset behavior (rst_n=0):
        //   - counter_bin_curr = 0
        //
        //   Special FIFO Behavior:
        //   This counter is optimized for FIFO read/write pointers. The MSB toggles
        //   on wraparound while lower bits reset to 0. This allows simple full/empty
        //   detection by comparing MSBs of read and write pointers.
        //
        //   Timing Diagram (WIDTH=3, MAX=4):
        //
        //   {signal: [
        //     {name: 'clk',              wave: 'p..........'},
        //     {name: 'rst_n',            wave: '01.........'},
        //     {name: 'enable',           wave: '0.1........'},
        //     {name: 'counter_bin_curr', wave: 'x.22222222.', data: ['000','000','001','010','011','100','101','110','111']},
        //     {name: 'counter_bin_next', wave: 'x.22222222.', data: ['000','001','010','011','100','101','110','111','000']},
        //     {},
        //     {name: 'Lower[1:0]',       wave: 'x.22220222.', data: ['00','01','10','11','00','01','10','11']},
        //     {name: 'MSB[2]',           wave: 'x.2...4..2.', data: ['0','0','1','1']},
        //     {},
        //     {name: 'Event',            wave: 'x.2...4...2', data: ['Count', 'Wrap (MSB flip)', 'Wrap (MSB flip)']}
        //   ]}
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // FIFO write pointer (8-entry FIFO, 4-bit counter with MSB for full/empty)
        //   counter_bin #(
        //       .WIDTH(4),          // 3 bits for addresses (0-7) + 1 MSB for full detection
        //       .MAX(8)             // Wrap at count 7
        //   ) u_wr_ptr (
        //       .clk              (clk),
        //       .rst_n            (rst_n),
        //       .enable           (wr_en & !fifo_full),
        //       .counter_bin_curr (wr_ptr),
        //       .counter_bin_next (wr_ptr_next)
        //   );
        //
        //   // Extract address and full detection bit
        //   assign wr_addr = wr_ptr[2:0];   // Lower 3 bits = FIFO address
        //   assign wr_msb  = wr_ptr[3];     // MSB for full/empty detection
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **FIFO-Specific Design:** MSB inversion behavior is NOT standard counter
        //     wraparound. This is specifically for FIFO pointer management.
        //   - For standard modulo-N counter, use counter_load_clear.sv instead
        //   - counter_bin_next provides 1-cycle lookahead for timing closure
        //   - enable=0 holds the count (does NOT reset)
        //   - MAX parameter defines when wraparound occurs (at count MAX-1)
        //   - Lower bits [WIDTH-2:0] count from 0 to MAX-1, then clear to 0
        //   - MSB [WIDTH-1] toggles on each wraparound
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - counter_load_clear.sv - Standard counter with load/clear (no MSB inversion)
        //   - counter_freq_invariant.sv - Time-based counter (ms/us)
        //   - counter_bingray.sv - Gray code counter for CDC
        //   - fifo_sync.sv - Uses this counter for read/write pointers
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_counter_bin.py
        //   Run: pytest val/common/test_counter_bin.py -v
        //   Coverage: 95%
        //
        //------------------------------------------------------------------------------
        // References:
        //------------------------------------------------------------------------------
        //   - "RTL Coding for FIFOs" - Cliff Cummings, SNUG 2002
        //   - FIFO pointer management technique (MSB for full/empty detection)
        //
        //==============================================================================
        
        `include "reset_defs.svh"
        
        module counter_bin #(
            parameter int WIDTH = 5,
            parameter int MAX   = 10
        ) (
 004646     input  logic             clk,
%000002     input  logic             rst_n,
%000000     input  logic             enable,
%000000     output logic [WIDTH-1:0] counter_bin_curr,
%000000     output logic [WIDTH-1:0] counter_bin_next
        );
        
            // Maximum value for lower bits (excludes MSB)
%000002     logic [WIDTH-2:0] w_max_val;
            assign w_max_val = (WIDTH-1)'(MAX - 1);
        
            // Combinational next-value logic
 021936     always_comb begin
%000000         if (enable) begin
                    // Check if lower bits reached MAX-1
%000000             if (counter_bin_curr[WIDTH-2:0] == w_max_val)
                        // Wraparound: invert MSB, clear lower bits
%000000                 counter_bin_next = {~counter_bin_curr[WIDTH-1], {(WIDTH - 1){1'b0}}};
                    else
                        // Normal increment
%000000                 counter_bin_next = counter_bin_curr + 1;
 021766         end else begin
                    // Hold current value when disabled
 021766             counter_bin_next = counter_bin_curr;
                end
            end
        
            // Registered counter output
            `ALWAYS_FF_RST(clk, rst_n,
                if (!rst_n)
                    counter_bin_curr <= 'b0;
                else
                    counter_bin_curr <= counter_bin_next;
 000022     )
        
        
        endmodule : counter_bin
        
        
