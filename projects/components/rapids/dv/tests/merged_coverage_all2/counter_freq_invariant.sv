//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: counter_freq_invariant
        // Purpose: //   Frequency-invariant time-based counter that generates consistent microsecond
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: counter_freq_invariant
        //==============================================================================
        // Description:
        //   Frequency-invariant time-based counter that generates consistent microsecond
        //   ticks regardless of input clock frequency. Divides arbitrary clock (100MHz-2GHz)
        //   to produce 1MHz tick rate for time-based operations. Supports runtime frequency
        //   reconfiguration via 7-bit freq_sel lookup table.
        //
        // Features:
        //   - Clock-frequency-agnostic timing (100MHz to 2GHz input range)
        //   - 1MHz output tick rate (1 tick per microsecond)
        //   - Runtime frequency reconfiguration (68 predefined freq_sel values)
        //   - Automatic prescaler calculation from lookup table
        //   - Synchronous reset for clean counter restart
        //   - Configurable counter width and prescaler range
        //   - Uses counter_load_clear internally for precise timing
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   COUNTER_WIDTH:
        //     Description: Width of microsecond output counter
        //     Type: int
        //     Range: 8 to 32
        //     Default: 16
        //     Constraints: Determines rollover period = 2^COUNTER_WIDTH microseconds
        //                  WIDTH=16 → 65.5ms, WIDTH=20 → 1.05s, WIDTH=32 → 71.6 minutes
        //
        //   PRESCALER_MAX:
        //     Description: Maximum prescaler counter value (must support highest freq)
        //     Type: int
        //     Range: 256 to 4096
        //     Default: 2048
        //     Constraints: Must be ≥ max(w_division_factor) = 2000 for 2GHz support
        //                  Prescaler width = $clog2(PRESCALER_MAX)
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     clk:           Clock input (100MHz to 2GHz supported)
        //     rst_n:         Asynchronous active-low reset
        //     sync_reset_n:  Synchronous reset (0=reset, 1=run)
        //     freq_sel[6:0]: Frequency selection (0-67 valid, 68-127 default to 1GHz)
        //
        //   Outputs:
        //     counter[COUNTER_WIDTH-1:0]: Microsecond counter (wraps at 2^WIDTH)
        //     tick:                        Single-cycle pulse every microsecond
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   Latency:        2 cycles (prescaler + output counter)
        //   Clock-to-Q:     2 flip-flop delays
        //   Tick Duration:  1 clock cycle
        //   Tick Period:    Exactly 1 microsecond (frequency-invariant)
        //   Reconfiguration: Immediate (takes effect next cycle after freq_sel change)
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   Frequency Selection Lookup:
        //   - freq_sel[6:0] maps to division factor via case statement
        //   - Example: freq_sel=0 → 100 (100MHz), freq_sel=47 → 1000 (1GHz)
        //   - Division factor = clock cycles per microsecond
        //   - Lookup table covers 100MHz to 2GHz in fine increments
        //
        //   Prescaler Operation:
        //   - Uses counter_load_clear to count (division_factor - 1) clock cycles
        //   - Asserts w_prescaler_done every microsecond
        //   - Automatically reloads with division factor on each tick
        //   - Clears when sync_reset_n=0 or freq_sel changes
        //
        //   Output Counter:
        //   - Increments on every w_prescaler_done pulse (1MHz rate)
        //   - Rolls over at 2^COUNTER_WIDTH microseconds
        //   - Cleared by sync_reset_n=0 or freq_sel change
        //
        //   Tick Pulse:
        //   - Single-cycle pulse coincident with counter increment
        //   - Only asserted when sync_reset_n=1 (gated during reset)
        //   - Clean edge for event synchronization
        //
        //   Frequency Change Sequence:
        //   1. Detect freq_sel change (r_prev_freq_sel != freq_sel)
        //   2. Assert r_clear_pulse for 1 cycle
        //   3. Reset prescaler and output counter
        //   4. Resume operation with new division factor
        //
        //   Timing Diagram (freq_sel=15 → 200MHz, COUNTER_WIDTH=16):
        //
        //   {signal: [
        //     {name: 'clk (200MHz)',  wave: 'p.....................'},
        //     {name: 'rst_n',         wave: '01....................'},
        //     {name: 'sync_reset_n',  wave: '0.10..........0.10....'},
        //     {name: 'freq_sel[6:0]', wave: 'x.=.........=.=.......', data: ['15(200MHz)','31(500MHz)','15(200MHz)']},
        //     {},
        //     {name: 'w_division_factor', wave: 'x.=.........=.=.......', data: ['200','500','200']},
        //     {name: 'prescaler_count',   wave: 'x.==......==..==......', data: ['0-199','0-199','0-499','0-199']},
        //     {name: 'w_prescaler_done',  wave: '0...10....10...10.....'},
        //     {},
        //     {name: 'tick',          wave: '0....10....10...10....'},
        //     {name: 'counter[15:0]', wave: 'x.=..=.=...=.=..=.=...', data: ['0','0','1','2','0','0','1']},
        //     {name: 'r_clear_pulse', wave: '01.0.......1.01.0.....'},
        //     {},
        //     {name: 'Event',         wave: 'x.2.4.....4.6.2.4.....', data: ['Reset','1μs tick','1μs tick','Freq change','Reset','1μs tick']},
        //     {name: 'Timing',        wave: 'x...2.....2...2.......', data: ['1μs @ 200clk','1μs @ 200clk','1μs @ 500clk']}
        //   ]}
        //
        //------------------------------------------------------------------------------
        // Frequency Selection Table (Partial):
        //------------------------------------------------------------------------------
        //   freq_sel | Clock Freq | Division Factor | Use Case
        //   ---------|------------|-----------------|---------------------------
        //   0        | 100MHz     | 100             | Low-speed FPGA
        //   10       | 150MHz     | 150             | Mid-range FPGA
        //   15       | 200MHz     | 200             | High-speed FPGA
        //   18       | 250MHz     | 250             | FPGA PCIe
        //   26       | 400MHz     | 400             | DDR controller
        //   31       | 500MHz     | 500             | High-speed ASIC
        //   47       | 1000MHz    | 1000            | 1GHz ASIC
        //   67       | 2000MHz    | 2000            | 2GHz ASIC
        //   default  | 1000MHz    | 1000            | Fallback (1GHz)
        //
        //   See module code for complete 68-entry lookup table (100MHz-2GHz).
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // 1ms timeout timer at 200MHz
        //   counter_freq_invariant #(
        //       .COUNTER_WIDTH(16),   // 65.5ms max
        //       .PRESCALER_MAX(2048)  // Supports up to 2GHz
        //   ) u_timer_1ms (
        //       .clk         (clk_200mhz),
        //       .rst_n       (rst_n),
        //       .sync_reset_n(timer_enable),    // 0=hold, 1=run
        //       .freq_sel    (7'd15),           // 200MHz = freq_sel[15]
        //       .counter     (usec_count),      // Microsecond counter
        //       .tick        (usec_tick)        // 1MHz tick output
        //   );
        //   assign timeout_1ms = (usec_count == 1000);  // 1ms = 1000μs
        //
        //   // Runtime frequency switching (clock source change)
        //   logic [6:0] current_freq_sel;
        //   always_comb begin
        //       case (clock_source)
        //           2'b00: current_freq_sel = 7'd10;  // 150MHz
        //           2'b01: current_freq_sel = 7'd15;  // 200MHz
        //           2'b10: current_freq_sel = 7'd18;  // 250MHz
        //           2'b11: current_freq_sel = 7'd26;  // 400MHz
        //       endcase
        //   end
        //
        //   counter_freq_invariant #(
        //       .COUNTER_WIDTH(20)    // 1.05s max
        //   ) u_timer_adaptive (
        //       .clk         (clk),
        //       .rst_n       (rst_n),
        //       .sync_reset_n(1'b1),              // Always running
        //       .freq_sel    (current_freq_sel),  // Runtime selection
        //       .counter     (time_usec),
        //       .tick        (tick_1mhz)
        //   );
        //
        //   // Millisecond timeout detection
        //   logic [9:0] msec_count;  // 0-999
        //   always_ff @(posedge clk or negedge rst_n) begin
        //       if (!rst_n) msec_count <= 0;
        //       else if (tick_1mhz) begin
        //           if (msec_count == 999) msec_count <= 0;
        //           else                   msec_count <= msec_count + 1;
        //       end
        //   end
        //   assign timeout_1sec = (msec_count == 999) && tick_1mhz;
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **Accurate timing requires correct freq_sel** - Mismatch causes timing error
        //   - **Lookup table is prescriptive** - Only 68 frequencies supported
        //   - For arbitrary frequencies, calculate nearest freq_sel or modify table
        //   - Prescaler uses counter_load_clear for precise cycle counting
        //   - sync_reset_n=0 freezes both prescaler and counter (not just reset)
        //   - Frequency changes reset counter to 0 (not seamless transition)
        //   - **Counter rollover is silent** - No overflow flag, wraps at 2^WIDTH
        //   - For timeout detection, compare counter value externally
        //   - tick pulse is single-cycle - use edge detector if multi-cycle needed
        //   - **Critical path:** Division factor lookup → prescaler comparison
        //   - Synthesis: Lookup table → case → mux (typically 2-3 LUT levels)
        //   - PRESCALER_MAX must be power of 2 for efficient counter implementation
        //   - **Design trade-off:** Large lookup table vs. runtime division (chose table for speed)
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - counter_bin.sv - Basic binary counter (no time base)
        //   - counter_load_clear.sv - Programmable counter (used internally)
        //   - clock_divider.sv - Integer clock division (creates derived clock)
        //   - clock_pulse.sv - Configurable pulse generator
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_counter_freq_invariant.py
        //   Run: pytest val/common/test_counter_freq_invariant.py -v
        //   Coverage: 92%
        //   Key Test Scenarios:
        //     - Multiple frequency selections (100MHz, 500MHz, 1GHz)
        //     - Tick rate verification (measure tick period)
        //     - Counter increment validation
        //     - sync_reset_n functionality
        //     - Frequency change during operation
        //     - Rollover behavior
        //
        //==============================================================================
        
        `include "reset_defs.svh"
        module counter_freq_invariant
        #(
            parameter int COUNTER_WIDTH = 16,     // Width of the output counter (default 16-bit = ~65ms rollover)
            parameter int PRESCALER_MAX = 2048    // Maximum value of the pre-scaler (supports up to 2GHz)
        ) (
 006844     input  logic                        clk,         // Input clock (100MHz to 2GHz)
 000012     input  logic                        rst_n,       // Active low reset
 000012     input  logic                        sync_reset_n,// Synchronous reset (0=reset, 1=run)
%000000     input  logic [6:0]                  freq_sel,    // Frequency selection (7-bit for fine control)
 000024     output logic [COUNTER_WIDTH-1:0]    o_counter,   // Output counter (increments every microsecond)
 000048     output logic                        tick         // Pulse every microsecond
        );
        
            // Configuration registers (combinational)
%000000     logic [10:0] w_division_factor;     // Clock cycles per microsecond (up to 2000 for 2GHz)
        
            // Frequency selection change detection (flopped)
%000000     logic [6:0] r_prev_freq_sel;        // Previous frequency selection
 000024     logic       r_clear_pulse;          // Indicates frequency selection changed or sync reset
        
            // Internal counters (combinational)
 000072     logic w_prescaler_done;
        
            // Frequency lookup table - Maps freq_sel to division factors for 1MHz output
            // Each entry represents clock cycles needed for 1 microsecond
 000012     always_comb begin
 000012         case (freq_sel)
                    // 100-200 MHz range
%000000             7'd0:   w_division_factor = 11'd100;    // 100MHz   -> 100 cycles/μs
 000012             7'd1:   w_division_factor = 11'd105;    // 105MHz   -> 105 cycles/μs
%000000             7'd2:   w_division_factor = 11'd110;    // 110MHz   -> 110 cycles/μs
%000000             7'd3:   w_division_factor = 11'd115;    // 115MHz   -> 115 cycles/μs
%000000             7'd4:   w_division_factor = 11'd120;    // 120MHz   -> 120 cycles/μs
%000000             7'd5:   w_division_factor = 11'd125;    // 125MHz   -> 125 cycles/μs
%000000             7'd6:   w_division_factor = 11'd130;    // 130MHz   -> 130 cycles/μs
%000000             7'd7:   w_division_factor = 11'd135;    // 135MHz   -> 135 cycles/μs
%000000             7'd8:   w_division_factor = 11'd140;    // 140MHz   -> 140 cycles/μs
%000000             7'd9:   w_division_factor = 11'd145;    // 145MHz   -> 145 cycles/μs
%000000             7'd10:  w_division_factor = 11'd150;    // 150MHz   -> 150 cycles/μs
%000000             7'd11:  w_division_factor = 11'd160;    // 160MHz   -> 160 cycles/μs
%000000             7'd12:  w_division_factor = 11'd170;    // 170MHz   -> 170 cycles/μs
%000000             7'd13:  w_division_factor = 11'd180;    // 180MHz   -> 180 cycles/μs
%000000             7'd14:  w_division_factor = 11'd190;    // 190MHz   -> 190 cycles/μs
%000000             7'd15:  w_division_factor = 11'd200;    // 200MHz   -> 200 cycles/μs
        
                    // 200-500 MHz range
%000000             7'd16:  w_division_factor = 11'd220;    // 220MHz   -> 220 cycles/μs
%000000             7'd17:  w_division_factor = 11'd240;    // 240MHz   -> 240 cycles/μs
%000000             7'd18:  w_division_factor = 11'd250;    // 250MHz   -> 250 cycles/μs
%000000             7'd19:  w_division_factor = 11'd260;    // 260MHz   -> 260 cycles/μs
%000000             7'd20:  w_division_factor = 11'd280;    // 280MHz   -> 280 cycles/μs
%000000             7'd21:  w_division_factor = 11'd300;    // 300MHz   -> 300 cycles/μs
%000000             7'd22:  w_division_factor = 11'd320;    // 320MHz   -> 320 cycles/μs
%000000             7'd23:  w_division_factor = 11'd340;    // 340MHz   -> 340 cycles/μs
%000000             7'd24:  w_division_factor = 11'd360;    // 360MHz   -> 360 cycles/μs
%000000             7'd25:  w_division_factor = 11'd380;    // 380MHz   -> 380 cycles/μs
%000000             7'd26:  w_division_factor = 11'd400;    // 400MHz   -> 400 cycles/μs
%000000             7'd27:  w_division_factor = 11'd420;    // 420MHz   -> 420 cycles/μs
%000000             7'd28:  w_division_factor = 11'd440;    // 440MHz   -> 440 cycles/μs
%000000             7'd29:  w_division_factor = 11'd460;    // 460MHz   -> 460 cycles/μs
%000000             7'd30:  w_division_factor = 11'd480;    // 480MHz   -> 480 cycles/μs
%000000             7'd31:  w_division_factor = 11'd500;    // 500MHz   -> 500 cycles/μs
        
                    // 500MHz-1GHz range
%000000             7'd32:  w_division_factor = 11'd520;    // 520MHz   -> 520 cycles/μs
%000000             7'd33:  w_division_factor = 11'd540;    // 540MHz   -> 540 cycles/μs
%000000             7'd34:  w_division_factor = 11'd560;    // 560MHz   -> 560 cycles/μs
%000000             7'd35:  w_division_factor = 11'd580;    // 580MHz   -> 580 cycles/μs
%000000             7'd36:  w_division_factor = 11'd600;    // 600MHz   -> 600 cycles/μs
%000000             7'd37:  w_division_factor = 11'd620;    // 620MHz   -> 620 cycles/μs
%000000             7'd38:  w_division_factor = 11'd640;    // 640MHz   -> 640 cycles/μs
%000000             7'd39:  w_division_factor = 11'd660;    // 660MHz   -> 660 cycles/μs
%000000             7'd40:  w_division_factor = 11'd680;    // 680MHz   -> 680 cycles/μs
%000000             7'd41:  w_division_factor = 11'd700;    // 700MHz   -> 700 cycles/μs
%000000             7'd42:  w_division_factor = 11'd750;    // 750MHz   -> 750 cycles/μs
%000000             7'd43:  w_division_factor = 11'd800;    // 800MHz   -> 800 cycles/μs
%000000             7'd44:  w_division_factor = 11'd850;    // 850MHz   -> 850 cycles/μs
%000000             7'd45:  w_division_factor = 11'd900;    // 900MHz   -> 900 cycles/μs
%000000             7'd46:  w_division_factor = 11'd950;    // 950MHz   -> 950 cycles/μs
%000000             7'd47:  w_division_factor = 11'd1000;   // 1000MHz  -> 1000 cycles/μs
        
                    // 1GHz-1.5GHz range
%000000             7'd48:  w_division_factor = 11'd1050;   // 1050MHz  -> 1050 cycles/μs
%000000             7'd49:  w_division_factor = 11'd1100;   // 1100MHz  -> 1100 cycles/μs
%000000             7'd50:  w_division_factor = 11'd1150;   // 1150MHz  -> 1150 cycles/μs
%000000             7'd51:  w_division_factor = 11'd1200;   // 1200MHz  -> 1200 cycles/μs
%000000             7'd52:  w_division_factor = 11'd1250;   // 1250MHz  -> 1250 cycles/μs
%000000             7'd53:  w_division_factor = 11'd1300;   // 1300MHz  -> 1300 cycles/μs
%000000             7'd54:  w_division_factor = 11'd1350;   // 1350MHz  -> 1350 cycles/μs
%000000             7'd55:  w_division_factor = 11'd1400;   // 1400MHz  -> 1400 cycles/μs
%000000             7'd56:  w_division_factor = 11'd1450;   // 1450MHz  -> 1450 cycles/μs
%000000             7'd57:  w_division_factor = 11'd1500;   // 1500MHz  -> 1500 cycles/μs
        
                    // 1.5GHz-2GHz range
%000000             7'd58:  w_division_factor = 11'd1550;   // 1550MHz  -> 1550 cycles/μs
%000000             7'd59:  w_division_factor = 11'd1600;   // 1600MHz  -> 1600 cycles/μs
%000000             7'd60:  w_division_factor = 11'd1650;   // 1650MHz  -> 1650 cycles/μs
%000000             7'd61:  w_division_factor = 11'd1700;   // 1700MHz  -> 1700 cycles/μs
%000000             7'd62:  w_division_factor = 11'd1750;   // 1750MHz  -> 1750 cycles/μs
%000000             7'd63:  w_division_factor = 11'd1800;   // 1800MHz  -> 1800 cycles/μs
%000000             7'd64:  w_division_factor = 11'd1850;   // 1850MHz  -> 1850 cycles/μs
%000000             7'd65:  w_division_factor = 11'd1900;   // 1900MHz  -> 1900 cycles/μs
%000000             7'd66:  w_division_factor = 11'd1950;   // 1950MHz  -> 1950 cycles/μs
%000000             7'd67:  w_division_factor = 11'd2000;   // 2000MHz  -> 2000 cycles/μs
        
                    // Reserved for future expansion
%000000             default: w_division_factor = 11'd1000;  // Default to 1GHz
                endcase
            end
        
            // Detect frequency selection changes and sync reset
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_prev_freq_sel <= 7'b0;
                    r_clear_pulse <= 1'b1;  // Start in reset state
                end
                else begin
                    r_prev_freq_sel <= freq_sel;
        
                    // Generate clear pulse when:
                    // 1. Frequency selection changes
                    // 2. sync_reset_n is deasserted (synchronous reset active)
                    r_clear_pulse <= (freq_sel != r_prev_freq_sel) || !sync_reset_n;
                end
 000192     )
        
        
            // Prescaler counter using the provided counter_load_clear
            // This generates a done pulse every microsecond
            counter_load_clear #(
                .MAX            (PRESCALER_MAX)
            ) prescaler_counter(
                .clk            (clk),
                .rst_n          (rst_n),
                .clear          (r_clear_pulse),         // Clear when frequency changes or sync reset
                .increment      (1'b1),                  // Always increment
                .load           (1'b1),                  // Always load the division factor
                .loadval        (w_division_factor[$clog2(PRESCALER_MAX)-1:0] - 1'b1), // Load cycles-1 for proper timing
                .done           (w_prescaler_done),
                /* verilator lint_off PINCONNECTEMPTY */
                .count          ()                       // Internal count not needed
                /* verilator lint_on PINCONNECTEMPTY */
            );
        
            // Generate microsecond tick signal and maintain output counter
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    o_counter <= 'b0;
                    tick <= 1'b0;
                end
                else begin
                    // Clear has highest priority - reset counter when in sync reset or frequency changes
                    if (r_clear_pulse) begin
                        o_counter <= 'b0;
                        tick <= 1'b0;
                    end
                    else begin
                        // Generate tick pulse every microsecond (only when not in sync reset)
                        if (w_prescaler_done && sync_reset_n) begin
                            tick <= 1'b1;
                            o_counter <= o_counter + 1'b1;  // Increment counter every microsecond
                        end
                        else begin
                            tick <= 1'b0;
                            // Keep counter value unchanged
                        end
                    end
                end
 000024     )
        
        
        endmodule : counter_freq_invariant
        
