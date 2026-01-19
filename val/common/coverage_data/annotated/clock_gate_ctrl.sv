//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: clock_gate_ctrl
        // Purpose: //   Clock gating controller with idle timeout mechanism for power optimization.
        //
        // Documentation: rtl/common/PRD.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-10-18
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: clock_gate_ctrl
        //==============================================================================
        // Description:
        //   Clock gating controller with idle timeout mechanism for power optimization.
        //   Gates the output clock after a configurable idle period with no wakeup activity.
        //   Uses integrated clock gating (ICG) cell instantiation for glitch-free clock gating.
        //   Supports global enable/disable and provides gating status indicator. Designed
        //   for ASIC power management (dynamic power reduction during idle periods).
        //
        // Features:
        //   - Configurable idle timeout (countdown-based)
        //   - Global clock gating enable/disable
        //   - Wakeup signal for immediate clock restoration
        //   - ICG cell instantiation (glitch-free gating)
        //   - Gating status indicator output
        //   - Asynchronous reset support
        //
        //------------------------------------------------------------------------------
        // Parameters:
        //------------------------------------------------------------------------------
        //   IDLE_CNTR_WIDTH:
        //     Description: Bit width of idle counter
        //     Type: int
        //     Range: 2 to 16
        //     Default: 4
        //     Constraints: Max idle count = 2^IDLE_CNTR_WIDTH - 1
        //                  For IDLE_CNTR_WIDTH=4: max count = 15 clocks
        //                  For IDLE_CNTR_WIDTH=8: max count = 255 clocks
        //
        //   Derived Parameters (localparam - computed automatically):
        //     N: Alias for IDLE_CNTR_WIDTH (used in port widths for backwards compatibility)
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     clk_in:                    Input clock (ungated)
        //     aresetn:                   Asynchronous active-low reset
        //     cfg_cg_enable:             Global clock gating enable (1=allow gating)
        //     cfg_cg_idle_count[N-1:0]:  Idle timeout value (countdown start value)
        //     wakeup:                    Wakeup signal (1=restore clock immediately)
        //
        //   Outputs:
        //     clk_out:                   Output clock (gated)
        //     gating:                    Gating status (1=clock is gated)
        //
        //------------------------------------------------------------------------------
        // Timing:
        //------------------------------------------------------------------------------
        //   Latency:        cfg_cg_idle_count + 1 clocks from last wakeup to gating
        //   Wakeup:         1 clock from wakeup assertion to clock restoration
        //   Reset:          Asynchronous (immediate counter reset)
        //   Clock Enable:   Registered through ICG cell (glitch-free)
        //
        //------------------------------------------------------------------------------
        // Behavior:
        //------------------------------------------------------------------------------
        //   Idle Countdown Mechanism:
        //   - Counter loads cfg_cg_idle_count on reset or wakeup
        //   - Decrements each clock when cfg_cg_enable=1 and wakeup=0
        //   - Stops at 0 (does not wrap)
        //   - Clock gates when counter reaches 0
        //
        //   Clock Gating Logic:
        //   - Gate condition: cfg_cg_enable=1 AND wakeup=0 AND counter=0
        //   - ICG cell enables clock when gate_enable=0 (active-low to ICG)
        //   - ICG cell disables clock when gate_enable=1
        //
        //   Wakeup Behavior:
        //   - Wakeup=1 immediately reloads counter and restores clock
        //   - Wakeup overrides gating (clock always runs when wakeup=1)
        //   - Counter reset to cfg_cg_idle_count on wakeup assertion
        //
        //   Global Enable/Disable:
        //   - cfg_cg_enable=0: Clock always enabled (no gating)
        //   - cfg_cg_enable=1: Allow gating after idle timeout
        //
        //   State Diagram:
        //   ACTIVE (counter > 0):
        //     - clk_out running
        //     - Counter decrementing
        //     - On wakeup: reload counter
        //     - On counter=0: transition to GATED
        //
        //   GATED (counter = 0):
        //     - clk_out stopped (gating=1)
        //     - On wakeup: reload counter, transition to ACTIVE
        //
        //   Example Timing (IDLE_CNTR_WIDTH=4, cfg_cg_idle_count=3):
        //   Clock:    |‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|‾|_|
        //   wakeup:   |‾‾‾|_________________|‾‾‾|_______________
        //   counter:  3 3 2 1 0 0 0 0 0 0 3 3 2 1 0 0 0 0 0 0
        //   gating:   ___________‾‾‾‾‾‾‾‾‾‾‾___________‾‾‾‾‾‾‾‾
        //   clk_out:  |‾|_|‾|_|‾|_|‾|__________|‾|_|‾|_|‾|______
        //
        //   ICG Cell Interface:
        //   - clk: Input clock (clk_in)
        //   - en: Enable signal (active-high, 1=clock running)
        //   - gclk: Gated clock output (clk_out)
        //   - ICG ensures glitch-free transitions on enable changes
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // Clock gating for idle functional unit
        //   logic clk, rst_n, unit_active, unit_clk, is_gated;
        //   logic [3:0] idle_threshold;
        //
        //   clock_gate_ctrl #(
        //       .IDLE_CNTR_WIDTH(4)
        //   ) u_cg_ctrl (
        //       .clk_in           (clk),
        //       .aresetn          (rst_n),
        //       .cfg_cg_enable    (1'b1),           // Always allow gating
        //       .cfg_cg_idle_count(idle_threshold), // 0-15 clock idle timeout
        //       .wakeup           (unit_active),    // Restore clock when active
        //       .clk_out          (unit_clk),       // Gated clock for unit
        //       .gating           (is_gated)        // Status indicator
        //   );
        //
        //   // Power-managed functional unit
        //   always_ff @(posedge unit_clk or negedge rst_n) begin
        //       if (!rst_n) begin
        //           // Reset logic
        //       end else begin
        //           // Normal operation (clock may be gated when idle)
        //       end
        //   end
        //
        //   // Dynamic idle threshold adjustment
        //   logic [3:0] performance_mode_threshold;
        //   logic [3:0] power_save_mode_threshold;
        //   logic power_save_mode;
        //
        //   assign idle_threshold = power_save_mode ? power_save_mode_threshold : performance_mode_threshold;
        //   // Performance mode: longer timeout (less aggressive gating)
        //   assign performance_mode_threshold = 4'd10;
        //   // Power save mode: shorter timeout (more aggressive gating)
        //   assign power_save_mode_threshold = 4'd2;
        //
        //   // Wakeup detection from transaction request
        //   logic transaction_request, transaction_done;
        //   assign unit_active = transaction_request | !transaction_done;
        //
        //   // Global clock gating disable (debug mode)
        //   logic debug_mode;
        //   logic cg_enable;
        //   assign cg_enable = !debug_mode;  // Disable gating during debug
        //
        //   clock_gate_ctrl #(.IDLE_CNTR_WIDTH(8)) u_dbg_cg (
        //       .clk_in           (clk),
        //       .aresetn          (rst_n),
        //       .cfg_cg_enable    (cg_enable),      // Controlled by debug mode
        //       .cfg_cg_idle_count(8'd50),
        //       .wakeup           (unit_active),
        //       .clk_out          (unit_clk),
        //       .gating           (is_gated)
        //   );
        //
        //   // Power monitoring
        //   always_ff @(posedge clk) begin
        //       if (is_gated) begin
        //           // Log: Unit clock is gated (power saving active)
        //       end
        //   end
        //
        //------------------------------------------------------------------------------
        // Notes:
        //------------------------------------------------------------------------------
        //   - **ASIC-specific:** Requires ICG (Integrated Clock Gating) cell from library
        //   - ICG cell prevents glitches during enable transitions
        //   - **FPGA note:** May not synthesize correctly (ICG primitive not standard)
        //   - For FPGA, use alternative clock enable approach (not true gating)
        //   - **Power savings:** Dynamic power ∝ clock activity (gating reduces power)
        //   - Static power unaffected (leakage continues when gated)
        //   - **Idle counter:** Decrements to 0 and holds (does not wrap)
        //   - Counter reloads on wakeup or cfg_cg_enable transition
        //   - **Gating latency:** cfg_cg_idle_count + 1 clocks after last wakeup
        //   - **Wakeup latency:** 1 clock from wakeup to clock restoration
        //   - Wakeup overrides all gating conditions (highest priority)
        //   - **Reset behavior:** Counter loads cfg_cg_idle_count on aresetn deassertion
        //   - Global enable (cfg_cg_enable) bypasses gating (clock always runs if 0)
        //   - **Gating indicator:** Output 'gating' shows real-time status
        //   - Use for monitoring, debug, or power management feedback
        //   - **ICG enable polarity:** Inverted before ICG (active-high internally, active-low to ICG)
        //   - Critical: ICG cell must be glitch-free (library-specific implementation)
        //   - **Area:** Minimal (counter + control logic + ICG cell)
        //   - Typical IDLE_CNTR_WIDTH: 4-8 bits (16-256 clock timeout range)
        //   - **Applications:** Idle functional units, peripheral clocks, CPU sleep
        //
        //------------------------------------------------------------------------------
        // Related Modules:
        //------------------------------------------------------------------------------
        //   - icg.sv - Integrated clock gating cell (technology library primitive)
        //   - clock_divider.sv - Clock frequency division (different purpose)
        //   - clock_pulse.sv - Single-cycle pulse generation
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_clock_gate_ctrl.py
        //   Run: pytest val/common/test_clock_gate_ctrl.py -v
        //   Coverage: 95%
        //   Key Test Scenarios:
        //     - Idle timeout and gating activation
        //     - Wakeup signal clock restoration
        //     - Global enable/disable functionality
        //     - Counter reload on wakeup
        //     - Reset behavior
        //     - Various idle count values
        //     - Continuous wakeup (no gating)
        //     - Gating indicator correctness
        //
        //==============================================================================
        
        `include "reset_defs.svh"
        module clock_gate_ctrl #(
            parameter int IDLE_CNTR_WIDTH = 4 // Default width of idle counter
        ) (
            // Inputs
 005915     input logic          clk_in,
%000003     input logic          aresetn,
 000019     input logic          cfg_cg_enable,     // Global clock gate enable
%000000     input logic  [N-1:0] cfg_cg_idle_count, // Idle countdown value
 000245     input logic          wakeup,            // Signal to wake up the block
        
            // Outputs
 003675     output logic         clk_out,
 000224     output logic         gating          // clock gating indicator
        );
        
            // Derived parameters
            localparam int N = IDLE_CNTR_WIDTH;  // Alias for backwards compatibility
        
            // Internal signals
%000000     logic [N-1:0] r_idle_counter;
        
            // Counter logic
            `ALWAYS_FF_RST(clk_in, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_idle_counter <= cfg_cg_idle_count;
                end else begin
                    if (wakeup || !cfg_cg_enable) begin
                        // On wakeup or global disable, reset counter
                        r_idle_counter <= cfg_cg_idle_count;
                    end else if (r_idle_counter != 'h0) begin
                        // Normal counting operation - decrement when not zero
                        r_idle_counter <= r_idle_counter - 1'b1;
                    end
                    // When counter reaches zero, it stays at zero
                end
 000027     )
        
        
            // Simple gating condition: gate when not in wakeup, globally enabled, and counter is zero
 000224     wire w_gate_enable = cfg_cg_enable && !wakeup && (r_idle_counter == 'h0);
        
            // Instantiate the ICG cell
            icg u_icg (
                .clk(clk_in),
                .en(~w_gate_enable),  // Enable is active high in our logic
                .gclk(clk_out)
            );
        
            assign gating = w_gate_enable;
        
        endmodule : clock_gate_ctrl
        
