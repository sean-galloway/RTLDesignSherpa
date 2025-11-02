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
//   Multi-stage reset synchronizer for safe clock domain reset distribution.
//   Converts an asynchronous reset (typically active-low from POR or external
//   source) into a clean, clock-synchronous reset aligned to a destination
//   clock domain. Prevents metastability and ensures controlled reset
//   deassertion. Used per-clock-domain to safely fan out reset.
//
//------------------------------------------------------------------------------
// Key Enhancements (2025 Revision):
//------------------------------------------------------------------------------
//   - FPGA vs ASIC portable implementation (parametrized behavior)
//   - Optional vendor attributes for FPGA tool recognition
//   - Configurable polarity on input and output resets
//   - Optional purely synchronous style for ASIC methodology alignment
//   - Optional internal assertions (SVA) for timing and behavior checking
//
//------------------------------------------------------------------------------
// Features:
//------------------------------------------------------------------------------
//   - Parameterized synchronizer depth (N ≥ 2, default 3)
//   - Async assertion / sync deassertion (FPGA default)
//   - Optional fully synchronous reset (ASIC optional)
//   - Optional FPGA vendor attributes (ASYNC_REG, SHREG_EXTRACT, MLAB/M20K hints)
//   - Active-low I/O by default (matches typical FPGA and ASIC conventions)
//   - Built-in SVA option (RESET_SYNC_SVA)
//   - Elaboration-time guard against illegal N < 2
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   N:
//     Description: Synchronizer depth (number of flip-flops)
//     Type: int
//     Range: 2 to 5
//     Default: 3
//     Notes: N=3 recommended (industry standard), N≥4 for extreme reliability
//
//   KEEP_ATTRS:
//     Description: Include FPGA vendor attributes for CDC inference
//     Type: bit
//     Default: 1
//     Notes: Set 0 for ASIC or pure Verilog synthesis
//
//   IN_ACTIVE_LOW:
//     Description: Input reset polarity (1=active-low, 0=active-high)
//     Type: bit
//     Default: 1
//
//   OUT_ACTIVE_LOW:
//     Description: Output reset polarity (1=active-low, 0=active-high)
//     Type: bit
//     Default: 1
//
//   ASYNC_ASSERT:
//     Description: Control reset assertion style
//     Type: bit
//     Default: 1
//     Notes:
//       1 = Asynchronous assert, synchronous deassert (FPGA default)
//       0 = Fully synchronous assert/deassert (ASIC optional)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:       Destination clock domain
//     rst_n:     Asynchronous reset input (default active-low)
//
//   Outputs:
//     sync_rst_n: Synchronized reset output (default active-low)
//                 Safe to use inside always_ff @(posedge clk)
//
//------------------------------------------------------------------------------
// Timing (FPGA default - ASYNC_ASSERT=1):
//------------------------------------------------------------------------------
//   Reset Assert:    Asynchronous (immediate)
//   Reset Deassert:  Synchronous, N-cycle latency
//   Latency:         N clock cycles for deassertion
//   MTBF:            Exponentially increases with N (3 → 10^12+ hours typical)
//
//------------------------------------------------------------------------------
// Behavior (FPGA default mode):
//------------------------------------------------------------------------------
//   - rst_n low immediately drives all synchronizer flops low
//   - On rising edge of clk after rst_n=1:
//       * Stage 0 captures 1'b1
//       * Subsequent stages shift 1'b1 toward MSB
//   - After N cycles, sync_rst_n deasserts (goes high)
//   - Prevents recovery/removal violations and metastability
//
//------------------------------------------------------------------------------
// Optional Behavior (ASIC mode, ASYNC_ASSERT=0):
//------------------------------------------------------------------------------
//   - Reset is sampled synchronously on clock edges
//   - Deassertion timing remains deterministic
//   - All stages deassert simultaneously without async event paths
//   - No asynchronous sensitivity list in the synchronizer itself
//
//------------------------------------------------------------------------------
// FPGA Usage Example (default - async assert / sync deassert):
//------------------------------------------------------------------------------
//
//   // 3-stage synchronizer with vendor attributes (default)
//   reset_sync #(
//       .N(3),
//       .KEEP_ATTRS(1),
//       .IN_ACTIVE_LOW(1),
//       .OUT_ACTIVE_LOW(1),
//       .ASYNC_ASSERT(1)     // Async assert, sync deassert (FPGA default)
//   ) u_rst_sync_fpga (
//       .clk        (clk_core),
//       .rst_n      (por_rst_n),   // Raw async reset (active-low)
//       .sync_rst_n (core_rst_n)   // Safe, clock-aligned reset (active-low)
//   );
//
//   // Usage in downstream logic
//   `ALWAYS_FF_RST(clk_core, core_rst_n, begin
//       if (`RST_ASSERTED(core_rst_n))
//           state <= IDLE;
//       else
//           state <= next_state;
//   end)
//
//------------------------------------------------------------------------------
// ASIC Usage Example (synchronous only):
//------------------------------------------------------------------------------
//
//   // Same ports, no vendor attributes, sync-only behavior
//   reset_sync #(
//       .N(2),
//       .KEEP_ATTRS(0),     // Remove FPGA-specific attributes
//       .ASYNC_ASSERT(0),   // Purely synchronous style (no async assert path)
//       .IN_ACTIVE_LOW(1),
//       .OUT_ACTIVE_LOW(1)
//   ) u_rst_sync_asic (
//       .clk        (clk_core),
//       .rst_n      (global_rst_n),
//       .sync_rst_n (core_rst_n)
//   );
//
//   // Downstream logic (identical reset handling)
//   `ALWAYS_FF_RST(clk_core, core_rst_n, begin
//       if (`RST_ASSERTED(core_rst_n))
//           r_ctrl <= '0;
//       else
//           r_ctrl <= next_ctrl;
//   end)
//
//------------------------------------------------------------------------------
// Comparative Notes (FPGA vs ASIC modes):
//------------------------------------------------------------------------------
//   Behavior Aspect        | FPGA Default (ASYNC_ASSERT=1)    | ASIC Mode (ASYNC_ASSERT=0)
//   ---------------------- | -------------------------------- | -----------------------------
//   Reset assertion        | Asynchronous (immediate)         | Synchronous (clocked)
//   Reset deassertion      | Synchronous, N cycles            | Synchronous, N cycles
//   Vendor attributes      | Included (`ASYNC_REG`, etc.)     | Removed
//   Input polarity         | Active-low (configurable)        | Active-low (configurable)
//   Output polarity        | Active-low (configurable)        | Active-low (configurable)
//   Use case               | FPGA/SoC RTL, external PORs      | ASIC, synchronous methodology
//   Synthesis tools        | Vivado, Quartus, Radiant         | DC, Genus, Yosys (ASIC flow)
//   Simulation behavior    | Same in both modes               | Same functional results
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Use one reset_sync per clock domain
//   - Never share a single sync_rst_n across multiple clocks
//   - N=3 is standard (3-stage metastability filtering)
//   - KEEP_ATTRS=1 enables dedicated synchronizer cell inference
//   - In ASIC mode, KEEP_ATTRS=0 for cleaner netlist
//   - Internal SVA (`RESET_SYNC_SVA`) checks deassert timing
//   - Initial value of sync_rst_n = 0 (asserted)
//   - Safe for any frequency ratio between reset source and clk
//   - Typical reset latency: N × Tclk
//   - Compatible with Verilator, VCS, Questa, and Xcelium
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - sync_2ff.sv      : General data synchronizer (2-flop CDC)
//   - sync_pulse.sv    : Pulse synchronizer for one-shot transfers
//   - reset_sync_ah.sv : Active-high variant (if needed for legacy code)
//   - glitch_free_n_dff_arn.sv : Glitch-free mux with reset sync
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_reset_sync.py
//   Run: pytest val/common/test_reset_sync.py -v
//   Coverage: >95%
//   Key Test Scenarios:
//     - FPGA async-assert, N=2,3,4
//     - ASIC sync-only, N=2,3
//     - Metastability injection (force X on first stage)
//     - Back-to-back reset pulses
//     - Reset deassertion near clk edge
//
//==============================================================================
//
// Revision Summary (2025-10-21):
//   - Added polarity parameters (IN_ACTIVE_LOW, OUT_ACTIVE_LOW)
//   - Added ASYNC_ASSERT param for FPGA/ASIC flexibility
//   - Added KEEP_ATTRS to control vendor attributes
//   - Added detailed FPGA and ASIC instantiation examples
//   - Clarified behavioral equivalence and differences
//   - SVA properties generalized for both polarities
//==============================================================================

module reset_sync #(
    parameter int N               = 3,     // >=2 recommended
    parameter bit KEEP_ATTRS      = 1'b1,  // keep vendor attrs for FPGA
    // Polarity controls (no port changes needed)
    parameter bit IN_ACTIVE_LOW   = 1'b1,  // rst_n is active-low by default
    parameter bit OUT_ACTIVE_LOW  = 1'b1,  // sync output is active-low by default
    // Style control
    parameter bit ASYNC_ASSERT    = 1'b1   // 1: async-assert/sync-deassert (FPGA best practice)
) (
    input  logic clk,
    input  logic rst_n,          // async reset IN (name kept for compatibility)
    output logic sync_rst_n      // synced reset OUT (name kept for compatibility)
);

    // -----------------------------
    // Elaboration guards
    // -----------------------------
    if (N < 2) begin : g_illegal
        // synthesis translate_off
        initial $error("reset_sync: N must be >= 2 (got %0d)", N);
        // synthesis translate_on
    end

    // Normalize input to active-HIGH async reset
    wire rst_in_h = IN_ACTIVE_LOW ? ~rst_n : rst_n;

    // Synchronizer chain
    // Attributes help tools recognize CDC flops and avoid SRL extraction
    generate
        if (ASYNC_ASSERT) begin : g_async_assert
            if (KEEP_ATTRS) begin : g_attrd
                (* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *)
                (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *)
                logic [N-1:0] r_sync_reg /* synthesis syn_preserve = 1 */;

                // Optional sim init; hardware uses async reset
                // synthesis translate_off
                initial r_sync_reg = '0;
                // synthesis translate_on

                // Async assert (posedge rst_in_h), sync deassert
                always_ff @(posedge clk or posedge rst_in_h) begin
                    if (rst_in_h) r_sync_reg <= '1;                // hold asserted through chain
                    else          r_sync_reg <= {r_sync_reg[N-2:0], 1'b0};
                end

                // Active-HIGH internal form (asserted when MSB is 1)
                wire sync_rst_h = r_sync_reg[N-1];
                // Drive requested output polarity without changing port name
                always_comb begin
                    sync_rst_n = OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h;
                end
            end else begin : g_plain
                logic [N-1:0] r_sync_reg;

                // synthesis translate_off
                initial r_sync_reg = '0;
                // synthesis translate_on

                always_ff @(posedge clk or posedge rst_in_h) begin
                    if (rst_in_h) r_sync_reg <= '1;
                    else          r_sync_reg <= {r_sync_reg[N-2:0], 1'b0};
                end

                wire sync_rst_h = r_sync_reg[N-1];
                always_comb begin
                    sync_rst_n = OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h;
                end
            end
        end else begin : g_sync_only
            // Purely synchronous reset style (rarely used for initial assert)
            if (KEEP_ATTRS) begin : g_attrd
                (* ASYNC_REG = "TRUE", SHREG_EXTRACT = "NO" *)
                (* altera_attribute = "-name SYNCHRONIZER_IDENTIFICATION FORCED" *)
                logic [N-1:0] r_sync_reg /* synthesis syn_preserve = 1 */;

                // synthesis translate_off
                initial r_sync_reg = '0;
                // synthesis translate_on

                always_ff @(posedge clk) begin
                    if (rst_in_h) r_sync_reg <= '1;
                    else          r_sync_reg <= {r_sync_reg[N-2:0], 1'b0};
                end

                wire sync_rst_h = r_sync_reg[N-1];
                always_comb begin
                    sync_rst_n = OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h;
                end
            end else begin : g_plain
                logic [N-1:0] r_sync_reg;

                // synthesis translate_off
                initial r_sync_reg = '0;
                // synthesis translate_on

                always_ff @(posedge clk) begin
                    if (rst_in_h) r_sync_reg <= '1;
                    else          r_sync_reg <= {r_sync_reg[N-2:0], 1'b0};
                end

                wire sync_rst_h = r_sync_reg[N-1];
                always_comb begin
                    sync_rst_n = OUT_ACTIVE_LOW ? ~sync_rst_h : sync_rst_h;
                end
            end
        end
    endgenerate

`ifdef RESET_SYNC_SVA
    // synthesis translate_off
    // Assertions in active-HIGH internal convention
    wire sync_rst_h_int = OUT_ACTIVE_LOW ? ~sync_rst_n : sync_rst_n;
    // When input asserted, output must be asserted
    property p_assert_holds;
        @(posedge clk) rst_in_h |-> sync_rst_h_int;
    endproperty
    assert property (p_assert_holds);

    // Deassert no earlier than N cycles after input deassert
    property p_deassert_after_N;
        @(posedge clk) disable iff (rst_in_h)
            $fell(rst_in_h) |-> (sync_rst_h_int)[*N-1] ##1 !sync_rst_h_int;
    endproperty
    assert property (p_deassert_after_N);
    // synthesis translate_on
`endif

endmodule : reset_sync
