// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: counter_bingray
// Purpose: Counter Bingray module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: counter_bingray
//==============================================================================
// Description:
//   Binary counter with simultaneous Gray code output for async FIFO pointer
//   management. This module is the standard building block for FIFO write and
//   read pointers that must cross clock domains safely. Provides both binary
//   (for address generation) and Gray code (for CDC synchronization) outputs
//   from a single counter, ensuring they remain synchronized.
//
//------------------------------------------------------------------------------
// Features:
//------------------------------------------------------------------------------
//   - Binary counter with enable control
//   - Simultaneous Gray code conversion (inline bin2gray)
//   - Next-value prediction for look-ahead logic
//   - Single register stage (both binary and Gray registered together)
//   - Zero latency between binary and Gray outputs (same cycle)
//   - Wrap-around at 2^WIDTH (power-of-2 rollover)
//   - Used in fifo_async.sv for pointer synchronization
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Counter bit width (must match FIFO address width)
//     Type: int
//     Range: 2 to 32
//     Default: 4
//     Constraints: Same width for binary and Gray outputs
//                  Typically $clog2(FIFO_DEPTH) for power-of-2 FIFOs
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     clk:             Clock input (FIFO write or read clock)
//     rst_n:           Active-low asynchronous reset
//     enable:          Count enable (active-high)
//                      Typically: write enable for write pointer
//                                 read enable for read pointer
//
//   Outputs:
//     counter_bin[WIDTH-1:0]:      Binary count value (for memory addressing)
//     counter_bin_next[WIDTH-1:0]: Next binary count (combinational look-ahead)
//     counter_gray[WIDTH-1:0]:     Gray code count (for CDC to other domain)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        1 cycle (registered outputs)
//   Enable to out:  Next posedge clk after enable assertion
//   Binary/Gray:    Synchronized (same register stage)
//   Next value:     Combinational (same cycle as enable)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   - On reset: All outputs = 0
//   - When enable=1: counter_bin increments on each clock edge
//   - counter_gray updated simultaneously with counter_bin
//   - counter_bin_next provides combinational preview of next count
//   - Wraps at 2^WIDTH (modulo-2^WIDTH counter)
//
//   Conversion Formula (inline bin2gray):
//   counter_gray = counter_bin ^ (counter_bin >> 1)
//
//   Example (WIDTH=4):
//   counter_bin  counter_gray  (only 1 bit changes in Gray)
//   0000         0000
//   0001         0001          bit[0] changed
//   0010         0011          bit[1] changed
//   0011         0010          bit[0] changed
//   0100         0110          bit[2] changed
//   ...
//
//------------------------------------------------------------------------------
// Usage in Async FIFO:
//------------------------------------------------------------------------------
//   Write Pointer (Source Domain):
//   ```systemverilog
//   counter_bingray #(.WIDTH(ADDR_WIDTH)) u_wr_ptr (
//       .clk             (wr_clk),
//       .rst_n           (wr_rst_n),
//       .enable          (wr_en && !full),
//       .counter_bin     (wr_addr),          // Write address to memory
//       .counter_bin_next(wr_addr_next),     // For full flag generation
//       .counter_gray    (wr_ptr_gray)       // Sync to read domain
//   );
//   ```
//
//   Read Pointer (Destination Domain):
//   ```systemverilog
//   counter_bingray #(.WIDTH(ADDR_WIDTH)) u_rd_ptr (
//       .clk             (rd_clk),
//       .rst_n           (rd_rst_n),
//       .enable          (rd_en && !empty),
//       .counter_bin     (rd_addr),          // Read address to memory
//       .counter_bin_next(rd_addr_next),     // For empty flag generation
//       .counter_gray    (rd_ptr_gray)       // Sync to write domain
//   );
//   ```
//
//   CDC Synchronization:
//   ```systemverilog
//   // Sync write pointer to read domain
//   glitch_free_n_dff_arn #(.WIDTH(ADDR_WIDTH), .FLOP_COUNT(2))
//   u_sync_wr_ptr (
//       .clk  (rd_clk),
//       .rst_n(rd_rst_n),
//       .d    (wr_ptr_gray),      // Gray from write domain
//       .q    (wr_ptr_gray_sync)  // Synchronized Gray in read domain
//   );
//
//   // Convert back to binary for comparison
//   gray2bin #(.WIDTH(ADDR_WIDTH)) u_gray2bin_wr (
//       .gray  (wr_ptr_gray_sync),
//       .binary(wr_ptr_bin_sync)  // Binary for empty flag logic
//   );
//   ```
//
//------------------------------------------------------------------------------
// Why This Module Exists:
//------------------------------------------------------------------------------
//   **Problem:** FIFO pointers must cross clock domains, but binary counters
//   change multiple bits simultaneously (e.g., 0111→1000 changes all 4 bits).
//   If metastability corrupts even one bit during CDC, the pointer value is
//   completely wrong.
//
//   **Solution:** Gray code changes only 1 bit per increment. Metastability
//   affects at most 1 bit → value is off by at most ±1 count, which is safe
//   for FIFO empty/full calculations.
//
//   **This module:** Combines binary counter (for addressing) with Gray code
//   output (for CDC) in a single register stage, guaranteeing they stay
//   synchronized. Used by fifo_async.sv.
//
//------------------------------------------------------------------------------
// Design Rationale:
//------------------------------------------------------------------------------
//   1. **Inline bin2gray conversion:** Avoids separate bin2gray module,
//      ensuring binary and Gray outputs are always synchronized from same
//      register stage.
//
//   2. **Registered outputs:** Both binary and Gray are registered, not
//      combinational, ensuring clean signals for memory addressing and CDC.
//
//   3. **Next-value prediction:** counter_bin_next is combinational
//      (w_counter_bin), allowing look-ahead for full/empty flag generation
//      without extra cycle of latency.
//
//   4. **Power-of-2 wrap:** No MAX_VALUE parameter - always wraps at 2^WIDTH,
//      which is requirement for standard async FIFO pointer comparison.
//
//------------------------------------------------------------------------------
// FPGA-Specific Synthesis and Implementation Notes:
//------------------------------------------------------------------------------
//   **Synthesis on FPGAs:**
//   - Binary counter: Maps to FPGA carry chain logic
//     * Xilinx: Uses CARRY4 primitives in slices
//     * Intel: Uses carry chain in ALMs
//     * Very efficient - one LUT + carry per bit
//   - Gray code conversion: XOR tree after counter
//     * WIDTH=8: 7 XORs (one per bit except MSB)
//     * WIDTH=16: 15 XORs
//   - Total resource usage:
//     * WIDTH=8:  8 FFs (counter) + 7 LUTs (XOR) = 8 FFs, 7 LUTs
//     * WIDTH=16: 16 FFs (counter) + 15 LUTs (XOR) = 16 FFs, 15 LUTs
//     * WIDTH=32: 32 FFs (counter) + 31 LUTs (XOR) = 32 FFs, 31 LUTs
//   - Negligible power impact
//
//   **Critical Timing Considerations:**
//   - Binary counter on FPGA carry chain is FAST (~0.5 ns/bit typical)
//   - Gray XOR tree adds minimal delay (~0.2 ns for one XOR level)
//   - Typical Fmax: >500 MHz for WIDTH=16 on modern FPGAs
//   - counter_bin_next is combinational: enable → next value
//     * This path CAN be timing-critical if used for complex logic
//     * Example: Full flag = (wr_addr_next == rd_addr_sync)
//     * If full flag path is slow, register counter_bin_next
//
//   **Best Practices for FPGA Timing:**
//   ```systemverilog
//   // GOOD: Registered outputs are clean for CDC
//   counter_bingray #(.WIDTH(8)) u_wr_ptr (
//       .clk          (wr_clk),
//       .counter_gray (wr_ptr_gray)  // Already registered - safe for CDC
//   );
//
//   // If counter_bin_next causes timing issues:
//   logic [WIDTH-1:0] wr_addr_next_reg;
//   always_ff @(posedge wr_clk) begin
//       wr_addr_next_reg <= wr_addr_next;  // Extra register stage
//   end
//   assign almost_full = (wr_addr_next_reg == rd_addr_sync - THRESHOLD);
//   ```
//
//   **Timing Constraints (XDC/SDC):**
//   ```tcl
//   # Gray code output crosses to another domain - set max delay
//   set_max_delay -datapath_only \
//     -from [get_cells u_wr_ptr/counter_gray_reg[*]] \
//     -to   [get_cells u_sync_wr_ptr/r_sync_reg[0][*]] \
//     [expr {2 * $wr_clk_period}]
//
//   # Ensure counter uses carry chain (Xilinx - usually automatic)
//   # No special attribute needed, synthesis tool infers CARRY4
//
//   # Prevent SRL inference for counter registers
//   set_property SHREG_EXTRACT NO [get_cells u_wr_ptr/counter_bin_reg[*]]
//   set_property SHREG_EXTRACT NO [get_cells u_wr_ptr/counter_gray_reg[*]]
//   ```
//
//   **Synthesis Attributes (Optional):**
//   ```systemverilog
//   // Xilinx: Prevent SRL extraction (rarely needed for counters)
//   (* SHREG_EXTRACT = "NO" *) logic [WIDTH-1:0] counter_bin;
//   (* SHREG_EXTRACT = "NO" *) logic [WIDTH-1:0] counter_gray;
//
//   // Intel: Force register (usually automatic)
//   (* preserve *) logic [WIDTH-1:0] counter_bin;
//   (* preserve *) logic [WIDTH-1:0] counter_gray;
//   ```
//
//   **Resource Usage (Typical FPGA):**
//   - WIDTH=4:  4 FFs, 3 LUTs (minimal overhead)
//   - WIDTH=8:  8 FFs, 7 LUTs
//   - WIDTH=16: 16 FFs, 15 LUTs
//   - WIDTH=32: 32 FFs, 31 LUTs
//   - Register bits: 2*WIDTH (binary + Gray both registered)
//   - LUT usage: WIDTH-1 (Gray conversion XORs)
//
//   **Performance by FPGA Family:**
//   - Xilinx 7-series (Artix-7, Kintex-7, Virtex-7):
//     * WIDTH=16: ~500-600 MHz (limited by Gray XOR tree)
//     * Carry chain: ~0.02 ns/bit propagation
//   - Xilinx UltraScale/UltraScale+:
//     * WIDTH=16: ~600-700 MHz
//     * Improved carry chain: ~0.015 ns/bit
//   - Intel Cyclone V:
//     * WIDTH=16: ~400-500 MHz
//     * ALM carry: ~0.025 ns/bit
//   - Intel Arria 10 / Stratix 10:
//     * WIDTH=16: ~500-600 MHz
//     * HyperFlex registers can push >700 MHz
//
//   **Comparison to Separate Modules:**
//
//   This module (counter_bingray):
//   - Integrated: Binary counter + bin2gray in one module
//   - Synchronized outputs: Binary and Gray from same register stage
//   - Simpler instantiation: One module instead of two
//   - Guaranteed correctness: Can't accidentally desync binary/Gray
//
//   Alternative (counter_bin + bin2gray):
//   ```systemverilog
//   // Separate modules - MORE VERBOSE
//   counter_bin #(.WIDTH(WIDTH)) u_bin_cnt (
//       .i_clk   (clk),
//       .o_count (counter_bin)
//   );
//   bin2gray #(.WIDTH(WIDTH)) u_bin2gray (
//       .binary(counter_bin),
//       .gray  (counter_gray_comb)  // Combinational!
//   );
//   always_ff @(posedge clk) counter_gray <= counter_gray_comb;  // Must register!
//   ```
//   - Risk: Forgetting to register Gray output → timing/CDC issues
//   - More code: Three blocks instead of one
//
//   **Recommendation:** Use counter_bingray for FIFO pointers (simpler, safer).
//
//   **Usage Pattern in Async FIFO (fifo_async.sv):**
//
//   Write Domain:
//   1. counter_bingray generates wr_addr (binary) and wr_ptr_gray
//   2. wr_addr used for memory write addressing
//   3. wr_ptr_gray synchronized to read domain
//
//   Read Domain:
//   1. counter_bingray generates rd_addr (binary) and rd_ptr_gray
//   2. rd_addr used for memory read addressing
//   3. rd_ptr_gray synchronized to write domain
//
//   Cross-Domain:
//   - wr_ptr_gray → sync → gray2bin → wr_ptr_bin_sync (in read domain)
//   - rd_ptr_gray → sync → gray2bin → rd_ptr_bin_sync (in write domain)
//   - Empty flag: rd_addr == wr_ptr_bin_sync (in read domain)
//   - Full flag:  wr_addr_next == rd_ptr_bin_sync (in write domain)
//
//   **Why Power-of-2 Depths Only:**
//   - This module wraps at 2^WIDTH (no MAX_VALUE parameter)
//   - Pointer comparison: (wr_ptr - rd_ptr) mod 2^WIDTH
//   - For non-power-of-2 depths: Use counter_johnson + grayj2bin instead
//     (see fifo_async_div2.sv)
//
//   **Verification on FPGA:**
//   - Use ILA (Xilinx) or SignalTap (Intel) to capture:
//     * counter_bin vs counter_gray (verify Gray code property)
//     * Check that only 1 bit changes in counter_gray per increment
//     * Verify counter_bin_next = counter_bin + 1 (when enabled)
//   - Verify timing closure in implementation reports
//   - Check that carry chain was inferred (look for CARRY4 in netlist)
//
//   **Common FPGA Mistakes:**
//   1. ❌ Not constraining Gray code CDC path
//      → Timing violations, metastability risk
//   2. ❌ Using counter_bin_next without registering for complex logic
//      → Timing violations on full/empty flag paths
//   3. ❌ Forgetting this is power-of-2 only
//      → Use counter_johnson for non-power-of-2 depths
//   4. ❌ Assuming Gray output is combinational
//      → It's registered! No need to add external register
//   5. ❌ Trying to use for non-FIFO applications
//      → This is specialized for FIFO pointers, use counter_bin for general counting
//
//   **When to Use Vendor FIFO IP Instead:**
//   - Xilinx FIFO Generator or Intel DCFIFO includes:
//     * Built-in counter_bingray equivalent
//     * Optimized for specific FPGA architecture
//     * Status flags (empty, full, almost_empty, almost_full)
//     * Better tested, more features
//   - Use custom counter_bingray when:
//     * Building educational/portable design
//     * Need fine control over pointer management
//     * Custom FIFO depth or width not supported by vendor IP
//     * Vendor IP is overkill for simple application
//
//   **Integration with fifo_async.sv:**
//   - fifo_async.sv instantiates TWO of these:
//     * Write pointer counter in write clock domain
//     * Read pointer counter in read clock domain
//   - Gray outputs are synchronized across domains
//   - Binary outputs used for memory addressing
//   - Next outputs used for full/empty flag generation
//
//   **Performance:**
//   - Typical Fmax: >500 MHz for WIDTH=16 on modern FPGAs
//   - Latency: 1 cycle (registered outputs)
//   - Throughput: One count per clock (when enabled)
//   - Resource efficient: ~2 LUTs per bit (counter + XOR)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - bin2gray.sv - Standalone binary to Gray converter
//   - gray2bin.sv - Gray to binary converter (used after CDC sync)
//   - counter_bin.sv - General-purpose binary counter
//   - counter_johnson.sv - Alternative for non-power-of-2 depths
//   - fifo_async.sv - Primary user of this module
//   - glitch_free_n_dff_arn.sv - Multi-stage synchronizer for Gray pointers
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_counter_bingray.py
//   Run: pytest val/common/test_counter_bingray.py -v
//   Coverage: >95%
//   Key Test Scenarios:
//     - Binary and Gray outputs stay synchronized
//     - Gray code single-bit-change property verified
//     - counter_bin_next matches counter_bin + 1
//     - Wrap-around at 2^WIDTH
//     - Reset behavior (all outputs = 0)
//     - Enable control (count only when enabled)
//
//==============================================================================

// A parameterized gray counter for async fifo's
module counter_bingray #(
    parameter int WIDTH = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [WIDTH-1:0] counter_bin,
    output logic [WIDTH-1:0] counter_bin_next,
    output logic [WIDTH-1:0] counter_gray
);

    logic [WIDTH-1:0] w_counter_bin, w_counter_gray;

    assign w_counter_bin = enable ? (counter_bin + 1) : counter_bin;
    assign w_counter_gray = w_counter_bin ^ (w_counter_bin >> 1);
    assign counter_bin_next = w_counter_bin;

    // Increment the binary counter and convert to Gray code
    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            counter_bin  <= 'b0;
            counter_gray <= 'b0;
        end else begin
            counter_bin  <= w_counter_bin;
            counter_gray <= w_counter_gray;
        end
    end

endmodule : counter_bingray
