// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bin2gray
// Purpose: //   Binary to Gray code converter. Converts standard binary encoding to Gray code
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: bin2gray
//==============================================================================
// Description:
//   Binary to Gray code converter. Converts standard binary encoding to Gray code
//   (reflected binary code) where only one bit changes between consecutive values.
//   This single-bit transition property is critical for safe clock domain crossing (CDC)
//   of multi-bit values. Fully combinational (zero latency) with parameterized width.
//
// Features:
//   - Parameterized width (1 to 64+ bits typical)
//   - Fully combinational (no clock required)
//   - Zero latency conversion
//   - Single-bit change between consecutive Gray codes
//   - Optimal for CDC applications
//   - Minimal area (XOR gates only)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Bit width of binary and Gray code values
//     Type: int
//     Range: 1 to 64
//     Default: 4
//     Constraints: Same width for input and output
//                  Larger widths supported but less common
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     binary[WIDTH-1:0]:    Binary input value
//
//   Outputs:
//     gray[WIDTH-1:0]:      Gray code output value
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        0 cycles (combinational)
//   Propagation:    XOR gate delay (depth = 1)
//   Critical Path:  Single XOR level
//   Clock:          None (combinational)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Gray Code Conversion Algorithm:
//   - MSB: gray[WIDTH-1] = binary[WIDTH-1] (MSB unchanged)
//   - Other bits: gray[i] = binary[i] XOR binary[i+1]
//   - Result: Each Gray code differs from neighbors by exactly 1 bit
//
//   Conversion Formula:
//   gray[n-1] = bin[n-1]
//   gray[i]   = bin[i] ^ bin[i+1]  for i = 0 to n-2
//
//   Example Conversion (WIDTH=4):
//   Binary  → Gray
//   0000    → 0000   (no bits set)
//   0001    → 0001   (bit 0 changes)
//   0010    → 0011   (bit 1 changes)
//   0011    → 0010   (bit 0 changes)
//   0100    → 0110   (bit 2 changes)
//   0101    → 0111   (bit 0 changes)
//   0110    → 0101   (bit 1 changes)
//   0111    → 0100   (bit 0 changes)
//   1000    → 1100   (bit 3 changes)
//   ...
//
//   Single-Bit-Change Property:
//   - 0000 → 0001: only bit[0] changed
//   - 0001 → 0011: only bit[1] changed
//   - 0011 → 0010: only bit[0] changed
//   - Guarantees no multi-bit glitches during CDC
//
//   Why Gray Code for CDC:
//   - Binary counter: 0111 → 1000 (all 4 bits change!)
//   - Gray counter:   0100 → 1100 (only bit[3] changes)
//   - Metastability affects only 1 bit → no corruption
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Convert 8-bit binary counter to Gray for CDC
//   logic [7:0] binary_count;
//   logic [7:0] gray_count;
//
//   bin2gray #(
//       .WIDTH(8)
//   ) u_bin2gray (
//       .binary(binary_count),
//       .gray  (gray_count)
//   );
//
//   // Synchronize Gray code across clock domain
//   logic [7:0] gray_sync;
//   glitch_free_n_dff_arn #(
//       .WIDTH(8),
//       .FLOP_COUNT(2)
//   ) u_gray_sync (
//       .clk (dst_clk),
//       .rst_n(dst_rst_n),
//       .d   (gray_count),     // Gray code from source domain
//       .q   (gray_sync)       // Synchronized Gray code
//   );
//
//   // Convert back to binary in destination domain
//   logic [7:0] binary_sync;
//   gray2bin #(
//       .WIDTH(8)
//   ) u_gray2bin (
//       .gray  (gray_sync),
//       .binary(binary_sync)  // Final binary value in dst domain
//   );
//
//   // Pointer synchronization for async FIFO
//   logic [ADDR_WIDTH-1:0] wr_ptr_bin, wr_ptr_gray;
//   bin2gray #(.WIDTH(ADDR_WIDTH)) u_wr_ptr_gray (
//       .binary(wr_ptr_bin),
//       .gray  (wr_ptr_gray)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Combinational only** - No clock, no registers
//   - Output valid same cycle as input (zero latency)
//   - **Critical for CDC:** Use Gray code for all multi-bit CDC
//   - Algorithm: Each bit XORed with next higher bit (except MSB)
//   - **Synthesis:** Maps to single XOR gate per bit (except MSB)
//   - Area: WIDTH-1 XOR gates (minimal)
//   - **Do NOT** synchronize binary counters directly (use Gray!)
//   - Always pair with gray2bin after synchronization
//   - Gray code guarantees only 1 bit changes per increment
//   - Prevents metastability-induced value corruption
//   - Used in: Async FIFOs, clock domain synchronizers, LFSR feedback
//   - **Not for arithmetic:** Convert back to binary for math operations
//   - Reversible: gray2bin reconstructs exact binary value
//   - Also called "reflected binary code"
//   - Minimum Hamming distance = 1 between consecutive codes
//
//------------------------------------------------------------------------------
// FPGA-Specific Synthesis and Implementation Notes:
//------------------------------------------------------------------------------
//   **Synthesis on FPGAs:**
//   - Maps to LUT logic (1 LUT per bit, except MSB passthrough)
//   - WIDTH=8: 7 LUTs (one XOR per bit 0-6)
//   - WIDTH=16: 15 LUTs
//   - No special primitives needed - pure combinational logic
//   - Xilinx: Implements as LUT1 (XOR function)
//   - Intel: Implements as adaptive LUT in ALM
//
//   **Critical Timing Considerations:**
//   - This module is combinational - timing depends on where it's used
//   - **FPGA Best Practice:** Register the Gray code output immediately!
//
//   Example (CORRECT for FPGA timing closure):
//   ```systemverilog
//   // BAD: Combinational path from counter to CDC synchronizer
//   bin2gray #(.WIDTH(8)) u_gray (.binary(counter), .gray(gray_code));
//   sync_2ff #(.WIDTH(8)) u_sync (.d(gray_code), ...);  // Long combo path!
//
//   // GOOD: Register Gray code before CDC (breaks long path)
//   logic [7:0] gray_code, gray_reg;
//   bin2gray #(.WIDTH(8)) u_gray (.binary(counter), .gray(gray_code));
//   always_ff @(posedge src_clk) gray_reg <= gray_code;  // Register!
//   sync_2ff #(.WIDTH(8)) u_sync (.d(gray_reg), ...);    // Clean CDC
//   ```
//
//   **Why Register the Output:**
//   - Counter logic + bin2gray XORs = long combinational path
//   - Can cause setup violations on fast clocks (>200 MHz)
//   - Registering adds 1 cycle latency but ensures timing closure
//   - Registered output is stable for CDC synchronizers
//
//   **Timing Constraints (XDC/SDC):**
//   ```tcl
//   # If Gray code crosses domains, set max delay on synchronizer input
//   set_max_delay -datapath_only \
//     -from [get_cells gray_reg_reg[*]] \
//     -to   [get_cells sync_stage0_reg[*]] \
//     [expr {2 * $clk_period}]
//
//   # Optional: Multicycle if Gray code generation is slow
//   set_multicycle_path 2 -setup \
//     -from [get_cells counter_reg[*]] \
//     -to   [get_cells gray_reg_reg[*]]
//   set_multicycle_path 1 -hold \
//     -from [get_cells counter_reg[*]] \
//     -to   [get_cells gray_reg_reg[*]]
//   ```
//
//   **Synthesis Attributes (Optional):**
//   - Generally not needed - logic is simple enough
//   - If synthesis tool warns about optimization:
//   ```systemverilog
//   (* keep = "true" *) wire [WIDTH-1:0] gray;  // Xilinx: prevent optimization
//   (* preserve *) wire [WIDTH-1:0] gray;       // Intel: preserve logic
//   ```
//
//   **FIFO Pointer Synchronization (Most Common Use):**
//   - Async FIFOs use Gray-coded pointers for CDC
//   - Typical flow:
//     1. Binary pointer increments in write clock domain
//     2. bin2gray converts to Gray (this module)
//     3. Gray code registered in source domain
//     4. Gray code synchronized to destination domain (2-FF sync)
//     5. gray2bin converts back to binary
//   - **Critical:** Gray code must be stable before synchronization!
//   - Always register Gray output before sending across domains
//
//   **Verification on FPGA:**
//   - Use ILA (Xilinx) or SignalTap (Intel) to capture:
//     * Binary input
//     * Gray output
//     * Verify single-bit changes
//   - Check for glitches on Gray code signals (should be clean)
//   - Verify timing closure in implementation reports
//
//   **Common FPGA Mistakes:**
//   1. ❌ Not registering Gray output before CDC
//      → Timing violations, metastability risk
//   2. ❌ Using Gray code for arithmetic operations
//      → Must convert back to binary first!
//   3. ❌ Assuming Gray code is "free" timing-wise
//      → XOR delays add up, especially for wide buses
//   4. ❌ Not pairing with gray2bin after synchronization
//      → Destination gets garbage values
//
//   **When to Use Vendor IP Instead:**
//   - For async FIFOs: Consider Xilinx FIFO Generator or Intel DCFIFO
//   - Vendor IP includes:
//     * Built-in Gray code conversion
//     * Optimized pointer management
//     * Status flag generation
//     * Better timing closure
//   - Use custom bin2gray when:
//     * Building educational/portable design
//     * Need fine control over CDC methodology
//     * Vendor IP doesn't fit requirements
//
//   **Resource Usage (Typical FPGA):**
//   - WIDTH=4:  3 LUTs (minimal)
//   - WIDTH=8:  7 LUTs
//   - WIDTH=16: 15 LUTs
//   - WIDTH=32: 31 LUTs
//   - No registers consumed (combinational only)
//   - Negligible power impact
//
//   **Performance:**
//   - Propagation delay: ~0.2-0.5 ns on modern FPGAs (one LUT level)
//   - Not on critical path if output is registered
//   - Scales linearly with WIDTH (one XOR per bit)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - gray2bin.sv - Gray to binary converter (reverse operation)
//   - glitch_free_n_dff_arn.sv - Multi-stage synchronizer for Gray codes
//   - fifo_async.sv - Uses Gray code for pointer synchronization
//   - counter_bingray.sv - Binary counter with Gray code output
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_bin2gray.py
//   Run: pytest val/common/test_bin2gray.py -v
//   Coverage: 100%
//   Key Test Scenarios:
//     - All input values (exhaustive for small widths)
//     - Single-bit-change verification between consecutive codes
//     - Reversibility test (bin2gray → gray2bin = identity)
//     - Various widths (4, 8, 16, 32)
//     - Edge cases (0x00, 0xFF, wrap-around)
//
//==============================================================================
module bin2gray #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] binary,
    output wire [WIDTH-1:0] gray
);

    genvar i;
    generate
        for (i = 0; i < WIDTH - 1; i++) begin : gen_gray
            assign gray[i] = binary[i] ^ binary[i+1];
        end
    endgenerate

    assign gray[WIDTH-1] = binary[WIDTH-1];

endmodule : bin2gray
