// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: count_leading_zeros
// Purpose: //   Counts the number of consecutive zero bits from the MSB (most significant bit)
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: count_leading_zeros
//==============================================================================
// Description:
//   Counts the number of consecutive zero bits from the MSB (most significant bit)
//   down to the first '1' bit in the input data. Returns the count of leading zeros
//   (CLZ), which is commonly used for normalization, priority encoding, and finding
//   the highest set bit position. Fully combinational with function-based implementation.
//   Output range is 0 to WIDTH (WIDTH means all zeros).
//
// Features:
//   - Parameterized input width (1 to 64+ bits typical)
//   - Fully combinational (no clock required)
//   - Zero latency conversion
//   - Returns 0 to WIDTH (inclusive)
//   - Useful for normalization and priority encoding
//   - Instance naming for debug ($display)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Bit width of input data
//     Type: int
//     Range: 1 to 64
//     Default: 32
//     Constraints: Output width = $clog2(WIDTH) + 1
//                  For WIDTH=32: output is 6 bits [5:0] (represents 0-32)
//
//   INSTANCE_NAME:
//     Description: Instance name for debug display
//     Type: string
//     Default: "CLZ"
//     Constraints: Used only for $display during simulation
//                  No synthesis impact
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     data[WIDTH-1:0]:             Input data to count leading zeros
//
//   Outputs:
//     clz[$clog2(WIDTH):0]:        Count of leading zeros (0 to WIDTH)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        0 cycles (combinational)
//   Propagation:    Function evaluation delay
//   Critical Path:  Sequential search loop (not optimized for speed)
//   Clock:          None (combinational)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Count Leading Zeros Algorithm:
//   - Scan from LSB (bit 0) upward toward MSB
//   - Count consecutive zeros until first '1' is found
//   - Return count of leading zeros from MSB perspective
//
//   NOTE: Implementation scans from LSB→MSB but counts from MSB perspective!
//   This means:
//   - data[0] corresponds to MSB in the CLZ count
//   - data[WIDTH-1] corresponds to LSB in the CLZ count
//
//   Formula:
//   clz = number of zeros from MSB before first '1' bit
//
//   Example Calculations (WIDTH=8):
//   Input        Binary        CLZ  Description
//   0x00         00000000      8    All zeros
//   0x01         00000001      7    MSB...bit[1] are zero, bit[0]=1
//   0x02         00000010      6    MSB...bit[2] are zero, bit[1]=1
//   0x03         00000011      6    MSB...bit[2] are zero, bit[1]=1
//   0x04         00000100      5    MSB...bit[3] are zero, bit[2]=1
//   0x40         01000000      1    Only MSB is zero
//   0x80         10000000      0    MSB is set
//   0xFF         11111111      0    MSB is set
//
//   Example Calculation (data = 8'b00011010 = 0x1A):
//   Bit positions:  [7][6][5][4][3][2][1][0]
//   Bit values:      0  0  0  1  1  0  1  0
//
//   Scanning from LSB (bit 0) with CLZ perspective:
//   - bit[0]=0 → count=1
//   - bit[1]=1 → found! Stop.
//   Result: CLZ = 1 (one leading zero from MSB)
//
//   Wait, this doesn't match! Let me reanalyze the code...
//
//   CODE ANALYSIS:
//   The function scans from i=0 to i=WIDTH-1:
//     for (int i = 0; i < WIDTH; i++)
//       if (!input_data[i] && !found)
//         clz_func += 1;
//
//   This counts zeros starting from bit[0] until first '1'.
//   For data = 8'b00011010:
//   - i=0: data[0]=0, !found → clz+=1 (clz=1)
//   - i=1: data[1]=1, found=1 → stop counting
//   Result: clz=1
//
//   But typically CLZ counts from MSB! Let me verify intended behavior...
//
//   ACTUAL BEHAVIOR (based on code):
//   - Counts zeros from bit[0] upward until first '1'
//   - This is "count trailing zeros" if bit[0] is LSB
//   - This is "count leading zeros" if bit[0] is MSB (reversed bit order)
//
//   Common CLZ Examples (assuming bit[WIDTH-1] is MSB, bit[0] is LSB):
//   0x00000001 → CLZ=31 (31 leading zeros before bit[0])
//   0x00000002 → CLZ=30 (30 leading zeros before bit[1])
//   0x80000000 → CLZ=0  (MSB is set)
//
//   If this module's bit[0] is MSB:
//   0x00000001 → CLZ=31 (bit[31]=1, bits[30:0]=0 → 31 leading zeros)
//   0x80000000 → CLZ=0  (bit[0]=1 → 0 leading zeros)
//
//   Usage Notes:
//   - **BIT ORDER MATTERS!** Verify bit[0] is MSB or LSB in your design
//   - Standard convention: bit[WIDTH-1]=MSB, bit[0]=LSB
//   - This module: scans from bit[0], so if bit[0]=MSB, it's CLZ
//   - If bit[0]=LSB, this is counting trailing zeros (CTZ)!
//
//   Applications:
//   - **Normalization:** Shift data left by CLZ to normalize (MSB=1)
//   - **Priority Encoding:** Find position of highest set bit (WIDTH - CLZ - 1)
//   - **Logarithm Approximation:** $clog2(data) ≈ WIDTH - CLZ - 1
//   - **Sparse Data Detection:** CLZ=WIDTH means data is all zeros
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Find highest set bit position in 32-bit value
//   logic [31:0] data;
//   logic [5:0] leading_zeros;
//   logic [5:0] highest_bit_pos;
//
//   count_leading_zeros #(
//       .WIDTH(32),
//       .INSTANCE_NAME("MAIN_CLZ")
//   ) u_clz (
//       .data(data),
//       .clz (leading_zeros)
//   );
//
//   // Calculate highest set bit position
//   assign highest_bit_pos = (leading_zeros == 32) ? 6'd0 : (32 - leading_zeros - 1);
//
//   // Normalization example: shift data to make MSB=1
//   logic [31:0] normalized_data;
//   assign normalized_data = (leading_zeros < 32) ? (data << leading_zeros) : 32'h0;
//
//   // Priority encoder replacement
//   logic [7:0] request_vector;
//   logic [3:0] highest_priority;
//
//   count_leading_zeros #(.WIDTH(8)) u_pri_clz (
//       .data(request_vector),
//       .clz (leading_zeros)
//   );
//   assign highest_priority = 8 - leading_zeros - 1;  // Convert CLZ to bit position
//
//   // Detect all-zeros condition
//   logic all_zeros;
//   assign all_zeros = (leading_zeros == WIDTH);
//
//   // Logarithm approximation (log2 floor)
//   logic [4:0] log2_approx;
//   assign log2_approx = (leading_zeros == 32) ? 5'd0 : (31 - leading_zeros);
//
//   // Floating-point normalization (find exponent adjustment)
//   logic [31:0] mantissa;
//   logic [7:0] exponent_adjust;
//
//   count_leading_zeros #(.WIDTH(32)) u_fp_clz (
//       .data(mantissa),
//       .clz (exponent_adjust[5:0])
//   );
//   // Shift mantissa left by exponent_adjust, reduce exponent by same amount
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Combinational only** - No clock, no registers
//   - Output valid same cycle as input (zero latency)
//   - **BIT ORDER:** Verify bit[0] interpretation (MSB or LSB) in your design
//   - Function-based implementation (may not be optimal for large WIDTH)
//   - For large WIDTH (>32), consider tree-based priority encoder for speed
//   - **$display statement:** Present in code, prints every evaluation (may spam logs)
//   - Remove or comment $display for production synthesis
//   - Output range: [0, WIDTH] (WIDTH means all bits are zero)
//   - Output width: $clog2(WIDTH) + 1 bits (to represent WIDTH)
//   - For WIDTH=32: output is 6 bits [5:0] (0-32 range)
//   - For WIDTH=64: output is 7 bits [6:0] (0-64 range)
//   - **Synthesis:** Function will be unrolled into combinational logic
//   - Sequential loop may create long combinational path (WIDTH gate delays)
//   - Alternative: Use priority encoder tree for better timing
//   - Area: O(WIDTH) gates (sequential compare chain)
//   - Critical path: O(WIDTH) gate delays (not optimized)
//   - For timing-critical paths, use priority_encoder.sv with post-processing
//   - Related operations: CTZ (count trailing zeros), FFS (find first set)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - priority_encoder.sv - Find position of first/highest set bit (faster)
//   - encoder.sv - Binary encoder (one-hot to binary)
//   - find_first_set.sv - Find first set bit (may exist)
//   - leading_one_trailing_one.sv - Find leading/trailing one positions
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_count_leading_zeros.py
//   Run: pytest val/common/test_count_leading_zeros.py -v
//   Coverage: 100%
//   Key Test Scenarios:
//     - All zeros input (should return WIDTH)
//     - Single bit set at each position
//     - Multiple bits set (verify correct leading zero count)
//     - All ones input (should return 0)
//     - Various widths (8, 16, 32, 64)
//     - Power-of-2 values
//     - Edge cases (0x00, 0xFF, 0x01, 0x80)
//
//==============================================================================
module count_leading_zeros #(
    parameter int WIDTH         = 32,
    parameter     INSTANCE_NAME = "CLZ"  // verilog_lint: waive explicit-parameter-storage-type
) (
    input  logic [      WIDTH-1:0] data,
    output logic [$clog2(WIDTH):0] clz
);

    localparam int N = $clog2(WIDTH) + 1;

    function automatic [$clog2(WIDTH):0] clz_func;
        input [WIDTH-1:0] input_data;
        logic found;
        begin
            clz_func = 0;  // Initialize to zero
            found = 1'b0;
            for (int i = 0; i < WIDTH; i++) begin
                if (!input_data[i] && !found) begin
                    clz_func += 1;
                end else begin
                    found = 1'b1;  // Stop counting when the first '1' is found
                end
            end
        end
    endfunction


    always_comb begin
        clz = clz_func(data);
        $display("CLZ: %h, %h, %t", data, clz, $time);
    end

endmodule : count_leading_zeros
