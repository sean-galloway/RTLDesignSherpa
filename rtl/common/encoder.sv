// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: encoder
// Purpose: //   Binary encoder that converts one-hot or thermometer-coded input to binary
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: encoder
//==============================================================================
// Description:
//   Binary encoder that converts one-hot or thermometer-coded input to binary
//   representation. Scans input from LSB to MSB and returns the binary position
//   of the highest (last) asserted bit. If multiple bits are set, the highest
//   bit index wins. If no bits are set, output is 0. Fully combinational.
//
// Features:
//   - Parameterized input width (2 to 256+ typical)
//   - Fully combinational (no clock required)
//   - Zero latency conversion
//   - Highest bit priority (LSB to MSB scan)
//   - Handles one-hot, thermometer, or arbitrary patterns
//   - Minimal area (sequential compare logic)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   N:
//     Description: Number of input bits to encode
//     Type: int
//     Range: 2 to 256
//     Default: 8
//     Constraints: Output width = $clog2(N)
//                  For N=8: output is 3 bits [2:0] (represents 0-7)
//                  For N=16: output is 4 bits [3:0] (represents 0-15)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     decoded[N-1:0]:          Input bit vector (one-hot, thermometer, or mixed)
//
//   Outputs:
//     data[$clog2(N)-1:0]:     Binary encoded output (position of highest set bit)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        0 cycles (combinational)
//   Propagation:    Sequential loop evaluation delay
//   Critical Path:  O(N) comparisons (not optimized)
//   Clock:          None (combinational)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Binary Encoding Algorithm:
//   - Scan input from bit 0 to bit N-1 (LSB to MSB)
//   - For each set bit, update output to that bit's index
//   - Final output is the index of the highest set bit
//   - If no bits set, output remains 0
//
//   Formula:
//   data = index of last '1' bit found (scanning LSB→MSB)
//
//   Example Encodings (N=8):
//   Input (decoded)  Binary     Output (data)  Description
//   00000000         8'b00000000    3'b000     No bits set → 0
//   00000001         8'b00000001    3'b000     Bit 0 set → 0
//   00000010         8'b00000010    3'b001     Bit 1 set → 1
//   00000100         8'b00000100    3'b010     Bit 2 set → 2
//   10000000         8'b10000000    3'b111     Bit 7 set → 7
//   11111111         8'b11111111    3'b111     All set → 7 (highest)
//   01010101         8'b01010101    3'b110     Bit 6 is highest → 6
//   10101010         8'b10101010    3'b111     Bit 7 is highest → 7
//
//   One-Hot Input Examples:
//   Input        Output   Description
//   00000001     3'b000   One-hot position 0
//   00000010     3'b001   One-hot position 1
//   00000100     3'b010   One-hot position 2
//   00001000     3'b011   One-hot position 3
//   00010000     3'b100   One-hot position 4
//   00100000     3'b101   One-hot position 5
//   01000000     3'b110   One-hot position 6
//   10000000     3'b111   One-hot position 7
//
//   Thermometer-Coded Input Examples:
//   Input        Output   Description
//   00000001     3'b000   Thermometer 1
//   00000011     3'b001   Thermometer 2 → highest bit is bit[1]
//   00000111     3'b010   Thermometer 3 → highest bit is bit[2]
//   00001111     3'b011   Thermometer 4 → highest bit is bit[3]
//   11111111     3'b111   Thermometer 8 → highest bit is bit[7]
//
//   Multiple Bits Set (Non-One-Hot):
//   Input        Output   Description
//   00000011     3'b001   Bits 0,1 set → highest is bit[1]
//   00001100     3'b011   Bits 2,3 set → highest is bit[3]
//   11000000     3'b111   Bits 6,7 set → highest is bit[7]
//   10000001     3'b111   Bits 0,7 set → highest is bit[7]
//
//   Behavior Summary:
//   - **One-hot input:** Returns position of the single set bit
//   - **Thermometer input:** Returns position of MSB of contiguous 1's
//   - **Multiple bits set:** Returns position of highest set bit
//   - **No bits set:** Returns 0 (may be ambiguous with bit[0] set!)
//
//   Ambiguity Note:
//   - Input 00000000 → output 0
//   - Input 00000001 → output 0
//   - These are indistinguishable! Use separate valid flag if needed.
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Convert one-hot request to binary index
//   logic [7:0] request_onehot;
//   logic [2:0] request_index;
//
//   encoder #(
//       .N(8)
//   ) u_req_enc (
//       .decoded(request_onehot),
//       .data   (request_index)
//   );
//
//   // Convert thermometer-coded signal to count
//   logic [15:0] thermometer_code;
//   logic [3:0] count_value;
//
//   encoder #(.N(16)) u_therm_enc (
//       .decoded(thermometer_code),
//       .data   (count_value)      // Position of highest '1' = count-1
//   );
//
//   // Priority encoder for interrupt controller
//   logic [31:0] interrupt_pending;
//   logic [4:0] highest_priority_int;
//
//   encoder #(.N(32)) u_int_enc (
//       .decoded(interrupt_pending),
//       .data   (highest_priority_int)  // Interrupt 31 has highest priority
//   );
//
//   // Address decoder reverse (encode back to binary)
//   logic [63:0] chip_select;
//   logic [5:0] selected_chip;
//
//   encoder #(.N(64)) u_cs_enc (
//       .decoded(chip_select),
//       .data   (selected_chip)
//   );
//
//   // Grant arbitration encoding
//   logic [7:0] grant_onehot;
//   logic [2:0] grant_id;
//   logic grant_valid;
//
//   encoder #(.N(8)) u_grant_enc (
//       .decoded(grant_onehot),
//       .data   (grant_id)
//   );
//   assign grant_valid = |grant_onehot;  // Avoid ambiguity with valid flag
//
//   // Mux select encoding
//   logic [15:0] mux_sel_onehot;
//   logic [3:0] mux_sel_binary;
//
//   encoder #(.N(16)) u_mux_enc (
//       .decoded(mux_sel_onehot),
//       .data   (mux_sel_binary)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Combinational only** - No clock, no registers
//   - Output valid same cycle as input (zero latency)
//   - **Highest bit priority:** Scanning LSB→MSB, last set bit wins
//   - Sequential loop implementation (simple but not optimal for timing)
//   - For large N (>32), consider tree-based priority encoder for speed
//   - **Ambiguity:** Cannot distinguish "no bits set" from "bit[0] set"
//   - Recommended: Use separate valid/enable output if detecting zero input
//   - Algorithm: Iterative comparison (data updated for each set bit)
//   - **Synthesis:** Unrolls to cascaded muxes or priority logic
//   - Area: O(N) comparators/muxes (sequential chain)
//   - Critical path: O(N) gate delays (worst case)
//   - For timing-critical paths, use priority_encoder.sv (tree-based)
//   - **Input flexibility:** Works with one-hot, thermometer, or arbitrary patterns
//   - One-hot assumption not enforced (if multiple bits set, highest wins)
//   - Output range: [0, N-1] but width is $clog2(N) bits
//   - For N=8: output is 3 bits, can represent 0-7 (exact fit)
//   - For N=7: output is 3 bits, can represent 0-6 (values 7 unused)
//   - Inverse of decoder.sv (but not exact inverse due to ambiguity)
//   - Use for: Interrupt encoding, arbiter grant encoding, mux select encoding
//   - **Not for:** High-speed paths (use priority_encoder_tree variant)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - decoder.sv - Binary to one-hot decoder (inverse operation)
//   - priority_encoder.sv - Optimized tree-based priority encoder (faster)
//   - count_leading_zeros.sv - Find leading zeros (different algorithm)
//   - arbiter_*.sv - Arbiters that generate one-hot grants (use encoder)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_encoder.py
//   Run: pytest val/common/test_encoder.py -v
//   Coverage: 100%
//   Key Test Scenarios:
//     - One-hot inputs (each bit position individually)
//     - Thermometer-coded inputs
//     - Multiple bits set (verify highest priority)
//     - All zeros input (should return 0)
//     - All ones input (should return N-1)
//     - Various widths (4, 8, 16, 32)
//     - Random bit patterns
//     - Edge cases (0x00, 0xFF, single bits)
//
//==============================================================================
module encoder #(
    parameter int N = 8
) (
    input  logic [        N-1:0] decoded,
    output logic [$clog2(N)-1:0] data
);
    always_comb begin
        data = 0;
        for (int i = 0; i < N; i++) begin
            if (decoded[i]) data = $clog2(N)'(i);
        end
    end
endmodule : encoder
