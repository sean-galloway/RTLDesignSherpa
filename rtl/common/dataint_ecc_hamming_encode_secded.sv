// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: dataint_ecc_hamming_encode_secded
// Purpose: //   Hamming SECDED (Single Error Correction, Double Error Detection) encoder.
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: dataint_ecc_hamming_encode_secded
//==============================================================================
// Description:
//   Hamming SECDED (Single Error Correction, Double Error Detection) encoder.
//   Generates parity bits for input data using Hamming code algorithm with
//   additional overall parity bit for double-error detection. Combinational logic
//   only - no clock required. Supports arbitrary data widths with automatic parity
//   bit calculation.
//
// Features:
//   - Single-bit error correction capability
//   - Double-bit error detection capability
//   - Parameterized data width (4 to 64+ bits typical)
//   - Fully combinational (zero latency)
//   - Automatic parity bit count calculation
//   - Standard Hamming code bit positioning
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Input data width (bits)
//     Type: int
//     Range: 4 to 128
//     Default: 4
//     Constraints: Parity bits = $clog2(WIDTH + $clog2(WIDTH) + 1)
//                  Total width = WIDTH + ParityBits + 1 (SECDED bit)
//
//   DEBUG:
//     Description: Enable debug display statements
//     Type: int
//     Range: 0 or 1
//     Default: 0
//     Constraints: Only affects simulation ($display calls)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     data[WIDTH-1:0]: Input data to encode
//
//   Outputs:
//     encoded_data[TotalWidth-1:0]: Data with parity bits inserted
//                                    TotalWidth = WIDTH + ParityBits + 1
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Hamming Code Positioning:
//   - Parity bits at positions: 1, 2, 4, 8, 16, ... (powers of 2)
//   - Data bits fill remaining positions
//   - Position 0: SECDED overall parity bit
//   - Example (WIDTH=4): Positions [0,1,2,3,4,5,6,7] = [P, P1, P2, D0, P4, D1, D2, D3]
//
//   Parity Calculation:
//   - Each parity bit P(2^i) covers positions where bit i of position number = 1
//   - P1 (pos 1): Covers all odd positions (1,3,5,7,9...)
//   - P2 (pos 2): Covers positions where bit 1 set (2,3,6,7,10,11...)
//   - P4 (pos 4): Covers positions where bit 2 set (4,5,6,7,12,13,14,15...)
//   - SECDED bit (MSB): XOR of all other bits (overall parity)
//
//   Example (WIDTH=4, data=4'b1010):
//   Position:     [7] [6] [5] [4] [3] [2] [1] [0]
//   Bit Type:     D3  D2  D1  P4  D0  P2  P1  PSEC
//   Data Value:   1   0   1   ?   0   ?   ?   ?
//   After Parity: 1   0   1   0   0   1   1   0
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Encode 32-bit data with SECDED
//   localparam int DATA_W = 32;
//   localparam int PARITY_BITS = $clog2(DATA_W + $clog2(DATA_W) + 1);
//   localparam int TOTAL_W = DATA_W + PARITY_BITS + 1;
//
//   logic [DATA_W-1:0] data_in;
//   logic [TOTAL_W-1:0] encoded;
//
//   dataint_ecc_hamming_encode_secded #(
//       .WIDTH(DATA_W),
//       .DEBUG(0)
//   ) u_ecc_enc (
//       .data         (data_in),
//       .encoded_data (encoded)
//   );
//
//   // Store or transmit encoded data
//   // Decoder can correct 1-bit errors, detect 2-bit errors
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Combinational only** - No clock, no registers
//   - Output width = WIDTH + $clog2(WIDTH + $clog2(WIDTH) + 1) + 1
//   - For WIDTH=32: ParityBits=6, TotalWidth=39 (22% overhead)
//   - For WIDTH=64: ParityBits=7, TotalWidth=72 (12.5% overhead)
//   - SECDED bit enables double-error detection (Hamming alone is SEC only)
//   - Use with dataint_ecc_hamming_decode_secded for error correction
//   - **Critical path:** Parity calculation (XOR tree depth = log2(TotalWidth))
//   - Synthesis: Efficiently maps to XOR gates
//   - **Not for high-speed paths** - XOR tree delay increases with WIDTH
//   - Typical use: Memory protection, register file ECC, packet integrity
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - dataint_ecc_hamming_decode_secded.sv - SECDED decoder (error correction)
//   - dataint_parity.sv - Simple parity (detection only, no correction)
//   - dataint_crc.sv - CRC (detection only, stronger than parity)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_dataint_ecc_hamming_encode_secded.py
//   Run: pytest val/common/test_dataint_ecc_hamming_encode_secded.py -v
//   Coverage: 87%
//   Key Test Scenarios:
//     - Various data widths (4, 8, 16, 32, 64)
//     - All-zeros, all-ones, alternating patterns
//     - Parity bit positioning verification
//     - Integration with decoder (encode → inject error → decode)
//
//==============================================================================
module dataint_ecc_hamming_encode_secded #(
    parameter int WIDTH = 4,
    parameter int DEBUG = 0
) (
    input  logic [     WIDTH-1:0] data,
    output logic [TotalWidth-1:0] encoded_data
);
    localparam int ParityBits = $clog2(WIDTH + $clog2(WIDTH) + 1);
    localparam int TotalWidth = WIDTH + ParityBits + 1;  // Including the SECDED bit

    // local wires
    logic [TotalWidth-1:0] w_data_with_parity;

    ////////////////////////////////////////////////////////////////////////////
    // Function to calculate the bit position for data insertion
    function automatic integer bit_position(input integer k);
        integer j, pos;
        begin
            pos = k + 1;  // Start at k+1 to account for the parity bit at position 0
            for (j = 0; j < ParityBits; j++) begin
                if (pos >= (2 ** j)) pos = pos + 1;
            end
            bit_position = pos - 1;  // Convert back to 0-based index
        end
        if (DEBUG != 0) $display("bit_position for data bit %d is %d", k, bit_position);
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Function to get a bit mask for the bits covered by a given parity bit
    function automatic [TotalWidth-1:0] get_covered_bits(input integer parity_bit);
        integer j;
        begin
            get_covered_bits = 'b0;
            for (j = 0; j < TotalWidth; j++) begin
                if (|(((j + 1) >> parity_bit) & 1)) get_covered_bits[j] = 1'b1;
            end
        end
        if (DEBUG != 0)
            $display("get_covered_bits for parity bit %d is %b", parity_bit, get_covered_bits);
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Insert data bits and calculate parity bits
    integer i;
    integer parity_pos;
    integer bit_index;
    logic [TotalWidth-1:0] w_covered_bits;
    always_comb begin
        // Initialize with zeros
        w_data_with_parity = {TotalWidth{1'b0}};

        // Insert data bits into the correct positions
        for (i = 0; i < WIDTH; i++) begin
            /* verilator lint_off SIDEEFFECT */
            w_data_with_parity[bit_position(i)] = data[i];
            /* verilator lint_on SIDEEFFECT */
        end

        // Calculate parity bits
        for (i = 0; i < ParityBits; i++) begin
            parity_pos = (2 ** i) - 1;
            if (DEBUG != 0) $display("Calculate Parity Bits, parity bit position: %d", parity_pos);
            w_data_with_parity[parity_pos] = 1'b0;  // Initialize to 0
            w_covered_bits = get_covered_bits(i);
            for (bit_index = 0; bit_index < TotalWidth; bit_index = bit_index + 1) begin
                if (w_covered_bits[bit_index]) begin
                    w_data_with_parity[parity_pos] =
                        w_data_with_parity[parity_pos] ^ w_data_with_parity[bit_index];
                end
            end
        end

        // Calculate the extra SECDED bit
        w_data_with_parity[TotalWidth-1] = ^w_data_with_parity[TotalWidth-2:0];

        // Assign to output
        encoded_data = w_data_with_parity;
    end

endmodule : dataint_ecc_hamming_encode_secded
