// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: dataint_ecc_hamming_decode_secded
// Purpose: //   Hamming SECDED (Single Error Correction, Double Error Detection) decoder.
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: dataint_ecc_hamming_decode_secded
//==============================================================================
// Description:
//   Hamming SECDED (Single Error Correction, Double Error Detection) decoder.
//   Corrects single-bit errors and detects double-bit errors in Hamming-encoded
//   data. Uses syndrome calculation to locate errors and overall parity check to
//   distinguish single vs. double errors. Registered output for pipeline integration.
//   Companion to dataint_ecc_hamming_encode_secded for end-to-end ECC protection.
//
// Features:
//   - Single-bit error correction (SEC)
//   - Double-bit error detection (DED)
//   - Syndrome-based error localization
//   - Overall parity discriminator for SECDED
//   - Registered outputs (1 cycle latency)
//   - Parameterized data width (4 to 128 bits)
//   - Error status flags (single/double error detection)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Original data width (before encoding)
//     Type: int
//     Range: 4 to 128
//     Default: 4
//     Constraints: Must match encoder WIDTH
//                  Total input width = WIDTH + ParityBits + 1 (SECDED bit)
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
//     clk:                             Clock input
//     rst_n:                           Asynchronous active-low reset
//     enable:                          Enable decoding operation
//     hamming_data[TotalWidth-1:0]:    Encoded data with parity bits
//                                       TotalWidth = WIDTH + ParityBits + 1
//
//   Outputs:
//     data[WIDTH-1:0]:                 Corrected data output (registered)
//     error_detected:                  Error flag (single or double)
//     double_error_detected:           Double-bit error flag (uncorrectable)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        1 cycle (syndrome calculation + correction registered)
//   Throughput:     1 correction per cycle
//   Clock-to-Q:     Registered outputs (1 FF delay)
//   Reset:          Asynchronous (immediate to 0)
//   Enable:         Synchronous gate (hold outputs when enable=0)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Syndrome Calculation:
//   - Syndrome is XOR of all bits covered by each parity bit
//   - Syndrome[i] = XOR(all positions where bit i of position number = 1)
//   - Zero syndrome → no error in Hamming data
//   - Non-zero syndrome → points to error bit position
//
//   Overall Parity Check:
//   - SECDED bit (MSB) is XOR of all other bits
//   - Recalculate overall parity and compare to received SECDED bit
//   - Parity mismatch → odd number of errors (1, 3, 5...)
//   - Parity match → even number of errors (0, 2, 4...)
//
//   Error Detection and Correction Logic:
//   1. **No Error (syndrome=0, parity match)**
//      - Pass data through unmodified
//      - error_detected = 0, double_error_detected = 0
//
//   2. **Single-bit Error in Hamming Data (syndrome≠0, parity mismatch)**
//      - Syndrome points to error bit position
//      - Flip bit at syndrome position to correct
//      - error_detected = 1, double_error_detected = 0
//      - ✅ CORRECTABLE
//
//   3. **Single-bit Error in SECDED Bit (syndrome=0, parity mismatch)**
//      - Error is in overall parity bit itself
//      - Data is correct, no correction needed
//      - error_detected = 1, double_error_detected = 0
//      - ✅ DETECTABLE (data unaffected)
//
//   4. **Double-bit Error (syndrome≠0, parity match)**
//      - Syndrome is non-zero but parity matches (even errors)
//      - Cannot reliably correct (multiple bit corruption)
//      - error_detected = 1, double_error_detected = 1
//      - ❌ UNCORRECTABLE (flag for upper layer handling)
//
//   Error Correction Example (WIDTH=4):
//   Received:  [7] [6] [5] [4] [3] [2] [1] [0]
//              D3  D2  D1  P4  D0  P2  P1  PSEC
//              1   0   1   0   0   1   0   0    (bit error at position 1)
//
//   Syndrome Calculation:
//   S1 = XOR(pos 1,3,5,7) = P1 ^ D0 ^ D1 ^ D3 = 0 ^ 0 ^ 1 ^ 1 = 0
//   S2 = XOR(pos 2,3,6,7) = P2 ^ D0 ^ D2 ^ D3 = 1 ^ 0 ^ 0 ^ 1 = 0
//   S4 = XOR(pos 4,5,6,7) = P4 ^ D1 ^ D2 ^ D3 = 0 ^ 1 ^ 0 ^ 1 = 0
//   Syndrome = [S4,S2,S1] = 001b = 1 → Error at bit position 1
//
//   Overall Parity:
//   Received PSEC = 0
//   Calculated = XOR(all bits except PSEC) = 1 (mismatch!)
//   Parity mismatch + non-zero syndrome → Single-bit error, CORRECT IT
//
//   Correction:
//   Flip bit[1]: 0 → 1
//   Corrected: [7] [6] [5] [4] [3] [2] [1] [0]
//              1   0   1   0   0   1   1   0  ✅
//
//   Error Detection Table:
//   | Syndrome | Overall Parity | Error Type | Action |
//   |----------|----------------|------------|--------|
//   | 0        | Match          | No error   | Pass through |
//   | 0        | Mismatch       | SECDED bit error | Flag, pass data |
//   | Non-zero | Mismatch       | Single-bit in data | Correct bit |
//   | Non-zero | Match          | Double-bit error | Flag uncorrectable |
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Decode 32-bit ECC-protected data
//   localparam int DATA_W = 32;
//   localparam int PARITY_BITS = $clog2(DATA_W + $clog2(DATA_W) + 1);
//   localparam int TOTAL_W = DATA_W + PARITY_BITS + 1;
//
//   logic clk, rst_n, enable;
//   logic [TOTAL_W-1:0] ecc_data;       // From memory/transmission
//   logic [DATA_W-1:0] corrected_data;
//   logic error_flag, double_error_flag;
//
//   dataint_ecc_hamming_decode_secded #(
//       .WIDTH(DATA_W),
//       .DEBUG(0)
//   ) u_ecc_dec (
//       .clk                  (clk),
//       .rst_n                (rst_n),
//       .enable               (enable),
//       .hamming_data         (ecc_data),
//       .data                 (corrected_data),
//       .error_detected       (error_flag),
//       .double_error_detected(double_error_flag)
//   );
//
//   // Error handling logic
//   always_ff @(posedge clk) begin
//       if (enable) begin
//           if (double_error_flag) begin
//               // Uncorrectable error → trigger recovery (retry, alert, etc.)
//               $error("Double-bit error detected! Data corrupted.");
//           end else if (error_flag) begin
//               // Single-bit error corrected → log and continue
//               $display("Single-bit error corrected at cycle %0t", $time);
//           end
//       end
//   end
//
//   // Memory scrubbing example (read-correct-writeback)
//   always_ff @(posedge clk) begin
//       if (enable && error_flag && !double_error_flag) begin
//           // Write corrected data back to memory
//           memory[addr] <= corrected_data;
//       end
//   end
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Registered outputs** - 1 cycle latency from enable to corrected data
//   - Must use same WIDTH as encoder (mismatch = undefined behavior)
//   - Total input width = WIDTH + $clog2(WIDTH + $clog2(WIDTH) + 1) + 1
//   - For WIDTH=32: TotalWidth=39 (32 data + 6 parity + 1 SECDED)
//   - **Single-bit errors:** Automatically corrected, data is valid
//   - **Double-bit errors:** Detected but NOT corrected (data invalid)
//   - **Triple+ errors:** May be undetected (exceeds SECDED capability)
//   - Error correction happens in-place (flips bit in internal register)
//   - Use for: Memory scrubbing, packet validation, register file protection
//   - **Not for high-speed paths** - Syndrome calculation adds logic depth
//   - Synthesis: Maps to XOR trees (efficient) + mux for correction
//   - **Critical path:** Syndrome calculation → error correction mux → output register
//   - Typical use: SRAM/register ECC, communication link error correction
//   - **Memory scrubbing:** Read → Decode → If error detected, write corrected data back
//   - Double-error flag should trigger system-level recovery (retry, reboot, etc.)
//   - SECDED provides good protection for memory (most errors are single-bit)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - dataint_ecc_hamming_encode_secded.sv - SECDED encoder (must use together)
//   - dataint_parity.sv - Simple parity (detection only, no correction)
//   - dataint_crc.sv - CRC (detection only, no correction)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_dataint_ecc_hamming_decode_secded.py
//   Run: pytest val/common/test_dataint_ecc_hamming_decode_secded.py -v
//   Coverage: 91%
//   Key Test Scenarios:
//     - No error (clean data passes through)
//     - Single-bit error injection and correction verification
//     - SECDED bit error (data unaffected)
//     - Double-bit error detection (uncorrectable flag)
//     - Various data widths (4, 8, 16, 32, 64)
//     - Encode → Inject error → Decode → Verify correction
//     - Syndrome calculation verification
//
//==============================================================================

`include "reset_defs.svh"
module dataint_ecc_hamming_decode_secded #(
    parameter int WIDTH = 4,
    parameter int DEBUG = 0
) (
    input  logic                      clk,
    rst_n,
    input  logic                      enable,
    input  logic [WIDTH+ParityBits:0] hamming_data,
    output logic [         WIDTH-1:0] data,
    output logic                      error_detected,
    output logic                      double_error_detected
);
    localparam int ParityBits = $clog2(WIDTH + $clog2(WIDTH) + 1);
    localparam int TotalWidth = WIDTH + ParityBits + 1;

    // local wires
    logic [ParityBits-1:0] w_syndrome;
    logic [ParityBits-1:0] w_syndrome_in;
    logic [ParityBits-1:0] w_syndrome_0_based;
    logic [TotalWidth-1:0] r_data_with_parity;
    logic                  w_overall_parity;
    logic                  w_overall_parity_in;

    initial begin
        if (DEBUG != 0) begin
            // Debug initialization if needed
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Function to calculate the bit position for data extraction
    function automatic integer bit_position(input integer k);
        integer j, pos;
        begin
            pos = k + 1;  // Start at k+1 to account for the parity bit at position 0
            for (j = 0; j < ParityBits; j++) begin
                if (pos >= (2 ** j)) pos = pos + 1;
            end
            bit_position = pos - 1;  // Convert to 0-based index
        end
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Function to get a bit mask for the bits covered by a given parity bit
    function automatic [TotalWidth-1:0] get_covered_bits(input integer parity_bit);
        integer j;
        begin
            get_covered_bits = 0;
            // FIXED: Exclude SECDED bit from Hamming parity calculations
            for (j = 0; j < TotalWidth - 1; j++) begin
                // Check if the k-th bit position is covered by the parity_bit
                if (|(((j + 1) >> parity_bit) & 1)) get_covered_bits[j] = 1'b1;
            end
        end
        if (DEBUG != 0)
            $display("get_covered_bits for parity bit %d is %b", parity_bit, get_covered_bits);
    endfunction

    ////////////////////////////////////////////////////////////////////////////
    // Check parity bits
    integer i;
    integer bit_index;
    integer parity_pos;
    logic [TotalWidth-1:0] w_covered_bits;
    always_comb begin : create_syndrome_covered_bits
        if (enable) begin
            for (i = 0; i < ParityBits; i++) begin
                parity_pos       = (2 ** i) - 1;
                w_syndrome_in[i] = hamming_data[parity_pos];
                w_syndrome[i]    = 1'b0;
                w_covered_bits   = get_covered_bits(i);
                for (bit_index = 0; bit_index < TotalWidth; bit_index++)
                    // Exclude the parity bit itself from the syndrome calculation
                    if (w_covered_bits[bit_index] && (bit_index != parity_pos))
                        w_syndrome[i] = w_syndrome[i] ^ hamming_data[bit_index];
                // Then XOR with the stored parity bit to get the syndrome
                w_syndrome[i] = w_syndrome[i] ^ w_syndrome_in[i];
            end
        end else begin
            parity_pos = 'b0;
            w_syndrome = 'b0;
            w_syndrome_in = 'b0;
            w_covered_bits = 'b0;
            i = 0;
            bit_index = 0;
        end
    end

    // create 0 based version of the syndrome
    assign w_syndrome_0_based = (w_syndrome - 1);

    ////////////////////////////////////////////////////////////////////////////
    // Check overall parity
    always_comb begin : check_overall_parity
        w_overall_parity_in =  hamming_data[TotalWidth-1];
        if (enable) begin
            w_overall_parity = ^hamming_data[TotalWidth-2:0];
        end else begin
            w_overall_parity = 'b0;
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Correct the data if there is a single-bit error
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
                   r_data_with_parity      <= 'b0;
                   error_detected        <= 'b0;
                   double_error_detected <= 'b0;
               end else if (enable) begin
                   r_data_with_parity      <= hamming_data;
                   error_detected        <= 'b0;
                   double_error_detected <= 'b0;
                   if (DEBUG != 0)
                       $display(
                           "w_overall_parity, w_overall_parity_in, w_syndrome %b %b %b",
                           w_overall_parity,
                           w_overall_parity_in,
                           w_syndrome
                       );

                   // FIXED: Proper SECDED error detection logic
                   if (w_overall_parity != w_overall_parity_in) begin
                       // There is definitely an error (parity mismatch)
                       error_detected <= 1'b1;

                       if (w_syndrome != {ParityBits{1'b0}}) begin
                           // Non-zero syndrome: single-bit error in Hamming data
                           // Correct the error using the syndrome
                           r_data_with_parity[w_syndrome_0_based] <= ~hamming_data[w_syndrome_0_based];
                           if (DEBUG != 0)
                               $display(
                                   "Single-bit error detected and corrected at position: %d",
                                   w_syndrome_0_based
                               );
                       end else begin
                           // Zero syndrome with parity mismatch: single-bit error in SECDED bit
                           // No correction needed for SECDED bit errors (they don't affect data)
                           if (DEBUG != 0)
                               $display("Single-bit error detected in SECDED bit (position %d)", TotalWidth-1);
                       end
                   end else if (w_syndrome != {ParityBits{1'b0}}) begin
                       // Parity matches but syndrome is non-zero: double-bit error
                       error_detected <= 1'b1;
                       double_error_detected <= 1'b1;
                       if (DEBUG != 0) $display("Double-bit error detected.");
                   end else begin
                       // No error detected
                       if (DEBUG != 0) $display("No error detected.");
                   end
               end
    )


    ////////////////////////////////////////////////////////////////////////////
    // Extract the corrected data
    genvar j;
    generate
        for (j = 0; j < WIDTH; j++) begin : gen_block
            assign data[j] = r_data_with_parity[bit_position(j)];
        end
    endgenerate

endmodule : dataint_ecc_hamming_decode_secded
