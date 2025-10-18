// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gray2bin
// Purpose: //   Gray code to binary converter. Converts reflected binary code (Gray code)
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: gray2bin
//==============================================================================
// Description:
//   Gray code to binary converter. Converts reflected binary code (Gray code)
//   back to standard binary encoding. This is the inverse operation of bin2gray
//   and is essential for completing clock domain crossing (CDC) flows. The MSB
//   remains unchanged, and each lower bit is derived by XORing all Gray code
//   bits from MSB down to that position. Fully combinational (zero latency).
//
// Features:
//   - Parameterized width (1 to 64+ bits typical)
//   - Fully combinational (no clock required)
//   - Zero latency conversion
//   - Exact inverse of bin2gray module
//   - Essential for CDC receive path
//   - Minimal area (XOR tree per bit)
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: Bit width of Gray code and binary values
//     Type: int
//     Range: 1 to 64
//     Default: 4
//     Constraints: Same width for input and output
//                  Must match WIDTH used in bin2gray encoder
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     gray[WIDTH-1:0]:      Gray code input value
//
//   Outputs:
//     binary[WIDTH-1:0]:    Binary output value
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        0 cycles (combinational)
//   Propagation:    XOR tree delay (depth = log2(WIDTH))
//   Critical Path:  XOR cascade from MSB to LSB
//   Clock:          None (combinational)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Gray to Binary Conversion Algorithm:
//   - MSB: binary[WIDTH-1] = gray[WIDTH-1] (MSB unchanged)
//   - Other bits: binary[i] = gray[WIDTH-1] XOR gray[WIDTH-2] XOR ... XOR gray[i]
//   - Result: Exact reconstruction of original binary value
//
//   Conversion Formula:
//   binary[n-1] = gray[n-1]
//   binary[i]   = gray[n-1] ^ gray[n-2] ^ ... ^ gray[i]  for i = 0 to n-2
//
//   This can be expressed as:
//   binary[i] = XOR_reduction(gray >> i)
//
//   Example Conversion (WIDTH=4):
//   Gray    → Binary
//   0000    → 0000   (MSB=0, all XORs=0)
//   0001    → 0001   (MSB=0, bit[0]=1)
//   0011    → 0010   (MSB=0, bit[1]=1)
//   0010    → 0011   (MSB=0, bit[1]=1, bit[0]=1)
//   0110    → 0100   (MSB=0, bit[2]=1)
//   0111    → 0101   (MSB=0, bit[2]=1, bit[0]=1)
//   0101    → 0110   (MSB=0, bit[2]=1, bit[1]=1)
//   0100    → 0111   (MSB=0, bit[2]=1, bit[1]=1, bit[0]=1)
//   1100    → 1000   (MSB=1)
//   ...
//
//   Bit-by-Bit Calculation Example (Gray = 0101 → Binary = ?):
//   binary[3] = gray[3]                               = 0
//   binary[2] = gray[3] ^ gray[2]                     = 0 ^ 1 = 1
//   binary[1] = gray[3] ^ gray[2] ^ gray[1]           = 0 ^ 1 ^ 0 = 1
//   binary[0] = gray[3] ^ gray[2] ^ gray[1] ^ gray[0] = 0 ^ 1 ^ 0 ^ 1 = 0
//   Result: Binary = 0110
//
//   Reversibility Property:
//   bin2gray(binary) → gray
//   gray2bin(gray) → binary
//   Therefore: gray2bin(bin2gray(X)) = X  (identity function)
//
//   Why This Algorithm Works:
//   - Gray code is cumulative XOR of binary bits
//   - XORing again cancels out intermediate bits
//   - Each binary bit is recovered by XORing all Gray bits above and including it
//   - Self-inverse property of XOR: A ^ B ^ B = A
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Complete CDC flow for 8-bit counter
//   // SOURCE DOMAIN: Convert binary to Gray
//   logic [7:0] src_binary_count;
//   logic [7:0] src_gray_count;
//
//   bin2gray #(
//       .WIDTH(8)
//   ) u_bin2gray (
//       .binary(src_binary_count),
//       .gray  (src_gray_count)
//   );
//
//   // Synchronize Gray code across clock domain
//   logic [7:0] dst_gray_sync;
//   glitch_free_n_dff_arn #(
//       .WIDTH(8),
//       .FLOP_COUNT(2)
//   ) u_gray_sync (
//       .clk  (dst_clk),
//       .rst_n(dst_rst_n),
//       .d    (src_gray_count),   // From source domain
//       .q    (dst_gray_sync)     // Synchronized Gray code
//   );
//
//   // DESTINATION DOMAIN: Convert Gray back to binary
//   logic [7:0] dst_binary_count;
//   gray2bin #(
//       .WIDTH(8)
//   ) u_gray2bin (
//       .gray  (dst_gray_sync),
//       .binary(dst_binary_count)  // Final binary value
//   );
//
//   // Async FIFO pointer synchronization example
//   // Write pointer (src domain)
//   logic [ADDR_WIDTH-1:0] wr_ptr_bin, wr_ptr_gray, wr_ptr_gray_sync, wr_ptr_bin_sync;
//
//   // Encode write pointer to Gray
//   bin2gray #(.WIDTH(ADDR_WIDTH)) u_wr_enc (
//       .binary(wr_ptr_bin),
//       .gray  (wr_ptr_gray)
//   );
//
//   // Synchronize to read domain
//   glitch_free_n_dff_arn #(.WIDTH(ADDR_WIDTH), .FLOP_COUNT(2)) u_wr_sync (
//       .clk  (rd_clk),
//       .rst_n(rd_rst_n),
//       .d    (wr_ptr_gray),
//       .q    (wr_ptr_gray_sync)
//   );
//
//   // Decode Gray to binary in read domain
//   gray2bin #(.WIDTH(ADDR_WIDTH)) u_wr_dec (
//       .gray  (wr_ptr_gray_sync),
//       .binary(wr_ptr_bin_sync)   // For empty/full calculation
//   );
//
//   // Bidirectional CDC (send and receive)
//   logic [15:0] local_value, remote_value;
//   logic [15:0] local_gray, remote_gray;
//
//   // Local → Remote (bin2gray on transmit)
//   bin2gray #(.WIDTH(16)) u_tx_gray (
//       .binary(local_value),
//       .gray  (local_gray)       // Crosses domain safely
//   );
//
//   // Remote → Local (gray2bin on receive after sync)
//   gray2bin #(.WIDTH(16)) u_rx_bin (
//       .gray  (remote_gray),     // After synchronization
//       .binary(remote_value)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Combinational only** - No clock, no registers
//   - Output valid same cycle as input (zero latency)
//   - **Must match WIDTH** used in bin2gray encoder
//   - Algorithm: Each bit is XOR reduction of gray[WIDTH-1:i]
//   - **Synthesis:** Maps to XOR tree (log depth) per bit
//   - Area: WIDTH * (WIDTH/2 average) XOR gates (more than bin2gray)
//   - Critical path: Longest XOR chain is for LSB (WIDTH XORs)
//   - **Always pair with bin2gray** for CDC flows
//   - Use after synchronizing Gray code to destination domain
//   - Binary output can be used for arithmetic, comparisons, indexing
//   - **Exact inverse:** gray2bin(bin2gray(X)) = X for all X
//   - Gray code sequence order preserved in binary output
//   - Used in: Async FIFO read path, CDC receivers, Gray counter decoding
//   - **Implementation:** Uses reduction XOR on shifted Gray code
//   - Hardware efficient: Single assign per bit using ^(gray >> i)
//   - Propagation delay scales with WIDTH (XOR tree depth)
//   - For timing-critical paths, consider pipelining if WIDTH > 32
//   - No glitches if input is stable (combinational logic)
//   - Recommended: Register input if coming from async source
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - bin2gray.sv - Gray code encoder (inverse operation)
//   - glitch_free_n_dff_arn.sv - Multi-stage synchronizer for Gray codes
//   - fifo_async.sv - Uses bin2gray → sync → gray2bin for pointers
//   - counter_bingray.sv - Binary counter with Gray code output
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_gray2bin.py
//   Run: pytest val/common/test_gray2bin.py -v
//   Coverage: 100%
//   Key Test Scenarios:
//     - All input values (exhaustive for small widths)
//     - Reversibility test (bin2gray → gray2bin = identity)
//     - Paired test with bin2gray module
//     - Various widths (4, 8, 16, 32)
//     - Edge cases (0x00, 0xFF, all patterns)
//     - Comparison with reference algorithm
//
//==============================================================================
module gray2bin #(
    parameter int WIDTH = 4
) (
    input  wire [WIDTH-1:0] gray,
    output wire [WIDTH-1:0] binary
);

    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_gray_to_bin
            assign binary[i] = ^(gray >> i);
        end
    endgenerate

endmodule : gray2bin
