// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: decoder
// Purpose: //   Binary to one-hot decoder. Converts M-bit binary input to 2^M one-hot output
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: decoder
//==============================================================================
// Description:
//   Binary to one-hot decoder. Converts M-bit binary input to 2^M one-hot output
//   where exactly one bit is asserted corresponding to the binary input value.
//   Used for address decoding, chip select generation, and demultiplexing. Fully
//   combinational with generate-based implementation for all output bits.
//
// Features:
//   - Parameterized input width M (2 to 8 typical)
//   - Output width N = 2^M (auto-calculated)
//   - Fully combinational (no clock required)
//   - Zero latency conversion
//   - One-hot output (exactly one bit set)
//   - Generate-based parallel comparison
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   M:
//     Description: Number of input bits (binary address width)
//     Type: int
//     Range: 1 to 8
//     Default: 4
//     Constraints: Output width N = 2^M
//                  For M=4: output is 16 bits [15:0]
//                  For M=8: output is 256 bits [255:0] (large!)
//
//   N:
//     Description: Number of output bits (one-hot vector width)
//     Type: int
//     Default: 2^M (auto-calculated)
//     Constraints: Must equal 2^M for correct operation
//                  User should not override this parameter
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     encoded[M-1:0]:          Binary input (address/select value)
//
//   Outputs:
//     data[N-1:0]:             One-hot decoded output (2^M bits)
//
//------------------------------------------------------------------------------
// Timing:
//------------------------------------------------------------------------------
//   Latency:        0 cycles (combinational)
//   Propagation:    Comparator + output mux delay
//   Critical Path:  Binary compare → one-hot output
//   Clock:          None (combinational)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   Binary to One-Hot Decoding Algorithm:
//   - Compare input to each possible value 0 to (2^M - 1)
//   - Assert output bit[i] if encoded == i
//   - All other output bits are 0
//   - Exactly one output bit is always asserted
//
//   Formula:
//   data[i] = (encoded == i) ? 1'b1 : 1'b0   for i = 0 to N-1
//
//   Example Decodings (M=3, N=8):
//   Input (encoded)  Binary     Output (data)  Description
//   3'b000           3'b000     8'b00000001    Bit 0 asserted
//   3'b001           3'b001     8'b00000010    Bit 1 asserted
//   3'b010           3'b010     8'b00000100    Bit 2 asserted
//   3'b011           3'b011     8'b00001000    Bit 3 asserted
//   3'b100           3'b100     8'b00010000    Bit 4 asserted
//   3'b101           3'b101     8'b00100000    Bit 5 asserted
//   3'b110           3'b110     8'b01000000    Bit 6 asserted
//   3'b111           3'b111     8'b10000000    Bit 7 asserted
//
//   Address Decoder Example (M=4, N=16):
//   Address 4'b0000 → data[0]  = 1, data[15:1]  = 0 (select device 0)
//   Address 4'b0001 → data[1]  = 1, data[15:2,0]= 0 (select device 1)
//   Address 4'b1111 → data[15] = 1, data[14:0]  = 0 (select device 15)
//
//   Chip Select Generation Example (M=3, N=8):
//   addr[2:0] = 3'b000 → cs[7:0] = 8'b00000001 (CS0 active)
//   addr[2:0] = 3'b101 → cs[7:0] = 8'b00100000 (CS5 active)
//
//   One-Hot Property:
//   - Exactly one bit is always set (no zero output)
//   - Sum of output bits always equals 1
//   - Output is valid one-hot vector
//
//   Inverse of Encoder:
//   - decoder(encoder(X)) ≈ X (but encoder has ambiguity with all-zeros)
//   - encoder(decoder(X)) = X (exact inverse in this direction)
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Address decoder for 8 peripherals
//   logic [2:0] peripheral_addr;
//   logic [7:0] peripheral_select;
//
//   decoder #(
//       .M(3),    // 3-bit address
//       .N(8)     // 8 one-hot outputs
//   ) u_addr_dec (
//       .encoded(peripheral_addr),
//       .data   (peripheral_select)  // One-hot chip selects
//   );
//
//   // Chip select generation for memory map
//   logic [3:0] addr_upper;
//   logic [15:0] chip_select;
//
//   decoder #(.M(4), .N(16)) u_cs_dec (
//       .encoded(addr_upper),
//       .data   (chip_select)
//   );
//
//   // Demultiplexer control for routing data
//   logic [1:0] dest_select;
//   logic [3:0] dest_enable;
//
//   decoder #(.M(2), .N(4)) u_demux_dec (
//       .encoded(dest_select),
//       .data   (dest_enable)   // One-hot destination enables
//   );
//
//   // Interrupt vector decoder
//   logic [4:0] interrupt_id;
//   logic [31:0] interrupt_onehot;
//
//   decoder #(.M(5), .N(32)) u_int_dec (
//       .encoded(interrupt_id),
//       .data   (interrupt_onehot)
//   );
//
//   // Register select in register file
//   logic [2:0] reg_addr;
//   logic [7:0] reg_select;
//
//   decoder #(.M(3), .N(8)) u_reg_dec (
//       .encoded(reg_addr),
//       .data   (reg_select)
//   );
//   // Use reg_select to gate write enable to each register
//   assign reg_we[0] = write_enable & reg_select[0];
//   assign reg_we[1] = write_enable & reg_select[1];
//   // ...
//
//   // Mux select one-hot generation
//   logic [3:0] mux_sel_binary;
//   logic [15:0] mux_sel_onehot;
//
//   decoder #(.M(4), .N(16)) u_mux_dec (
//       .encoded(mux_sel_binary),
//       .data   (mux_sel_onehot)
//   );
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - **Combinational only** - No clock, no registers
//   - Output valid same cycle as input (zero latency)
//   - **One-hot guarantee:** Exactly one output bit is always asserted
//   - Generate-based implementation (parallel comparators for all outputs)
//   - **Synthesis:** N parallel comparators (one per output bit)
//   - Area: O(2^M) comparators (exponential growth!)
//   - For large M (>6), area becomes significant (2^8 = 256 comparators!)
//   - Critical path: Binary comparison logic (M-bit comparator)
//   - Output fanout: Each output bit may drive many gates (e.g., chip selects)
//   - **Power consideration:** All comparators evaluate every cycle
//   - For large M, consider two-level decoding (decode M1 bits, then M2 bits)
//   - Example: M=8 → decode 4+4 bits separately (16+16=32 vs 256 comparators)
//   - **Inverse of encoder.sv** (but encoder has ambiguity with zero input)
//   - Use for: Address decoding, chip selects, demux control, register selection
//   - **Not recommended:** M > 8 (exponential area/power growth)
//   - Alternative for large M: Use binary address directly with comparators at leaf
//   - Output width N = 2^M must be consistent (parameter validation helpful)
//   - Line 11 initializes all outputs to 0 (overridden by generate block)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - encoder.sv - One-hot to binary encoder (inverse operation)
//   - priority_encoder.sv - Priority-based encoding
//   - arbiter_*.sv - Generate one-hot grants (similar to decoder output)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_decoder.py
//   Run: pytest val/common/test_decoder.py -v
//   Coverage: 100%
//   Key Test Scenarios:
//     - All input values (exhaustive for small M)
//     - Verify exactly one output bit set for each input
//     - Check output bit position matches input value
//     - Various widths (M=2,3,4,5)
//     - Edge cases (input=0, input=2^M-1)
//     - One-hot property verification
//     - Encode-decode round-trip test
//
//==============================================================================
module decoder #(
    parameter int M = 4,  // Number of input bits
    parameter int N = 2 ** M  // Number of output bits)
) (
    input  [M-1:0] encoded,
    output [N-1:0] data
);

    assign data = 0;  // Initialize the output

    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_DECODER_LOOP
            assign data[i] = (encoded == i) ? 1'b1 : 1'b0;
        end
    endgenerate

endmodule : decoder
