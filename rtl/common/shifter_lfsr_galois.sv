// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: shifter_lfsr_galois
// Purpose: //   Galois-configuration Linear Feedback Shift Register (LFSR) with configurable
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: shifter_lfsr_galois
//==============================================================================
// Description:
//   Galois-configuration Linear Feedback Shift Register (LFSR) with configurable
//   tap positions. Uses right-shift architecture with XOR feedback applied at
//   internal tap positions. Suitable for pseudo-random number generation, CRC
//   computation, and pattern generation.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   WIDTH:
//     Description: LFSR register width in bits
//     Type: int
//     Range: 2 to 128
//     Default: 8
//     Constraints: Determines sequence length (2^WIDTH - 1 states for maximal taps)
//
//   TAP_INDEX_WIDTH:
//     Description: Bit width for tap position indices
//     Type: int
//     Range: $clog2(WIDTH) to 16
//     Default: 12
//     Constraints: Must be wide enough to represent WIDTH (TAP_INDEX_WIDTH >= $clog2(WIDTH))
//
//   TAP_COUNT:
//     Description: Number of feedback tap positions
//     Type: int
//     Range: 1 to 8
//     Default: 4
//     Constraints: Determines feedback complexity. Use maximal-length tap sets for full period.
//
//   Derived Parameters (localparam):
//     TIW: Alias for TAP_INDEX_WIDTH (used for array sizing)
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Galois LFSRs apply feedback at multiple internal positions
//   - Right-shift operation: MSB=0, tap XORs applied if LSB=1
//   - Maximal-length tap sets produce sequences of period (2^WIDTH - 1)
//   - lfsr_done pulses when LFSR returns to seed value
//   - Tap positions are 1-indexed (tap 1 = bit 0, tap WIDTH = bit WIDTH-1)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - shifter_lfsr_fibonacci.sv - Fibonacci LFSR (external feedback)
//   - shifter_lfsr.sv - Generic LFSR wrapper
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_shifter_lfsr_galois.py
//   Run: pytest val/common/test_shifter_lfsr_galois.py -v
//
//==============================================================================


// Maximal-Length Tap Sets (Galois: XOR mask applied when the shifted-out LSB is 1)
// +----------------------------------------------------------------------------+
//   This module applies the tap mask to the post-shift value whenever the
//   outgoing LSB is 1, so the tap numbers ARE the polynomial exponents: for
//   x^n + x^a + x^b + 1 the taps are [n, a, b]. That makes this table identical
//   to the standard published set (and to the table in shifter_lfsr.sv).
//
//   Do NOT reuse these numbers for shifter_lfsr_fibonacci.sv -- that module
//   encodes the same polynomials differently and has its own table.
//   Verified by simulation for n = 3..16: each row below yields period 2^n - 1.
// +----------------------------------------------------------------------------+
// +-----+--------------+-----+-------------+-----+-----------------+-----+-----------------+
// |   n |   XOR taps   |   n |  XOR taps   |   n |    XOR taps     |   n |    XOR taps     |
// +-----+--------------+-----+-------------+-----+-----------------+-----+-----------------+
// |   3 |          3,2 |  45 | 45,44,42,41 |  87 |           87,74 | 129 |         129,124 |
// |   4 |          4,3 |  46 | 46,45,26,25 |  88 |     88,87,17,16 | 130 |         130,127 |
// |   5 |          5,3 |  47 |       47,42 |  89 |           89,51 | 131 |   131,130,84,83 |
// |   6 |          6,5 |  48 | 48,47,21,20 |  90 |     90,89,72,71 | 132 |         132,103 |
// |   7 |          7,6 |  49 |       49,40 |  91 |       91,90,8,7 | 133 |   133,132,82,81 |
// |   8 |      8,6,5,4 |  50 | 50,49,24,23 |  92 |     92,91,80,79 | 134 |          134,77 |
// |   9 |          9,5 |  51 | 51,50,36,35 |  93 |           93,91 | 135 |         135,124 |
// |  10 |         10,7 |  52 |       52,49 |  94 |           94,73 | 136 |   136,135,11,10 |
// |  11 |         11,9 |  53 | 53,52,38,37 |  95 |           95,84 | 137 |         137,116 |
// |  12 |     12,6,4,1 |  54 | 54,53,18,17 |  96 |     96,94,49,47 | 138 | 138,137,131,130 |
// |  13 |     13,4,3,1 |  55 |       55,31 |  97 |           97,91 | 139 | 139,136,134,131 |
// |  14 |     14,5,3,1 |  56 | 56,55,35,34 |  98 |           98,87 | 140 |         140,111 |
// |  15 |        15,14 |  57 |       57,50 |  99 |     99,97,54,52 | 141 | 141,140,110,109 |
// |  16 |   16,15,13,4 |  58 |       58,39 | 100 |          100,63 | 142 |         142,121 |
// |  17 |        17,14 |  59 | 59,58,38,37 | 101 |   101,100,95,94 | 143 | 143,142,123,122 |
// |  18 |        18,11 |  60 |       60,59 | 102 |   102,101,36,35 | 144 |   144,143,75,74 |
// |  19 |     19,6,2,1 |  61 | 61,60,46,45 | 103 |          103,94 | 145 |          145,93 |
// |  20 |        20,17 |  62 |   62,61,6,5 | 104 |   104,103,94,93 | 146 |   146,145,87,86 |
// |  21 |        21,19 |  63 |       63,62 | 105 |          105,89 | 147 | 147,146,110,109 |
// |  22 |        22,21 |  64 | 64,63,61,60 | 106 |          106,91 | 148 |         148,121 |
// |  23 |        23,18 |  65 |       65,47 | 107 |   107,105,44,42 | 149 |   149,148,40,39 |
// |  24 |  24,23,22,17 |  66 | 66,65,57,56 | 108 |          108,77 | 150 |          150,97 |
// |  25 |        25,22 |  67 | 67,66,58,57 | 109 | 109,108,103,102 | 151 |         151,148 |
// |  26 |     26,6,2,1 |  68 |       68,59 | 110 |   110,109,98,97 | 152 |   152,151,87,86 |
// |  27 |     27,5,2,1 |  69 | 69,67,42,40 | 111 |         111,101 | 153 |         153,152 |
// |  28 |        28,25 |  70 | 70,69,55,54 | 112 |   112,110,69,67 | 154 |   154,152,27,25 |
// |  29 |        29,27 |  71 |       71,65 | 113 |         113,104 | 155 | 155,154,124,123 |
// |  30 |     30,6,4,1 |  72 | 72,66,25,19 | 114 |   114,113,33,32 | 156 |   156,155,41,40 |
// |  31 |        31,28 |  73 |       73,48 | 115 | 115,114,101,100 | 157 | 157,156,131,130 |
// |  32 |    32,22,2,1 |  74 | 74,73,59,58 | 116 |   116,115,46,45 | 158 | 158,157,132,131 |
// |  33 |        33,20 |  75 | 75,74,65,64 | 117 |   117,115,99,97 | 159 |         159,128 |
// |  34 |    34,27,2,1 |  76 | 76,75,41,40 | 118 |          118,85 | 160 | 160,159,142,141 |
// |  35 |        35,33 |  77 | 77,76,47,46 | 119 |         119,111 | 161 |         161,143 |
// |  36 |        36,25 |  78 | 78,77,59,58 | 120 |     120,113,9,2 | 162 |   162,161,75,74 |
// |  37 | 37,5,4,3,2,1 |  79 |       79,70 | 121 |         121,103 | 163 | 163,162,104,103 |
// |  38 |     38,6,5,1 |  80 | 80,79,43,42 | 122 |   122,121,63,62 | 164 | 164,163,151,150 |
// |  39 |        39,35 |  81 |       81,77 | 123 |         123,121 | 165 | 165,164,135,134 |
// |  40 |  40,38,21,19 |  82 | 82,79,47,44 | 124 |          124,87 | 166 | 166,165,128,127 |
// |  41 |        41,38 |  83 | 83,82,38,37 | 125 |   125,124,18,17 | 167 |         167,161 |
// |  42 |  42,41,20,19 |  84 |       84,71 | 126 |   126,125,90,89 | 168 | 168,166,153,151 |
// |  43 |  43,42,38,37 |  85 | 85,84,58,57 | 127 |         127,126 |     |                 |
// |  44 |  44,43,18,17 |  86 | 86,85,74,73 | 128 |  128,126,101,99 |     |                 |
// +-----+--------------+-----+-------------+-----+-----------------+-----+-----------------+

`include "reset_defs.svh"
module shifter_lfsr_galois #(
    parameter int WIDTH = 8,           // Width of the LFSR
    parameter int TAP_INDEX_WIDTH = 12,
    parameter int TAP_COUNT = 4,        // Number of taps
    parameter int TIW = TAP_INDEX_WIDTH
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic                     enable,     // enable the lfsr
    input  logic                     seed_load,  // enable the seed for the lfsr
    input  logic [     WIDTH-1:0]    seed_data,  // seed value
    input  logic [TAP_COUNT*TIW-1:0] taps,       // Concatenated tap positions
    output logic [     WIDTH-1:0]    lfsr_out,   // LFSR output
    output logic                     lfsr_done  // the lfsr has wrapped around to the seed
);

    logic [WIDTH-1:0]  r_lfsr;
    logic [TIW-1:0]    w_tap_positions [TAP_COUNT];  // verilog_lint: waive unpacked-dimensions-range-ordering
    logic              w_feedback;
    logic [WIDTH-1:0]  w_next_lfsr;

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    always_comb begin
        for (int i = 0; i < TAP_COUNT; i++) begin
            w_tap_positions[i] = taps[i*TIW+:TIW];
        end
    end

    // Observe when the lfsr has looped back
    assign lfsr_done = (lfsr_out == seed_data) ? 1'b1 : 1'b0;

    // Get the LSB for feedback
    assign w_feedback = r_lfsr[0];

    // Calculate next LFSR state with proper Galois feedback
    always_comb begin
        // Start with right shift (include 0 in MSB)
        w_next_lfsr = {1'b0, r_lfsr[WIDTH-1:1]};

        // Apply Galois feedback taps if LSB is 1
        if (w_feedback) begin
            for (int j = 0; j < TAP_COUNT; j++) begin
                /* verilator lint_off WIDTHEXPAND */
                if (w_tap_positions[j] > 0 && w_tap_positions[j] <= WIDTH) begin
                    // Apply XOR to the tap positions
                    w_next_lfsr[w_tap_positions[j]-1] = w_next_lfsr[w_tap_positions[j]-1] ^ 1'b1;
                /* verilator lint_on WIDTHEXPAND */
                end
            end
        end
    end

    // Update LFSR state
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            // Reset LFSR to a non-zero value
            r_lfsr <= {WIDTH{1'b1}};  // initialization to all 1's
        end else if (enable) begin
            if (seed_load) begin
                r_lfsr <= seed_data;
            end else begin
                // Update with the next state calculated in combinational logic
                r_lfsr <= w_next_lfsr;
            end
        end
    )


    assign lfsr_out = r_lfsr[WIDTH-1:0];

endmodule : shifter_lfsr_galois
