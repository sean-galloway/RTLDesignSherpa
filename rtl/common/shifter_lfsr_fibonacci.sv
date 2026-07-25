// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: shifter_lfsr_fibonacci
// Purpose: //   Fibonacci-configuration Linear Feedback Shift Register (LFSR) with configurable
//
// Documentation: docs/markdown/RTLCommon/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

//==============================================================================
// Module: shifter_lfsr_fibonacci
//==============================================================================
// Description:
//   Fibonacci-configuration Linear Feedback Shift Register (LFSR) with configurable
//   tap positions. Uses right-shift architecture with XOR feedback applied at the
//   MSB. Suitable for pseudo-random number generation, scrambling, and pattern
//   generation.
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
//   - Fibonacci LFSRs apply feedback at the MSB only (external feedback)
//   - Right-shift operation: MSB=feedback, all bits shift right
//   - Maximal-length tap sets produce sequences of period (2^WIDTH - 1)
//   - lfsr_done pulses when LFSR returns to seed value
//   - Tap positions are 1-indexed (tap 1 = bit 0, tap WIDTH = bit WIDTH-1)
//   - Different feedback than Galois LFSR (see shifter_lfsr_galois.sv)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - shifter_lfsr_galois.sv - Galois LFSR (internal feedback)
//   - shifter_lfsr.sv - Generic LFSR wrapper
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_shifter_lfsr_fibonacci.py
//   Run: pytest val/common/test_shifter_lfsr_fibonacci.py -v
//
//==============================================================================


// Maximal-Length Tap Sets (XOR feedback, right-shift, feedback into MSB)
// +----------------------------------------------------------------------------+
//   THESE TAP NUMBERS ARE SPECIFIC TO THIS MODULE'S SHIFT DIRECTION.
//   Do NOT copy the table from shifter_lfsr.sv (XNOR, left-shift) or use the
//   tap column published for Galois LFSRs -- the same polynomial needs different
//   tap positions here, and a wrong set does not merely shorten the sequence:
//   it drives the register to 0, where the `|r_lfsr` guard freezes it forever.
//   Measured: WIDTH=4 taps [4,3] locks at zero in ONE step; taps [4,1] runs 15.
//
//   The polynomials are the standard primitive set (same source as the table in
//   shifter_lfsr.sv). Only the tap ENCODING differs. This module's feedback is
//   fb = ^(lfsr & taps) shifted into the MSB, which makes the characteristic
//   polynomial x^WIDTH + SUM over taps of x^(tap-1). So for the published
//   polynomial x^n + x^a + x^b + 1, the taps here are [a+1, b+1, 1] -- note
//   that tap 1 is ALWAYS present (it supplies the constant term) and n itself
//   is NOT a tap (the width supplies the leading term).
//
//   To convert any row of the 168-entry table in shifter_lfsr.sv: drop the
//   leading n, add 1 to every remaining number, then append 1.
// +----------------------------------------------------------------------------+
// +-----+-------------+-----+------------+-----+---------------+-----+---------------+
// |   n |  XOR taps   |   n |  XOR taps  |   n |   XOR taps    |   n |   XOR taps    |
// +-----+-------------+-----+------------+-----+---------------+-----+---------------+
// |   3 |         3,1 |  45 | 45,43,42,1 |  87 |          75,1 | 129 |         125,1 |
// |   4 |         4,1 |  46 | 46,27,26,1 |  88 |    88,18,17,1 | 130 |         128,1 |
// |   5 |         4,1 |  47 |       43,1 |  89 |          52,1 | 131 |   131,85,84,1 |
// |   6 |         6,1 |  48 | 48,22,21,1 |  90 |    90,73,72,1 | 132 |         104,1 |
// |   7 |         7,1 |  49 |       41,1 |  91 |      91,9,8,1 | 133 |   133,83,82,1 |
// |   8 |     7,6,5,1 |  50 | 50,25,24,1 |  92 |    92,81,80,1 | 134 |          78,1 |
// |   9 |         6,1 |  51 | 51,37,36,1 |  93 |          92,1 | 135 |         125,1 |
// |  10 |         8,1 |  52 |       50,1 |  94 |          74,1 | 136 |   136,12,11,1 |
// |  11 |        10,1 |  53 | 53,39,38,1 |  95 |          85,1 | 137 |         117,1 |
// |  12 |     7,5,2,1 |  54 | 54,19,18,1 |  96 |    95,50,48,1 | 138 | 138,132,131,1 |
// |  13 |     5,4,2,1 |  55 |       32,1 |  97 |          92,1 | 139 | 137,135,132,1 |
// |  14 |     6,4,2,1 |  56 | 56,36,35,1 |  98 |          88,1 | 140 |         112,1 |
// |  15 |        15,1 |  57 |       51,1 |  99 |    98,55,53,1 | 141 | 141,111,110,1 |
// |  16 |   16,14,5,1 |  58 |       40,1 | 100 |          64,1 | 142 |         122,1 |
// |  17 |        15,1 |  59 | 59,39,38,1 | 101 |   101,96,95,1 | 143 | 143,124,123,1 |
// |  18 |        12,1 |  60 |       60,1 | 102 |   102,37,36,1 | 144 |   144,76,75,1 |
// |  19 |     7,3,2,1 |  61 | 61,47,46,1 | 103 |          95,1 | 145 |          94,1 |
// |  20 |        18,1 |  62 |   62,7,6,1 | 104 |   104,95,94,1 | 146 |   146,88,87,1 |
// |  21 |        20,1 |  63 |       63,1 | 105 |          90,1 | 147 | 147,111,110,1 |
// |  22 |        22,1 |  64 | 64,62,61,1 | 106 |          92,1 | 148 |         122,1 |
// |  23 |        19,1 |  65 |       48,1 | 107 |   106,45,43,1 | 149 |   149,41,40,1 |
// |  24 |  24,23,18,1 |  66 | 66,58,57,1 | 108 |          78,1 | 150 |          98,1 |
// |  25 |        23,1 |  67 | 67,59,58,1 | 109 | 109,104,103,1 | 151 |         149,1 |
// |  26 |     7,3,2,1 |  68 |       60,1 | 110 |   110,99,98,1 | 152 |   152,88,87,1 |
// |  27 |     6,3,2,1 |  69 | 68,43,41,1 | 111 |         102,1 | 153 |         153,1 |
// |  28 |        26,1 |  70 | 70,56,55,1 | 112 |   111,70,68,1 | 154 |   153,28,26,1 |
// |  29 |        28,1 |  71 |       66,1 | 113 |         105,1 | 155 | 155,125,124,1 |
// |  30 |     7,5,2,1 |  72 | 67,26,20,1 | 114 |   114,34,33,1 | 156 |   156,42,41,1 |
// |  31 |        29,1 |  73 |       49,1 | 115 | 115,102,101,1 | 157 | 157,132,131,1 |
// |  32 |    23,3,2,1 |  74 | 74,60,59,1 | 116 |   116,47,46,1 | 158 | 158,133,132,1 |
// |  33 |        21,1 |  75 | 75,66,65,1 | 117 |  116,100,98,1 | 159 |         129,1 |
// |  34 |    28,3,2,1 |  76 | 76,42,41,1 | 118 |          86,1 | 160 | 160,143,142,1 |
// |  35 |        34,1 |  77 | 77,48,47,1 | 119 |         112,1 | 161 |         144,1 |
// |  36 |        26,1 |  78 | 78,60,59,1 | 120 |    114,10,3,1 | 162 |   162,76,75,1 |
// |  37 | 6,5,4,3,2,1 |  79 |       71,1 | 121 |         104,1 | 163 | 163,105,104,1 |
// |  38 |     7,6,2,1 |  80 | 80,44,43,1 | 122 |   122,64,63,1 | 164 | 164,152,151,1 |
// |  39 |        36,1 |  81 |       78,1 | 123 |         122,1 | 165 | 165,136,135,1 |
// |  40 |  39,22,20,1 |  82 | 80,48,45,1 | 124 |          88,1 | 166 | 166,129,128,1 |
// |  41 |        39,1 |  83 | 83,39,38,1 | 125 |   125,19,18,1 | 167 |         162,1 |
// |  42 |  42,21,20,1 |  84 |       72,1 | 126 |   126,91,90,1 | 168 | 167,154,152,1 |
// |  43 |  43,39,38,1 |  85 | 85,59,58,1 | 127 |         127,1 |     |               |
// |  44 |  44,19,18,1 |  86 | 86,75,74,1 | 128 | 127,102,100,1 |     |               |
// +-----+-------------+-----+------------+-----+---------------+-----+---------------+

`include "reset_defs.svh"
module shifter_lfsr_fibonacci #(
    parameter int WIDTH           = 8,   // Width of the LFSR
    parameter int TAP_INDEX_WIDTH = 12,
    parameter int TAP_COUNT       = 4,   // Number of taps
    parameter int TIW = TAP_INDEX_WIDTH
) (
    input  logic                     clk,
    input  logic                     rst_n,
    input  logic                     enable,     // enable the lfsr
    input  logic                     seed_load,  // enable the seed for the lfsr
    input  logic [        WIDTH-1:0] seed_data,  // seed value
    input  logic [TAP_COUNT*TIW-1:0] taps,       // Concatenated tap positions
    output logic [        WIDTH-1:0] lfsr_out,   // LFSR output
    output logic                     lfsr_done  // the lfsr has wrapped around to the seed
);
    // Calculate feedback bit based on tap positions
    logic [WIDTH-1:0] w_taps;
    logic [WIDTH-1:0] r_lfsr;
    logic w_feedback;
    logic [TIW-1:0]   w_tap_positions [TAP_COUNT]; // verilog_lint: waive unpacked-dimensions-range-ordering

    ////////////////////////////////////////////////////////////////////////////
    // Split concatenated tap positions into separate groups for each tap
    always_comb begin
        for (int i = 0; i < TAP_COUNT; i++) w_tap_positions[i] = taps[i*TIW+:TIW];
    end

    always_comb begin
        w_taps = 'b0;
        for (int i = 0; i < TAP_COUNT; i++)
            /* verilator lint_off WIDTHTRUNC */
            if (w_tap_positions[i] > 0) w_taps[w_tap_positions[i]-1'b1] = 1'b1;
            /* verilator lint_on WIDTHTRUNC */
    end

    ////////////////////////////////////////////////////////////////////////////
    // Calculate feedback by XORing tapped bits
    assign w_feedback = ^(r_lfsr & w_taps);

    ////////////////////////////////////////////////////////////////////////////
    // observe when the lfsr has looped back
    assign lfsr_done = (lfsr_out == seed_data) ? 1'b1 : 1'b0;

    // Output value immediately
    assign lfsr_out = r_lfsr;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_lfsr <= 'b0;  // initialization to all 0's
        end else begin
            if (enable) begin
                if (seed_load) begin
                    r_lfsr <= seed_data;  // Load seed
                end else if (|r_lfsr) begin // Only shift if we have non-zero value
                    // Fibonacci LFSR: Shift right, feedback to MSB
                    r_lfsr <= {w_feedback, r_lfsr[WIDTH-1:1]};
                end
            end
        end
    )


endmodule : shifter_lfsr_fibonacci
