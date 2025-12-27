// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_comparator
// Purpose: BF16 magnitude comparator for max/min finding operations
//
// Documentation: BF16_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-12-25
//

`timescale 1ns / 1ps

//==============================================================================
// Module: math_bf16_comparator
//==============================================================================
// Description:
//   Compares two BF16 floating-point values by magnitude (absolute value).
//   Returns the larger magnitude value and comparison flags. This is useful
//   for finding maximum absolute values in quantization operations.
//
// Features:
//   - Magnitude comparison (ignores sign)
//   - Proper handling of special values (zero, infinity, NaN)
//   - Single-cycle combinational operation
//   - NaN propagation (NaN is considered larger than any finite value)
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     i_a[15:0]:     First BF16 operand
//     i_b[15:0]:     Second BF16 operand
//
//   Outputs:
//     ow_max[15:0]:  Value with larger magnitude (preserves original sign)
//     ow_a_greater:  1 if |a| > |b|
//     ow_equal:      1 if |a| == |b|
//
//------------------------------------------------------------------------------
// BF16 Format:
//------------------------------------------------------------------------------
//   [15]    = Sign bit (0=positive, 1=negative)
//   [14:7]  = Exponent (8 bits, bias=127)
//   [6:0]   = Mantissa (7 bits, implicit leading 1 for normalized)
//
//   Special values:
//   - Zero:     exp=0x00, mant=0x00
//   - Subnorm:  exp=0x00, mant!=0x00 (treated as zero in BF16)
//   - Infinity: exp=0xFF, mant=0x00
//   - NaN:      exp=0xFF, mant!=0x00
//
//------------------------------------------------------------------------------
// Comparison Rules:
//------------------------------------------------------------------------------
//   1. NaN > everything (if either is NaN, return NaN)
//   2. Infinity > any finite value
//   3. For finite values: compare exponent first, then mantissa
//   4. Zero == -Zero (both have magnitude 0)
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Find max absolute value for quantization scaling
//   math_bf16_comparator u_cmp (
//       .i_a(value_a),
//       .i_b(value_b),
//       .ow_max(max_value),
//       .ow_a_greater(a_wins),
//       .ow_equal(tie)
//   );
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_math_bf16_comparator.py
//   Run: pytest val/common/test_math_bf16_comparator.py -v
//
//==============================================================================
module math_bf16_comparator (
    input  logic [15:0] i_a,
    input  logic [15:0] i_b,
    output logic [15:0] ow_max,
    output logic        ow_a_greater,
    output logic        ow_equal
);

// BF16 field extraction
wire       w_sign_a = i_a[15];
wire [7:0] w_exp_a  = i_a[14:7];
wire [6:0] w_mant_a = i_a[6:0];

wire       w_sign_b = i_b[15];
wire [7:0] w_exp_b  = i_b[14:7];
wire [6:0] w_mant_b = i_b[6:0];

// Magnitude (absolute value) - clear sign bit
wire [14:0] w_mag_a = i_a[14:0];
wire [14:0] w_mag_b = i_b[14:0];

// Special value detection
// Zero: exp=0, mant=0 (including subnormals treated as zero)
wire w_a_is_zero = (w_exp_a == 8'h00);
wire w_b_is_zero = (w_exp_b == 8'h00);

// Infinity: exp=FF, mant=0
wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 7'h00);
wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 7'h00);

// NaN: exp=FF, mant!=0
wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 7'h00);
wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 7'h00);

// Magnitude comparison using the 15-bit unsigned magnitude
// Since exponent is in higher bits, this naturally gives correct ordering
wire w_mag_a_greater = (w_mag_a > w_mag_b);
wire w_mag_b_greater = (w_mag_b > w_mag_a);
wire w_mag_equal     = (w_mag_a == w_mag_b);

// Handle special cases for comparison
// NaN handling: NaN is considered larger than any other value
// If both NaN: a wins (arbitrary but consistent)
// If one NaN: NaN wins

wire w_any_nan = w_a_is_nan | w_b_is_nan;

// Result computation
always_comb begin
    // Default: use magnitude comparison
    ow_a_greater = w_mag_a_greater;
    ow_equal     = w_mag_equal;
    ow_max       = w_mag_a_greater ? i_a : i_b;

    // Special case: NaN handling
    // NaN is considered "larger" for max-finding purposes
    if (w_a_is_nan) begin
        // a is NaN - a wins
        ow_max       = i_a;
        ow_a_greater = 1'b1;
        ow_equal     = 1'b0;
    end else if (w_b_is_nan) begin
        // b is NaN - b wins
        ow_max       = i_b;
        ow_a_greater = 1'b0;
        ow_equal     = 1'b0;
    end else if (w_mag_equal) begin
        // Equal magnitudes - prefer a (consistent tie-breaking)
        ow_max       = i_a;
        ow_a_greater = 1'b0;
        ow_equal     = 1'b1;
    end
end

endmodule : math_bf16_comparator
