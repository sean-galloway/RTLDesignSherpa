// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_int_to_bf16
// Purpose: Convert signed integer to BF16 floating-point for de-quantization
//
// Documentation: BF16_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-12-25
//

`timescale 1ns / 1ps

//==============================================================================
// Module: math_int_to_bf16
//==============================================================================
// Description:
//   Converts a signed integer to BF16 floating-point representation. Used for
//   de-quantization operations in neural network inference where integer
//   accumulator results need to be converted back to floating-point.
//
// Features:
//   - Parameterized integer width (8, 16, 32 bits typical)
//   - Round-to-Nearest-Even (RNE) rounding for mantissa
//   - Proper handling of zero and maximum values
//   - Single-cycle combinational operation
//   - Overflow to infinity for very large integers
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   INT_WIDTH:
//     Description: Bit width of input signed integer
//     Type: int
//     Range: 8 to 32 (typical)
//     Default: 32
//     Constraints: Must accommodate expected accumulator range
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     i_int[INT_WIDTH-1:0]: Signed integer input (two's complement)
//
//   Outputs:
//     ow_bf16[15:0]:        BF16 result
//     ow_is_zero:           1 if input was zero
//
//------------------------------------------------------------------------------
// Integer to BF16 Conversion:
//------------------------------------------------------------------------------
//   BF16 format: sign[15], exp[14:7], mant[6:0]
//   Value = (-1)^sign * 2^(exp-127) * 1.mantissa
//
//   Conversion process:
//   1. Handle zero as special case
//   2. Extract sign and compute absolute value
//   3. Find position of most significant bit using CLZ
//   4. Compute exponent: exp = 127 + (msb_position)
//   5. Extract 7 mantissa bits (bits after leading 1)
//   6. Apply RNE rounding
//   7. Check for overflow (clamp to infinity if exp > 254)
//
//   Examples:
//   - INT 1 -> BF16 0x3F80 (1.0)
//   - INT 127 -> BF16 0x42FE (127.0)
//   - INT -128 -> BF16 0xC300 (-128.0)
//   - INT 0 -> BF16 0x0000 (+0.0)
//   - INT 256 -> BF16 0x4380 (256.0)
//
//------------------------------------------------------------------------------
// Usage Example:
//------------------------------------------------------------------------------
//   // Convert INT32 accumulator result to BF16
//   math_int_to_bf16 #(
//       .INT_WIDTH(32)
//   ) u_int_to_bf16 (
//       .i_int(accumulator_result),
//       .ow_bf16(bf16_result),
//       .ow_is_zero(result_is_zero)
//   );
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_math_int_to_bf16.py
//   Run: pytest val/common/test_math_int_to_bf16.py -v
//
//==============================================================================
module math_int_to_bf16 #(
    parameter int INT_WIDTH = 32
) (
    input  logic signed [INT_WIDTH-1:0] i_int,
    output logic [15:0]                 ow_bf16,
    output logic                        ow_is_zero
);

// Compute CLZ output width
localparam int CLZ_WIDTH = $clog2(INT_WIDTH) + 1;

// Extract sign and compute absolute value
wire w_sign = i_int[INT_WIDTH-1];
wire [INT_WIDTH-1:0] w_abs_value = w_sign ? (~i_int + 1'b1) : i_int;

// Zero detection
wire w_is_zero = (i_int == 0);

// Count leading zeros to find MSB position
// The count_leading_zeros module counts from bit[0] upward (CTZ-like behavior)
// We need to bit-reverse the input to get true CLZ behavior
// Bit-reverse: bit[i] -> bit[WIDTH-1-i]
wire [INT_WIDTH-1:0] w_abs_reversed;
generate
    for (genvar i = 0; i < INT_WIDTH; i++) begin : gen_bit_reverse
        assign w_abs_reversed[i] = w_abs_value[INT_WIDTH-1-i];
    end
endgenerate

wire [CLZ_WIDTH-1:0] w_clz;

count_leading_zeros #(
    .WIDTH(INT_WIDTH),
    .INSTANCE_NAME("INT_TO_BF16_CLZ")
) u_clz (
    .data(w_abs_reversed),
    .clz(w_clz)
);

// The MSB position is: (INT_WIDTH - 1 - CLZ)
// For example, INT_WIDTH=32:
//   - If CLZ=31, MSB at position 0, value = 1
//   - If CLZ=24, MSB at position 7, value = 128-255
//   - If CLZ=0,  MSB at position 31, value = 2^31

// Exponent calculation:
// The leading 1 is at bit position (INT_WIDTH - 1 - CLZ)
// BF16 exponent = 127 + bit_position
// = 127 + (INT_WIDTH - 1 - CLZ)
// = 127 + INT_WIDTH - 1 - CLZ
// = (126 + INT_WIDTH) - CLZ

localparam int EXP_BASE = 126 + INT_WIDTH;  // For INT_WIDTH=32: 158
wire signed [9:0] w_exp_raw = 10'(EXP_BASE) - 10'({{(10-CLZ_WIDTH){1'b0}}, w_clz});

// Clamp exponent to valid BF16 range [1, 254]
// exp=0 is reserved for zero/subnormal
// exp=255 is reserved for inf/nan
wire w_exp_overflow = (w_exp_raw > 10'sd254);
wire w_exp_underflow = (w_exp_raw < 10'sd1);
wire [7:0] w_exp_clamped = w_exp_overflow ? 8'd255 :
                           w_exp_underflow ? 8'd0 :
                           w_exp_raw[7:0];

// Normalize the absolute value by shifting left to align MSB at top
// After shift: MSB is at bit [INT_WIDTH-1], mantissa bits follow
// Shift amount = CLZ (move leading 1 to MSB position)
wire [INT_WIDTH-1:0] w_normalized = w_abs_value << w_clz;

// Extract mantissa bits (7 bits after the leading 1)
// w_normalized[INT_WIDTH-1] is the leading 1 (implied, not stored)
// w_normalized[INT_WIDTH-2:INT_WIDTH-8] are the 7 mantissa bits
// w_normalized[INT_WIDTH-9] is the guard bit (first bit after mantissa)
// w_normalized[INT_WIDTH-10] is the round bit
// w_normalized[INT_WIDTH-11:0] contribute to sticky bit

// For INT_WIDTH=32:
// - Mantissa: bits [30:24]
// - Guard: bit [23]
// - Round: bit [22]
// - Sticky: bits [21:0]

wire [6:0] w_mantissa_raw;
wire       w_guard;
wire       w_round_bit;
wire       w_sticky;

generate
    if (INT_WIDTH >= 10) begin : gen_full_rounding
        // Have enough bits for full rounding
        assign w_mantissa_raw = w_normalized[INT_WIDTH-2:INT_WIDTH-8];
        assign w_guard = w_normalized[INT_WIDTH-9];
        assign w_round_bit = w_normalized[INT_WIDTH-10];
        assign w_sticky = |w_normalized[INT_WIDTH-11:0];
    end else if (INT_WIDTH >= 9) begin : gen_partial_rounding
        // Have guard bit but not full round/sticky
        assign w_mantissa_raw = w_normalized[INT_WIDTH-2:INT_WIDTH-8];
        assign w_guard = w_normalized[INT_WIDTH-9];
        assign w_round_bit = 1'b0;
        assign w_sticky = 1'b0;
    end else begin : gen_no_rounding
        // Very narrow integer, minimal or no rounding bits
        // For INT_WIDTH=8: mantissa = bits [6:0], no extra bits
        assign w_mantissa_raw = w_normalized[INT_WIDTH-2:0];
        assign w_guard = 1'b0;
        assign w_round_bit = 1'b0;
        assign w_sticky = 1'b0;
    end
endgenerate

// Round-to-Nearest-Even (RNE) logic:
// Round up if:
// - guard=1 AND (round=1 OR sticky=1)  [clearly > 0.5]
// - guard=1 AND round=0 AND sticky=0 AND mantissa_lsb=1  [exactly 0.5, round to even]
wire w_mantissa_lsb = w_mantissa_raw[0];
wire w_round_up = w_guard & (w_round_bit | w_sticky | w_mantissa_lsb);

// Apply rounding to mantissa
// If mantissa overflows (0x7F + 1 = 0x80), increment exponent
wire [7:0] w_mantissa_rounded = {1'b0, w_mantissa_raw} + {7'b0, w_round_up};
wire w_mantissa_overflow = w_mantissa_rounded[7];

// Adjust exponent if mantissa overflows
wire [8:0] w_exp_adjusted = {1'b0, w_exp_clamped} + {8'b0, w_mantissa_overflow};

// Final mantissa (if overflow, use upper 7 bits which will be 0x00 after 0x7F->0x80)
// Actually when 0x7F + 1 = 0x80, the mantissa becomes 0x00 (bits [6:0] of 0x80)
// This is correct because overflow means we've gone from 1.111...1 to 10.000...0
// which normalizes to 1.000...0 * 2^1, i.e., increment exponent and zero mantissa
wire [6:0] w_mantissa_final = w_mantissa_overflow ? 7'b0 : w_mantissa_rounded[6:0];

// Check if exponent adjustment caused overflow to infinity
wire w_inf_overflow = (w_exp_adjusted > 9'd254) | w_exp_overflow;

// Final exponent
wire [7:0] w_exp_final = w_inf_overflow ? 8'd255 : w_exp_adjusted[7:0];

// Assemble BF16 result
// Zero has special encoding: sign=0, exp=0, mant=0
// Infinity: exp=0xFF, mant=0
always_comb begin
    if (w_is_zero) begin
        // Zero -> +0.0
        ow_bf16 = 16'h0000;
        ow_is_zero = 1'b1;
    end else if (w_inf_overflow) begin
        // Overflow to infinity (preserves sign)
        ow_bf16 = {w_sign, 8'hFF, 7'h00};
        ow_is_zero = 1'b0;
    end else if (w_exp_underflow) begin
        // Underflow to zero (shouldn't happen for integers >= 1)
        ow_bf16 = {w_sign, 8'h00, 7'h00};
        ow_is_zero = 1'b1;
    end else begin
        // Normal case
        ow_bf16 = {w_sign, w_exp_final, w_mantissa_final};
        ow_is_zero = 1'b0;
    end
end

endmodule : math_int_to_bf16
