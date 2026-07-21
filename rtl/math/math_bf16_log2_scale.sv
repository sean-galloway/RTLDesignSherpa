// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_log2_scale
// Purpose: Compute power-of-2 quantization scale from BF16 max value
//
// Documentation: BF16_ARCHITECTURE.md
// Subsystem: common
//
// Author: Claude AI / sean galloway
// Created: 2025-12-26
//

`timescale 1ns / 1ps

//==============================================================================
// Module: math_bf16_log2_scale
//==============================================================================
// Description:
//   Computes power-of-2 based quantization parameters from a BF16 max value.
//   This enables efficient quantization using bit shifts instead of multiplies,
//   reducing power consumption at the cost of slightly lower precision.
//
// Operation:
//   Given max_value (typically max(|x_i|) of a vector):
//   1. Find the smallest power-of-2 >= max_value
//   2. Return scale_exp such that scale = 2^scale_exp >= max_value
//   3. For quantization: q_i = round(x_i * 127 / scale)
//                           = round(x_i >> (scale_exp - 7))  [approximately]
//
// Power-of-2 Quantization Benefits:
//   - Multiply by 127/scale becomes shift by (7 - scale_exp) + bias correction
//   - ~90% power reduction vs full BF16 multiply
//   - Simpler hardware (shifters vs multipliers)
//   - Lower latency (shift is faster than multiply)
//
// Accuracy Trade-off:
//   - Standard quantization: scale = max/127 (continuous)
//   - Power-of-2 quantization: scale = 2^ceil(log2(max)) (discrete)
//   - Worst case: quantization range is 2x optimal (if max just above power of 2)
//   - Typical case: ~1.4x quantization range vs optimal
//
// Use Case:
//   Low-power inference mode where accuracy can be slightly reduced
//   to save significant power in the multiply operations.
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     i_max_value[15:0]:  BF16 max magnitude (|max|, sign bit ignored)
//
//   Outputs:
//     ow_scale_exp[7:0]:  Biased exponent of power-of-2 scale (BF16 bias)
//                         Actual scale = 2^(ow_scale_exp - 127)
//     ow_quant_shift[4:0]: Right shift amount for quantization
//                         q_i = (value << 7) >> ow_quant_shift (approximately)
//     ow_dequant_shift[4:0]: Left shift amount for de-quantization
//                         x_i = q_i << ow_dequant_shift (approximately)
//     ow_scale_bf16[15:0]: BF16 representation of the power-of-2 scale
//     ow_is_zero:         1 if max_value is zero (special case)
//     ow_is_overflow:     1 if max_value too large for INT8 range
//
//------------------------------------------------------------------------------
// Example Values:
//------------------------------------------------------------------------------
//   max_value = 1.0 (exp=127):
//     scale_exp = 127, scale = 1.0
//     quant_shift = 0, dequant_shift = 0
//
//   max_value = 2.5 (exp=128, mant=0x20):
//     scale_exp = 129 (rounds up to 4.0)
//     quant_shift = 2, dequant_shift = 2
//
//   max_value = 100.0 (exp=133, mant=0x48):
//     scale_exp = 134 (rounds up to 128.0)
//     quant_shift = 7, dequant_shift = 7
//
//------------------------------------------------------------------------------
module math_bf16_log2_scale (
    input  logic [15:0] i_max_value,
    output logic [7:0]  ow_scale_exp,
    output logic [4:0]  ow_quant_shift,
    output logic [4:0]  ow_dequant_shift,
    output logic [15:0] ow_scale_bf16,
    output logic        ow_is_zero,
    output logic        ow_is_overflow
);

//------------------------------------------------------------------------------
// BF16 field extraction (magnitude only - ignore sign)
//------------------------------------------------------------------------------
wire [7:0] w_exp  = i_max_value[14:7];
wire [6:0] w_mant = i_max_value[6:0];

//------------------------------------------------------------------------------
// Special value detection
//------------------------------------------------------------------------------
wire w_is_zero     = (w_exp == 8'h00);  // Zero or subnormal
wire w_is_inf      = (w_exp == 8'hFF) & (w_mant == 7'h00);
wire w_is_nan      = (w_exp == 8'hFF) & (w_mant != 7'h00);

//------------------------------------------------------------------------------
// Determine power-of-2 scale
//------------------------------------------------------------------------------
// For max_value with exponent E and mantissa M:
//   value = 2^(E-127) * (1 + M/128)
//
// We need scale >= value, where scale is a power of 2
// If mantissa is 0: scale = 2^(E-127), scale_exp = E
// If mantissa > 0: scale = 2^(E-126), scale_exp = E+1
//
// This ensures scale is the smallest power of 2 >= max_value

wire w_has_mantissa = (w_mant != 7'h00);
wire [8:0] w_scale_exp_raw = {1'b0, w_exp} + {8'b0, w_has_mantissa};

// Clamp to valid BF16 exponent range
wire w_exp_overflow = (w_scale_exp_raw > 9'd254);
wire [7:0] w_scale_exp_clamped = w_exp_overflow ? 8'd254 : w_scale_exp_raw[7:0];

//------------------------------------------------------------------------------
// Compute shift amounts for quantization
//------------------------------------------------------------------------------
// For INT8 quantization with range [-128, +127]:
// We want: q = round(x * 127 / scale)
//
// With power-of-2 scale = 2^N (where N = scale_exp - 127):
//   q = round(x / 2^N * 127)
//   q = round(x >> N * 127)  [approximately]
//
// More precisely, for x with exponent E_x:
//   x / scale = x / 2^N = x * 2^(-N)
//   This is equivalent to subtracting N from x's exponent
//
// For direct bit manipulation:
//   quant_shift = scale_exp - 127 (unbiased scale exponent)
//   But we need to account for the 127 multiplier...
//
// Actually, let's think about it differently:
// If scale = 2^N and we want q = x * 127 / scale:
//   q = x * 127 / 2^N
//   q = (x * 127) >> N
//
// Or equivalently, if x is expressed in fixed-point:
//   q_shift = N - 7 (since 127 ~= 2^7)
//
// For dequantization: x = q * scale / 127 ~= q * 2^N / 128 = q << (N-7)

wire signed [8:0] w_unbiased_scale = $signed({1'b0, w_scale_exp_clamped}) - 9'sd127;

// Quantization shift: for x_fixed * 127 / 2^N
// If x is in natural units and we want INT8:
// quant_shift = max(0, unbiased_scale)
// (negative unbiased means scale < 1, which shouldn't happen for max values)

wire [4:0] w_quant_shift_raw = (w_unbiased_scale < 9'sd0) ? 5'd0 :
                               (w_unbiased_scale > 9'sd31) ? 5'd31 :
                               w_unbiased_scale[4:0];

// Dequantization shift: same as quant shift for symmetric scaling
wire [4:0] w_dequant_shift_raw = w_quant_shift_raw;

//------------------------------------------------------------------------------
// Build BF16 representation of scale
//------------------------------------------------------------------------------
// Power-of-2 scale has mantissa = 0 (represents exactly 2^(exp-127))
wire [15:0] w_scale_bf16 = {1'b0, w_scale_exp_clamped, 7'h00};

//------------------------------------------------------------------------------
// Check for overflow (max value too large for INT8)
//------------------------------------------------------------------------------
// If scale > 128, then max value could produce INT8 > 127
// This happens when scale_exp > 134 (2^7 = 128)
// Actually, scale = 128 is fine (maps to INT8 127)
// Overflow when scale_exp > 134 AND has mantissa
wire w_result_overflow = (w_scale_exp_clamped > 8'd134);

//------------------------------------------------------------------------------
// Output assignment
//------------------------------------------------------------------------------
always_comb begin
    // Default: normal operation
    ow_scale_exp = w_scale_exp_clamped;
    ow_quant_shift = w_quant_shift_raw;
    ow_dequant_shift = w_dequant_shift_raw;
    ow_scale_bf16 = w_scale_bf16;
    ow_is_zero = 1'b0;
    ow_is_overflow = 1'b0;

    // Special cases
    if (w_is_nan | w_is_inf) begin
        // NaN or Inf max value -> overflow
        ow_scale_exp = 8'd254;
        ow_quant_shift = 5'd31;
        ow_dequant_shift = 5'd31;
        ow_scale_bf16 = 16'h7F80;  // +Inf
        ow_is_overflow = 1'b1;
    end else if (w_is_zero) begin
        // Zero max value -> special case (all zeros)
        // Use scale = 1.0 to avoid division by zero
        ow_scale_exp = 8'd127;
        ow_quant_shift = 5'd0;
        ow_dequant_shift = 5'd0;
        ow_scale_bf16 = 16'h3F80;  // 1.0
        ow_is_zero = 1'b1;
    end else if (w_result_overflow) begin
        // Max value too large
        ow_is_overflow = 1'b1;
    end
end

endmodule : math_bf16_log2_scale
