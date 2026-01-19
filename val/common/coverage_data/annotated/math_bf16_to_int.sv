//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_bf16_to_int
        // Purpose: Convert BF16 floating-point to signed 8-bit integer with rounding and saturation
        //
        // Documentation: BF16_ARCHITECTURE.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-12-25
        //
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: math_bf16_to_int
        //==============================================================================
        // Description:
        //   Converts a BF16 floating-point value to a signed 8-bit integer with
        //   rounding and saturation. Used for quantization operations in neural
        //   network inference.
        //
        // Features:
        //   - Round-to-Nearest-Even (RNE) rounding
        //   - Saturation to [-128, +127] range
        //   - Proper handling of special values (zero, infinity, NaN)
        //   - Single-cycle combinational operation
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     i_bf16[15:0]:    BF16 input value
        //
        //   Outputs:
        //     ow_int8[7:0]:    Signed INT8 result (two's complement)
        //     ow_overflow:     1 if saturated to +127 (magnitude too large, positive)
        //     ow_underflow:    1 if saturated to -128 (magnitude too large, negative)
        //     ow_is_zero:      1 if input was zero or rounded to zero
        //
        //------------------------------------------------------------------------------
        // BF16 to INT8 Conversion:
        //------------------------------------------------------------------------------
        //   BF16 format: sign[15], exp[14:7], mant[6:0]
        //   Value = (-1)^sign * 2^(exp-127) * 1.mantissa
        //
        //   Conversion process:
        //   1. Check for special cases (zero, inf, nan)
        //   2. Extract magnitude: (1.mantissa) * 2^(exp-127)
        //   3. Round to nearest integer using RNE
        //   4. Apply sign
        //   5. Saturate to [-128, +127]
        //
        //   Examples:
        //   - BF16 1.0 (0x3F80) -> INT8 1
        //   - BF16 127.0 (0x42FE) -> INT8 127
        //   - BF16 128.0 (0x4300) -> INT8 127 (overflow, saturated)
        //   - BF16 -128.0 (0xC300) -> INT8 -128
        //   - BF16 0.5 (0x3F00) -> INT8 0 (rounds to even)
        //   - BF16 0.0 (0x0000) -> INT8 0
        //
        //------------------------------------------------------------------------------
        // Usage Example:
        //------------------------------------------------------------------------------
        //   // Quantize BF16 activation to INT8
        //   math_bf16_to_int u_quant (
        //       .i_bf16(scaled_activation),
        //       .ow_int8(quantized_value),
        //       .ow_overflow(saturated_high),
        //       .ow_underflow(saturated_low),
        //       .ow_is_zero(is_zero)
        //   );
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_math_bf16_to_int.py
        //   Run: pytest val/common/test_math_bf16_to_int.py -v
        //
        //==============================================================================
        module math_bf16_to_int (
%000006     input  logic [15:0] i_bf16,
 000013     output logic [7:0]  ow_int8,
 000012     output logic        ow_overflow,
 000011     output logic        ow_underflow,
 000010     output logic        ow_is_zero
        );
        
        // BF16 field extraction
 000015 wire       w_sign  = i_bf16[15];
%000009 wire [7:0] w_exp   = i_bf16[14:7];
%000006 wire [6:0] w_mant  = i_bf16[6:0];
        
        // Special value detection
%000004 wire w_is_zero     = (w_exp == 8'h00);  // Zero or subnormal (flush to zero)
%000002 wire w_is_inf      = (w_exp == 8'hFF) & (w_mant == 7'h00);
%000002 wire w_is_nan      = (w_exp == 8'hFF) & (w_mant != 7'h00);
        
        // Extended mantissa with implied leading 1 (8 bits total: 1.mmmmmmm)
        // Represents value in range [1.0, 2.0)
%000001 wire [7:0] w_ext_mant = {1'b1, w_mant};
        
        // Unbiased exponent (signed)
        // exp=127 means 2^0 = 1.0 multiplier
        // exp=134 means 2^7 = 128 multiplier (max for INT8)
%000008 wire signed [8:0] w_unbiased_exp = $signed({1'b0, w_exp}) - 9'sd127;
        
        // Compute shift amount for converting 1.mmmmmmm to integer
        // We need to shift the 8-bit mantissa (1.mmmmmmm) by (exp-127) positions
        // Since mantissa represents 1.mmmmmmm, after shifting by (exp-127):
        //   - If exp=127: result = 1.mmmmmmm >> 0 = 1 (integer part only)
        //   - If exp=134: result = 1.mmmmmmm << 7 = 1mmmmmmm (max 255)
        //   - If exp>134: overflow
        
        // For proper rounding, we need extra bits
        // Use 16-bit intermediate: 8 bits integer, 8 bits fractional
        // Position mantissa at fixed point: integer.fraction
%000000 wire [15:0] w_positioned;
        
        // Shift amount interpretation:
        // - exp=127 (shift=0): integer part is 1.xxx -> 1
        // - exp=128 (shift=1): integer part is 1x.xx -> 2-3
        // - exp=134 (shift=7): integer part is 1xxxxxxx -> 128-255
        // - exp=135 (shift=8): would need 9 bits -> overflow
        
        // Position the mantissa in a 16-bit field
        // Upper 8 bits = integer, lower 8 bits = fraction
        // Start with mantissa at position [14:7] (treating bit 14 as ones place)
        // Then shift left by (exp - 127)
        
        // Clamp shift to valid range
%000008 wire signed [8:0] w_shift_raw = w_unbiased_exp;
%000000 wire [3:0] w_shift_clamped;
 000015 wire w_exp_overflow;
 000010 wire w_exp_underflow;
        
        // Detect overflow/underflow conditions based on exponent
        // INT8 signed range: -128 to +127
        // Max positive magnitude: 127 -> exp ~= 127 + 6 = 133 (2^6 * 1.xxx = 64-127)
        // Actually 127 = 0x7F = 0111_1111, which is slightly less than 128 = 2^7
        // So we can have exp up to 133 for positive, but need to check final value
        
        assign w_exp_overflow = (w_shift_raw > 9'sd7);   // Would exceed 8-bit unsigned
        assign w_exp_underflow = (w_shift_raw < 9'sd0);  // Value < 1.0
        
        // Clamp shift amount to [0, 7]
        assign w_shift_clamped = w_exp_overflow ? 4'd7 :
                                 w_exp_underflow ? 4'd0 :
                                 w_shift_raw[3:0];
        
        // Position mantissa: start at bits [14:7], shift left by w_shift_clamped
        // But for RNE rounding, we need the fractional bits too
        // Use different approach: keep mantissa at [15:8] as integer.fraction base
        // Then shift left
        
        // Actually, let's be more precise:
        // w_ext_mant = 8'b1mmmmmmm represents 1.mmmmmmm in fixed point
        // If we want integer + fraction with 8 fractional bits:
        //   Start with w_ext_mant at bits [15:8] = 1mmmmmmm.00000000
        //   But this represents value 1.mmmmmmm, so we need to adjust
        //
        // Better approach:
        //   Use 16-bit field where bit[15] = 128, bit[14] = 64, ..., bit[8] = 1, bit[7] = 0.5, etc.
        //   Place w_ext_mant such that bit[7] of w_ext_mant (the leading 1) is at position (7 + shift)
        //
        //   For shift=0: leading 1 at position 7 -> value = 1.xxx
        //   For shift=7: leading 1 at position 14 -> value = 128.xxx to 255.xxx
        
        // Simplified: create 16-bit value with w_ext_mant positioned based on shift
        // w_ext_mant[7:0] = 1mmmmmmm
        // For shift=0: {8'b0, w_ext_mant} = 0000_0000.1mmm_mmmm (but we want 1.mmm in integer)
        //
        // Let me reconsider: we have 1.mmmmmmm * 2^shift
        // The integer part is: floor(1.mmmmmmm * 2^shift)
        //
        // For 1.mmmmmmm (8 bits total), multiplying by 2^shift:
        // - shift=0: integer=1, fraction=0.mmmmmmm
        // - shift=1: integer=1m (2 bits), fraction=0.mmmmmm
        // - shift=7: integer=1mmmmmmm (8 bits), fraction=0
        
        // Use 16-bit arithmetic: [15:8] = integer, [7:0] = fraction
        // Initial: mantissa represents 1.mmmmmmm
        // Place at [14:7] to represent 128.fraction, then shift
        
        // Cleaner implementation:
        // 1. Start with full precision in 16 bits
        // 2. w_ext_mant = 1mmmmmmm represents 1.0 to 1.9921875
        // 3. Shift left by unbiased_exp to get actual value
        // 4. Bits [15:8] = integer part, bits [7:0] = fractional part
        
%000000 wire [22:0] w_full_shift = {w_ext_mant, 15'b0} >> (4'd7 - w_shift_clamped);
%000007 wire [7:0] w_int_part = w_full_shift[22:15];
%000002 wire [6:0] w_frac_part = w_full_shift[14:8];
%000006 wire       w_guard_bit = w_full_shift[14];  // First bit after integer
 000012 wire       w_round_bit = w_full_shift[13];  // Second bit after integer
%000006 wire       w_sticky = |w_full_shift[12:0];  // OR of remaining bits
        
        // Wait, let me simplify with a different approach
        // Just shift the extended mantissa and track rounding bits
        
        // Actually let me use a barrel shifter approach:
        // Extended value: {w_ext_mant, 8'b0} = 16 bits with mantissa at top
        // This represents 1.mmmmmmm * 256 (value 256-511 in integer terms)
        // Divide by 2^(7-shift) to get actual value
        
        // For shift=0: divide by 128 -> result 2-3.99
        // For shift=7: divide by 1 -> result 256-511
        
        // Hmm, let me just do direct computation
        // w_ext_mant = 8'b1mmmmmmm represents 1.mmmmmmm
        // Integer result = floor(1.mmmmmmm * 2^shift) with rounding
        
        // Using 16-bit intermediate with proper positioning
%000000 wire [15:0] w_shifted_value;
%000000 wire [15:0] w_base_value = {8'b0, w_ext_mant};  // 0x0080 to 0x00FF (128 to 255)
        
        // Shift left by unbiased exponent (clamped to 0-7)
        // After shift: integer in bits [15:8], fraction in bits [7:0]... no wait
        // Let's be more careful
        
        // Start fresh with cleaner logic:
        // w_ext_mant in [128, 255] represents 1.0 to 1.9921875
        // Multiply by 2^shift:
        // - shift=0: result in [128, 255] -> integer 1, fraction 0-127
        // - shift=1: result in [256, 510] -> integer 2-3, fraction varies
        // - shift=7: result in [16384, 32640] -> integer 128-255 (but we only care about 127 max)
        
        // Use 15-bit shift result to avoid overflow in intermediate
%000002 wire [14:0] w_raw_shifted = ({7'b0, w_ext_mant} << w_shift_clamped);
        
        // Extract integer and fractional parts
        // After shifting: value is w_ext_mant * 2^shift
        // Original w_ext_mant represents 1.mmmmmmm = 1 + m/128
        // Shifted: (128 + m) * 2^shift / 128 = (128 + m) >> (7 - shift)
        //
        // Hmm, this is getting confusing. Let me use a cleaner model.
        
        // Model the value as fixed-point with 7 fractional bits:
        // w_ext_mant[7:0] = 1.mmmmmmm in fixed-point (bit 7 is integer, bits 6:0 are fraction)
        // The true value is w_ext_mant / 128.0 (since bit 7 represents 1, bit 6 represents 0.5, etc.)
        //
        // After multiplying by 2^shift: value = w_ext_mant * 2^shift / 128
        // For shift=7: value = w_ext_mant (128-255)
        // For shift=0: value = w_ext_mant / 128 (1.0 - 1.99)
        
        // So for integer result: floor(w_ext_mant * 2^shift / 128) with rounding
        // = (w_ext_mant << shift) >> 7, with rounding bits from bits [6:0] after shift
        
        // Use 15-bit intermediate for shifted mantissa
%000002 wire [14:0] w_mant_shifted = {7'b0, w_ext_mant} << w_shift_clamped;
        
        // Now divide by 128 (right shift by 7) to get integer part
        // But we need to track rounding bits before the division
        // The bits that would be shifted out during >>7 are the fractional bits
        
        // For >>7:
        // - Bits [14:7] become the integer result
        // - Bit [6] is the guard bit (most significant fractional bit)
        // - Bit [5] is the round bit
        // - Bits [4:0] contribute to sticky bit
        
%000007 wire [7:0] w_magnitude_raw = w_mant_shifted[14:7];
%000006 wire       w_guard = w_mant_shifted[6];
 000012 wire       w_round_rne = w_mant_shifted[5];
%000006 wire       w_sticky_rne = |w_mant_shifted[4:0];
        
        // Round-to-Nearest-Even logic:
        // Round up if:
        // - guard=1 AND (round=1 OR sticky=1)  [clearly > 0.5]
        // - guard=1 AND round=0 AND sticky=0 AND lsb=1  [exactly 0.5, round to even]
 000010 wire w_lsb = w_magnitude_raw[0];
%000004 wire w_round_up = w_guard & (w_round_rne | w_sticky_rne | w_lsb);
        
        // Apply rounding
%000000 wire [8:0] w_magnitude_rounded = {1'b0, w_magnitude_raw} + {8'b0, w_round_up};
        
        // Check for overflow after rounding (magnitude > 255 not possible with 8-bit input + 1-bit round)
        // But we need to check against INT8 range: -128 to +127
        // For positive: max is 127
        // For negative: max magnitude is 128
        
        // Determine if value is too large for INT8
 000014 wire w_too_large_positive = ~w_sign & (w_magnitude_rounded > 9'd127);
%000009 wire w_too_large_negative = w_sign & (w_magnitude_rounded > 9'd128);
        
        // When exp_overflow is true, the magnitude is definitely too large
        // Use exp_overflow to also determine which saturation direction
 000014 wire w_exp_ovf_positive = w_exp_overflow & ~w_sign;
%000009 wire w_exp_ovf_negative = w_exp_overflow & w_sign;
        
 000013 wire w_any_overflow = w_too_large_positive | w_too_large_negative | w_exp_overflow;
        
        // Final magnitude after saturation
 000011 wire [7:0] w_magnitude_sat;
        assign w_magnitude_sat = w_any_overflow ?
                                 (w_sign ? 8'd128 : 8'd127) :
                                 w_magnitude_rounded[7:0];
        
        // Convert to signed two's complement
 000012 wire [7:0] w_result_signed = w_sign ? (~w_magnitude_sat + 8'd1) : w_magnitude_sat;
        
        // Handle special cases
 000060 always_comb begin
            // Default: normal conversion
 000060     ow_int8 = w_result_signed;
 000060     ow_overflow = (w_too_large_positive | w_exp_ovf_positive) & ~w_is_zero & ~w_is_nan;
 000060     ow_underflow = (w_too_large_negative | w_exp_ovf_negative) & ~w_is_zero & ~w_is_nan;
 000060     ow_is_zero = 1'b0;
        
            // Special cases (highest priority)
%000002     if (w_is_nan) begin
                // NaN -> 0 (could also be saturate to max, but 0 is safer)
%000002         ow_int8 = 8'd0;
%000002         ow_overflow = 1'b0;
%000002         ow_underflow = 1'b0;
%000002         ow_is_zero = 1'b0;  // Not technically zero, but invalid
%000004     end else if (w_is_inf) begin
                // +Inf -> +127, -Inf -> -128
%000004         ow_int8 = w_sign ? 8'h80 : 8'h7F;
%000004         ow_overflow = ~w_sign;
%000004         ow_underflow = w_sign;
%000004         ow_is_zero = 1'b0;
 000013     end else if (w_is_zero) begin
                // Zero -> 0
 000013         ow_int8 = 8'd0;
 000013         ow_overflow = 1'b0;
 000013         ow_underflow = 1'b0;
 000013         ow_is_zero = 1'b1;
 000012     end else if (w_exp_underflow) begin
                // Value < 1.0, may round to 0 or ±1
                // For |value| < 0.5, result is 0
                // For 0.5 <= |value| < 1.0, result rounds to ±1
                // Since exp < 127, value is at most 0.9921875
                // Actually with exp=126, value is 0.5 to 0.9921875
                // With exp=125, value is 0.25 to 0.4960...
                // Need to check if rounds to 1
        
                // For exp=126: value = 0.5 to 0.9921875
                // These should round to 0 (0.5 rounds to even = 0) or 1 (>0.5)
                // Simplified: if exp < 126, always round to 0
                // If exp == 126, check mantissa for rounding
%000008         if (w_exp < 8'd126) begin
                    // Definitely < 0.5, rounds to 0
%000008             ow_int8 = 8'd0;
%000008             ow_is_zero = 1'b1;
%000000         end else if (w_exp == 8'd126) begin
                    // Value is 0.5 to 0.9921875
                    // 0.5 exactly (mant=0) rounds to 0 (RNE)
                    // > 0.5 rounds to 1
%000000             if (w_mant == 7'd0) begin
                        // Exactly 0.5, round to even (0)
%000000                 ow_int8 = 8'd0;
%000000                 ow_is_zero = 1'b1;
%000004             end else begin
                        // > 0.5, round to ±1
%000004                 ow_int8 = w_sign ? 8'hFF : 8'h01;  // -1 or +1
%000004                 ow_is_zero = 1'b0;
                    end
%000000         end else begin
                    // exp == 126 already handled, this shouldn't happen
%000000             ow_int8 = 8'd0;
%000000             ow_is_zero = 1'b1;
                end
            end
        end
        
        endmodule : math_bf16_to_int
        
