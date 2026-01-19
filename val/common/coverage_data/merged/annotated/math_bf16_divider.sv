//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_bf16_divider
        // Purpose: BF16 floating-point divider with special case handling and RNE rounding
        //
        // Documentation: BF16_ARCHITECTURE.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-12-26
        //
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: math_bf16_divider
        //==============================================================================
        // Description:
        //   Divides two BF16 floating-point numbers. Used for scale factor calculation
        //   in quantization operations (e.g., 127/max for quantizer multiplier).
        //
        // Features:
        //   - Full IEEE-style special case handling (zero, infinity, NaN)
        //   - Round-to-Nearest-Even (RNE) rounding
        //   - Combinational implementation (single-cycle)
        //   - Division by zero produces signed infinity
        //   - 0/0 and inf/inf produce NaN
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     i_a[15:0]:        BF16 dividend (numerator)
        //     i_b[15:0]:        BF16 divisor (denominator)
        //
        //   Outputs:
        //     ow_result[15:0]:  BF16 quotient (a / b)
        //     ow_overflow:      Result overflowed to infinity
        //     ow_underflow:     Result underflowed to zero
        //     ow_div_by_zero:   Division by zero occurred
        //     ow_invalid:       Invalid operation (0/0 or inf/inf)
        //
        //------------------------------------------------------------------------------
        // Division Algorithm:
        //------------------------------------------------------------------------------
        //   For BF16: sign[15], exp[14:7], mant[6:0]
        //   Value = (-1)^sign * 2^(exp-127) * 1.mantissa
        //
        //   Result:
        //     sign_r = sign_a XOR sign_b
        //     exp_r  = exp_a - exp_b + 127 (re-add bias)
        //     mant_r = (1.mant_a) / (1.mant_b)
        //
        //   The mantissa division produces a result in range [0.5, 2):
        //     - If 1.mant_a >= 1.mant_b: result in [1, 2), no normalization
        //     - If 1.mant_a < 1.mant_b:  result in [0.5, 1), shift left, exp-1
        //
        //------------------------------------------------------------------------------
        // Test:
        //------------------------------------------------------------------------------
        //   Location: val/common/test_math_bf16_divider.py
        //   Run: pytest val/common/test_math_bf16_divider.py -v
        //
        //==============================================================================
        module math_bf16_divider (
 000013     input  logic [15:0] i_a,
 000012     input  logic [15:0] i_b,
 000016     output logic [15:0] ow_result,
%000004     output logic        ow_overflow,
%000004     output logic        ow_underflow,
%000006     output logic        ow_div_by_zero,
%000004     output logic        ow_invalid
        );
        
        // BF16 field extraction
        // Format: [15]=sign, [14:7]=exponent, [6:0]=mantissa
        
 000013 wire       w_sign_a = i_a[15];
 000018 wire [7:0] w_exp_a  = i_a[14:7];
 000015 wire [6:0] w_mant_a = i_a[6:0];
        
 000016 wire       w_sign_b = i_b[15];
 000019 wire [7:0] w_exp_b  = i_b[14:7];
 000012 wire [6:0] w_mant_b = i_b[6:0];
        
        // Special value detection
        
        // Zero: exp=0, mant=0
%000004 wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 7'h00);
%000008 wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 7'h00);
        
        // Subnormal: exp=0, mant!=0 (flushed to zero per BF16 convention)
%000002 wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 7'h00);
%000002 wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 7'h00);
        
        // Infinity: exp=FF, mant=0
%000004 wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 7'h00);
%000004 wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 7'h00);
        
        // NaN: exp=FF, mant!=0
%000004 wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 7'h00);
%000002 wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 7'h00);
        
        // Effective zero (includes subnormals in FTZ mode)
%000006 wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
 000010 wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
        
        // Result sign: XOR of input signs
 000019 wire w_sign_result = w_sign_a ^ w_sign_b;
        
        //------------------------------------------------------------------------------
        // Exponent calculation
        //------------------------------------------------------------------------------
        // exp_result = exp_a - exp_b + bias
        // Using signed arithmetic to handle underflow/overflow properly
        // exp_a - exp_b can range from -254 to +254
        // Adding bias (127) gives range -127 to +381
        
%000008 wire signed [9:0] w_exp_diff = signed'({2'b0, w_exp_a}) - signed'({2'b0, w_exp_b}) + 10'sd127;
        
        // Normalization will adjust exponent:
        //   - quotient >= 2.0: exp+1 (right shift)
        //   - quotient in [1.0, 2.0): no change
        //   - quotient < 1.0: exp-1 (left shift)
%000008 wire signed [9:0] w_exp_no_shift = w_exp_diff;           // No normalization needed
 000012 wire signed [9:0] w_exp_left_shift = w_exp_diff - 10'sd1;   // Quotient < 1.0
%000004 wire signed [9:0] w_exp_right_shift = w_exp_diff + 10'sd1;  // Quotient >= 2.0
        
        //------------------------------------------------------------------------------
        // Mantissa division
        //------------------------------------------------------------------------------
        // Dividend: 1.mant_a (8 bits: 1 + 7 mantissa bits)
        // Divisor:  1.mant_b (8 bits: 1 + 7 mantissa bits)
        //
        // For proper precision, we extend the dividend and perform integer division:
        // quotient = (dividend << 14) / divisor
        // This gives us 15 bits of quotient with proper alignment
        //
        // Result range analysis for mantissas in [1.0, 2.0):
        //   - Min: 1.0 / ~2.0 = ~0.5   -> needs left shift, exp-1
        //   - Max: ~2.0 / 1.0 = ~2.0   -> needs right shift, exp+1
        //   - Equal: 1.x / 1.x = 1.y  -> no shift needed
        
%000001 wire [7:0] w_dividend = {1'b1, w_mant_a};  // 1.mant_a
%000001 wire [7:0] w_divisor  = {1'b1, w_mant_b};  // 1.mant_b
        
        // Extend dividend for precision: dividend << 14 gives us 22-bit numerator
        // The quotient will have its "1.0" position at bit 14
%000000 wire [21:0] w_dividend_ext = {w_dividend, 14'b0};
        
        // Perform division (combinational - synthesizes to divider circuit)
        // Note: For high-speed implementation, consider Newton-Raphson or Goldschmidt
        // Use 16-bit quotient to capture possible overflow case (quotient >= 2.0)
%000000 wire [21:0] w_quotient_raw = w_dividend_ext / {14'b0, w_divisor};
%000000 wire [15:0] w_quotient = w_quotient_raw[15:0];
        
        // Compute remainder for rounding
%000000 wire [21:0] w_remainder = w_dividend_ext - (w_quotient_raw * {14'b0, w_divisor});
        
        // Normalization cases:
        // - Bit 15 set: quotient >= 2.0, need right shift (exp+1)
        // - Bit 14 set, bit 15 clear: quotient in [1.0, 2.0), no shift
        // - Bit 14 clear: quotient < 1.0, need left shift (exp-1)
%000000 wire w_quotient_ge_2 = w_quotient[15];
 000027 wire w_quotient_ge_1 = w_quotient[14] | w_quotient[15];
%000000 wire w_needs_right_shift = w_quotient_ge_2;
 000026 wire w_needs_left_shift = ~w_quotient_ge_1;
        
        // Normalized quotient: align so bit 14 contains the implied 1
        // After normalization, mantissa is at bits [13:7], rounding bits at [6:0]
%000000 wire [15:0] w_quotient_norm = w_needs_right_shift ? {1'b0, w_quotient[15:1]} :
                                       w_needs_left_shift  ? {w_quotient[14:0], 1'b0} :
                                       w_quotient;
        
        // Extract 7-bit mantissa (bits below the leading 1)
        // After normalization, bit 14 is always 1 (the implicit leading 1)
        // Mantissa is bits [13:7], with bits [6:0] for rounding
 000017 wire [6:0] w_mant_raw = w_quotient_norm[13:7];
        
        // Rounding bits
 000027 wire w_guard = w_quotient_norm[6];
 000018 wire w_round_bit = w_quotient_norm[5];
        // Include shifted-out bit for right shift in sticky
 000017 wire w_sticky_bit = |w_quotient_norm[4:0] | (w_remainder != 0) |
                            (w_needs_right_shift & w_quotient[0]);
        
        // Round-to-Nearest-Even (RNE)
        // Round up if: guard=1 AND (round=1 OR sticky=1 OR LSB=1)
 000027 wire w_lsb = w_mant_raw[0];
 000027 wire w_round_up = w_guard & (w_round_bit | w_sticky_bit | w_lsb);
        
        // Apply rounding
%000000 wire [7:0] w_mant_rounded = {1'b0, w_mant_raw} + {7'b0, w_round_up};
%000000 wire w_mant_overflow = w_mant_rounded[7];
        
        // Final mantissa
 000016 wire [6:0] w_mant_final = w_mant_overflow ? 7'h00 : w_mant_rounded[6:0];
        
        // Select exponent based on normalization
%000008 wire signed [9:0] w_exp_selected = w_needs_right_shift ? w_exp_right_shift :
                                           w_needs_left_shift  ? w_exp_left_shift :
                                           w_exp_no_shift;
        
        // Adjust for mantissa rounding overflow
%000008 wire signed [9:0] w_exp_adjusted = w_mant_overflow ? (w_exp_selected + 10'sd1) : w_exp_selected;
        
        // Check for exponent overflow/underflow
 000010 wire w_exp_overflow  = (w_exp_adjusted > 10'sd254);
 000012 wire w_exp_underflow = (w_exp_adjusted < 10'sd1);
        
        // Clamp exponent to valid range
 000028 wire [7:0] w_exp_final = w_exp_overflow  ? 8'hFF :
                                 w_exp_underflow ? 8'h00 :
                                 w_exp_adjusted[7:0];
        
        //------------------------------------------------------------------------------
        // Special case handling
        //------------------------------------------------------------------------------
        
        // NaN propagation: any NaN input produces NaN output
%000002 wire w_any_nan = w_a_is_nan | w_b_is_nan;
        
        // Invalid operations: 0/0 or inf/inf
%000004 wire w_zero_div_zero = w_a_eff_zero & w_b_eff_zero;
%000002 wire w_inf_div_inf = w_a_is_inf & w_b_is_inf;
%000004 wire w_invalid_op = w_zero_div_zero | w_inf_div_inf;
        
        // Division by zero (non-zero / zero = infinity)
%000006 wire w_div_by_zero = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan & w_b_eff_zero;
        
        // Zero result: zero / non-zero finite OR finite / infinity
%000002 wire w_finite_div_inf = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan & w_b_is_inf;
%000006 wire w_result_zero = (w_a_eff_zero & ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan) | w_finite_div_inf;
        
        // Infinity result: infinity / finite OR finite / zero (div by zero)
 000010 wire w_result_inf = (w_a_is_inf & ~w_b_is_inf & ~w_b_is_nan) | w_div_by_zero;
        
        //------------------------------------------------------------------------------
        // Final result assembly
        //------------------------------------------------------------------------------
        
 000144 always_comb begin
            // Default: normal division result
 000144     ow_result = {w_sign_result, w_exp_final, w_mant_final};
 000144     ow_overflow = 1'b0;
 000144     ow_underflow = 1'b0;
 000144     ow_div_by_zero = 1'b0;
 000144     ow_invalid = 1'b0;
        
            // Special case priority (highest to lowest)
 000017     if (w_any_nan | w_invalid_op) begin
                // NaN result: quiet NaN with sign preserved
 000017         ow_result = {w_sign_result, 8'hFF, 7'h40};  // Canonical qNaN
 000017         ow_invalid = w_invalid_op;
 000016     end else if (w_result_inf | w_exp_overflow) begin
                // Infinity result
 000016         ow_result = {w_sign_result, 8'hFF, 7'h00};
 000016         ow_overflow = w_exp_overflow & ~w_result_inf & ~w_div_by_zero;
 000016         ow_div_by_zero = w_div_by_zero;
 000012     end else if (w_result_zero | w_exp_underflow) begin
                // Zero result
 000012         ow_result = {w_sign_result, 8'h00, 7'h00};
 000012         ow_underflow = w_exp_underflow & ~w_result_zero;
            end
        end
        
        endmodule : math_bf16_divider
        
