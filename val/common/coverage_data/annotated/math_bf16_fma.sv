//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_bf16_fma
        // Purpose: BF16 Fused Multiply-Add with FP32 accumulator for AI training
        //
        // Documentation: BF16_ARCHITECTURE.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-11-25
        //
        // AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
        // Generator: bin/rtl_generators/bf16/bf16_fma.py
        // Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common
        //
        
        `timescale 1ns / 1ps
        
        module math_bf16_fma(
%000000     input  logic [15:0] i_a,
%000000     input  logic [15:0] i_b,
 000883     input  logic [31:0] i_c,
 001422     output logic [31:0] ow_result,
%000000     output logic        ow_overflow,
%000000     output logic        ow_underflow,
%000002     output logic        ow_invalid
        );
        
        // BF16 field extraction
        // BF16: [15]=sign, [14:7]=exp, [6:0]=mant
        
%000001 wire       w_sign_a = i_a[15];
%000009 wire [7:0] w_exp_a  = i_a[14:7];
%000000 wire [6:0] w_mant_a = i_a[6:0];
        
 000043 wire       w_sign_b = i_b[15];
 000089 wire [7:0] w_exp_b  = i_b[14:7];
%000000 wire [6:0] w_mant_b = i_b[6:0];
        
        // FP32 field extraction
        // FP32: [31]=sign, [30:23]=exp, [22:0]=mant
        
 000883 wire        w_sign_c  = i_c[31];
 003532 wire [7:0]  w_exp_c   = i_c[30:23];
 015875 wire [22:0] w_mant_c  = i_c[22:0];
        
        // Special case detection - BF16 operands
%000008 wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 7'h00);
 000046 wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 7'h00);
%000000 wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 7'h00);
%000000 wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 7'h00);
%000004 wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 7'h00);
%000002 wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 7'h00);
%000002 wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 7'h00);
%000002 wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 7'h00);
        
        // Effective zero (FTZ for subnormals)
%000008 wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
 000046 wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
%000008 wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;
 000048 wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;
        
        // Special case detection - FP32 addend
 000890 wire w_c_is_zero = (w_exp_c == 8'h00) & (w_mant_c == 23'h0);
%000000 wire w_c_is_subnormal = (w_exp_c == 8'h00) & (w_mant_c != 23'h0);
%000004 wire w_c_is_inf = (w_exp_c == 8'hFF) & (w_mant_c == 23'h0);
%000001 wire w_c_is_nan = (w_exp_c == 8'hFF) & (w_mant_c != 23'h0);
 000890 wire w_c_eff_zero = w_c_is_zero | w_c_is_subnormal;
 000883 wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;
        
        // BF16 multiplication: a * b
        
        // Product sign
 000042 wire w_prod_sign = w_sign_a ^ w_sign_b;
        
        // Mantissa multiplication (8x8 with implied 1)
%000000 wire [7:0] w_mant_a_ext = {w_a_is_normal, w_mant_a};
%000000 wire [7:0] w_mant_b_ext = {w_b_is_normal, w_mant_b};
        
%000000 wire [15:0] w_prod_mant_raw;
        math_multiplier_dadda_4to2_008 u_mant_mult (
            .i_multiplier(w_mant_a_ext),
            .i_multiplicand(w_mant_b_ext),
            .ow_product(w_prod_mant_raw)
        );
        
        // Product exponent: exp_a + exp_b - bias (SIGNED to detect underflow!)
 000024 wire signed [10:0] w_prod_exp_raw = $signed({3'b0, w_exp_a}) + $signed({3'b0, w_exp_b}) - 11'sd127;
        
        // Normalization detection (product >= 2.0)
%000000 wire w_prod_needs_norm = w_prod_mant_raw[15];
        
        // Normalized product exponent
 000024 wire signed [10:0] w_prod_exp_adj = w_prod_exp_raw + {10'b0, w_prod_needs_norm};
        
        // Detect product underflow: when product exponent is too small to represent
        // Product is effectively zero if exp < 1 (or exp goes negative)
 000032 wire w_prod_underflow = w_prod_exp_adj[10] | (w_prod_exp_adj < 11'sd1);
        
        // Clamp product exponent for downstream use (will be overridden by special cases)
%000000 wire [9:0] w_prod_exp = w_prod_underflow ? 10'd0 : w_prod_exp_adj[9:0];
        
        // Extended product mantissa to FP32 precision (23 bits)
        // Product is either 1x.xxxxxxx_xxxxxxxx or 01.xxxxxx_xxxxxxxxx
%000000 wire [23:0] w_prod_mant_ext;  // With implied 1
        assign w_prod_mant_ext = w_prod_needs_norm ?
            {1'b1, w_prod_mant_raw[14:0], 8'b0} :  // Shift right, add zeros
            {1'b1, w_prod_mant_raw[13:0], 9'b0};   // No shift
        
        // Addend (c) alignment
        // Need to align c with product based on exponent difference
        
        // Extended addend mantissa with implied 1
 000883 wire [23:0] w_c_mant_ext = w_c_is_normal ? {1'b1, w_mant_c} : 24'h0;
        
        // Exponent difference for alignment
%000000 wire [9:0] w_exp_c_ext = {2'b0, w_exp_c};
 002686 wire signed [10:0] w_exp_diff = $signed({1'b0, w_prod_exp}) - $signed({1'b0, w_exp_c_ext});
        
        // Determine which operand has larger exponent
 002841 wire w_prod_exp_larger = w_exp_diff >= 0;
%000000 wire [9:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff[9:0] : (~w_exp_diff[9:0] + 10'd1);
        
        // Clamp shift amount to prevent over-shifting
 000847 wire [5:0] w_shift_clamped = (w_shift_amt > 10'd48) ? 6'd48 : w_shift_amt[5:0];
        
        // Extended mantissas for addition (48 bits to capture all precision)
%000000 wire [47:0] w_prod_mant_48 = {w_prod_mant_ext, 24'b0};
%000000 wire [47:0] w_c_mant_48    = {w_c_mant_ext, 24'b0};
        
        // Aligned mantissas
%000000 wire [47:0] w_mant_larger, w_mant_smaller_shifted;
 001553 wire        w_sign_larger, w_sign_smaller;
%000000 wire [9:0]  w_exp_result_pre;
        
        assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_48 : w_c_mant_48;
        assign w_mant_smaller_shifted = w_prod_exp_larger ?
            (w_c_mant_48 >> w_shift_clamped) : (w_prod_mant_48 >> w_shift_clamped);
        assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;
        assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;
        assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp : w_exp_c_ext;
        
        // Addition of aligned mantissas using Han-Carlson structural adder
        
        // Effective operation: add or subtract based on signs
 000845 wire w_effective_sub = w_sign_larger ^ w_sign_smaller;
        
        // For subtraction, invert smaller operand (two's complement: ~B + 1)
        // The +1 is handled via carry-in to the adder
 000845 wire [47:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_shifted : w_mant_smaller_shifted;
        
        // 48-bit Han-Carlson structural adder
%000000 wire [47:0] w_adder_sum;
 006613 wire        w_adder_cout;
        math_adder_han_carlson_048 u_wide_adder (
            .i_a(w_mant_larger),
            .i_b(w_adder_b),
            .i_cin(w_effective_sub),  // +1 for two's complement subtraction
            .ow_sum(w_adder_sum),
            .ow_cout(w_adder_cout)
        );
        
        // Result sign determination
        // For subtraction: if no carry out, result is negative (A < B)
        // For addition: carry out means magnitude overflow (need right shift)
 001256 wire w_sum_negative = w_effective_sub & ~w_adder_cout;
 001090 wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;
        
        // Absolute value of result
        // If negative (subtraction with A < B), need to negate the result
%000000 wire [47:0] w_negated_sum;
 001477 wire        w_neg_cout;
        math_adder_han_carlson_048 u_negate_adder (
            .i_a(~w_adder_sum),
            .i_b(48'h0),
            .i_cin(1'b1),  // ~sum + 1 = -sum
            .ow_sum(w_negated_sum),
            .ow_cout(w_neg_cout)
        );
        
        // Handle addition overflow (carry out for same-sign addition)
        // When addition overflows, prepend carry bit and shift right
 004656 wire w_add_overflow = ~w_effective_sub & w_adder_cout;
%000000 wire [47:0] w_sum_with_carry = {w_adder_cout, w_adder_sum[47:1]};  // Right shift, prepend carry
        
        // Select appropriate absolute value
%000000 wire [47:0] w_sum_abs = w_sum_negative ? w_negated_sum :
                                w_add_overflow ? w_sum_with_carry : w_adder_sum;
        
        // Normalization
        
        // Count leading zeros for normalization
        // NOTE: count_leading_zeros module counts from bit[0] (trailing zeros)
        // To get actual leading zeros from MSB, we bit-reverse the input
        // For WIDTH=48, clz output is $clog2(48)+1 = 7 bits (0-48 range)
        
        // Bit-reverse function for 48-bit value
%000000 wire [47:0] w_sum_abs_reversed;
        genvar i;
        generate
            for (i = 0; i < 48; i = i + 1) begin : gen_bit_reverse
                assign w_sum_abs_reversed[i] = w_sum_abs[47 - i];
            end
        endgenerate
        
%000000 wire [6:0] w_lz_count_raw;
        count_leading_zeros #(.WIDTH(48)) u_clz (
            .data(w_sum_abs_reversed),
            .clz(w_lz_count_raw)
        );
        
        // Clamp LZ count to 6 bits for shift (max useful shift is 47)
 000640 wire [5:0] w_lz_count = (w_lz_count_raw > 7'd47) ? 6'd47 : w_lz_count_raw[5:0];
        
        // Normalized mantissa (shift left by LZ count)
%000000 wire [47:0] w_mant_normalized = w_sum_abs << w_lz_count;
        
        // Adjusted exponent
        // exp_result_pre - lz_count + add_overflow (subtract leading zeros, add 1 for carry overflow)
%000000 wire signed [10:0] w_exp_adjusted = $signed({1'b0, w_exp_result_pre}) - $signed({4'b0, w_lz_count_raw}) + {10'b0, w_add_overflow};
        
        // Round-to-Nearest-Even and FP32 packing
        
        // Extract 23-bit mantissa with guard, round, sticky
        // Bit 47 is the implied 1 (not stored), bits [46:24] are the 23-bit mantissa
 007773 wire [22:0] w_mant_23 = w_mant_normalized[46:24];
 010479 wire w_guard  = w_mant_normalized[23];
 005943 wire w_round  = w_mant_normalized[22];
 004751 wire w_sticky = |w_mant_normalized[21:0];
        
        // RNE rounding decision
 009863 wire w_round_up = w_guard & (w_round | w_sticky | w_mant_23[0]);
        
        // Apply rounding
 000640 wire [23:0] w_mant_rounded = {1'b0, w_mant_23} + {23'b0, w_round_up};
 000640 wire w_round_overflow = w_mant_rounded[23];
        
        // Final mantissa (23 bits)
        // When rounding overflows (mantissa goes from 0x7FFFFF to 0x800000), the value
        // becomes exactly 2.0, which normalizes to 1.0 * 2^1. The mantissa for 1.0 is 0.
 005372 wire [22:0] w_mant_final = w_round_overflow ? 23'h0 : w_mant_rounded[22:0];
        
        // Final exponent with rounding adjustment
%000000 wire signed [10:0] w_exp_final = w_exp_adjusted + {10'b0, w_round_overflow};
        
        // Special case handling
        
        // Any NaN input
%000001 wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;
        
        // Invalid: 0 * inf or inf - inf
%000004 wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;
        // Product is zero if either operand is zero/subnormal, OR if the product underflows
 000046 wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero | w_prod_underflow;
%000002 wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
%000002 wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);
%000002 wire w_invalid = w_invalid_mul | w_invalid_add;
        
        // Overflow and underflow detection
        // Use signed comparison - negative exponent is underflow, not overflow
%000004 wire w_overflow_cond = ~w_exp_final[10] & (w_exp_final > 11'sd254);
 000052 wire w_underflow_cond = w_exp_final[10] | (w_exp_final < 11'sd1);
        
        // Final result assembly
        
 050310 always_comb begin
            // Default: normal result
 050310     ow_result = {w_result_sign, w_exp_final[7:0], w_mant_final};
 050310     ow_overflow = 1'b0;
 050310     ow_underflow = 1'b0;
 050310     ow_invalid = 1'b0;
        
            // Special cases - PRIORITY ORDER MATTERS!
            // 1. NaN/Invalid first (highest priority)
            // 2. Infinity cases
            // 3. Zero operand pass-through (BEFORE overflow/underflow check!)
            // 4. Overflow/underflow
            // 5. Normal result (default)
        
 000011     if (w_any_nan | w_invalid) begin
 000011         ow_result = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN
 000011         ow_invalid = w_invalid;
%000002     end else if (w_prod_is_inf & ~w_c_is_inf) begin
%000002         ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product infinity
%000002     end else if (w_c_is_inf) begin
%000002         ow_result = {w_sign_c, 8'hFF, 23'h0};  // Addend infinity
 000092     end else if (w_prod_is_zero & w_c_eff_zero) begin
                // 0 * 0 + 0 = 0 (sign from IEEE rules)
 000092         ow_result = {w_prod_sign & w_sign_c, 8'h00, 23'h0};
 004596     end else if (w_prod_is_zero) begin
                // 0 * X + C = C (pass-through addend when product is zero)
 004596         ow_result = i_c;
 000802     end else if (w_c_eff_zero) begin
                // A * B + 0 = A * B (product only, extend to FP32)
 000802         ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_ext[22:0]};
 000738     end else if (w_sum_abs == 48'h0) begin
                // Exact zero result: IEEE 754 round-to-nearest gives +0
                // (Exception: both operands negative gives -0, but that's handled by
                // the zero product cases above)
 000738         ow_result = 32'h0;  // Positive zero
%000000     end else if (w_overflow_cond) begin
%000000         ow_result = {w_result_sign, 8'hFF, 23'h0};  // Overflow to inf
%000000         ow_overflow = 1'b1;
%000000     end else if (w_underflow_cond) begin
%000000         ow_result = {w_result_sign, 8'h00, 23'h0};  // Underflow to zero
%000000         ow_underflow = 1'b1;
            end
        end
        
        endmodule
        
