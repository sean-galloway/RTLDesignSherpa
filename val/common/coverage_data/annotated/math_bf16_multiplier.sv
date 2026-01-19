//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_bf16_multiplier
        // Purpose: Complete BF16 multiplier with special case handling and RNE rounding
        //
        // Documentation: BF16_ARCHITECTURE.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-11-25
        //
        // AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
        // Generator: bin/rtl_generators/bf16/bf16_multiplier.py
        // Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common
        //
        
        `timescale 1ns / 1ps
        
        module math_bf16_multiplier(
%000000     input  logic [15:0] i_a,
%000000     input  logic [15:0] i_b,
%000000     output logic [15:0] ow_result,
%000000     output logic        ow_overflow,
%000000     output logic        ow_underflow,
%000002     output logic        ow_invalid
        );
        
        // BF16 field extraction
        // Format: [15]=sign, [14:7]=exponent, [6:0]=mantissa
        
%000008 wire       w_sign_a = i_a[15];
 000011 wire [7:0] w_exp_a  = i_a[14:7];
%000000 wire [6:0] w_mant_a = i_a[6:0];
        
%000005 wire       w_sign_b = i_b[15];
%000008 wire [7:0] w_exp_b  = i_b[14:7];
%000000 wire [6:0] w_mant_b = i_b[6:0];
        
        // Special value detection
        
        // Zero: exp=0, mant=0
%000004 wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 7'h00);
%000002 wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 7'h00);
        
        // Subnormal: exp=0, mant!=0 (flushed to zero per BF16 convention)
%000000 wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 7'h00);
%000000 wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 7'h00);
        
        // Infinity: exp=FF, mant=0
%000004 wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 7'h00);
%000002 wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 7'h00);
        
        // NaN: exp=FF, mant!=0
%000004 wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 7'h00);
%000002 wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 7'h00);
        
        // Effective zero (includes subnormals in FTZ mode)
%000004 wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
%000002 wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
        
        // Normal number (has implied leading 1)
%000002 wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;
%000002 wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;
        
        // Result sign: XOR of input signs
%000007 wire w_sign_result = w_sign_a ^ w_sign_b;
        
        // Mantissa multiplication (8x8 with Dadda 4:2 tree)
%000000 wire [15:0] w_mant_product;
%000000 wire        w_needs_norm;
%000000 wire [6:0]  w_mant_mult_out;
%000000 wire        w_round_bit;
%000000 wire        w_sticky_bit;
        
        math_bf16_mantissa_mult u_mant_mult (
            .i_mant_a(w_mant_a),
            .i_mant_b(w_mant_b),
            .i_a_is_normal(w_a_is_normal),
            .i_b_is_normal(w_b_is_normal),
            .ow_product(w_mant_product),
            .ow_needs_norm(w_needs_norm),
            .ow_mant_out(w_mant_mult_out),
            .ow_round_bit(w_round_bit),
            .ow_sticky_bit(w_sticky_bit)
        );
        
        // Exponent addition
%000007 wire [7:0] w_exp_sum;
%000000 wire       w_exp_overflow;
%000000 wire       w_exp_underflow;
%000002 wire       w_exp_a_zero, w_exp_b_zero;
%000006 wire       w_exp_a_inf, w_exp_b_inf;
%000006 wire       w_exp_a_nan, w_exp_b_nan;
        
        math_bf16_exponent_adder u_exp_add (
            .i_exp_a(w_exp_a),
            .i_exp_b(w_exp_b),
            .i_norm_adjust(w_needs_norm),
            .ow_exp_out(w_exp_sum),
            .ow_overflow(w_exp_overflow),
            .ow_underflow(w_exp_underflow),
            .ow_a_is_zero(w_exp_a_zero),
            .ow_b_is_zero(w_exp_b_zero),
            .ow_a_is_inf(w_exp_a_inf),
            .ow_b_is_inf(w_exp_b_inf),
            .ow_a_is_nan(w_exp_a_nan),
            .ow_b_is_nan(w_exp_b_nan)
        );
        
        // Round-to-Nearest-Even (RNE) rounding
        // Round up if:
        //   - round_bit=1 AND (sticky_bit=1 OR LSB=1)
        // This implements RNE: ties round to even
        
%000002 wire w_lsb = w_mant_mult_out[0];
%000000 wire w_round_up = w_round_bit & (w_sticky_bit | w_lsb);
        
        // Apply rounding to mantissa
%000000 wire [7:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {7'b0, w_round_up};
        
        // Check for mantissa overflow from rounding (rare)
%000000 wire w_mant_round_overflow = w_mant_rounded[7];
        
        // Final mantissa (7 bits)
%000000 wire [6:0] w_mant_final = w_mant_round_overflow ? 
            7'h00 : w_mant_rounded[6:0];  // Overflow means 1.0 -> needs exp adjust
        
        // Exponent adjustment for rounding overflow
%000007 wire [7:0] w_exp_final = w_mant_round_overflow ? (w_exp_sum + 8'd1) : w_exp_sum;
        
        // Check for exponent overflow after rounding adjustment
%000000 wire w_final_overflow = w_exp_overflow | (w_exp_final == 8'hFF);
        
        // Special case result handling
        
        // NaN propagation: any NaN input produces NaN output
%000002 wire w_any_nan = w_a_is_nan | w_b_is_nan;
        
        // Invalid operation: 0 * inf = NaN
%000002 wire w_invalid_op = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);
        
        // Zero result: either input is (effective) zero
%000004 wire w_result_zero = w_a_eff_zero | w_b_eff_zero;
        
        // Infinity result: either input is infinity (and not invalid)
%000002 wire w_result_inf = (w_a_is_inf | w_b_is_inf) & ~w_invalid_op;
        
        // Final result assembly
        
 000052 always_comb begin
            // Default: normal multiplication result
 000052     ow_result = {w_sign_result, w_exp_final, w_mant_final};
 000052     ow_overflow = 1'b0;
 000052     ow_underflow = 1'b0;
 000052     ow_invalid = 1'b0;
        
            // Special case priority (highest to lowest)
 000014     if (w_any_nan | w_invalid_op) begin
                // NaN result: quiet NaN with sign preserved
 000014         ow_result = {w_sign_result, 8'hFF, 7'h40};  // Canonical qNaN
 000014         ow_invalid = w_invalid_op;
%000000     end else if (w_result_inf | w_final_overflow) begin
                // Infinity result
%000000         ow_result = {w_sign_result, 8'hFF, 7'h00};
%000000         ow_overflow = w_final_overflow & ~w_result_inf;
%000000     end else if (w_result_zero | w_exp_underflow) begin
                // Zero result
%000000         ow_result = {w_sign_result, 8'h00, 7'h00};
%000000         ow_underflow = w_exp_underflow & ~w_result_zero;
            end
        end
        
        endmodule
        
