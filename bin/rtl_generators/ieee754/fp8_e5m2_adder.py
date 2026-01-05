# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E5M2Adder
# Purpose: FP8 E5M2 Adder Generator
#
# Implements floating-point addition for FP8 E5M2 format.
# FP8 E5M2: [7]=sign, [6:2]=exp (bias=15), [1:0]=mantissa
#
# Extended mantissa: 6 bits (2 mant + 1 implicit + 3 GRS)
#
# Note: E5M2 HAS infinity! exp=31, mant=0 is infinity
# NaN: exp=31, mant!=0
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from .rtl_header import generate_rtl_header


def generate_fp8_e5m2_adder(output_path):
    """
    Generate FP8 E5M2 floating-point adder.

    Args:
        output_path: Directory to write the generated file

    Returns:
        Module name string
    """

    module_name = 'math_fp8_e5m2_adder'

    content = '''`timescale 1ns / 1ps

module math_fp8_e5m2_adder (
    input  logic [7:0] i_a,
    input  logic [7:0] i_b,
    output logic [7:0] ow_result,
    output logic       ow_overflow,
    output logic       ow_underflow,
    output logic       ow_invalid
);

// FP8 E5M2 field extraction
// Format: [7]=sign, [6:2]=exp, [1:0]=mant

wire       w_sign_a = i_a[7];
wire [4:0] w_exp_a  = i_a[6:2];
wire [1:0] w_mant_a = i_a[1:0];

wire       w_sign_b = i_b[7];
wire [4:0] w_exp_b  = i_b[6:2];
wire [1:0] w_mant_b = i_b[1:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 2'h0);
wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 2'h0);
wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 2'h0);
wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 2'h0);
wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 2'h0);
wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 2'h0);
wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 2'h0);
wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 2'h0);

wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;
wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;
wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;
wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;

// Exponent comparison and operand swap
// Always put larger exponent operand first

wire w_a_exp_larger = (w_exp_a >= w_exp_b);

// Swapped operands (larger exponent first)
wire       w_sign_larger  = w_a_exp_larger ? w_sign_a : w_sign_b;
wire [4:0] w_exp_larger   = w_a_exp_larger ? w_exp_a : w_exp_b;
wire [1:0] w_mant_larger  = w_a_exp_larger ? w_mant_a : w_mant_b;
wire       w_larger_normal = w_a_exp_larger ? w_a_is_normal : w_b_is_normal;

wire       w_sign_smaller  = w_a_exp_larger ? w_sign_b : w_sign_a;
wire [4:0] w_exp_smaller   = w_a_exp_larger ? w_exp_b : w_exp_a;
wire [1:0] w_mant_smaller  = w_a_exp_larger ? w_mant_b : w_mant_a;
wire       w_smaller_normal = w_a_exp_larger ? w_b_is_normal : w_a_is_normal;

wire [4:0] w_exp_diff = w_exp_larger - w_exp_smaller;

// Extended mantissas with implied bit
// Format: 1.mm + 3 GRS bits = 6 bits total

wire [5:0] w_mant_larger_ext = w_larger_normal ? {1'b1, w_mant_larger, 3'b0} : 6'h0;
wire [5:0] w_mant_smaller_ext = w_smaller_normal ? {1'b1, w_mant_smaller, 3'b0} : 6'h0;

// Mantissa alignment (shift smaller mantissa right)

// Clamp shift amount
wire [2:0] w_shift_amt = (w_exp_diff > 5'd6) ? 3'd6 : w_exp_diff[2:0];

// Shift and capture sticky bits
wire [5:0] w_mant_smaller_shifted = w_mant_smaller_ext >> w_shift_amt;

// Sticky bit from shifted-out bits
wire [5:0] w_shift_mask = (6'h3F >> (6 - w_shift_amt));
wire w_sticky_from_shift = |(w_mant_smaller_ext & w_shift_mask);

// Mantissa addition/subtraction

wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

// 7-bit addition to handle overflow
wire [6:0] w_mant_sum_raw;
wire [6:0] w_mant_larger_7 = {1'b0, w_mant_larger_ext};
wire [6:0] w_mant_smaller_7 = {1'b0, w_mant_smaller_shifted};

assign w_mant_sum_raw = w_effective_sub ?
    (w_mant_larger_7 - w_mant_smaller_7) :
    (w_mant_larger_7 + w_mant_smaller_7);

// Result sign (subtraction may invert if |B| > |A|)
wire w_sum_negative = w_effective_sub & w_mant_sum_raw[6];
wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;

// Absolute value of sum
wire [6:0] w_mant_sum_abs = w_sum_negative ? (~w_mant_sum_raw + 7'd1) : w_mant_sum_raw;

// Normalization using priority encoder (simple for 7 bits)

// Find leading one position
wire [2:0] w_lz_count;
assign w_lz_count = w_mant_sum_abs[6] ? 3'd0 :
                    w_mant_sum_abs[5] ? 3'd1 :
                    w_mant_sum_abs[4] ? 3'd2 :
                    w_mant_sum_abs[3] ? 3'd3 :
                    w_mant_sum_abs[2] ? 3'd4 :
                    w_mant_sum_abs[1] ? 3'd5 : 3'd6;

// Handle addition overflow (bit 6 set)
wire w_add_overflow = ~w_effective_sub & w_mant_sum_abs[6];

// Normalized mantissa
// For normal case (bit 5 = 1), lz_count = 1, but no shift needed since implied 1 is at correct position
// For cancellation (bit 4 = 1), lz_count = 2, need shift by 1 to move implied 1 to bit 5
wire [2:0] w_norm_shift = w_add_overflow ? 3'd0 :
    (w_lz_count <= 3'd1) ? 3'd0 : (w_lz_count - 3'd1);
wire [6:0] w_mant_norm = w_add_overflow ?
    {1'b0, w_mant_sum_abs[6:1]} : (w_mant_sum_abs << w_norm_shift);

// Capture sticky bit lost during overflow right-shift
wire w_overflow_lost_sticky = w_add_overflow & w_mant_sum_abs[0];

// Adjusted exponent
wire signed [6:0] w_exp_adjusted = $signed({2'b0, w_exp_larger}) +
    {6'b0, w_add_overflow} - $signed({4'b0, w_norm_shift});

// Round-to-Nearest-Even rounding

// Extract mantissa, guard, round, sticky
// After normalization, implied 1 is at bit 5, mantissa at [4:3], GRS at [2:0]
wire [1:0] w_mant_pre = w_mant_norm[4:3];
wire w_guard = w_mant_norm[2];
wire w_round = w_mant_norm[1];
wire w_sticky = w_mant_norm[0] | w_sticky_from_shift | w_overflow_lost_sticky;

// RNE: round up if G=1 and (R=1 or S=1 or LSB=1)
wire w_round_up = w_guard & (w_round | w_sticky | w_mant_pre[0]);

// Apply rounding
wire [2:0] w_mant_rounded = {1'b0, w_mant_pre} + {2'b0, w_round_up};
wire w_round_overflow = w_mant_rounded[2];

// Final mantissa
wire [1:0] w_mant_final = w_round_overflow ? 2'h0 : w_mant_rounded[1:0];

// Final exponent
wire signed [6:0] w_exp_final = w_exp_adjusted + {6'b0, w_round_overflow};

// Special case handling

wire w_any_nan = w_a_is_nan | w_b_is_nan;
wire w_both_inf = w_a_is_inf & w_b_is_inf;
wire w_inf_sub = w_both_inf & (w_sign_a != w_sign_b);
wire w_invalid = w_inf_sub;

// Overflow: exp > 30
wire w_overflow = ~w_exp_final[6] & (w_exp_final > 7'sd30);

// Underflow: exp < 1
wire w_underflow = w_exp_final[6] | (w_exp_final < 7'sd1);

// Result assembly

logic [7:0] r_result;
logic       r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {w_result_sign, w_exp_final[4:0], w_mant_final};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_any_nan | w_invalid) begin
        r_result = {1'b0, 5'h1F, 2'h1};  // qNaN
        r_invalid = w_invalid;
    end else if (w_a_is_inf) begin
        r_result = {w_sign_a, 5'h1F, 2'h0};
    end else if (w_b_is_inf) begin
        r_result = {w_sign_b, 5'h1F, 2'h0};
    end else if (w_overflow) begin
        r_result = {w_result_sign, 5'h1F, 2'h0};  // Infinity
        r_overflow = 1'b1;
    end else if (w_underflow | (w_mant_sum_abs == 7'h0)) begin
        r_result = {w_result_sign, 5'h00, 2'h0};
        r_underflow = w_underflow & (w_mant_sum_abs != 7'h0);
    end else if (w_a_eff_zero) begin
        r_result = i_b;
    end else if (w_b_eff_zero) begin
        r_result = i_a;
    end
end

// Output assignment
assign ow_result = r_result;
assign ow_overflow = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid = r_invalid;

endmodule
'''

    # Write with proper header
    header = generate_rtl_header(
        module_name=module_name,
        purpose='FP8 E5M2 floating-point adder',
        generator_script='fp8_e5m2_adder.py'
    )

    filename = f'{module_name}.sv'
    with open(f'{output_path}/{filename}', 'w') as f:
        f.write(header + content + '\n')

    return module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e5m2_adder(output_path)
    print(f'Generated: {module_name}.sv')
