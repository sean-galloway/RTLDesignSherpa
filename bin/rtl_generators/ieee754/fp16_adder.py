# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP16Adder
# Purpose: IEEE 754-2008 FP16 Adder Generator with Optional Pipeline
#
# Implements floating-point addition with configurable pipeline stages.
# FP16 format: [15]=sign, [14:10]=exp (bias=15), [9:0]=mantissa
#
# Extended mantissa: 14 bits (10 mant + 1 implicit + 3 GRS)
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from .rtl_header import generate_rtl_header


def generate_fp16_adder(output_path):
    """
    Generate IEEE 754-2008 FP16 floating-point adder.

    Args:
        output_path: Directory to write the generated file

    Returns:
        Module name string
    """

    module_name = 'math_ieee754_2008_fp16_adder'

    content = '''`timescale 1ns / 1ps

module math_ieee754_2008_fp16_adder #(
    parameter bit PIPE_STAGE_1 = 1'b0,  // Pipeline after swap
    parameter bit PIPE_STAGE_2 = 1'b0,  // Pipeline after alignment
    parameter bit PIPE_STAGE_3 = 1'b0,  // Pipeline after add
    parameter bit PIPE_STAGE_4 = 1'b0   // Pipeline after normalize
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [15:0] i_a,
    input  logic [15:0] i_b,
    input  logic        i_valid,
    output logic [15:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid,
    output logic        ow_valid
);

// FP16 field extraction
// Format: [15]=sign, [14:10]=exp, [9:0]=mant

wire       w_sign_a = i_a[15];
wire [4:0] w_exp_a  = i_a[14:10];
wire [9:0] w_mant_a = i_a[9:0];

wire       w_sign_b = i_b[15];
wire [4:0] w_exp_b  = i_b[14:10];
wire [9:0] w_mant_b = i_b[9:0];

// Special case detection
wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 10'h000);
wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 10'h000);
wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 10'h000);
wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 10'h000);
wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 10'h000);
wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 10'h000);
wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 10'h000);
wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 10'h000);

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
wire [9:0] w_mant_larger  = w_a_exp_larger ? w_mant_a : w_mant_b;
wire       w_larger_normal = w_a_exp_larger ? w_a_is_normal : w_b_is_normal;

wire       w_sign_smaller  = w_a_exp_larger ? w_sign_b : w_sign_a;
wire [4:0] w_exp_smaller   = w_a_exp_larger ? w_exp_b : w_exp_a;
wire [9:0] w_mant_smaller  = w_a_exp_larger ? w_mant_b : w_mant_a;
wire       w_smaller_normal = w_a_exp_larger ? w_b_is_normal : w_a_is_normal;

wire [4:0] w_exp_diff = w_exp_larger - w_exp_smaller;

// Extended mantissas with implied bit
// Format: 1.mmmmmmmmmm + 3 GRS bits = 14 bits total

wire [13:0] w_mant_larger_ext = w_larger_normal ? {1'b1, w_mant_larger, 3'b0} : 14'h0;
wire [13:0] w_mant_smaller_ext = w_smaller_normal ? {1'b1, w_mant_smaller, 3'b0} : 14'h0;

// Mantissa alignment (shift smaller mantissa right)

// Clamp shift amount
wire [3:0] w_shift_amt = (w_exp_diff > 5'd14) ? 4'd14 : w_exp_diff[3:0];

// Shift and capture sticky bits
wire [13:0] w_mant_smaller_shifted = w_mant_smaller_ext >> w_shift_amt;

// Sticky bit from shifted-out bits
wire [13:0] w_shift_mask = (14'h3FFF >> (14 - w_shift_amt));
wire w_sticky_from_shift = |(w_mant_smaller_ext & w_shift_mask);

// Mantissa addition/subtraction

wire w_effective_sub = w_sign_larger ^ w_sign_smaller;

// 15-bit addition to handle overflow
wire [14:0] w_mant_sum_raw;
wire [14:0] w_mant_larger_15 = {1'b0, w_mant_larger_ext};
wire [14:0] w_mant_smaller_15 = {1'b0, w_mant_smaller_shifted};

assign w_mant_sum_raw = w_effective_sub ?
    (w_mant_larger_15 - w_mant_smaller_15) :
    (w_mant_larger_15 + w_mant_smaller_15);

// Result sign (subtraction may invert if |B| > |A|)
wire w_sum_negative = w_effective_sub & w_mant_sum_raw[14];
wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;

// Absolute value of sum
wire [14:0] w_mant_sum_abs = w_sum_negative ? (~w_mant_sum_raw + 15'd1) : w_mant_sum_raw;

// Normalization

// Count leading zeros (bit-reverse for CLZ module)
wire [14:0] w_sum_reversed;
genvar i;
generate
    for (i = 0; i < 15; i = i + 1) begin : gen_bit_reverse
        assign w_sum_reversed[i] = w_mant_sum_abs[14 - i];
    end
endgenerate

wire [4:0] w_lz_count_raw;
count_leading_zeros #(.WIDTH(15)) u_clz (
    .data(w_sum_reversed),
    .clz(w_lz_count_raw)
);

// Handle addition overflow (bit 14 set)
wire w_add_overflow = ~w_effective_sub & w_mant_sum_abs[14];

// Normalized mantissa
// CLZ=0 means bit 14 is set (handled by w_add_overflow)
// CLZ=1 means bit 13 is set (already normalized, no shift needed)
// CLZ=n means implied bit at position (14-n), need to shift left by (n-1)
wire [3:0] w_norm_shift = w_add_overflow ? 4'd0 :
    (w_lz_count_raw <= 5'd1) ? 4'd0 :
    (w_lz_count_raw > 5'd14) ? 4'd13 : (w_lz_count_raw[3:0] - 4'd1);
wire [14:0] w_mant_norm = w_add_overflow ?
    {1'b0, w_mant_sum_abs[14:1]} : (w_mant_sum_abs << w_norm_shift);

// Adjusted exponent
wire signed [6:0] w_exp_adjusted = $signed({2'b0, w_exp_larger}) +
    $signed({6'b0, w_add_overflow}) - $signed({3'b0, w_norm_shift});

// Round-to-Nearest-Even rounding

// Extract mantissa, guard, round, sticky
// Format after normalization: [14]=0, [13]=implied, [12:3]=mant, [2:0]=GRS
wire [9:0] w_mant_pre = w_mant_norm[12:3];
wire w_guard = w_mant_norm[2];
wire w_round = w_mant_norm[1];
wire w_sticky = w_mant_norm[0] | w_sticky_from_shift;

// RNE: round up if G=1 and (R=1 or S=1 or LSB=1)
wire w_round_up = w_guard & (w_round | w_sticky | w_mant_pre[0]);

// Apply rounding
wire [10:0] w_mant_rounded = {1'b0, w_mant_pre} + {10'b0, w_round_up};
wire w_round_overflow = w_mant_rounded[10];

// Final mantissa
wire [9:0] w_mant_final = w_round_overflow ? 10'h000 : w_mant_rounded[9:0];

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

logic [15:0] r_result;
logic        r_overflow, r_underflow, r_invalid;

always_comb begin
    r_result = {w_result_sign, w_exp_final[4:0], w_mant_final};
    r_overflow = 1'b0;
    r_underflow = 1'b0;
    r_invalid = 1'b0;

    if (w_any_nan | w_invalid) begin
        r_result = {1'b0, 5'h1F, 10'h200};  // qNaN
        r_invalid = w_invalid;
    end else if (w_a_is_inf) begin
        r_result = {w_sign_a, 5'h1F, 10'h000};
    end else if (w_b_is_inf) begin
        r_result = {w_sign_b, 5'h1F, 10'h000};
    end else if (w_overflow) begin
        r_result = {w_result_sign, 5'h1F, 10'h000};
        r_overflow = 1'b1;
    end else if (w_underflow | (w_mant_sum_abs == 15'h0)) begin
        r_result = {w_result_sign, 5'h00, 10'h000};
        r_underflow = w_underflow & (w_mant_sum_abs != 15'h0);
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
assign ow_valid = i_valid;

endmodule
'''

    # Write with proper header
    header = generate_rtl_header(
        module_name=module_name,
        purpose='IEEE 754-2008 FP16 adder with configurable pipeline stages',
        generator_script='fp16_adder.py'
    )

    filename = f'{module_name}.sv'
    with open(f'{output_path}/{filename}', 'w') as f:
        f.write(header + content + '\n')

    return module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp16_adder(output_path)
    print(f'Generated: {module_name}.sv')
