# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP32FMA
# Purpose: IEEE 754-2008 FP32 Fused Multiply-Add Generator
#
# Implements FMA: result = (a * b) + c
# Where a, b, c, and result are all FP32.
#
# Key characteristics:
#   - Single rounding at the end (fused operation)
#   - 24x24 mantissa multiplication (48-bit product)
#   - 72-bit wide accumulator for full precision
#   - FTZ (Flush-To-Zero) mode for subnormals by default; full IEEE 754-2008
#     gradual underflow on inputs and outputs when SUBNORMAL_SUPPORT=1
#   - RNE (Round-to-Nearest-Even) rounding
#
# FP32 format: [31]=sign, [30:23]=exp (bias=127), [22:0]=mantissa
#
# Architecture:
#   Stage 1: Field extraction from a, b, c
#   Stage 2: 24x24 Dadda multiply -> 48-bit product
#   Stage 3: Alignment (72-bit operands, barrel shifter)
#   Stage 4: 72-bit Han-Carlson addition
#   Stage 5: Normalization (72-bit CLZ + shift)
#   Stage 6: RNE rounding to FP32
#   Stage 7: Special case handling
#
# Subnormal handling:
#   SUBNORMAL_SUPPORT=0 (default): FTZ. Subnormal inputs are treated as zero
#     and results never subnormal (byte-identical legacy behavior).
#   SUBNORMAL_SUPPORT=1: subnormal operands decode with hidden bit 0 at
#     effective biased exponent 1. The raw (unnormalized) 48-bit product is
#     placed in the accumulator frame at its true position (frame exponent
#     exp_a_adj+exp_b_adj-bias+1 -- equivalent to the legacy needs_norm
#     placement for all-normal operands, and exact for subnormal products,
#     which the normalization CLZ then re-normalizes), so the alignment
#     shift range is unchanged. Every bit the alignment shift drops below
#     the frame folds into a TRUE sticky; on an effective subtract a bare
#     in-frame tie with only align-sticky rounds DOWN (the dropped bits make
#     the exact sum smaller than the in-frame value). When the normalized
#     exponent is below 1 the exact result lies in the subnormal range: the
#     normalized vector is right-shifted onto the subnormal grid with sticky
#     capture and rounded RNE; a rounding carry out of pre-round exponent 0
#     produces min-normal, not a flush (math BUG-004 ruling). ow_underflow
#     asserts only for a tiny after-rounding result that is also inexact.
#     The legacy c=0 product-only shortcut paths (truncated product, FTZ
#     flush) are taken only when SUBNORMAL_SUPPORT=0; at =1 a zero addend
#     flows through the main datapath so a*b+0 rounds exactly once.
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP32FMA(Module):
    """
    Generates IEEE 754-2008 FP32 Fused Multiply-Add.

    Architecture:
    1. FP32 multiplication (24x24 mantissa using Dadda tree)
    2. Align addend with product using exponent difference
    3. 72-bit addition using Han-Carlson structural adder
    4. Normalize result (CLZ + left shift)
    5. Round to FP32 precision (RNE)
    6. Handle special cases (NaN, Inf, Zero, overflow, underflow)

    The 72-bit accumulator provides full precision:
    - 48-bit product mantissa
    - Plus guard bits for alignment
    - Single rounding at end (true fused operation)

    Subnormal handling: FTZ (flush-to-zero) by default, matching the legacy
    datapath bit-for-bit; SUBNORMAL_SUPPORT=1 adds full IEEE 754-2008
    gradual underflow on inputs and outputs (decode at effective exponent
    1-bias, raw product placed at its true frame position, TRUE sticky
    through the alignment shift, subnormal-grid right shift with sticky
    capture and RNE, BUG-004 min-normal carry-out rule).
    """

    module_str = 'math_ieee754_2008_fp32_fma'
    port_str = '''
    input  logic [31:0] i_a,           // FP32 operand A
    input  logic [31:0] i_b,           // FP32 operand B
    input  logic [31:0] i_c,           // FP32 addend
    output logic [31:0] ow_result,     // FP32 result = (a * b) + c
    output logic        ow_overflow,   // Overflow
    output logic        ow_underflow,  // Underflow
    output logic        ow_invalid     // Invalid operation (NaN)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_parameter(self):
        """Inject the SUBNORMAL_SUPPORT parameter into the module header.

        The Param parser cannot carry inline comments, so patch the header
        after start() with the exact declaration (mirrors the adder and
        multiplier families).
        """
        header = self.start_instructions[0]
        old = f'module {self.module_name}(\n'
        new = (f'module {self.module_name} #(\n'
               "    parameter bit SUBNORMAL_SUPPORT = 1'b0  "
               "// 0: FTZ (legacy); 1: IEEE 754-2008 gradual underflow\n) (\n")
        if old not in header:
            raise RuntimeError(f'module header patch failed for {self.module_name}')
        self.start_instructions[0] = header.replace(old, new, 1)

    def generate_field_extraction(self):
        """Extract fields from all FP32 operands."""
        self.comment('FP32 field extraction')
        self.comment('FP32: [31]=sign, [30:23]=exp, [22:0]=mant')
        self.instruction('')

        # Operand A
        self.instruction('wire        w_sign_a = i_a[31];')
        self.instruction('wire [7:0]  w_exp_a  = i_a[30:23];')
        self.instruction('wire [22:0] w_mant_a = i_a[22:0];')
        self.instruction('')

        # Operand B
        self.instruction('wire        w_sign_b = i_b[31];')
        self.instruction('wire [7:0]  w_exp_b  = i_b[30:23];')
        self.instruction('wire [22:0] w_mant_b = i_b[22:0];')
        self.instruction('')

        # Operand C (addend)
        self.instruction('wire        w_sign_c = i_c[31];')
        self.instruction('wire [7:0]  w_exp_c  = i_c[30:23];')
        self.instruction('wire [22:0] w_mant_c = i_c[22:0];')
        self.instruction('')

    def generate_special_case_detection(self):
        """Detect special cases for all operands."""
        self.comment('Special case detection')
        self.instruction('')

        # Operand A
        self.comment('Operand A special cases')
        self.instruction("wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h0);")
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h0);")
        self.instruction("wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h0);")
        self.instruction("wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h0);")
        self.comment('Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1')
        self.comment('only true zeros are effective zero')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('')

        # Operand B
        self.comment('Operand B special cases')
        self.instruction("wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 23'h0);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 23'h0);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 23'h0);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h0);")
        self.comment('Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1')
        self.comment('only true zeros are effective zero')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | (w_b_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('')

        # Operand C
        self.comment('Operand C (addend) special cases')
        self.instruction("wire w_c_is_zero = (w_exp_c == 8'h00) & (w_mant_c == 23'h0);")
        self.instruction("wire w_c_is_subnormal = (w_exp_c == 8'h00) & (w_mant_c != 23'h0);")
        self.instruction("wire w_c_is_inf = (w_exp_c == 8'hFF) & (w_mant_c == 23'h0);")
        self.instruction("wire w_c_is_nan = (w_exp_c == 8'hFF) & (w_mant_c != 23'h0);")
        self.comment('Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1')
        self.comment('only true zeros are effective zero')
        self.instruction('wire w_c_eff_zero = w_c_is_zero | (w_c_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('wire w_c_is_normal = ~w_c_eff_zero & ~w_c_is_inf & ~w_c_is_nan;')
        self.instruction('')

        self.comment('Hidden-bit feeds: 0 for subnormals when SUBNORMAL_SUPPORT=1 (they decode as')
        self.comment('0.mantissa at effective exponent 1-bias). Identical to *_is_normal when')
        self.comment('SUBNORMAL_SUPPORT=0.')
        self.instruction('wire w_a_h1 = w_a_is_normal & (~SUBNORMAL_SUPPORT | ~w_a_is_subnormal);')
        self.instruction('wire w_b_h1 = w_b_is_normal & (~SUBNORMAL_SUPPORT | ~w_b_is_subnormal);')
        self.instruction('wire w_c_h1 = w_c_is_normal & (~SUBNORMAL_SUPPORT | ~w_c_is_subnormal);')
        self.instruction('')

        self.comment('Exponents adjusted for subnormal decode: a subnormal operates at effective')
        self.comment('biased exponent 1. Identical to the raw exponent when SUBNORMAL_SUPPORT=0.')
        self.instruction("wire [7:0] w_exp_a_adj = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ? 8'd1 : w_exp_a;")
        self.instruction("wire [7:0] w_exp_b_adj = (SUBNORMAL_SUPPORT & w_b_is_subnormal) ? 8'd1 : w_exp_b;")
        self.instruction("wire [7:0] w_exp_c_adj = (SUBNORMAL_SUPPORT & w_c_is_subnormal) ? 8'd1 : w_exp_c;")
        self.instruction('')

    def generate_product_computation(self):
        """Generate FP32 product computation (24x24 mantissa multiply)."""
        self.comment('FP32 multiplication: a * b')
        self.instruction('')

        self.comment('Product sign')
        self.instruction('wire w_prod_sign = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Extended mantissas with implied/hidden bit (24-bit).')
        self.comment('At SUBNORMAL_SUPPORT=1 a subnormal decodes as 0.mantissa (hidden bit 0)')
        self.comment('at effective exponent 1; the select folds to the legacy is_normal')
        self.comment('behavior (zero for any non-normal) when SUBNORMAL_SUPPORT=0.')
        self.instruction("wire [23:0] w_mant_a_ext = (w_a_is_normal | (SUBNORMAL_SUPPORT & w_a_is_subnormal)) ? {w_a_h1, w_mant_a} : 24'h0;")
        self.instruction("wire [23:0] w_mant_b_ext = (w_b_is_normal | (SUBNORMAL_SUPPORT & w_b_is_subnormal)) ? {w_b_h1, w_mant_b} : 24'h0;")
        self.instruction('')

        self.comment('24x24 mantissa multiplication using Dadda tree (48-bit product)')
        self.instruction('wire [47:0] w_prod_mant_raw;')
        self.instruction('math_multiplier_dadda_4to2_024 u_mant_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(w_prod_mant_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Product exponent: exp_a + exp_b - bias (127)')
        self.comment('Use signed arithmetic to correctly handle underflow')
        self.instruction("wire signed [9:0] w_prod_exp_raw = $signed({2'b0, w_exp_a}) + $signed({2'b0, w_exp_b}) - 10'sd127;")
        self.instruction('')

        self.comment('Normalization detection (product >= 2.0)')
        self.comment('With 24x24 multiply: 1.xxx * 1.yyy = 01.xxx or 1x.xxx')
        self.comment('Check bit[47] for overflow (result >= 2.0)')
        self.instruction('wire w_prod_needs_norm = w_prod_mant_raw[47];')
        self.instruction('')

        self.comment('Normalized product exponent (add 1 if needs normalization)')
        self.instruction("wire signed [9:0] w_prod_exp = w_prod_exp_raw + {9'b0, w_prod_needs_norm};")
        self.instruction('')

        self.comment('Normalized 48-bit product mantissa')
        self.comment('Shift right by 1 if overflow, keeping bit[47] as implied 1')
        self.instruction('wire [47:0] w_prod_mant_norm = w_prod_needs_norm ?')
        self.instruction('    w_prod_mant_raw : {w_prod_mant_raw[46:0], 1\'b0};')
        self.instruction('')

        self.comment('-' * 77)
        self.comment('SUBNORMAL_SUPPORT=1 product frame placement')
        self.comment('')
        self.comment('With a subnormal operand the raw 48-bit product can fall below the')
        self.comment('legacy needs_norm normalization range. The raw product is therefore')
        self.comment('placed in the accumulator frame at its TRUE (unnormalized) position,')
        self.comment('at frame exponent exp_a_adj + exp_b_adj - bias + 1 (bit 71 of the')
        self.comment('frame carries 2^(frame_exp-127), so the raw significand product maps')
        self.comment('exactly for both normalization cases); the normalization CLZ then')
        self.comment('left-shifts it into [1,2) with the matching exponent debit. For')
        self.comment('all-normal operands this placement is bit-equivalent to the legacy')
        self.comment('{needs_norm shift, w_prod_exp} pair (same value at every frame bit,')
        self.comment('one position lower, compensated by one extra LZ count). The selects')
        self.comment('below fold to the legacy signals when SUBNORMAL_SUPPORT=0.')
        self.comment('-' * 77)
        self.instruction("wire signed [9:0] w_prod_exp_raw_adj = $signed({2'b0, w_exp_a_adj}) + $signed({2'b0, w_exp_b_adj}) - 10'sd127;")
        self.instruction("wire signed [9:0] w_prod_exp_x = SUBNORMAL_SUPPORT ? (w_prod_exp_raw_adj + 10'sd1) : w_prod_exp;")
        self.instruction('wire [47:0] w_prod_mant_x = SUBNORMAL_SUPPORT ? w_prod_mant_raw : w_prod_mant_norm;')
        self.instruction('')

    def generate_addend_alignment(self):
        """Generate addend alignment logic for 72-bit accumulator."""
        self.comment('Addend (c) alignment')
        self.comment('Extend both product and addend to 72 bits for full precision')
        self.instruction('')

        self.comment('Extended addend mantissa with implied/hidden bit (24-bit)')
        self.comment('Same subnormal decode as the product operands')
        self.instruction("wire [23:0] w_mant_c_ext = (w_c_is_normal | (SUBNORMAL_SUPPORT & w_c_is_subnormal)) ? {w_c_h1, w_mant_c} : 24'h0;")
        self.instruction('')

        self.comment('Exponent difference for alignment')
        self.comment('w_prod_exp_x is signed, w_exp_c_adj is unsigned; sign-extend product exp for comparison')
        self.instruction("wire signed [10:0] w_prod_exp_ext = {{1{w_prod_exp_x[9]}}, w_prod_exp_x};  // Sign-extend")
        self.instruction("wire signed [10:0] w_exp_c_ext = {3'b0, w_exp_c_adj};  // Zero-extend (always positive)")
        self.instruction('wire signed [10:0] w_exp_diff = w_prod_exp_ext - w_exp_c_ext;')
        self.instruction('')

        self.comment('Determine which operand has larger exponent')
        self.instruction('wire w_prod_exp_larger = w_exp_diff >= 0;')
        self.instruction("wire [10:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff : (~w_exp_diff + 11'd1);")
        self.instruction('')

        self.comment('Clamp shift amount to prevent over-shifting (72-bit max)')
        self.instruction("wire [6:0] w_shift_clamped = (w_shift_amt > 11'd72) ? 7'd72 : w_shift_amt[6:0];")
        self.instruction('')

        self.comment('Extended mantissas for addition (72 bits)')
        self.comment('Product: 48-bit mantissa extended to 72 bits')
        self.comment('Addend: 24-bit mantissa extended to 72 bits')
        self.instruction("wire [71:0] w_prod_mant_72 = {w_prod_mant_x, 24'b0};")
        self.instruction("wire [71:0] w_c_mant_72    = {w_mant_c_ext, 48'b0};")
        self.instruction('')

        self.comment('SUBNORMAL_SUPPORT=1: TRUE sticky through the alignment shift. Every')
        self.comment('bit of the smaller exponent operand that the right shift drops below')
        self.comment('the frame folds into this sticky (the clamped shift == width makes the')
        self.comment('mask all-ones, so the whole-operand-dropped case folds in for free).')
        self.comment('The legacy datapath dropped these bits silently; this is constant 0')
        self.comment('when SUBNORMAL_SUPPORT=0, so the =0 behavior is byte-identical.')
        self.instruction("wire [71:0] w_align_mask = (72'h000000000000000001 << w_shift_clamped) - 72'h000000000000000001;")
        self.instruction('wire [71:0] w_align_sticky_vec = (w_prod_exp_larger ? w_c_mant_72 : w_prod_mant_72) & w_align_mask;')
        self.instruction('wire        w_align_sticky = SUBNORMAL_SUPPORT & (|w_align_sticky_vec);')
        self.instruction('')

        self.comment('Aligned mantissas')
        self.instruction('wire [71:0] w_mant_larger, w_mant_smaller_shifted;')
        self.instruction('wire        w_sign_larger, w_sign_smaller;')
        self.instruction('wire signed [10:0] w_exp_result_pre;')
        self.instruction('')

        self.comment('Select aligned operands based on exponent comparison')
        self.comment('Smaller exponent operand gets right-shifted for alignment')
        self.instruction('assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_72 : w_c_mant_72;')
        self.instruction('assign w_mant_smaller_shifted = w_prod_exp_larger ?')
        self.instruction('    (w_c_mant_72 >> w_shift_clamped) : (w_prod_mant_72 >> w_shift_clamped);')
        self.instruction('assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;')
        self.instruction('assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;')
        self.instruction('assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp_ext : w_exp_c_ext;')
        self.instruction('')

    def generate_addition(self):
        """Generate the 72-bit addition using Han-Carlson structural adder."""
        self.comment('72-bit Addition using Han-Carlson structural adder')
        self.instruction('')

        self.comment('Effective operation: add or subtract based on signs')
        self.instruction('wire w_effective_sub = w_sign_larger ^ w_sign_smaller;')
        self.instruction('')

        self.comment('For subtraction, invert smaller operand (two\'s complement: ~B + 1)')
        self.comment('The +1 is handled via carry-in to the adder')
        self.instruction('wire [71:0] w_adder_b = w_effective_sub ? ~w_mant_smaller_shifted : w_mant_smaller_shifted;')
        self.instruction('')

        self.comment('72-bit Han-Carlson structural adder')
        self.instruction('wire [71:0] w_adder_sum;')
        self.instruction('wire        w_adder_cout;')
        self.instruction('math_adder_han_carlson_072 u_wide_adder (')
        self.instruction('    .i_a(w_mant_larger),')
        self.instruction('    .i_b(w_adder_b),')
        self.instruction('    .i_cin(w_effective_sub),  // +1 for two\'s complement subtraction')
        self.instruction('    .ow_sum(w_adder_sum),')
        self.instruction('    .ow_cout(w_adder_cout)')
        self.instruction(');')
        self.instruction('')

        self.comment('Result sign determination')
        self.comment('For subtraction: if no carry out, result is negative (A < B)')
        self.comment('For addition: carry out means magnitude overflow (need right shift)')
        self.instruction('wire w_sum_negative = w_effective_sub & ~w_adder_cout;')
        self.instruction('wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;')
        self.instruction('')

        self.comment('Absolute value of result')
        self.comment('If negative (subtraction with A < B), need to negate the result')
        self.instruction('wire [71:0] w_negated_sum;')
        self.instruction('wire        w_neg_cout;')
        self.instruction('math_adder_han_carlson_072 u_negate_adder (')
        self.instruction('    .i_a(~w_adder_sum),')
        self.instruction("    .i_b(72'h0),")
        self.instruction("    .i_cin(1'b1),  // ~sum + 1 = -sum")
        self.instruction('    .ow_sum(w_negated_sum),')
        self.instruction('    .ow_cout(w_neg_cout)')
        self.instruction(');')
        self.instruction('')

        self.comment('Handle addition overflow (carry out for same-sign addition)')
        self.comment('When addition overflows, prepend carry bit and shift right')
        self.instruction('wire w_add_overflow = ~w_effective_sub & w_adder_cout;')
        self.instruction('wire [71:0] w_sum_with_carry = {w_adder_cout, w_adder_sum[71:1]};  // Right shift, prepend carry')
        self.instruction('')

        self.comment('Select appropriate absolute value')
        self.instruction('wire [71:0] w_sum_abs = w_sum_negative ? w_negated_sum :')
        self.instruction('                        w_add_overflow ? w_sum_with_carry : w_adder_sum;')
        self.instruction('')

    def generate_normalization(self):
        """Generate normalization logic with 72-bit CLZ."""
        self.comment('Normalization')
        self.instruction('')

        self.comment('Count leading zeros for normalization')
        self.comment('count_leading_zeros counts from the MSB (fixed by d62b794d; the old')
        self.comment('module counted trailing zeros and needed a bit-reverse wrapper here)')
        self.comment('For WIDTH=72, clz output is $clog2(72)+1 = 8 bits (0-72 range)')
        self.instruction('')

        self.instruction('wire [7:0] w_lz_count_raw;')
        self.instruction('count_leading_zeros #(.WIDTH(72)) u_clz (')
        self.instruction('    .data(w_sum_abs),')
        self.instruction('    .clz(w_lz_count_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Clamp LZ count to 7 bits for shift (max useful shift is 71)')
        self.instruction("wire [6:0] w_lz_count = (w_lz_count_raw > 8'd71) ? 7'd71 : w_lz_count_raw[6:0];")
        self.instruction('')

        self.comment('Normalized mantissa (shift left by LZ count)')
        self.instruction('wire [71:0] w_mant_normalized = w_sum_abs << w_lz_count;')
        self.instruction('')

        self.comment('Adjusted exponent')
        self.comment('exp_result_pre is already signed 11-bit')
        self.instruction("wire signed [10:0] w_exp_adjusted = w_exp_result_pre - $signed({3'b0, w_lz_count_raw}) + {10'b0, w_add_overflow};")
        self.instruction('')

    def generate_rounding_and_packing(self):
        """Generate rounding and FP32 packing."""
        self.comment('Round-to-Nearest-Even and FP32 packing')
        self.instruction('')

        self.comment('-' * 77)
        self.comment('Gradual-underflow result path (SUBNORMAL_SUPPORT=1 only)')
        self.comment('')
        self.comment('When the fully normalized exponent is below 1 the exact result lies')
        self.comment('in the subnormal range: right-shift the normalized 72-bit vector onto')
        self.comment('the subnormal grid (exponent 1-bias) with TRUE sticky capture (the')
        self.comment('clamped shift == width makes the mask all-ones, so the shift keeps')
        self.comment('every dropped bit as sticky and leaves guard=0, rounding to zero),')
        self.comment('then round RNE exactly as on the normal path. The alignment sticky')
        self.comment('from above folds into the sticky as well -- the left normalization')
        self.comment('shift loses nothing, and bits the alignment dropped belong to the')
        self.comment('exact sum regardless of which of the two shifts moved them. With')
        self.comment('SUBNORMAL_SUPPORT=0 w_subnorm_active is constant 0 and every select')
        self.comment('below folds to the legacy signal.')
        self.comment('-' * 77)
        self.instruction("wire w_subnorm_active = SUBNORMAL_SUPPORT & (w_exp_adjusted < 11'sd1);")
        self.instruction("wire signed [10:0] w_sub_shift_s = 11'sd1 - w_exp_adjusted;  // >= 1 when active")
        self.instruction("wire w_sub_clamp = (w_sub_shift_s > 11'sd72);")
        self.instruction("wire [6:0] w_sub_shift = w_sub_clamp ? 7'd72 : w_sub_shift_s[6:0];")
        self.instruction("wire [71:0] w_sub_mask = (72'h000000000000000001 << w_sub_shift) - 72'h000000000000000001;")
        self.instruction('wire [71:0] w_mant_rnd = w_subnorm_active ? (w_mant_normalized >> w_sub_shift) : w_mant_normalized;')
        self.instruction('wire w_subnorm_shift_sticky = w_subnorm_active & (|(w_mant_normalized & w_sub_mask));')
        self.instruction('')

        self.comment('Extract 23-bit mantissa with guard, round, sticky')
        self.comment('Bit 71 is the implied 1 (not stored), bits [70:48] are the 23-bit mantissa')
        self.instruction('wire [22:0] w_mant_23 = w_mant_rnd[70:48];')
        self.instruction('wire w_guard  = w_mant_rnd[47];')
        self.instruction('wire w_round  = w_mant_rnd[46];')
        self.comment('Sticky from the rounding vector itself plus the two TRUE-sticky')
        self.comment('sources (subnormal-grid shift mask, alignment shift drops)')
        self.instruction('wire w_sticky_core = (|w_mant_rnd[45:0]) | w_subnorm_shift_sticky;')
        self.instruction('wire w_sticky = w_sticky_core | w_align_sticky;')
        self.instruction('')

        self.comment('RNE rounding decision')
        self.comment('Round up iff guard=1 AND (round | sticky | LSB). With SUBNORMAL_SUPPORT=1')
        self.comment('the align-sticky enters with its sign: on an effective ADD the dropped')
        self.comment('bits make the exact sum LARGER than the in-frame value (tie breaks')
        self.comment('UP like any sticky); on an effective SUBTRACT they make it SMALLER,')
        self.comment('so a bare in-frame tie with only align-sticky must round DOWN -- the')
        self.comment('exact value sits just below the tie point regardless of the kept LSB.')
        self.comment('w_dropped_tie is constant 0 when SUBNORMAL_SUPPORT=0 (legacy RNE).')
        self.instruction('wire w_dropped_tie = SUBNORMAL_SUPPORT & w_align_sticky & w_effective_sub &')
        self.instruction("    ~w_round & ~w_sticky_core;")
        self.instruction('wire w_round_up = w_guard & ~w_dropped_tie &')
        self.instruction("    (w_round | w_sticky_core | w_mant_23[0] | (w_align_sticky & ~w_effective_sub));")
        self.instruction('')

        self.comment('Apply rounding')
        self.instruction("wire [23:0] w_mant_rounded = {1'b0, w_mant_23} + {23'b0, w_round_up};")
        self.instruction('wire w_round_overflow = w_mant_rounded[23];')
        self.instruction('')

        self.comment('Final mantissa (23 bits)')
        self.comment('When rounding overflows, mantissa becomes 0 (1.111...1 -> 10.0 -> 1.0 with exp+1)')
        self.instruction("wire [22:0] w_mant_final = w_round_overflow ? 23'h000000 : w_mant_rounded[22:0];")
        self.instruction('')

        self.comment('Final exponent with rounding adjustment')
        self.comment('Exponent base is 0 on the subnormal path: a rounding carry out of')
        self.comment('pre-round exponent 0 yields min-normal, not a flush (math BUG-004')
        self.comment('ruling); such a carry takes the normal default branch in the result')
        self.comment('assembly below, so it neither flushes nor flags underflow')
        self.instruction("wire signed [10:0] w_exp_base = w_subnorm_active ? 11'sd0 : w_exp_adjusted;")
        self.instruction("wire signed [10:0] w_exp_final = w_exp_base + {10'b0, w_round_overflow};")
        self.instruction('')

    def generate_special_case_handling(self):
        """Generate special case result selection."""
        self.comment('Special case handling')
        self.instruction('')

        self.comment('Any NaN input')
        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;')
        self.instruction('')

        self.comment('Invalid operations: 0 * inf or inf - inf')
        self.instruction('wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;')
        self.instruction('wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero;')
        self.instruction('wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);')
        self.instruction('wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);')
        self.instruction('wire w_invalid = w_invalid_mul | w_invalid_add;')
        self.instruction('')

        self.comment('Overflow and underflow detection')
        self.comment('Use signed comparison - negative exponent is underflow, not overflow')
        self.instruction("wire w_overflow_cond = ~w_exp_final[10] & (w_exp_final > 11'sd254);")
        self.instruction("wire w_underflow_cond = w_exp_final[10] | (w_exp_final < 11'sd1);")
        self.instruction('')
        self.comment('Product-only overflow/underflow (for c=0 shortcut path)')
        self.comment('w_prod_exp is now signed; use signed comparison')
        self.instruction("wire w_prod_overflow = (w_prod_exp > 10'sd254);")
        self.instruction("wire w_prod_underflow = (w_prod_exp < 10'sd1);")
        self.instruction('')

    def generate_result_assembly(self):
        """Generate final result assembly."""
        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    // Default: normal result')
        self.instruction('    ow_result = {w_result_sign, w_exp_final[7:0], w_mant_final};')
        self.instruction("    ow_overflow = 1'b0;")
        self.instruction("    ow_underflow = 1'b0;")
        self.instruction("    ow_invalid = 1'b0;")
        self.instruction('')
        self.instruction('    // Special case priority (highest to lowest)')
        self.instruction('    if (w_any_nan | w_invalid) begin')
        self.instruction("        ow_result = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN")
        self.instruction('        ow_invalid = w_invalid;')
        self.instruction('    end else if (w_prod_is_inf & ~w_c_is_inf) begin')
        self.instruction("        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product infinity")
        self.instruction('    end else if (w_c_is_inf) begin')
        self.instruction("        ow_result = {w_sign_c, 8'hFF, 23'h0};  // Addend infinity")
        self.instruction('    end else if (w_prod_is_zero & w_c_eff_zero) begin')
        self.instruction("        ow_result = {w_prod_sign & w_sign_c, 8'h00, 23'h0};  // 0*b+0 = 0")
        self.instruction('    end else if (w_prod_is_zero) begin')
        self.instruction('        ow_result = i_c;  // 0 * b + c = c')
        self.instruction('    end else if (~SUBNORMAL_SUPPORT & w_c_eff_zero & w_prod_overflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 8'hFF, 23'h0};  // Product overflow to inf")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (~SUBNORMAL_SUPPORT & w_c_eff_zero & w_prod_underflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 8'h00, 23'h0};  // Product underflow to zero")
        self.instruction("        ow_underflow = 1'b1;")
        self.instruction('    end else if (~SUBNORMAL_SUPPORT & w_c_eff_zero) begin')
        self.instruction('        // Product only: a * b + 0 (TRUNCATED product, legacy quirk')
        self.instruction('        // kept bit-for-bit at SUBNORMAL_SUPPORT=0; at =1 a zero')
        self.instruction('        // addend flows through the main datapath so the product')
        self.instruction('        // rounds exactly once)')
        self.instruction('        ow_result = {w_prod_sign, w_prod_exp[7:0], w_prod_mant_norm[46:24]};')
        self.instruction('    end else if (w_overflow_cond) begin')
        self.instruction("        ow_result = {w_result_sign, 8'hFF, 23'h0};  // Overflow to inf")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (w_underflow_cond | (w_sum_abs == 72\'h0)) begin')
        self.instruction('        if (SUBNORMAL_SUPPORT) begin')
        self.instruction('            // Gradual underflow: the rounded subnormal result (or signed')
        self.instruction('            // zero when the rounded result vanishes) comes straight from')
        self.instruction('            // the shifted vector. This branch is only reachable with')
        self.instruction('            // w_exp_final == 0: a rounding carry into min-normal')
        self.instruction('            // (w_exp_final == 1) takes the normal default branch above,')
        self.instruction('            // so the BUG-004 carry-out neither flushes nor flags.')
        self.instruction('            // ow_underflow per IEEE 754: tiny AFTER rounding AND')
        self.instruction('            // inexact. An exact zero sum (in-frame cancellation with')
        self.instruction('            // nothing dropped into the align sticky) flushes to a')
        self.instruction('            // signed zero with no flag -- its exponent bookkeeping is')
        self.instruction('            // meaningless (exp_adjusted = pre - 72 can be >= 1).')
        self.instruction("            if ((w_sum_abs == 72'h0) && !w_align_sticky) begin")
        self.instruction("                ow_result = {w_result_sign, 8'h00, 23'h0};  // exact zero sum")
        self.instruction("                ow_underflow = 1'b0;")
        self.instruction('            end else begin')
        self.instruction('                ow_result = {w_result_sign, w_exp_final[7:0], w_mant_final};')
        self.instruction('                ow_underflow = w_guard | w_round | w_sticky;')
        self.instruction('            end')
        self.instruction('        end else begin')
        self.instruction("            ow_result = {w_result_sign, 8'h00, 23'h0};  // Underflow to zero")
        self.instruction("            ow_underflow = w_underflow_cond & (w_sum_abs != 72'h0);")
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP32 FMA."""
        self.generate_field_extraction()
        self.generate_special_case_detection()
        self.generate_product_computation()
        self.generate_addend_alignment()
        self.generate_addition()
        self.generate_normalization()
        self.generate_rounding_and_packing()
        self.generate_special_case_handling()
        self.generate_result_assembly()

        self.start()
        self.generate_parameter()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP32 Fused Multiply-Add with full precision accumulation',
            generator_script='fp32_fma.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp32_fma(output_path):
    """
    Generate IEEE 754-2008 FP32 FMA.

    Args:
        output_path: Directory to write the generated file

    Returns:
        Module name string
    """
    fma = FP32FMA()
    fma.verilog(output_path)
    return fma.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_fp32_fma(output_path)
    print(f'Generated: {module_name}.sv')
