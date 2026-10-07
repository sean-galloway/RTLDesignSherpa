# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP16FMA
# Purpose: IEEE 754-2008 FP16 Fused Multiply-Add Generator
#
# Implements FMA: result = (a * b) + c
# Where a, b, c, and result are all FP16.
#
# Key characteristics:
#   - Single rounding at the end (fused operation)
#   - 11x11 mantissa multiplication (22-bit product)
#   - 44-bit wide accumulator for full precision
#   - FTZ (Flush-To-Zero) mode for subnormals by default; full IEEE 754-2008
#     gradual underflow on inputs and outputs when SUBNORMAL_SUPPORT=1
#   - RNE (Round-to-Nearest-Even) rounding
#
# FP16 format: [15]=sign, [14:10]=exp (bias=15), [9:0]=mantissa
#
# Architecture:
#   Stage 1: Field extraction from a, b, c
#   Stage 2: 11x11 Dadda multiply -> 22-bit product
#   Stage 3: Alignment (44-bit operands)
#   Stage 4: 44-bit addition
#   Stage 5: Normalization (44-bit CLZ + shift)
#   Stage 6: RNE rounding to FP16
#   Stage 7: Special case handling
#
# Subnormal handling:
#   SUBNORMAL_SUPPORT=0 (default): FTZ. Subnormal inputs are treated as zero
#     and results never subnormal (byte-identical legacy behavior).
#   SUBNORMAL_SUPPORT=1: subnormal operands decode with hidden bit 0 at
#     effective biased exponent 1. The raw (unnormalized) 22-bit product is
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


class FP16FMA(Module):
    """
    Generates IEEE 754-2008 FP16 Fused Multiply-Add.

    Uses 44-bit accumulator for full precision:
    - 22-bit product mantissa
    - Plus guard bits for alignment
    - Single rounding at end (true fused operation)

    Subnormal handling: FTZ (flush-to-zero) by default, matching the legacy
    datapath bit-for-bit; SUBNORMAL_SUPPORT=1 adds full IEEE 754-2008
    gradual underflow on inputs and outputs (decode at effective exponent
    1-bias, raw product placed at its true frame position, TRUE sticky
    through the alignment shift, subnormal-grid right shift with sticky
    capture and RNE, BUG-004 min-normal carry-out rule).
    """

    module_str = 'math_ieee754_2008_fp16_fma'
    port_str = '''
    input  logic [15:0] i_a,           // FP16 operand A
    input  logic [15:0] i_b,           // FP16 operand B
    input  logic [15:0] i_c,           // FP16 addend
    output logic [15:0] ow_result,     // FP16 result = (a * b) + c
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
        """Extract fields from all FP16 operands."""
        self.comment('FP16 field extraction')
        self.comment('FP16: [15]=sign, [14:10]=exp, [9:0]=mant')
        self.instruction('')

        self.instruction('wire       w_sign_a = i_a[15];')
        self.instruction('wire [4:0] w_exp_a  = i_a[14:10];')
        self.instruction('wire [9:0] w_mant_a = i_a[9:0];')
        self.instruction('')

        self.instruction('wire       w_sign_b = i_b[15];')
        self.instruction('wire [4:0] w_exp_b  = i_b[14:10];')
        self.instruction('wire [9:0] w_mant_b = i_b[9:0];')
        self.instruction('')

        self.instruction('wire       w_sign_c = i_c[15];')
        self.instruction('wire [4:0] w_exp_c  = i_c[14:10];')
        self.instruction('wire [9:0] w_mant_c = i_c[9:0];')
        self.instruction('')

    def generate_special_case_detection(self):
        """Detect special cases for all operands."""
        self.comment('Special case detection')
        self.instruction('')

        self.comment('Operand A')
        self.instruction("wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 10'h0);")
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 10'h0);")
        self.instruction("wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 10'h0);")
        self.instruction("wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 10'h0);")
        self.comment('Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1')
        self.comment('only true zeros are effective zero')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('')

        self.comment('Operand B')
        self.instruction("wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 10'h0);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 10'h0);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 10'h0);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 10'h0);")
        self.comment('Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1')
        self.comment('only true zeros are effective zero')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | (w_b_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('')

        self.comment('Operand C (addend)')
        self.instruction("wire w_c_is_zero = (w_exp_c == 5'h00) & (w_mant_c == 10'h0);")
        self.instruction("wire w_c_is_subnormal = (w_exp_c == 5'h00) & (w_mant_c != 10'h0);")
        self.instruction("wire w_c_is_inf = (w_exp_c == 5'h1F) & (w_mant_c == 10'h0);")
        self.instruction("wire w_c_is_nan = (w_exp_c == 5'h1F) & (w_mant_c != 10'h0);")
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
        self.instruction("wire [4:0] w_exp_a_adj = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ? 5'd1 : w_exp_a;")
        self.instruction("wire [4:0] w_exp_b_adj = (SUBNORMAL_SUPPORT & w_b_is_subnormal) ? 5'd1 : w_exp_b;")
        self.instruction("wire [4:0] w_exp_c_adj = (SUBNORMAL_SUPPORT & w_c_is_subnormal) ? 5'd1 : w_exp_c;")
        self.instruction('')

    def generate_product_computation(self):
        """Generate FP16 product computation."""
        self.comment('FP16 multiplication: a * b')
        self.instruction('')

        self.comment('Product sign')
        self.instruction('wire w_prod_sign = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Extended mantissas with implied/hidden bit (11-bit).')
        self.comment('At SUBNORMAL_SUPPORT=1 a subnormal decodes as 0.mantissa (hidden bit 0)')
        self.comment('at effective exponent 1; the select folds to the legacy is_normal')
        self.comment('behavior (zero for any non-normal) when SUBNORMAL_SUPPORT=0.')
        self.instruction("wire [10:0] w_mant_a_ext = (w_a_is_normal | (SUBNORMAL_SUPPORT & w_a_is_subnormal)) ? {w_a_h1, w_mant_a} : 11'h0;")
        self.instruction("wire [10:0] w_mant_b_ext = (w_b_is_normal | (SUBNORMAL_SUPPORT & w_b_is_subnormal)) ? {w_b_h1, w_mant_b} : 11'h0;")
        self.instruction('')

        self.comment('11x11 mantissa multiplication using Dadda tree (22-bit product)')
        self.instruction('wire [21:0] w_prod_mant_raw;')
        self.instruction('math_multiplier_dadda_4to2_011 u_mant_mult (')
        self.instruction('    .i_multiplier(w_mant_a_ext),')
        self.instruction('    .i_multiplicand(w_mant_b_ext),')
        self.instruction('    .ow_product(w_prod_mant_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Product exponent: exp_a + exp_b - bias (15)')
        self.comment('Use signed arithmetic to correctly handle underflow')
        self.instruction("wire signed [6:0] w_prod_exp_raw = $signed({2'b0, w_exp_a}) + $signed({2'b0, w_exp_b}) - 7'sd15;")
        self.instruction('')

        self.comment('Normalization detection (product >= 2.0)')
        self.instruction('wire w_prod_needs_norm = w_prod_mant_raw[21];')
        self.instruction('')

        self.comment('Normalized product exponent')
        self.instruction("wire signed [6:0] w_prod_exp = w_prod_exp_raw + {6'b0, w_prod_needs_norm};")
        self.instruction('')

        self.comment('Normalized 22-bit product mantissa')
        self.instruction('wire [21:0] w_prod_mant_norm = w_prod_needs_norm ?')
        self.instruction('    w_prod_mant_raw : {w_prod_mant_raw[20:0], 1\'b0};')
        self.instruction('')

        self.comment('-' * 77)
        self.comment('SUBNORMAL_SUPPORT=1 product frame placement')
        self.comment('')
        self.comment('With a subnormal operand the raw 22-bit product can fall below the')
        self.comment('legacy needs_norm normalization range. The raw product is therefore')
        self.comment('placed in the accumulator frame at its TRUE (unnormalized) position,')
        self.comment('at frame exponent exp_a_adj + exp_b_adj - bias + 1 (bit 43 of the')
        self.comment('frame carries 2^(frame_exp-bias), so the raw significand product maps')
        self.comment('exactly for both normalization cases); the normalization CLZ then')
        self.comment('left-shifts it into [1,2) with the matching exponent debit. For')
        self.comment('all-normal operands this placement is bit-equivalent to the legacy')
        self.comment('{needs_norm shift, w_prod_exp} pair (same value at every frame bit,')
        self.comment('one position lower, compensated by one extra LZ count). The selects')
        self.comment('below fold to the legacy signals when SUBNORMAL_SUPPORT=0.')
        self.comment('-' * 77)
        self.instruction("wire signed [6:0] w_prod_exp_raw_adj = $signed({2'b0, w_exp_a_adj}) + $signed({2'b0, w_exp_b_adj}) - 7'sd15;")
        self.instruction("wire signed [6:0] w_prod_exp_x = SUBNORMAL_SUPPORT ? (w_prod_exp_raw_adj + 7'sd1) : w_prod_exp;")
        self.instruction('wire [21:0] w_prod_mant_x = SUBNORMAL_SUPPORT ? w_prod_mant_raw : w_prod_mant_norm;')
        self.instruction('')

    def generate_addend_alignment(self):
        """Generate addend alignment logic for 44-bit accumulator."""
        self.comment('Addend (c) alignment')
        self.comment('Extend both product and addend to 44 bits for full precision')
        self.instruction('')

        self.comment('Extended addend mantissa with implied/hidden bit (11-bit)')
        self.comment('Same subnormal decode as the product operands')
        self.instruction("wire [10:0] w_mant_c_ext = (w_c_is_normal | (SUBNORMAL_SUPPORT & w_c_is_subnormal)) ? {w_c_h1, w_mant_c} : 11'h0;")
        self.instruction('')

        self.comment('Exponent difference for alignment')
        self.comment('w_prod_exp_x is signed, w_exp_c_adj is unsigned; sign-extend product exp for comparison')
        self.instruction("wire signed [7:0] w_prod_exp_ext = {{1{w_prod_exp_x[6]}}, w_prod_exp_x};  // Sign-extend")
        self.instruction("wire signed [7:0] w_exp_c_ext = {3'b0, w_exp_c_adj};  // Zero-extend (always positive)")
        self.instruction('wire signed [7:0] w_exp_diff = w_prod_exp_ext - w_exp_c_ext;')
        self.instruction('')

        self.comment('Determine which operand has larger exponent')
        self.instruction('wire w_prod_exp_larger = w_exp_diff >= 0;')
        self.instruction("wire [7:0] w_shift_amt = w_exp_diff >= 0 ? w_exp_diff : (~w_exp_diff + 8'd1);")
        self.instruction('')

        self.comment('Clamp shift amount (44-bit max)')
        self.instruction("wire [5:0] w_shift_clamped = (w_shift_amt > 8'd44) ? 6'd44 : w_shift_amt[5:0];")
        self.instruction('')

        self.comment('Extended mantissas for addition (44 bits)')
        self.instruction("wire [43:0] w_prod_mant_44 = {w_prod_mant_x, 22'b0};")
        self.instruction("wire [43:0] w_c_mant_44    = {w_mant_c_ext, 33'b0};")
        self.instruction('')

        self.comment('SUBNORMAL_SUPPORT=1: TRUE sticky through the alignment shift. Every')
        self.comment('bit of the smaller exponent operand that the right shift drops below')
        self.comment('the frame folds into this sticky (the clamped shift == width makes')
        self.comment('the mask all-ones, so the whole-operand-dropped case folds in for')
        self.comment('free). The legacy datapath dropped these bits silently; this is')
        self.comment('constant 0 when SUBNORMAL_SUPPORT=0, so =0 behavior is byte-identical.')
        self.instruction("wire [43:0] w_align_mask = (44'h000000000001 << w_shift_clamped) - 44'h000000000001;")
        self.instruction('wire [43:0] w_align_sticky_vec = (w_prod_exp_larger ? w_c_mant_44 : w_prod_mant_44) & w_align_mask;')
        self.instruction('wire        w_align_sticky = SUBNORMAL_SUPPORT & (|w_align_sticky_vec);')
        self.instruction('')

        self.comment('Aligned mantissas')
        self.instruction('wire [43:0] w_mant_larger, w_mant_smaller_shifted;')
        self.instruction('wire        w_sign_larger, w_sign_smaller;')
        self.instruction('wire signed [7:0] w_exp_result_pre;')
        self.instruction('')

        self.instruction('assign w_mant_larger = w_prod_exp_larger ? w_prod_mant_44 : w_c_mant_44;')
        self.instruction('assign w_mant_smaller_shifted = w_prod_exp_larger ?')
        self.instruction('    (w_c_mant_44 >> w_shift_clamped) : (w_prod_mant_44 >> w_shift_clamped);')
        self.instruction('assign w_sign_larger  = w_prod_exp_larger ? w_prod_sign : w_sign_c;')
        self.instruction('assign w_sign_smaller = w_prod_exp_larger ? w_sign_c : w_prod_sign;')
        self.instruction('assign w_exp_result_pre = w_prod_exp_larger ? w_prod_exp_ext : w_exp_c_ext;')
        self.instruction('')

    def generate_addition(self):
        """Generate the 44-bit addition."""
        self.comment('44-bit Addition')
        self.instruction('')

        self.instruction('wire w_effective_sub = w_sign_larger ^ w_sign_smaller;')
        self.instruction('')

        self.comment('For subtraction, compute two\'s complement')
        self.instruction('wire [44:0] w_mant_larger_45 = {1\'b0, w_mant_larger};')
        self.instruction('wire [44:0] w_mant_smaller_45 = {1\'b0, w_mant_smaller_shifted};')
        self.instruction('')

        self.instruction('wire [44:0] w_adder_sum = w_effective_sub ?')
        self.instruction('    (w_mant_larger_45 - w_mant_smaller_45) :')
        self.instruction('    (w_mant_larger_45 + w_mant_smaller_45);')
        self.instruction('')

        self.comment('Result sign determination')
        self.instruction('wire w_sum_negative = w_effective_sub & w_adder_sum[44];')
        self.instruction('wire w_result_sign = w_sum_negative ? ~w_sign_larger : w_sign_larger;')
        self.instruction('')

        self.comment('Absolute value of result')
        self.instruction("wire [44:0] w_sum_abs = w_sum_negative ? (~w_adder_sum + 45'd1) : w_adder_sum;")
        self.instruction('')

        self.comment('Handle addition overflow')
        self.instruction('wire w_add_overflow = ~w_effective_sub & w_sum_abs[44];')
        self.instruction('wire [44:0] w_sum_adjusted = w_add_overflow ? {1\'b0, w_sum_abs[44:1]} : w_sum_abs;')
        self.instruction('')

    def generate_normalization(self):
        """Generate normalization logic."""
        self.comment('Normalization')
        self.instruction('')

        self.comment('Count leading zeros (count_leading_zeros counts from the MSB)')
        self.instruction('wire [43:0] w_sum_44 = w_sum_adjusted[43:0];')
        self.instruction('')

        self.instruction('wire [6:0] w_lz_count_raw;')
        self.instruction('count_leading_zeros #(.WIDTH(44)) u_clz (')
        self.instruction('    .data(w_sum_44),')
        self.instruction('    .clz(w_lz_count_raw)')
        self.instruction(');')
        self.instruction('')

        self.comment('Clamp LZ count')
        self.instruction("wire [5:0] w_lz_count = (w_lz_count_raw > 7'd43) ? 6'd43 : w_lz_count_raw[5:0];")
        self.instruction('')

        self.comment('Normalized mantissa')
        self.instruction('wire [43:0] w_mant_normalized = w_sum_44 << w_lz_count;')
        self.instruction('')

        self.comment('Adjusted exponent')
        self.comment('exp_result_pre is already signed 8-bit')
        self.instruction("wire signed [7:0] w_exp_adjusted = w_exp_result_pre -")
        self.instruction("    $signed({1'b0, w_lz_count_raw}) + {7'b0, w_add_overflow};")
        self.instruction('')

    def generate_rounding_and_packing(self):
        """Generate rounding and FP16 packing."""
        self.comment('Round-to-Nearest-Even and FP16 packing')
        self.instruction('')

        self.comment('-' * 77)
        self.comment('Gradual-underflow result path (SUBNORMAL_SUPPORT=1 only)')
        self.comment('')
        self.comment('When the fully normalized exponent is below 1 the exact result lies')
        self.comment('in the subnormal range: right-shift the normalized 44-bit vector onto')
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
        self.instruction("wire w_subnorm_active = SUBNORMAL_SUPPORT & (w_exp_adjusted < 8'sd1);")
        self.instruction("wire signed [7:0] w_sub_shift_s = 8'sd1 - w_exp_adjusted;  // >= 1 when active")
        self.instruction("wire w_sub_clamp = (w_sub_shift_s > 8'sd44);")
        self.instruction("wire [5:0] w_sub_shift = w_sub_clamp ? 6'd44 : w_sub_shift_s[5:0];")
        self.instruction("wire [43:0] w_sub_mask = (44'h000000000001 << w_sub_shift) - 44'h000000000001;")
        self.instruction('wire [43:0] w_mant_rnd = w_subnorm_active ? (w_mant_normalized >> w_sub_shift) : w_mant_normalized;')
        self.instruction('wire w_subnorm_shift_sticky = w_subnorm_active & (|(w_mant_normalized & w_sub_mask));')
        self.instruction('')

        self.comment('Extract 10-bit mantissa with guard, round, sticky')
        self.comment('Bit 43 is implied 1, bits [42:33] are the 10-bit mantissa')
        self.instruction('wire [9:0] w_mant_10 = w_mant_rnd[42:33];')
        self.instruction('wire w_guard  = w_mant_rnd[32];')
        self.instruction('wire w_round  = w_mant_rnd[31];')
        self.comment('Sticky from the rounding vector itself plus the two TRUE-sticky')
        self.comment('sources (subnormal-grid shift mask, alignment shift drops)')
        self.instruction('wire w_sticky_core = (|w_mant_rnd[30:0]) | w_subnorm_shift_sticky;')
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
        self.instruction("    (w_round | w_sticky_core | w_mant_10[0] | (w_align_sticky & ~w_effective_sub));")
        self.instruction('')

        self.comment('Apply rounding')
        self.instruction("wire [10:0] w_mant_rounded = {1'b0, w_mant_10} + {10'b0, w_round_up};")
        self.instruction('wire w_round_overflow = w_mant_rounded[10];')
        self.instruction('')

        self.comment('Final mantissa')
        self.comment('When rounding overflows, mantissa becomes 0 (1.111...1 -> 10.0 -> 1.0 with exp+1)')
        self.instruction("wire [9:0] w_mant_final = w_round_overflow ? 10'h000 : w_mant_rounded[9:0];")
        self.instruction('')

        self.comment('Final exponent')
        self.comment('Exponent base is 0 on the subnormal path: a rounding carry out of')
        self.comment('pre-round exponent 0 yields min-normal, not a flush (math BUG-004')
        self.comment('ruling); such a carry takes the normal default branch in the result')
        self.comment('assembly below, so it neither flushes nor flags underflow')
        self.instruction("wire signed [7:0] w_exp_base = w_subnorm_active ? 8'sd0 : w_exp_adjusted;")
        self.instruction("wire signed [7:0] w_exp_final = w_exp_base + {7'b0, w_round_overflow};")
        self.instruction('')

    def generate_special_case_handling(self):
        """Generate special case result selection."""
        self.comment('Special case handling')
        self.instruction('')

        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan | w_c_is_nan;')
        self.instruction('wire w_prod_is_inf = w_a_is_inf | w_b_is_inf;')
        self.instruction('wire w_prod_is_zero = w_a_eff_zero | w_b_eff_zero;')
        self.instruction('wire w_invalid_mul = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);')
        self.instruction('wire w_invalid_add = w_prod_is_inf & w_c_is_inf & (w_prod_sign != w_sign_c);')
        self.instruction('wire w_invalid = w_invalid_mul | w_invalid_add;')
        self.instruction('')

        self.instruction("wire w_overflow_cond = ~w_exp_final[7] & (w_exp_final > 8'sd30);")
        self.instruction("wire w_underflow_cond = w_exp_final[7] | (w_exp_final < 8'sd1);")
        self.instruction('')
        self.comment('Product-only overflow/underflow (for c=0 shortcut path)')
        self.comment('w_prod_exp is now signed; use signed comparison')
        self.instruction("wire w_prod_overflow = (w_prod_exp > 7'sd30);")
        self.instruction("wire w_prod_underflow = (w_prod_exp < 7'sd1);")
        self.instruction('')

    def generate_result_assembly(self):
        """Generate final result assembly."""
        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    ow_result = {w_result_sign, w_exp_final[4:0], w_mant_final};')
        self.instruction("    ow_overflow = 1'b0;")
        self.instruction("    ow_underflow = 1'b0;")
        self.instruction("    ow_invalid = 1'b0;")
        self.instruction('')
        self.instruction('    if (w_any_nan | w_invalid) begin')
        self.instruction("        ow_result = {1'b0, 5'h1F, 10'h200};  // qNaN")
        self.instruction('        ow_invalid = w_invalid;')
        self.instruction('    end else if (w_prod_is_inf & ~w_c_is_inf) begin')
        self.instruction("        ow_result = {w_prod_sign, 5'h1F, 10'h0};")
        self.instruction('    end else if (w_c_is_inf) begin')
        self.instruction("        ow_result = {w_sign_c, 5'h1F, 10'h0};")
        self.instruction('    end else if (w_prod_is_zero & w_c_eff_zero) begin')
        self.instruction("        ow_result = {w_prod_sign & w_sign_c, 5'h00, 10'h0};  // 0*b+0 = 0")
        self.instruction('    end else if (w_prod_is_zero) begin')
        self.instruction('        ow_result = i_c;  // 0*b+c = c')
        self.instruction('    end else if (~SUBNORMAL_SUPPORT & w_c_eff_zero & w_prod_overflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 5'h1F, 10'h0};  // Product overflow to inf")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (~SUBNORMAL_SUPPORT & w_c_eff_zero & w_prod_underflow) begin')
        self.instruction("        ow_result = {w_prod_sign, 5'h00, 10'h0};  // Product underflow to zero")
        self.instruction("        ow_underflow = 1'b1;")
        self.instruction('    end else if (~SUBNORMAL_SUPPORT & w_c_eff_zero) begin')
        self.instruction('        // Product only: a*b+0 (TRUNCATED product, legacy quirk kept')
        self.instruction('        // bit-for-bit at SUBNORMAL_SUPPORT=0; at =1 a zero addend')
        self.instruction('        // flows through the main datapath so the product rounds')
        self.instruction('        // exactly once)')
        self.instruction('        ow_result = {w_prod_sign, w_prod_exp[4:0], w_prod_mant_norm[20:11]};  // a*b+0 (normal)')
        self.instruction('    end else if (w_overflow_cond) begin')
        self.instruction("        ow_result = {w_result_sign, 5'h1F, 10'h0};")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction("    end else if (w_underflow_cond | (w_sum_44 == 44'h0)) begin")
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
        self.instruction('            // meaningless (exp_adjusted = pre - 44 can be >= 1).')
        self.instruction("            if ((w_sum_44 == 44'h0) && !w_align_sticky) begin")
        self.instruction("                ow_result = {w_result_sign, 5'h00, 10'h0};  // exact zero sum")
        self.instruction("                ow_underflow = 1'b0;")
        self.instruction('            end else begin')
        self.instruction('                ow_result = {w_result_sign, w_exp_final[4:0], w_mant_final};')
        self.instruction('                ow_underflow = w_guard | w_round | w_sticky;')
        self.instruction('            end')
        self.instruction('        end else begin')
        self.instruction("            ow_result = {w_result_sign, 5'h00, 10'h0};")
        self.instruction("            ow_underflow = w_underflow_cond & (w_sum_44 != 44'h0);")
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP16 FMA."""
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

        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP16 Fused Multiply-Add with full precision accumulation',
            generator_script='fp16_fma.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp16_fma(output_path):
    """Generate FP16 FMA."""
    fma = FP16FMA()
    fma.verilog(output_path)
    return fma.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp16_fma(output_path)
    print(f'Generated: {module_name}.sv')
