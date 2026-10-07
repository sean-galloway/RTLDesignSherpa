# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP16Multiplier
# Purpose: IEEE 754-2008 FP16 Complete Multiplier Generator
#
# Complete FP16 multiplier combining:
# - Mantissa multiplication (11x11 Dadda tree)
# - Exponent addition with bias handling
# - Special case handling (zero, inf, NaN, subnormal)
# - RNE (Round-to-Nearest-Even) rounding
#
# FP16 format: [15]=sign, [14:10]=exp (bias=15), [9:0]=mantissa
#
# Subnormal handling:
#   SUBNORMAL_SUPPORT=0 (default): FTZ. Subnormal inputs are treated as zero
#     and results never subnormal (byte-identical legacy behavior).
#   SUBNORMAL_SUPPORT=1: subnormal operands decode with hidden bit 0 at
#     effective exponent 1-bias. Products below 1.0 are left-normalized with
#     an exponent debit; a true product exponent below 1 right-shifts the
#     normalized {hidden, mant, GRS} vector onto the subnormal grid with TRUE
#     (unfolded) sticky capture, rounded RNE. A rounding carry out of
#     pre-round exponent 0 produces min-normal, not a flush (math BUG-004
#     ruling); ow_underflow asserts only for a tiny after-rounding result
#     that is also inexact (multiplication, unlike addition, rounds inexact
#     at the subnormal boundary). The fp16 mantissa_mult zeroes a subnormal
#     operand outright, so the decoded-significand product comes from a
#     parallel 11x11 Dadda multiply selected only when =1 sees a subnormal.
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP16Multiplier(Module):
    """
    Generates complete FP16 multiplier.

    Architecture (combinational):
    1. Field extraction + special case detection
    2. Sign = sign_a XOR sign_b
    3. 11x11 Dadda tree -> 22-bit product
    4. Exponent = exp_a + exp_b - 15 + norm_adjust
    5. Normalization + RNE rounding
    6. Special case priority assembly

    Subnormal handling: FTZ (flush-to-zero) by default, matching the legacy
    datapath bit-for-bit; SUBNORMAL_SUPPORT=1 adds full IEEE 754-2008
    gradual underflow on inputs and outputs (decode at effective exponent
    1-bias, left normalization of sub-1.0 products, subnormal-grid right
    shift with TRUE sticky, RNE, BUG-004 min-normal carry-out rule).
    """

    module_str = 'math_ieee754_2008_fp16_multiplier'
    port_str = '''
    input  logic [15:0] i_a,           // FP16 operand A
    input  logic [15:0] i_b,           // FP16 operand B
    output logic [15:0] ow_result,     // FP16 result
    output logic        ow_overflow,   // Overflow to infinity
    output logic        ow_underflow,  // Underflow to zero
    output logic        ow_invalid     // Invalid operation (0 * inf)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_parameter(self):
        """Inject the SUBNORMAL_SUPPORT parameter into the module header.

        The Param parser cannot carry inline comments, so patch the header
        after start() with the exact declaration (mirrors the adder family).
        """
        header = self.start_instructions[0]
        old = f'module {self.module_name}(\n'
        new = (f'module {self.module_name} #(\n'
               "    parameter bit SUBNORMAL_SUPPORT = 1'b0  "
               "// 0: FTZ (legacy); 1: IEEE 754-2008 gradual underflow\n) (\n")
        if old not in header:
            raise RuntimeError(f'module header patch failed for {self.module_name}')
        self.start_instructions[0] = header.replace(old, new, 1)

    def verilog(self, file_path):
        """Generate the complete FP16 multiplier."""

        self.comment('IEEE 754-2008 FP16 field extraction')
        self.comment('Format: [15]=sign, [14:10]=exponent, [9:0]=mantissa')
        self.instruction('')
        self.instruction('wire       w_sign_a = i_a[15];')
        self.instruction('wire [4:0] w_exp_a  = i_a[14:10];')
        self.instruction('wire [9:0] w_mant_a = i_a[9:0];')
        self.instruction('')
        self.instruction('wire       w_sign_b = i_b[15];')
        self.instruction('wire [4:0] w_exp_b  = i_b[14:10];')
        self.instruction('wire [9:0] w_mant_b = i_b[9:0];')
        self.instruction('')

        self.comment('Special value detection')
        self.instruction('')
        self.comment('Zero: exp=0, mant=0')
        self.instruction("wire w_a_is_zero = (w_exp_a == 5'h00) & (w_mant_a == 10'h000);")
        self.instruction("wire w_b_is_zero = (w_exp_b == 5'h00) & (w_mant_b == 10'h000);")
        self.instruction('')
        self.comment('Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)')
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 5'h00) & (w_mant_a != 10'h000);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 5'h00) & (w_mant_b != 10'h000);")
        self.instruction('')
        self.comment('Infinity: exp=1F, mant=0')
        self.instruction("wire w_a_is_inf = (w_exp_a == 5'h1F) & (w_mant_a == 10'h000);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 5'h1F) & (w_mant_b == 10'h000);")
        self.instruction('')
        self.comment('NaN: exp=1F, mant!=0')
        self.instruction("wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 10'h000);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 10'h000);")
        self.instruction('')
        self.comment('Effective zero: FTZ folds subnormals into zero; with SUBNORMAL_SUPPORT=1')
        self.comment('only true zeros are effective zero')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | (w_b_is_subnormal & ~SUBNORMAL_SUPPORT);')
        self.instruction('')
        self.comment('Normal number (has implied leading 1)')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
        self.instruction('')
        self.comment('Hidden-1 flags: 0 for subnormals when SUBNORMAL_SUPPORT=1 (they decode as')
        self.comment('0.mantissa at effective exponent 1-bias). Identical to *_is_normal when')
        self.comment('SUBNORMAL_SUPPORT=0.')
        self.instruction('wire w_a_h1 = w_a_is_normal & (~SUBNORMAL_SUPPORT | ~w_a_is_subnormal);')
        self.instruction('wire w_b_h1 = w_b_is_normal & (~SUBNORMAL_SUPPORT | ~w_b_is_subnormal);')
        self.instruction('')
        self.comment('Exponents adjusted for subnormal decode: a subnormal operates at effective')
        self.comment('biased exponent 1. Identical to the raw exponent when SUBNORMAL_SUPPORT=0.')
        self.instruction("wire [4:0] w_exp_a_adj = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ? 5'd1 : w_exp_a;")
        self.instruction("wire [4:0] w_exp_b_adj = (SUBNORMAL_SUPPORT & w_b_is_subnormal) ? 5'd1 : w_exp_b;")
        self.instruction('')

        self.comment('Result sign: XOR of input signs')
        self.instruction('wire w_sign_result = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Mantissa multiplication (11x11 with Dadda tree)')
        self.instruction('wire [21:0] w_mant_product;')
        self.instruction('wire        w_needs_norm;')
        self.instruction('wire [9:0]  w_mant_mult_out;')
        self.instruction('wire        w_round_bit;')
        self.instruction('wire        w_sticky_bit;')
        self.instruction('')
        self.instruction('math_ieee754_2008_fp16_mantissa_mult u_mant_mult (')
        self.instruction('    .i_mant_a(w_mant_a),')
        self.instruction('    .i_mant_b(w_mant_b),')
        self.instruction('    .i_a_is_normal(w_a_is_normal),')
        self.instruction('    .i_b_is_normal(w_b_is_normal),')
        self.instruction('    .ow_product(w_mant_product),')
        self.instruction('    .ow_needs_norm(w_needs_norm),')
        self.instruction('    .ow_mant_out(w_mant_mult_out),')
        self.instruction('    .ow_round_bit(w_round_bit),')
        self.instruction('    .ow_sticky_bit(w_sticky_bit)')
        self.instruction(');')
        self.instruction('')
        self.comment('The fp16 mantissa_mult zeroes a subnormal operand outright (its')
        self.comment('i_*_is_normal selects 1.mant vs 0.0), so it cannot produce the')
        self.comment('decoded subnormal product. A parallel 11x11 Dadda multiply on the')
        self.comment('decoded significands ({hidden1, mant}: 1.mant for normals, 0.mant for')
        self.comment('subnormals at SUBNORMAL_SUPPORT=1) supplies it, selected only when =1')
        self.comment('sees a subnormal operand -- the =0 datapath is byte-identical.')
        self.instruction("wire [10:0] w_sig_a = {w_a_h1, w_mant_a};")
        self.instruction("wire [10:0] w_sig_b = {w_b_h1, w_mant_b};")
        self.instruction('wire [21:0] w_mant_product_dec;')
        self.instruction('math_multiplier_dadda_4to2_011 u_mant_mult_dec (')
        self.instruction('    .i_multiplier(w_sig_a),')
        self.instruction('    .i_multiplicand(w_sig_b),')
        self.instruction('    .ow_product(w_mant_product_dec)')
        self.instruction(');')
        self.instruction('wire w_any_subn = SUBNORMAL_SUPPORT & (w_a_is_subnormal | w_b_is_subnormal);')
        self.instruction('wire [21:0] w_mant_product_eff = w_any_subn ? w_mant_product_dec : w_mant_product;')
        self.instruction('wire w_needs_norm_eff = w_mant_product_eff[21];')
        self.instruction('')

        self.comment('Exponent addition')
        self.instruction('wire [4:0] w_exp_sum;')
        self.instruction('wire       w_exp_overflow;')
        self.instruction('wire       w_exp_underflow;')
        self.instruction('wire       w_exp_a_zero, w_exp_b_zero;')
        self.instruction('wire       w_exp_a_inf, w_exp_b_inf;')
        self.instruction('')
        self.instruction('math_ieee754_2008_fp16_exponent_adder u_exp_add (')
        self.instruction('    .i_exp_a(w_exp_a_adj),')
        self.instruction('    .i_exp_b(w_exp_b_adj),')
        self.instruction('    .i_norm_adjust(w_needs_norm_eff),')
        self.instruction('    .ow_exp_out(w_exp_sum),')
        self.instruction('    .ow_overflow(w_exp_overflow),')
        self.instruction('    .ow_underflow(w_exp_underflow),')
        self.instruction('    .ow_a_is_zero(w_exp_a_zero),')
        self.instruction('    .ow_b_is_zero(w_exp_b_zero),')
        self.instruction('    .ow_a_is_inf(w_exp_a_inf),')
        self.instruction('    .ow_b_is_inf(w_exp_b_inf)')
        self.instruction(');')
        self.instruction('')

        self.comment('-' * 73)
        self.comment('Gradual-underflow datapath (SUBNORMAL_SUPPORT=1 only)')
        self.comment('')
        self.comment('With a subnormal operand the 22-bit product can fall below 1.0,')
        self.comment('which the legacy needs_norm normalization never sees: left-shift')
        self.comment('the product back into [1,2) and debit the exponent by the same')
        self.comment('amount. When the true product exponent is below 1 the exact')
        self.comment('result lies in the subnormal range: right-shift the normalized')
        self.comment('{hidden, mant, GRS} vector onto the subnormal grid (exponent')
        self.comment('1-bias), folding EVERY shifted-out bit into the sticky (TRUE')
        self.comment('unfolded sticky, math ISSUE-001), then round RNE exactly as on')
        self.comment('the normal path. A rounding carry out of pre-round exponent 0')
        self.comment('produces min-normal, not a flush (math BUG-004 ruling). With')
        self.comment('SUBNORMAL_SUPPORT=0 w_left_shift, w_norm_rescue and')
        self.comment('w_subnorm_path are constant 0 and this block folds away.')
        self.comment('-' * 73)
        self.instruction('')
        self.comment('Left normalization for products below 1.0 (only possible with a')
        self.comment('subnormal operand at SUBNORMAL_SUPPORT=1; the loop keeps the')
        self.comment('highest set bit, last assignment wins)')
        self.instruction('logic [4:0] r_left_shift;')
        self.instruction('always_comb begin')
        self.instruction("    r_left_shift = 5'd0;")
        self.instruction('    for (int i = 0; i < 20; i++) begin')
        self.instruction("        if (w_mant_product_eff[i]) r_left_shift = 5'd20 - 5'(i);")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.instruction('wire w_prod_lt1 = ~w_mant_product_eff[21] & ~w_mant_product_eff[20];')
        self.instruction('wire [4:0] w_left_shift = (SUBNORMAL_SUPPORT & w_prod_lt1 &')
        self.instruction("    (|w_mant_product_eff[19:0])) ? r_left_shift : 5'd0;")
        self.instruction('')
        self.comment('Normalized significand in [1,2) with the hidden bit at [20];')
        self.comment('identical to the legacy product view (w_mant_product_eff[21:1] /')
        self.comment('w_mant_product_eff[20:0]) whenever no left normalization applies')
        self.instruction('wire [20:0] w_mant_norm = w_needs_norm_eff ? w_mant_product_eff[21:1] :')
        self.instruction("    ((w_left_shift != 5'd0) ? ({1'b0, w_mant_product_eff[19:0]} << w_left_shift)")
        self.instruction('        : w_mant_product_eff[20:0]);')
        self.instruction('')
        self.comment('True product exponent on the subnormal-adjusted exponents')
        self.instruction('wire signed [8:0] w_exp_true = $signed({4\'b0000, w_exp_a_adj}) +')
        self.instruction('    $signed({4\'b0000, w_exp_b_adj}) - 9\'sd15 +')
        self.instruction("    $signed({8'b00000000, w_needs_norm_eff}) - $signed({4'b0000, w_left_shift});")
        self.instruction('')
        self.comment('Subnormal output path: shift the normalized vector onto the grid')
        self.instruction("wire w_subnorm_path = SUBNORMAL_SUPPORT & (w_exp_true < 9'sd1);")
        self.comment('Shift amount 1-exp_true, clamped so the mask still captures the')
        self.comment('whole vector (a clamped shift leaves guard=0, so nothing rounds)')
        self.instruction("wire signed [8:0] w_sub_shift_s = 9'sd1 - w_exp_true;  // >= 1 when active")
        self.instruction("wire w_shift_all = (w_sub_shift_s > 9'sd21);")
        self.instruction("wire [4:0] w_sub_shift = w_shift_all ? 5'd21 : w_sub_shift_s[4:0];")
        self.instruction("wire [21:0] w_sig_v = {1'b0, w_mant_norm};")
        self.instruction("wire [21:0] w_sub_mask = (22'h000001 << w_sub_shift) - 22'h000001;")
        self.instruction('wire [21:0] w_v_shifted = w_sig_v >> w_sub_shift;')
        self.instruction('wire [9:0] w_sub_mant = w_v_shifted[19:10];')
        self.instruction('wire w_sub_g = w_v_shifted[9];')
        self.instruction('wire w_sub_r = w_v_shifted[8];')
        self.instruction('wire w_sub_sticky = (|w_v_shifted[7:0]) | (|(w_sig_v & w_sub_mask));')
        self.instruction('')
        self.comment('Effective rounding inputs: with a subnormal operand at =1 the')
        self.comment('decoded product replaces the legacy mantissa_mult outputs (which')
        self.comment('zeroed the subnormal); the subnormal / left-rescue paths further')
        self.comment('replace them with the shifted / left-normalized vector. Every')
        self.comment('select folds to the legacy signal when SUBNORMAL_SUPPORT=0.')
        self.instruction('wire [9:0] w_eff_mant = w_needs_norm_eff ? w_mant_product_eff[20:11] :')
        self.instruction('    w_mant_product_eff[19:10];')
        self.instruction('wire w_eff_g = w_needs_norm_eff ? w_mant_product_eff[10] : w_mant_product_eff[9];')
        self.instruction('wire w_eff_rs = w_needs_norm_eff ? (|w_mant_product_eff[9:0]) :')
        self.instruction('    (|w_mant_product_eff[8:0]);')
        self.instruction("wire w_norm_rescue = SUBNORMAL_SUPPORT & (w_left_shift != 5'd0) & ~w_subnorm_path;")
        self.instruction('wire w_path_apply = w_subnorm_path | w_norm_rescue;')
        self.instruction('wire [9:0] w_path_mant = w_subnorm_path ? w_sub_mant : w_mant_norm[19:10];')
        self.instruction('wire w_path_g = w_subnorm_path ? w_sub_g : w_mant_norm[9];')
        self.instruction('wire w_path_r = w_subnorm_path ? w_sub_r : w_mant_norm[8];')
        self.instruction('wire w_path_sticky = w_subnorm_path ? w_sub_sticky : (|w_mant_norm[7:0]);')
        self.instruction('wire [9:0] w_mant_eff = w_path_apply ? w_path_mant :')
        self.instruction('    (w_any_subn ? w_eff_mant : w_mant_mult_out);')
        self.instruction('wire w_guard_eff = w_path_apply ? w_path_g :')
        self.instruction('    (w_any_subn ? w_eff_g : w_round_bit);')
        self.instruction('wire w_round_eff = w_path_apply ? w_path_r : 1\'b0;  // fp16 sticky_bit already folds R|S')
        self.instruction('wire w_sticky_eff = w_path_apply ? w_path_sticky :')
        self.instruction('    (w_any_subn ? w_eff_rs : w_sticky_bit);')
        self.instruction('')

        self.comment('Round-to-Nearest-Even (RNE) rounding')
        self.comment('Round up if:')
        self.comment('  - guard_bit=1 AND (round_bit=1 OR sticky_bit=1 OR LSB=1)')
        self.comment('mantissa_mult exports GUARD as round_bit and (R|S) as sticky_bit')
        self.comment('(see its NAMING NOTE), so this is textbook G & (R|S|LSB) RNE --')
        self.comment('sweep-verified vs an exact-product reference (math BUG-003 (was MATH-007), 2026-08-10).')
        self.instruction('')
        self.instruction('wire w_lsb = w_mant_eff[0];')
        self.instruction('wire w_round_up = w_guard_eff & (w_round_eff | w_sticky_eff | w_lsb);')
        self.instruction('')

        self.comment('Apply rounding to mantissa')
        self.instruction("wire [10:0] w_mant_rounded = {1'b0, w_mant_eff} + {10'b0, w_round_up};")
        self.instruction('')

        self.comment('Check for mantissa overflow from rounding')
        self.instruction('wire w_mant_round_overflow = w_mant_rounded[10];')
        self.instruction('')

        self.comment('Final mantissa (10 bits)')
        self.instruction('wire [9:0] w_mant_final = w_mant_round_overflow ?')
        self.instruction("    10'h000 : w_mant_rounded[9:0];  // Overflow means 1.0 -> needs exp adjust")
        self.instruction('')

        self.comment('Exponent base: 0 on the subnormal path (a rounding carry out of')
        self.comment('pre-round exponent 0 yields min-normal, not a flush -- math BUG-004')
        self.comment('ruling), the debit-corrected exponent when left normalization')
        self.comment('applied, otherwise the adder sum')
        self.instruction("wire [4:0] w_exp_base = w_subnorm_path ? 5'd0 :")
        self.instruction('    (w_norm_rescue ? w_exp_true[4:0] : w_exp_sum);')
        self.instruction("wire [4:0] w_exp_final = w_mant_round_overflow ? (w_exp_base + 5'd1) : w_exp_base;")
        self.instruction('')

        self.comment('Check for exponent overflow after rounding adjustment')
        self.instruction("wire w_final_overflow = w_exp_overflow | (w_exp_final == 5'h1F);")
        self.instruction('')

        self.comment('IEEE 754 detects underflow AFTER rounding (math BUG-004, was MATH-008): when the')
        self.comment('pre-round exponent sum is exactly 0 (one below the normal range) and')
        self.comment('mantissa rounding carries out, the result is exactly the minimum')
        self.comment('normal (exp 1, mant 0) and must not be flushed. The exponent adder')
        self.comment('saturates its output on underflow, so recompute "sum was exactly 0"')
        self.comment('from the raw exponents here.')
        self.instruction("wire w_exp_sum_was_zero = ({1'b0, w_exp_a} + {1'b0, w_exp_b} + {5'b0, w_needs_norm}) == 6'd15;")
        self.instruction('wire w_uf_rescued = w_exp_sum_was_zero & w_mant_round_overflow;')
        self.instruction('')

        self.comment('Special case result handling')
        self.instruction('')
        self.comment('NaN propagation: any NaN input produces NaN output')
        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan;')
        self.instruction('')
        self.comment('Invalid operation: 0 * inf = NaN')
        self.instruction('wire w_invalid_op = (w_a_eff_zero & w_b_is_inf) | (w_b_eff_zero & w_a_is_inf);')
        self.instruction('')
        self.comment('Zero result: either input is (effective) zero')
        self.instruction('wire w_result_zero = w_a_eff_zero | w_b_eff_zero;')
        self.instruction('')
        self.comment('Infinity result: either input is infinity (and not invalid)')
        self.instruction('wire w_result_inf = (w_a_is_inf | w_b_is_inf) & ~w_invalid_op;')
        self.instruction('')

        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    // Default: normal multiplication result')
        self.instruction('    ow_result = {w_sign_result, w_exp_final, w_mant_final};')
        self.instruction("    ow_overflow = 1'b0;")
        self.instruction("    ow_underflow = 1'b0;")
        self.instruction("    ow_invalid = 1'b0;")
        self.instruction('')
        self.instruction('    // Special case priority (highest to lowest)')
        self.instruction('    if (w_any_nan | w_invalid_op) begin')
        self.instruction("        // NaN result: quiet NaN with sign preserved")
        self.instruction("        ow_result = {w_sign_result, 5'h1F, 10'h200};  // Canonical qNaN")
        self.instruction('        ow_invalid = w_invalid_op;')
        self.instruction('    end else if (w_result_inf | w_final_overflow) begin')
        self.instruction('        // Infinity result')
        self.instruction("        ow_result = {w_sign_result, 5'h1F, 10'h000};")
        self.instruction('        ow_overflow = w_final_overflow & ~w_result_inf;')
        self.instruction('    end else if (SUBNORMAL_SUPPORT) begin')
        self.instruction('        // Gradual underflow: the tiny result (subnormal, or zero when')
        self.instruction('        // the rounded product vanishes) comes straight from the')
        self.instruction('        // shifted vector; a true-zero operand flushes through the')
        self.instruction('        // all-zero product path. Anything not tiny keeps the default')
        self.instruction('        // normal result assigned above.')
        self.instruction('        if (w_subnorm_path) begin')
        self.instruction('            ow_result = {w_sign_result, w_exp_final, w_mant_final};')
        self.instruction('            // IEEE underflow: tiny AFTER rounding AND inexact. The')
        self.instruction('            // multiplier, unlike the adder, rounds inexact at the')
        self.instruction('            // subnormal boundary, so this flag can assert; a carry')
        self.instruction('            // into min-normal (exp 1) is not tiny and stays silent.')
        self.instruction("            ow_underflow = (w_exp_final == 5'h00) &")
        self.instruction('                (w_guard_eff | w_round_eff | w_sticky_eff);')
        self.instruction('        end')
        self.instruction('    end else if (w_result_zero | (w_exp_underflow & ~w_uf_rescued)) begin')
        self.instruction('        // Zero result')
        self.instruction("        ow_result = {w_sign_result, 5'h00, 10'h000};")
        self.instruction('        ow_underflow = w_exp_underflow & ~w_result_zero & ~w_uf_rescued;')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

        self.start()
        self.generate_parameter()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='Complete IEEE 754-2008 FP16 multiplier with special case handling and RNE rounding',
            generator_script='fp16_multiplier.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp16_multiplier(output_path):
    """Generate complete FP16 multiplier."""
    mult = FP16Multiplier()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp16_multiplier(output_path)
    print(f'Generated: {module_name}.sv')
