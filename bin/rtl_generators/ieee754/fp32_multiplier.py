# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP32Multiplier
# Purpose: Complete IEEE 754-2008 FP32 Multiplier Generator
#
# Implements a full IEEE 754-2008 single-precision multiplier with:
# - Sign computation (XOR of input signs)
# - Exponent addition with bias handling
# - 24x24 mantissa multiplication (Dadda tree with 4:2 compressors)
# - Normalization and rounding (Round-to-Nearest-Even)
# - Special case handling (zero, inf, NaN)
# - FTZ mode for subnormals
#
# FP32 Format (IEEE 754-2008):
#   [31]    - Sign bit
#   [30:23] - 8-bit biased exponent (bias = 127)
#   [22:0]  - 23-bit mantissa (implied leading 1 for normalized)
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
#     at the subnormal boundary).
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP32Multiplier(Module):
    """
    Generates complete IEEE 754-2008 FP32 multiplier.

    Architecture:
    1. Extract sign, exponent, mantissa from inputs
    2. Compute result sign (XOR)
    3. Detect special cases (zero, inf, NaN, subnormal)
    4. Multiply mantissas (24x24 with Dadda 4:2 tree)
    5. Add exponents with bias subtraction
    6. Normalize and round result
    7. Assemble final FP32 output

    Follows IEEE 754-2008 conventions:
    - Subnormals flushed to zero (FTZ mode) by default; full gradual
      underflow on inputs and outputs when SUBNORMAL_SUPPORT=1
    - Round-to-nearest-even (RNE) rounding
    - Relaxed exception handling (status flags only)
    """

    module_str = 'math_ieee754_2008_fp32_multiplier'
    port_str = '''
    input  logic [31:0] i_a,           // FP32 operand A
    input  logic [31:0] i_b,           // FP32 operand B
    output logic [31:0] ow_result,     // FP32 product
    output logic        ow_overflow,   // Overflow to infinity
    output logic        ow_underflow,  // Underflow to zero
    output logic        ow_invalid     // Invalid operation (NaN)
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

    def generate_field_extraction(self):
        """Extract sign, exponent, and mantissa from FP32 operands."""
        self.comment('IEEE 754-2008 FP32 field extraction')
        self.comment('Format: [31]=sign, [30:23]=exponent, [22:0]=mantissa')
        self.instruction('')
        self.instruction('wire        w_sign_a = i_a[31];')
        self.instruction('wire [7:0]  w_exp_a  = i_a[30:23];')
        self.instruction('wire [22:0] w_mant_a = i_a[22:0];')
        self.instruction('')
        self.instruction('wire        w_sign_b = i_b[31];')
        self.instruction('wire [7:0]  w_exp_b  = i_b[30:23];')
        self.instruction('wire [22:0] w_mant_b = i_b[22:0];')
        self.instruction('')

    def generate_special_case_detection(self):
        """Detect special values in inputs."""
        self.comment('Special value detection')
        self.instruction('')

        self.comment('Zero: exp=0, mant=0')
        self.instruction("wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h000000);")
        self.instruction("wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 23'h000000);")
        self.instruction('')

        self.comment('Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)')
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h000000);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 23'h000000);")
        self.instruction('')

        self.comment('Infinity: exp=FF, mant=0')
        self.instruction("wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h000000);")
        self.instruction("wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 23'h000000);")
        self.instruction('')

        self.comment('NaN: exp=FF, mant!=0')
        self.instruction("wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h000000);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h000000);")
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

        self.comment('Hidden-bit feeds for the mantissa multiplier: 0 for subnormals when')
        self.comment('SUBNORMAL_SUPPORT=1 (they decode as 0.mantissa at effective exponent')
        self.comment('1-bias). Identical to *_is_normal when SUBNORMAL_SUPPORT=0.')
        self.instruction('wire w_a_h1 = w_a_is_normal & (~SUBNORMAL_SUPPORT | ~w_a_is_subnormal);')
        self.instruction('wire w_b_h1 = w_b_is_normal & (~SUBNORMAL_SUPPORT | ~w_b_is_subnormal);')
        self.instruction('')

        self.comment('Exponents adjusted for subnormal decode: a subnormal operates at effective')
        self.comment('biased exponent 1. Identical to the raw exponent when SUBNORMAL_SUPPORT=0.')
        self.instruction("wire [7:0] w_exp_a_adj = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ? 8'd1 : w_exp_a;")
        self.instruction("wire [7:0] w_exp_b_adj = (SUBNORMAL_SUPPORT & w_b_is_subnormal) ? 8'd1 : w_exp_b;")
        self.instruction('')

    def generate_sign_computation(self):
        """Compute result sign."""
        self.comment('Result sign: XOR of input signs')
        self.instruction('wire w_sign_result = w_sign_a ^ w_sign_b;')
        self.instruction('')

    def generate_mantissa_multiplication(self):
        """Instantiate mantissa multiplier."""
        self.comment('Mantissa multiplication (24x24 with Dadda 4:2 tree)')
        self.instruction('wire [47:0] w_mant_product;')
        self.instruction('wire        w_needs_norm;')
        self.instruction('wire [22:0] w_mant_mult_out;')
        self.instruction('wire        w_guard_bit;')
        self.instruction('wire        w_round_bit;')
        self.instruction('wire        w_sticky_bit;')
        self.instruction('')
        self.instruction('math_ieee754_2008_fp32_mantissa_mult u_mant_mult (')
        self.instruction('    .i_mant_a(w_mant_a),')
        self.instruction('    .i_mant_b(w_mant_b),')
        self.instruction('    .i_a_is_normal(w_a_h1),')
        self.instruction('    .i_b_is_normal(w_b_h1),')
        self.instruction('    .ow_product(w_mant_product),')
        self.instruction('    .ow_needs_norm(w_needs_norm),')
        self.instruction('    .ow_mant_out(w_mant_mult_out),')
        self.instruction('    .ow_guard_bit(w_guard_bit),')
        self.instruction('    .ow_round_bit(w_round_bit),')
        self.instruction('    .ow_sticky_bit(w_sticky_bit)')
        self.instruction(');')
        self.instruction('')

    def generate_exponent_addition(self):
        """Instantiate exponent adder."""
        self.comment('Exponent addition')
        self.instruction('wire [7:0] w_exp_sum;')
        self.instruction('wire       w_exp_overflow;')
        self.instruction('wire       w_exp_underflow;')
        self.instruction('wire       w_exp_a_zero, w_exp_b_zero;')
        self.instruction('wire       w_exp_a_inf, w_exp_b_inf;')
        self.instruction('wire       w_exp_a_nan, w_exp_b_nan;')
        self.instruction('')
        self.instruction('math_ieee754_2008_fp32_exponent_adder u_exp_add (')
        self.instruction('    .i_exp_a(w_exp_a_adj),')
        self.instruction('    .i_exp_b(w_exp_b_adj),')
        self.instruction('    .i_norm_adjust(w_needs_norm),')
        self.instruction('    .ow_exp_out(w_exp_sum),')
        self.instruction('    .ow_overflow(w_exp_overflow),')
        self.instruction('    .ow_underflow(w_exp_underflow),')
        self.instruction('    .ow_a_is_zero(w_exp_a_zero),')
        self.instruction('    .ow_b_is_zero(w_exp_b_zero),')
        self.instruction('    .ow_a_is_inf(w_exp_a_inf),')
        self.instruction('    .ow_b_is_inf(w_exp_b_inf),')
        self.instruction('    .ow_a_is_nan(w_exp_a_nan),')
        self.instruction('    .ow_b_is_nan(w_exp_b_nan)')
        self.instruction(');')
        self.instruction('')

    def generate_gradual_underflow(self):
        """Generate the SUBNORMAL_SUPPORT=1 gradual-underflow datapath.

        Every expression folds to the legacy value when SUBNORMAL_SUPPORT=0
        (w_left_shift / w_norm_rescue / w_subnorm_path are constant 0).
        """
        self.comment('-' * 73)
        self.comment('Gradual-underflow datapath (SUBNORMAL_SUPPORT=1 only)')
        self.comment('')
        self.comment('With a subnormal operand the 48-bit product can fall below 1.0,')
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
        self.instruction('logic [5:0] r_left_shift;')
        self.instruction('always_comb begin')
        self.instruction("    r_left_shift = 6'd0;")
        self.instruction('    for (int i = 0; i < 47; i++) begin')
        self.instruction("        if (w_mant_product[i]) r_left_shift = 6'd46 - 6'(i);")
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')
        self.instruction('wire w_prod_lt1 = ~w_mant_product[47] & ~w_mant_product[46];')
        self.instruction('wire [5:0] w_left_shift = (SUBNORMAL_SUPPORT & w_prod_lt1 &')
        self.instruction("    (|w_mant_product[45:0])) ? r_left_shift : 6'd0;")
        self.instruction('')
        self.comment('Normalized significand in [1,2) with the hidden bit at [46];')
        self.comment('identical to the legacy product view (w_mant_product[47:1] /')
        self.comment('w_mant_product[46:0]) whenever no left normalization applies')
        self.instruction('wire [46:0] w_mant_norm = w_needs_norm ? w_mant_product[47:1] :')
        self.instruction("    ((w_left_shift != 6'd0) ? ({1'b0, w_mant_product[45:0]} << w_left_shift)")
        self.instruction('        : w_mant_product[46:0]);')
        self.instruction('')
        self.comment('True product exponent on the subnormal-adjusted exponents')
        self.instruction('wire signed [10:0] w_exp_true = $signed({3\'b000, w_exp_a_adj}) +')
        self.instruction('    $signed({3\'b000, w_exp_b_adj}) - 11\'sd127 +')
        self.instruction("    $signed({10'b0000000000, w_needs_norm}) - $signed({5'b00000, w_left_shift});")
        self.instruction('')
        self.comment('Subnormal output path: shift the normalized vector onto the grid')
        self.instruction("wire w_subnorm_path = SUBNORMAL_SUPPORT & (w_exp_true < 11'sd1);")
        self.comment('Shift amount 1-exp_true, clamped so the mask still captures the')
        self.comment('whole vector (a clamped shift leaves guard=0, so nothing rounds)')
        self.instruction("wire signed [10:0] w_sub_shift_s = 11'sd1 - w_exp_true;  // >= 1 when active")
        self.instruction("wire w_shift_all = (w_sub_shift_s > 11'sd47);")
        self.instruction("wire [5:0] w_sub_shift = w_shift_all ? 6'd47 : w_sub_shift_s[5:0];")
        self.instruction("wire [47:0] w_sig_v = {1'b0, w_mant_norm};")
        self.instruction("wire [47:0] w_sub_mask = (48'h000000000001 << w_sub_shift) - 48'h000000000001;")
        self.instruction('wire [47:0] w_v_shifted = w_sig_v >> w_sub_shift;')
        self.instruction('wire [22:0] w_sub_mant = w_v_shifted[45:23];')
        self.instruction('wire w_sub_g = w_v_shifted[22];')
        self.instruction('wire w_sub_r = w_v_shifted[21];')
        self.instruction('wire w_sub_sticky = (|w_v_shifted[20:0]) | (|(w_sig_v & w_sub_mask));')
        self.instruction('')
        self.comment('Effective rounding inputs: the =1 corrections override the')
        self.comment('mantissa_mult outputs only on the subnormal / left-rescue paths;')
        self.comment('every select folds to the legacy signal when SUBNORMAL_SUPPORT=0')
        self.instruction("wire w_norm_rescue = SUBNORMAL_SUPPORT & (w_left_shift != 6'd0) & ~w_subnorm_path;")
        self.instruction('wire w_path_apply = w_subnorm_path | w_norm_rescue;')
        self.instruction('wire [22:0] w_path_mant = w_subnorm_path ? w_sub_mant : w_mant_norm[45:23];')
        self.instruction('wire w_path_g = w_subnorm_path ? w_sub_g : w_mant_norm[22];')
        self.instruction('wire w_path_r = w_subnorm_path ? w_sub_r : w_mant_norm[21];')
        self.instruction('wire w_path_sticky = w_subnorm_path ? w_sub_sticky : (|w_mant_norm[20:0]);')
        self.instruction('wire [22:0] w_mant_eff = w_path_apply ? w_path_mant : w_mant_mult_out;')
        self.instruction('wire w_guard_eff = w_path_apply ? w_path_g : w_guard_bit;')
        self.instruction('wire w_round_eff = w_path_apply ? w_path_r : w_round_bit;')
        self.instruction('wire w_sticky_eff = w_path_apply ? w_path_sticky : w_sticky_bit;')
        self.instruction('')

    def generate_rounding(self):
        """Generate round-to-nearest-even logic."""
        self.comment('Round-to-Nearest-Even (RNE) rounding')
        self.comment('Textbook RNE: round up iff guard=1 AND (round | sticky | LSB).')
        self.comment('Guard is the first bit below the kept mantissa; sticky arrives TRUE')
        self.comment('(unfolded) from mantissa_mult (or the subnormal shifter above).')
        self.instruction('')

        self.instruction('wire w_lsb = w_mant_eff[0];')
        self.instruction('wire w_round_up = w_guard_eff & (w_round_eff | w_sticky_eff | w_lsb);  // true RNE (math ISSUE-001 (was MATH-001) family)')
        self.instruction('')

        self.comment('Apply rounding to mantissa')
        self.instruction("wire [23:0] w_mant_rounded = {1'b0, w_mant_eff} + {23'b0, w_round_up};")
        self.instruction('')

        self.comment('Check for mantissa overflow from rounding (rare)')
        self.instruction('wire w_mant_round_overflow = w_mant_rounded[23];')
        self.instruction('')

        self.comment('Final mantissa (23 bits)')
        self.instruction('wire [22:0] w_mant_final = w_mant_round_overflow ? ')
        self.instruction("    23'h000000 : w_mant_rounded[22:0];  // Overflow means 1.0 -> needs exp adjust")
        self.instruction('')

        self.comment('Exponent base: 0 on the subnormal path (a rounding carry out of')
        self.comment('pre-round exponent 0 yields min-normal, not a flush -- math BUG-004')
        self.comment('ruling), the debit-corrected exponent when left normalization')
        self.comment('applied, otherwise the adder sum')
        self.instruction("wire [7:0] w_exp_base = w_subnorm_path ? 8'd0 :")
        self.instruction('    (w_norm_rescue ? w_exp_true[7:0] : w_exp_sum);')
        self.instruction("wire [7:0] w_exp_final = w_mant_round_overflow ? (w_exp_base + 8'd1) : w_exp_base;")
        self.instruction('')

        self.comment('Check for exponent overflow after rounding adjustment')
        self.instruction("wire w_final_overflow = w_exp_overflow | (w_exp_final == 8'hFF);")
        self.instruction('')

        self.comment('IEEE 754 detects underflow AFTER rounding (math BUG-004, was MATH-008): when the')
        self.comment('pre-round exponent sum is exactly 0 (one below the normal range) and')
        self.comment('mantissa rounding carries out, the result is exactly the minimum')
        self.comment('normal (exp 1, mant 0) and must not be flushed. The exponent adder')
        self.comment('saturates its output on underflow, so recompute "sum was exactly 0"')
        self.comment('from the raw exponents here.')
        self.instruction("wire w_exp_sum_was_zero = ({1'b0, w_exp_a} + {1'b0, w_exp_b} + {8'b0, w_needs_norm}) == 9'd127;")
        self.instruction('wire w_uf_rescued = w_exp_sum_was_zero & w_mant_round_overflow;')
        self.instruction('')

    def generate_special_case_handling(self):
        """Generate special case result selection."""
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

    def generate_result_assembly(self):
        """Generate final result assembly."""
        self.comment('Final result assembly')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    // Default: normal multiplication result')
        self.instruction('    ow_result = {w_sign_result, w_exp_final, w_mant_final};')
        self.instruction('    ow_overflow = 1\'b0;')
        self.instruction('    ow_underflow = 1\'b0;')
        self.instruction('    ow_invalid = 1\'b0;')
        self.instruction('')
        self.instruction('    // Special case priority (highest to lowest)')
        self.instruction('    if (w_any_nan | w_invalid_op) begin')
        self.instruction('        // NaN result: quiet NaN with sign preserved')
        self.instruction("        ow_result = {w_sign_result, 8'hFF, 23'h400000};  // Canonical qNaN")
        self.instruction('        ow_invalid = w_invalid_op;')
        self.instruction('    end else if (w_result_inf | w_final_overflow) begin')
        self.instruction('        // Infinity result')
        self.instruction("        ow_result = {w_sign_result, 8'hFF, 23'h000000};")
        self.instruction('        ow_overflow = w_final_overflow & ~w_result_inf;')
        self.instruction("    end else if (SUBNORMAL_SUPPORT) begin")
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
        self.instruction("            ow_underflow = (w_exp_final == 8'h00) &")
        self.instruction('                (w_guard_eff | w_round_eff | w_sticky_eff);')
        self.instruction('        end')
        self.instruction('    end else if (w_result_zero | (w_exp_underflow & ~w_uf_rescued)) begin')
        self.instruction('        // Zero result')
        self.instruction("        ow_result = {w_sign_result, 8'h00, 23'h000000};")
        self.instruction('        ow_underflow = w_exp_underflow & ~w_result_zero & ~w_uf_rescued;')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP32 multiplier."""
        self.generate_field_extraction()
        self.generate_special_case_detection()
        self.generate_sign_computation()
        self.generate_mantissa_multiplication()
        self.generate_exponent_addition()
        self.generate_gradual_underflow()
        self.generate_rounding()
        self.generate_special_case_handling()
        self.generate_result_assembly()

        self.start()
        self.generate_parameter()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='Complete IEEE 754-2008 FP32 multiplier with special case handling and RNE rounding',
            generator_script='fp32_multiplier.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp32_multiplier(output_path):
    """
    Generate complete FP32 multiplier.

    Args:
        output_path: Directory to write the generated file
    """
    mult = FP32Multiplier()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_fp32_multiplier(output_path)
    print(f'Generated: {module_name}.sv')
