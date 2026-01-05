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
    - Subnormals flushed to zero (FTZ mode)
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

        self.comment('Effective zero (includes subnormals in FTZ mode)')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;')
        self.instruction('')

        self.comment('Normal number (has implied leading 1)')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_inf & ~w_a_is_nan;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_inf & ~w_b_is_nan;')
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
        self.instruction('wire        w_round_bit;')
        self.instruction('wire        w_sticky_bit;')
        self.instruction('')
        self.instruction('math_ieee754_2008_fp32_mantissa_mult u_mant_mult (')
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
        self.instruction('    .i_exp_a(w_exp_a),')
        self.instruction('    .i_exp_b(w_exp_b),')
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

    def generate_rounding(self):
        """Generate round-to-nearest-even logic."""
        self.comment('Round-to-Nearest-Even (RNE) rounding')
        self.comment('Round up if:')
        self.comment('  - round_bit=1 AND (sticky_bit=1 OR LSB=1)')
        self.comment('This implements RNE: ties round to even')
        self.instruction('')
        self.instruction('wire w_lsb = w_mant_mult_out[0];')
        self.instruction('wire w_round_up = w_round_bit & (w_sticky_bit | w_lsb);')
        self.instruction('')

        self.comment('Apply rounding to mantissa')
        self.instruction("wire [23:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {23'b0, w_round_up};")
        self.instruction('')

        self.comment('Check for mantissa overflow from rounding (rare)')
        self.instruction('wire w_mant_round_overflow = w_mant_rounded[23];')
        self.instruction('')

        self.comment('Final mantissa (23 bits)')
        self.instruction('wire [22:0] w_mant_final = w_mant_round_overflow ? ')
        self.instruction("    23'h000000 : w_mant_rounded[22:0];  // Overflow means 1.0 -> needs exp adjust")
        self.instruction('')

        self.comment('Exponent adjustment for rounding overflow')
        self.instruction("wire [7:0] w_exp_final = w_mant_round_overflow ? (w_exp_sum + 8'd1) : w_exp_sum;")
        self.instruction('')

        self.comment('Check for exponent overflow after rounding adjustment')
        self.instruction("wire w_final_overflow = w_exp_overflow | (w_exp_final == 8'hFF);")
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
        self.instruction('    end else if (w_result_zero | w_exp_underflow) begin')
        self.instruction('        // Zero result')
        self.instruction("        ow_result = {w_sign_result, 8'h00, 23'h000000};")
        self.instruction('        ow_underflow = w_exp_underflow & ~w_result_zero;')
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
        self.generate_rounding()
        self.generate_special_case_handling()
        self.generate_result_assembly()

        self.start()
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
