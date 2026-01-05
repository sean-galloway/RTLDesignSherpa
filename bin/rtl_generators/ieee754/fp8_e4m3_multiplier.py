# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP8E4M3Multiplier
# Purpose: FP8 E4M3 Complete Multiplier Generator
#
# Complete FP8 E4M3 multiplier combining:
# - Mantissa multiplication (4x4 direct multiply)
# - Exponent addition with bias handling
# - Special case handling (zero, NaN, subnormal)
# - RNE (Round-to-Nearest-Even) rounding
#
# FP8 E4M3 format: [7]=sign, [6:3]=exp (bias=7), [2:0]=mantissa
#
# Note: E4M3 has NO infinity representation!
# - exp=15, mant=111 is NaN
# - exp=15, mant=000-110 are valid max normal values
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP8E4M3Multiplier(Module):
    """
    Generates complete FP8 E4M3 multiplier.

    Architecture (combinational):
    1. Field extraction + special case detection
    2. Sign = sign_a XOR sign_b
    3. 4x4 direct multiply -> 8-bit product
    4. Exponent = exp_a + exp_b - 7 + norm_adjust
    5. Normalization + RNE rounding
    6. Special case priority assembly
    """

    module_str = 'math_fp8_e4m3_multiplier'
    port_str = '''
    input  logic [7:0] i_a,           // FP8 E4M3 operand A
    input  logic [7:0] i_b,           // FP8 E4M3 operand B
    output logic [7:0] ow_result,     // FP8 E4M3 result
    output logic       ow_overflow,   // Overflow to max value
    output logic       ow_underflow,  // Underflow to zero
    output logic       ow_invalid     // Invalid operation (0 * large or NaN)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the complete FP8 E4M3 multiplier."""

        self.comment('FP8 E4M3 field extraction')
        self.comment('Format: [7]=sign, [6:3]=exponent, [2:0]=mantissa')
        self.instruction('')
        self.instruction('wire       w_sign_a = i_a[7];')
        self.instruction('wire [3:0] w_exp_a  = i_a[6:3];')
        self.instruction('wire [2:0] w_mant_a = i_a[2:0];')
        self.instruction('')
        self.instruction('wire       w_sign_b = i_b[7];')
        self.instruction('wire [3:0] w_exp_b  = i_b[6:3];')
        self.instruction('wire [2:0] w_mant_b = i_b[2:0];')
        self.instruction('')

        self.comment('Special value detection')
        self.instruction('')
        self.comment('Zero: exp=0, mant=0')
        self.instruction("wire w_a_is_zero = (w_exp_a == 4'h0) & (w_mant_a == 3'h0);")
        self.instruction("wire w_b_is_zero = (w_exp_b == 4'h0) & (w_mant_b == 3'h0);")
        self.instruction('')
        self.comment('Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)')
        self.instruction("wire w_a_is_subnormal = (w_exp_a == 4'h0) & (w_mant_a != 3'h0);")
        self.instruction("wire w_b_is_subnormal = (w_exp_b == 4'h0) & (w_mant_b != 3'h0);")
        self.instruction('')
        self.comment('NaN: exp=15, mant=111 (E4M3 specific - no infinity!)')
        self.instruction("wire w_a_is_nan = (w_exp_a == 4'hF) & (w_mant_a == 3'h7);")
        self.instruction("wire w_b_is_nan = (w_exp_b == 4'hF) & (w_mant_b == 3'h7);")
        self.instruction('')
        self.comment('Effective zero (includes subnormals in FTZ mode)')
        self.instruction('wire w_a_eff_zero = w_a_is_zero | w_a_is_subnormal;')
        self.instruction('wire w_b_eff_zero = w_b_is_zero | w_b_is_subnormal;')
        self.instruction('')
        self.comment('Normal number (has implied leading 1)')
        self.instruction('wire w_a_is_normal = ~w_a_eff_zero & ~w_a_is_nan;')
        self.instruction('wire w_b_is_normal = ~w_b_eff_zero & ~w_b_is_nan;')
        self.instruction('')

        self.comment('Result sign: XOR of input signs')
        self.instruction('wire w_sign_result = w_sign_a ^ w_sign_b;')
        self.instruction('')

        self.comment('Mantissa multiplication (4x4 direct multiply)')
        self.instruction('wire [7:0] w_mant_product;')
        self.instruction('wire       w_needs_norm;')
        self.instruction('wire [2:0] w_mant_mult_out;')
        self.instruction('wire       w_round_bit;')
        self.instruction('wire       w_sticky_bit;')
        self.instruction('')
        self.instruction('math_fp8_e4m3_mantissa_mult u_mant_mult (')
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

        self.comment('Exponent addition')
        self.instruction('wire [3:0] w_exp_sum;')
        self.instruction('wire       w_exp_overflow;')
        self.instruction('wire       w_exp_underflow;')
        self.instruction('wire       w_exp_a_zero, w_exp_b_zero;')
        self.instruction('wire       w_exp_a_nan, w_exp_b_nan;')
        self.instruction('')
        self.instruction('math_fp8_e4m3_exponent_adder u_exp_add (')
        self.instruction('    .i_exp_a(w_exp_a),')
        self.instruction('    .i_exp_b(w_exp_b),')
        self.instruction('    .i_norm_adjust(w_needs_norm),')
        self.instruction('    .ow_exp_out(w_exp_sum),')
        self.instruction('    .ow_overflow(w_exp_overflow),')
        self.instruction('    .ow_underflow(w_exp_underflow),')
        self.instruction('    .ow_a_is_zero(w_exp_a_zero),')
        self.instruction('    .ow_b_is_zero(w_exp_b_zero),')
        self.instruction('    .ow_a_is_nan(w_exp_a_nan),')
        self.instruction('    .ow_b_is_nan(w_exp_b_nan)')
        self.instruction(');')
        self.instruction('')

        self.comment('Round-to-Nearest-Even (RNE) rounding')
        self.comment('Round up if:')
        self.comment('  - round_bit=1 AND (sticky_bit=1 OR LSB=1)')
        self.instruction('')
        self.instruction('wire w_lsb = w_mant_mult_out[0];')
        self.instruction('wire w_round_up = w_round_bit & (w_sticky_bit | w_lsb);')
        self.instruction('')

        self.comment('Apply rounding to mantissa')
        self.instruction("wire [3:0] w_mant_rounded = {1'b0, w_mant_mult_out} + {3'b0, w_round_up};")
        self.instruction('')

        self.comment('Check for mantissa overflow from rounding')
        self.instruction('wire w_mant_round_overflow = w_mant_rounded[3];')
        self.instruction('')

        self.comment('Final mantissa (3 bits)')
        self.instruction('wire [2:0] w_mant_final = w_mant_round_overflow ?')
        self.instruction("    3'h0 : w_mant_rounded[2:0];  // Overflow means 1.0 -> needs exp adjust")
        self.instruction('')

        self.comment('Exponent adjustment for rounding overflow')
        self.instruction("wire [3:0] w_exp_final = w_mant_round_overflow ? (w_exp_sum + 4'd1) : w_exp_sum;")
        self.instruction('')

        self.comment('Check for exponent overflow after rounding adjustment')
        self.comment('E4M3: exp=15 with mant=111 is NaN, so max normal is exp=15, mant=110')
        self.instruction("wire w_final_overflow = w_exp_overflow | (w_exp_final == 4'hF & w_mant_final == 3'h7);")
        self.instruction('')

        self.comment('Special case result handling')
        self.instruction('')
        self.comment('NaN propagation: any NaN input produces NaN output')
        self.instruction('wire w_any_nan = w_a_is_nan | w_b_is_nan;')
        self.instruction('')
        self.comment('Zero result: either input is (effective) zero')
        self.instruction('wire w_result_zero = w_a_eff_zero | w_b_eff_zero;')
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
        self.instruction('    if (w_any_nan) begin')
        self.instruction("        // NaN result: canonical NaN (exp=15, mant=111)")
        self.instruction("        ow_result = {w_sign_result, 4'hF, 3'h7};")
        self.instruction("        ow_invalid = 1'b1;")
        self.instruction('    end else if (w_final_overflow) begin')
        self.instruction('        // Saturate to max normal (E4M3 has no infinity)')
        self.instruction("        ow_result = {w_sign_result, 4'hF, 3'h6};  // Max normal value")
        self.instruction("        ow_overflow = 1'b1;")
        self.instruction('    end else if (w_result_zero | w_exp_underflow) begin')
        self.instruction('        // Zero result')
        self.instruction("        ow_result = {w_sign_result, 4'h0, 3'h0};")
        self.instruction('        ow_underflow = w_exp_underflow & ~w_result_zero;')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='Complete FP8 E4M3 multiplier with special case handling and RNE rounding',
            generator_script='fp8_e4m3_multiplier.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp8_e4m3_multiplier(output_path):
    """Generate complete FP8 E4M3 multiplier."""
    mult = FP8E4M3Multiplier()
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp8_e4m3_multiplier(output_path)
    print(f'Generated: {module_name}.sv')
