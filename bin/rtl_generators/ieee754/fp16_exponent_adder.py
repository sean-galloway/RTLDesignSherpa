# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP16ExponentAdder
# Purpose: IEEE 754-2008 FP16 Exponent Adder Generator
#
# Adds two 5-bit exponents with bias handling and overflow/underflow detection.
# FP16 bias = 15
#
# For multiplication: result_exp = exp_a + exp_b - bias + norm_adjust
#
# FP16 format: [15]=sign, [14:10]=exp (bias=15), [9:0]=mantissa
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP16ExponentAdder(Module):
    """
    Generates FP16 exponent adder with bias handling.

    Computes: result = exp_a + exp_b - 15 + norm_adjust

    Detects:
    - Overflow (result > 30, as 31 is reserved for inf/nan)
    - Underflow (result < 1)
    - Special cases (zero, inf, nan exponents)
    """

    module_str = 'math_ieee754_2008_fp16_exponent_adder'
    port_str = '''
    input  logic [4:0] i_exp_a,        // FP16 exponent A (5 bits)
    input  logic [4:0] i_exp_b,        // FP16 exponent B (5 bits)
    input  logic       i_norm_adjust,  // +1 if mantissa product >= 2.0
    output logic [4:0] ow_exp_out,     // Result exponent (5 bits)
    output logic       ow_overflow,    // Exponent overflow
    output logic       ow_underflow,   // Exponent underflow
    output logic       ow_a_is_zero,   // exp_a == 0 (zero or subnormal)
    output logic       ow_b_is_zero,   // exp_b == 0 (zero or subnormal)
    output logic       ow_a_is_inf,    // exp_a == 31 (inf or nan)
    output logic       ow_b_is_inf     // exp_b == 31 (inf or nan)
    '''

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        """Generate the FP16 exponent adder."""

        self.comment('Special case detection')
        self.comment('exp = 0: Zero (if mantissa = 0) or subnormal')
        self.comment('exp = 31: Inf (if mantissa = 0) or NaN (if mantissa != 0)')
        self.instruction('')
        self.instruction("assign ow_a_is_zero = (i_exp_a == 5'h00);")
        self.instruction("assign ow_b_is_zero = (i_exp_b == 5'h00);")
        self.instruction("assign ow_a_is_inf  = (i_exp_a == 5'h1F);")
        self.instruction("assign ow_b_is_inf  = (i_exp_b == 5'h1F);")
        self.instruction('')

        self.comment('Exponent addition with bias handling')
        self.comment('result_exp = exp_a + exp_b - bias + norm_adjust')
        self.comment('')
        self.comment('Use 7-bit intermediate to detect overflow/underflow')
        self.comment('Bias = 15 (5\'h0F) per IEEE 754-2008 FP16')
        self.instruction('')

        self.comment('Extended precision for overflow/underflow detection')
        self.instruction('wire [6:0] w_exp_sum_raw;')
        self.instruction('')

        self.comment("Calculate: exp_a + exp_b - bias + norm_adjust")
        self.comment("Rearranged as: (exp_a + exp_b + norm_adjust) - 7'd15")
        self.instruction("assign w_exp_sum_raw = {2'b0, i_exp_a} + {2'b0, i_exp_b} + ")
        self.instruction("                       {6'b0, i_norm_adjust} - 7'd15;")
        self.instruction('')

        self.comment('Underflow detection: result <= 0 (signed comparison)')
        self.comment('If MSB of 7-bit result is set, it\'s negative (underflow)')
        self.instruction("wire w_underflow_raw = w_exp_sum_raw[6] | (w_exp_sum_raw == 7'd0);")
        self.instruction('')

        self.comment('Overflow detection: result > 30 (31 reserved for inf/nan)')
        self.comment('Only check overflow if not underflow')
        self.instruction("wire w_overflow_raw = ~w_underflow_raw & (w_exp_sum_raw > 7'd30);")
        self.instruction('')

        self.comment('Special cases override normal overflow/underflow')
        self.instruction('wire w_either_special = ow_a_is_inf | ow_b_is_inf | ow_a_is_zero | ow_b_is_zero;')
        self.instruction('')

        self.instruction('assign ow_overflow  = w_overflow_raw & ~w_either_special;')
        self.instruction('assign ow_underflow = w_underflow_raw & ~w_either_special;')
        self.instruction('')

        self.comment('Result exponent with saturation')
        self.comment('- Zero/subnormal input: result is zero (exp=0)')
        self.comment('- Inf/NaN input: result is inf (exp=31)')
        self.comment('- Overflow: saturate to 31 (inf)')
        self.comment('- Underflow: saturate to 0 (zero)')
        self.comment('- Normal: use computed value')
        self.instruction('')

        self.instruction('always_comb begin')
        self.instruction('    if (ow_a_is_zero | ow_b_is_zero) begin')
        self.instruction("        ow_exp_out = 5'h00;  // Zero result (or handled as special case)")
        self.instruction('    end else if (ow_a_is_inf | ow_b_is_inf) begin')
        self.instruction("        ow_exp_out = 5'h1F;  // Infinity/NaN result")
        self.instruction('    end else if (ow_overflow) begin')
        self.instruction("        ow_exp_out = 5'h1F;  // Overflow to infinity")
        self.instruction('    end else if (ow_underflow) begin')
        self.instruction("        ow_exp_out = 5'h00;  // Underflow to zero")
        self.instruction('    end else begin')
        self.instruction('        ow_exp_out = w_exp_sum_raw[4:0];')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP16 exponent adder with bias handling and overflow/underflow detection',
            generator_script='fp16_exponent_adder.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp16_exponent_adder(output_path):
    """Generate FP16 exponent adder."""
    adder = FP16ExponentAdder()
    adder.verilog(output_path)
    return adder.module_name


if __name__ == '__main__':
    import sys
    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'
    module_name = generate_fp16_exponent_adder(output_path)
    print(f'Generated: {module_name}.sv')
