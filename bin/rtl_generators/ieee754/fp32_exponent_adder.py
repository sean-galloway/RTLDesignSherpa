# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FP32ExponentAdder
# Purpose: IEEE 754-2008 FP32 Exponent Adder Generator
#
# FP32 has an 8-bit exponent with bias 127.
# For multiplication: exp_result = exp_a + exp_b - bias
#
# Additionally handles:
# - Normalization adjustment (+1 if mantissa product >= 2.0)
# - Overflow detection (exponent > 254)
# - Underflow detection (exponent < 1 after bias subtraction)
# - Special case handling (inf, zero, subnormal)
#
# Documentation: docs/IEEE754_ARCHITECTURE.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2026-01-01

from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class FP32ExponentAdder(Module):
    """
    Generates FP32 exponent adder for multiplication.

    IEEE 754-2008 FP32 exponent characteristics:
    - 8-bit biased exponent
    - Bias = 127
    - exp_result = exp_a + exp_b - 127 + norm_adjust

    Special values:
    - exp = 0: Zero or subnormal
    - exp = 255: Inf or NaN
    """

    module_str = 'math_ieee754_2008_fp32_exponent_adder'
    port_str = '''
    input  logic [7:0]  i_exp_a,        // 8-bit exponent A
    input  logic [7:0]  i_exp_b,        // 8-bit exponent B
    input  logic        i_norm_adjust,  // +1 if mantissa needs normalization
    output logic [7:0]  ow_exp_out,     // 8-bit result exponent
    output logic        ow_overflow,    // Exponent overflow (inf)
    output logic        ow_underflow,   // Exponent underflow (zero)
    output logic        ow_a_is_zero,   // Input A is zero
    output logic        ow_b_is_zero,   // Input B is zero
    output logic        ow_a_is_inf,    // Input A is infinity
    output logic        ow_b_is_inf,    // Input B is infinity
    output logic        ow_a_is_nan,    // Input A is NaN (needs mantissa check)
    output logic        ow_b_is_nan     // Input B is NaN (needs mantissa check)
    '''

    # IEEE 754-2008 FP32 bias
    BIAS = 127
    EXP_MAX = 255
    EXP_MIN = 0

    def __init__(self):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def generate_special_case_detection(self):
        """Detect special exponent values."""
        self.comment('Special case detection')
        self.comment('exp = 0: Zero (if mantissa = 0) or subnormal')
        self.comment('exp = 255: Inf (if mantissa = 0) or NaN (if mantissa != 0)')
        self.instruction('')
        self.instruction("assign ow_a_is_zero = (i_exp_a == 8'h00);  // Note: caller checks mantissa")
        self.instruction("assign ow_b_is_zero = (i_exp_b == 8'h00);")
        self.instruction("assign ow_a_is_inf  = (i_exp_a == 8'hFF);  // Caller checks mantissa for NaN")
        self.instruction("assign ow_b_is_inf  = (i_exp_b == 8'hFF);")
        self.instruction("assign ow_a_is_nan  = (i_exp_a == 8'hFF);  // Actual NaN needs mantissa != 0")
        self.instruction("assign ow_b_is_nan  = (i_exp_b == 8'hFF);")
        self.instruction('')

    def generate_exponent_addition(self):
        """Generate exponent addition with bias subtraction."""
        self.comment('Exponent addition with bias handling')
        self.comment('result_exp = exp_a + exp_b - bias + norm_adjust')
        self.comment('')
        self.comment('Use 10-bit intermediate to detect overflow/underflow')
        self.comment("Bias = 127 (8'h7F) per IEEE 754-2008")
        self.instruction('')

        # Use wider arithmetic to detect overflow/underflow
        self.instruction('// Extended precision for overflow/underflow detection')
        self.instruction('wire [9:0] w_exp_sum_raw;')
        self.instruction('')

        # exp_a + exp_b - bias + norm_adjust
        # = exp_a + exp_b - 127 + norm_adjust
        # Reorder to avoid negative intermediate: (exp_a + exp_b + norm_adjust) - 127
        self.instruction('// Calculate: exp_a + exp_b - bias + norm_adjust')
        self.instruction("// Rearranged as: (exp_a + exp_b + norm_adjust) - 10'd127")
        self.instruction("assign w_exp_sum_raw = {2'b0, i_exp_a} + {2'b0, i_exp_b} + ")
        self.instruction("                       {9'b0, i_norm_adjust} - 10'd127;")
        self.instruction('')

    def generate_overflow_underflow_detection(self):
        """Generate overflow and underflow detection."""
        self.comment('Underflow detection: result <= 0 (signed comparison)')
        self.comment("If MSB of 10-bit result is set, it's negative (underflow)")
        self.comment('Must check underflow BEFORE overflow since negative values appear large in unsigned')
        self.instruction('wire w_underflow_raw = w_exp_sum_raw[9] | (w_exp_sum_raw == 10\'d0);')
        self.instruction('')

        self.comment('Overflow detection: result > 254 (255 reserved for inf/nan)')
        self.comment('Only check overflow if not underflow (negative values wrap to large positive)')
        self.instruction("wire w_overflow_raw = ~w_underflow_raw & (w_exp_sum_raw > 10'd254);")
        self.instruction('')

        self.comment('Special cases override normal overflow/underflow')
        self.instruction('wire w_either_special = ow_a_is_inf | ow_b_is_inf | ow_a_is_zero | ow_b_is_zero;')
        self.instruction('')
        self.instruction('assign ow_overflow  = w_overflow_raw & ~w_either_special;')
        self.instruction('assign ow_underflow = w_underflow_raw & ~w_either_special;')
        self.instruction('')

    def generate_result_selection(self):
        """Generate final exponent result with saturation."""
        self.comment('Result exponent with saturation')
        self.comment('- Zero/subnormal input: result is zero (exp=0)')
        self.comment('- Inf/NaN input: result is inf (exp=255)')
        self.comment('- Overflow: saturate to 255 (inf)')
        self.comment('- Underflow: saturate to 0 (zero)')
        self.comment('- Normal: use computed value')
        self.instruction('')
        self.instruction('always_comb begin')
        self.instruction('    if (ow_a_is_zero | ow_b_is_zero) begin')
        self.instruction("        ow_exp_out = 8'h00;  // Zero result (or handled as special case)")
        self.instruction('    end else if (ow_a_is_inf | ow_b_is_inf) begin')
        self.instruction("        ow_exp_out = 8'hFF;  // Infinity/NaN result")
        self.instruction('    end else if (ow_overflow) begin')
        self.instruction("        ow_exp_out = 8'hFF;  // Overflow to infinity")
        self.instruction('    end else if (ow_underflow) begin')
        self.instruction("        ow_exp_out = 8'h00;  // Underflow to zero")
        self.instruction('    end else begin')
        self.instruction('        ow_exp_out = w_exp_sum_raw[7:0];')
        self.instruction('    end')
        self.instruction('end')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete FP32 exponent adder."""
        self.generate_special_case_detection()
        self.generate_exponent_addition()
        self.generate_overflow_underflow_detection()
        self.generate_result_selection()

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose='IEEE 754-2008 FP32 exponent adder with bias handling and overflow/underflow detection',
            generator_script='fp32_exponent_adder.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_fp32_exponent_adder(output_path):
    """
    Generate FP32 exponent adder.

    Args:
        output_path: Directory to write the generated file
    """
    adder = FP32ExponentAdder()
    adder.verilog(output_path)
    return adder.module_name


if __name__ == '__main__':
    import sys

    output_path = sys.argv[1] if len(sys.argv) > 1 else '.'

    module_name = generate_fp32_exponent_adder(output_path)
    print(f'Generated: {module_name}.sv')
