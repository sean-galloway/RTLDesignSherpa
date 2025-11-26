# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Dadda4to2Multiplier
# Purpose: Dadda Multiplier with 4:2 Compressors
#
# This implements a Dadda reduction tree using 4:2 compressors instead of
# 3:2 CSA cells. For an 8x8 multiplier (BF16 mantissa):
# - 3 reduction stages (vs 4 with 3:2 CSA)
# - ~18 4:2 compressors
# - Critical path: 9 XOR delays (3 per stage)
#
# The key insight is that 4:2 compressors reduce column height faster:
# - 4:2 reduces 5 inputs to 2 outputs
# - 3:2 (CSA/FA) reduces 3 inputs to 2 outputs
#
# Documentation: docs/bf16-research.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-11-24

import math
import itertools
from rtl_generators.verilog.module import Module
from .rtl_header import generate_rtl_header


class Dadda4to2Multiplier(Module):
    """
    Generates a Dadda multiplier using 4:2 compressors.

    For 8-bit operands (BF16 mantissa):
    - 64 partial products from AND gates
    - 3-stage Dadda reduction with 4:2 compressors
    - ~18 compressors total
    - Final CPA on 16-bit result
    """

    module_str = 'math_multiplier_dadda_4to2'
    param_str = 'parameter int N=8'
    port_str = '''
    input  logic [N-1:0]    i_multiplier,
    input  logic [N-1:0]    i_multiplicand,
    output logic [2*N-1:0]  ow_product
    '''

    def __init__(self, buswidth):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.buswidth = buswidth
        self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'
        self.params.set_param_value('N', self.buswidth)

        # Counters for unique naming
        self.compressor_count = 0
        self.ha_count = 0
        self.fa_count = 0

    @staticmethod
    def generate_dadda_heights(n):
        """
        Generate Dadda height sequence for reduction.

        The Dadda sequence determines target heights: 2, 3, 4, 6, 9, 13, 19, 28, ...
        Each stage reduces to the next smaller Dadda number.

        For 8-bit multiply: max column height is 8
        Target heights: 6 -> 4 -> 3 -> 2
        """
        heights = [2]
        while heights[-1] < n:
            next_height = math.floor(heights[-1] * 1.5)
            heights.append(next_height)
        return heights[::-1]  # Reverse for reduction order

    @staticmethod
    def get_target_height(current_height, dadda_heights):
        """Get the target height for reduction from Dadda sequence."""
        for h in dadda_heights:
            if h < current_height:
                return h
        return 2

    def generate_partial_products(self):
        """Generate partial product matrix using AND gates."""
        N = self.buswidth
        max_digits = len(str(N - 1))

        bit_groups = {i: [] for i in range(2 * N)}

        self.comment('Partial Products (AND gate array)')
        for i, j in itertools.product(range(N), range(N)):
            formatted_i = str(i).zfill(max_digits)
            formatted_j = str(j).zfill(max_digits)
            sig = f'w_pp_{formatted_i}_{formatted_j}'
            self.instruction(f'wire {sig} = i_multiplier[{i}] & i_multiplicand[{j}];')
            bit_groups[i + j].append(sig)

        self.instruction('')
        return bit_groups

    def apply_4to2_compressor(self, bit_groups, col, inputs, max_col_digits):
        """
        Apply a single 4:2 compressor to a column.

        4:2 compressor takes 5 inputs (X1, X2, X3, X4, Cin) and produces:
        - Sum (same column)
        - Carry (column + 1)
        - Cout (column + 1, independent of Cin)
        """
        formatted_col = str(col).zfill(max_col_digits)
        comp_id = str(self.compressor_count).zfill(3)
        self.compressor_count += 1

        sum_name = f'w_c4to2_sum_{formatted_col}_{comp_id}'
        carry_name = f'w_c4to2_carry_{formatted_col}_{comp_id}'
        cout_name = f'w_c4to2_cout_{formatted_col}_{comp_id}'

        # Get cin from previous compressor's cout if available
        # For first compressor in column, use 0
        cin = inputs[4] if len(inputs) > 4 else "1'b0"

        self.instruction(f'wire {sum_name}, {carry_name}, {cout_name};')
        self.instruction(f'math_compressor_4to2 u_c4to2_{formatted_col}_{comp_id} (')
        self.instruction(f'    .i_x1({inputs[0]}), .i_x2({inputs[1]}),')
        self.instruction(f'    .i_x3({inputs[2]}), .i_x4({inputs[3]}),')
        self.instruction(f'    .i_cin({cin}),')
        self.instruction(f'    .ow_sum({sum_name}), .ow_carry({carry_name}), .ow_cout({cout_name})')
        self.instruction(');')

        return sum_name, carry_name, cout_name

    def apply_full_adder(self, bit_groups, col, inputs, max_col_digits):
        """Apply a 3:2 compressor (full adder) when only 3 inputs available."""
        formatted_col = str(col).zfill(max_col_digits)
        fa_id = str(self.fa_count).zfill(3)
        self.fa_count += 1

        sum_name = f'w_fa_sum_{formatted_col}_{fa_id}'
        carry_name = f'w_fa_carry_{formatted_col}_{fa_id}'

        self.instruction(f'wire {sum_name}, {carry_name};')
        self.instruction(f'math_adder_full u_fa_{formatted_col}_{fa_id} (')
        self.instruction(f'    .i_a({inputs[0]}), .i_b({inputs[1]}), .i_c({inputs[2]}),')
        self.instruction(f'    .ow_sum({sum_name}), .ow_carry({carry_name})')
        self.instruction(');')

        return sum_name, carry_name

    def apply_half_adder(self, bit_groups, col, inputs, max_col_digits):
        """Apply a half adder when only 2 inputs need reduction."""
        formatted_col = str(col).zfill(max_col_digits)
        ha_id = str(self.ha_count).zfill(3)
        self.ha_count += 1

        sum_name = f'w_ha_sum_{formatted_col}_{ha_id}'
        carry_name = f'w_ha_carry_{formatted_col}_{ha_id}'

        self.instruction(f'wire {sum_name}, {carry_name};')
        self.instruction(f'math_adder_half u_ha_{formatted_col}_{ha_id} (')
        self.instruction(f'    .i_a({inputs[0]}), .i_b({inputs[1]}),')
        self.instruction(f'    .ow_sum({sum_name}), .ow_carry({carry_name})')
        self.instruction(');')

        return sum_name, carry_name

    def dadda_reduction_4to2(self, bit_groups):
        """
        Perform Dadda reduction using 4:2 compressors.

        Strategy:
        1. Use 4:2 compressors when column height >= 4
        2. Chain compressor Cout to next compressor Cin within same column
        3. Fall back to FA/HA for remaining reductions
        """
        N = self.buswidth
        max_col_digits = len(str(2 * N - 1))

        # Get max height and Dadda sequence
        max_height = max(len(group) for group in bit_groups.values())
        dadda_heights = self.generate_dadda_heights(max_height)

        stage = 1
        while max_height > 2:
            target = self.get_target_height(max_height, dadda_heights)
            self.comment(f'Dadda Reduction Stage {stage}: height {max_height} -> {target}')
            self.instruction('')

            for col in range(2 * N - 1):
                # Reduce this column to target height
                while len(bit_groups[col]) > target:
                    height = len(bit_groups[col])

                    if height >= 4:
                        # Use 4:2 compressor (consumes 4 inputs, produces 1 sum + 2 carries)
                        inputs = bit_groups[col][:4]
                        bit_groups[col] = bit_groups[col][4:]

                        sum_out, carry_out, cout_out = self.apply_4to2_compressor(
                            bit_groups, col, inputs, max_col_digits
                        )

                        # Sum stays in current column
                        bit_groups[col].append(sum_out)
                        # Both carries go to next column
                        if col + 1 < 2 * N:
                            bit_groups[col + 1].append(carry_out)
                            bit_groups[col + 1].append(cout_out)

                    elif height == 3:
                        # Use full adder
                        inputs = bit_groups[col][:3]
                        bit_groups[col] = bit_groups[col][3:]

                        sum_out, carry_out = self.apply_full_adder(
                            bit_groups, col, inputs, max_col_digits
                        )

                        bit_groups[col].append(sum_out)
                        if col + 1 < 2 * N:
                            bit_groups[col + 1].append(carry_out)

                    elif height == 2 and target < 2:
                        # Use half adder (rare case)
                        inputs = bit_groups[col][:2]
                        bit_groups[col] = bit_groups[col][2:]

                        sum_out, carry_out = self.apply_half_adder(
                            bit_groups, col, inputs, max_col_digits
                        )

                        bit_groups[col].append(sum_out)
                        if col + 1 < 2 * N:
                            bit_groups[col + 1].append(carry_out)
                    else:
                        break

            max_height = max(len(group) for group in bit_groups.values())
            stage += 1
            self.instruction('')

        return bit_groups

    def generate_final_cpa(self, bit_groups):
        """
        Generate final carry-propagate addition.

        After Dadda reduction, each column has at most 2 bits.
        Use Han-Carlson adder for optimal 16-bit CPA.
        """
        N = self.buswidth
        max_col_digits = len(str(2 * N - 1))

        self.comment('Final CPA: Two operands from reduction tree')

        # Extract two operands from bit_groups
        self.instruction(f'wire [2*N-1:0] w_cpa_a, w_cpa_b;')

        for col in range(2 * N):
            formatted_col = str(col).zfill(max_col_digits)
            bits = bit_groups.get(col, [])

            if len(bits) == 0:
                self.instruction(f"assign w_cpa_a[{col}] = 1'b0;")
                self.instruction(f"assign w_cpa_b[{col}] = 1'b0;")
            elif len(bits) == 1:
                self.instruction(f'assign w_cpa_a[{col}] = {bits[0]};')
                self.instruction(f"assign w_cpa_b[{col}] = 1'b0;")
            else:  # len(bits) >= 2
                self.instruction(f'assign w_cpa_a[{col}] = {bits[0]};')
                self.instruction(f'assign w_cpa_b[{col}] = {bits[1]};')

        self.instruction('')

        # Instantiate the final adder
        self.comment('Han-Carlson prefix adder for final CPA')
        self.instruction('wire w_cpa_cout;  // Unused for unsigned multiply')
        self.instruction(f'math_adder_han_carlson_{str(2*N).zfill(3)} u_final_cpa (')
        self.instruction('    .i_a(w_cpa_a),')
        self.instruction('    .i_b(w_cpa_b),')
        self.instruction("    .i_cin(1'b0),")
        self.instruction('    .ow_sum(ow_product),')
        self.instruction('    .ow_cout(w_cpa_cout)')
        self.instruction(');')
        self.instruction('')

    def verilog(self, file_path):
        """Generate the complete Dadda 4:2 multiplier."""
        bit_groups = self.generate_partial_products()
        bit_groups = self.dadda_reduction_4to2(bit_groups)
        self.generate_final_cpa(bit_groups)

        self.start()
        self.end()

        # Write with proper header
        filename = f'{self.module_name}.sv'
        header = generate_rtl_header(
            module_name=self.module_name,
            purpose=f'Dadda {self.buswidth}x{self.buswidth} multiplier with 4:2 compressors for BF16 mantissa',
            generator_script='dadda_4to2_multiplier.py'
        )
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        content = '\n'.join(all_instructions)
        with open(f'{file_path}/{filename}', 'w') as f:
            f.write(header + content + '\n')


def generate_dadda_4to2_multiplier(width, output_path):
    """
    Generate a Dadda multiplier with 4:2 compressors.

    Args:
        width: Operand width (typically 8 for BF16 mantissa)
        output_path: Directory to write the generated file
    """
    mult = Dadda4to2Multiplier(width)
    mult.verilog(output_path)
    return mult.module_name


if __name__ == '__main__':
    import sys

    # Default to 8-bit for BF16 mantissa
    width = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    output_path = sys.argv[2] if len(sys.argv) > 2 else '.'

    module_name = generate_dadda_4to2_multiplier(width, output_path)
    print(f'Generated: {module_name}.sv')
