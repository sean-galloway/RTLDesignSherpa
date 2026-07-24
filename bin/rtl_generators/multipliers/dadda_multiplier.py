# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: DaddaTree
# Purpose: Dadda Multiplier implementation
#
# Documentation: docs/markdown/RTLCommon/index.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import itertools
import math
from rtl_generators.verilog.module import Module
from .multiplier_mixin import MultiplierMixin


class DaddaTree(Module, MultiplierMixin):
    module_str = 'math_multiplier_dadda_tree'
    param_str = 'parameter int N=8'
    port_str = '''
    input  [N-1:0]    i_multiplier,
    input  [N-1:0]    i_multiplicand,
    output [2*N-1:0]  ow_product
    '''

    def __init__(self, buswidth):
        Module.__init__(self, module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.buswidth = buswidth
        self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'
        self.params.set_param_value('N', self.buswidth)

    @staticmethod
    def generate_dadda_numbers(n=100):
        '''
        Generates a list of Dadda numbers.

        Dadda's maximum-height sequence (Dadda 1965): d(1) = 2, d(j+1) = floor(1.5 * d(j)).
        These are the per-stage column-height ceilings of the reduction tree. A leading 1
        is included so the list can also be read as the full descending goal set.

        Args:
            n (int): The number of Dadda numbers to generate. Defaults to 100.

        Returns:
            list: A list of Dadda numbers.

        Example:
        ```python
        dadda_nums = generate_dadda_numbers(10)
        print(dadda_nums)
        # Output: [1, 2, 3, 4, 6, 9, 13, 19, 28, 42]
        '''
        # Canonical Dadda recurrence: d(1) = 2, d(j+1) = floor(1.5 * d(j))
        #   -> 1, 2, 3, 4, 6, 9, 13, 19, 28, 42, 63, ...
        # A prior version alternated *1.5 and *4/3, yielding 1,2,3,4,6,8,12,16,24,32,48.
        # Every term from the 5th on was smaller than Dadda's, so each stage would have
        # over-reduced. See bin/rtl_generators/bf16/dadda_4to2_multiplier.py, which has
        # always used the canonical form.
        dadda_numbers = [1, 2]
        while len(dadda_numbers) < n:
            dadda_numbers.append(math.floor(dadda_numbers[-1] * 1.5))
        return dadda_numbers

    def dadda_reduction(self, bit_groups, N):
        '''
        Performs a true Dadda reduction on the partial-product bit groups.

        Dadda reduces in STAGES. Each stage has a single target column height,
        taken from the Dadda sequence walked downwards (e.g. for N=8: 6, 4, 3, 2).
        Within a stage every column is reduced to -- and no further than -- that
        stage's target, using the fewest compressors that achieve it:

            excess = height - target
            excess >= 2  ->  full adder  (3 bits in, sum here + carry to col+1: -2)
            excess == 1  ->  half adder  (2 bits in, sum here + carry to col+1: -1)

        That "no further than" is the whole point of Dadda over Wallace: Wallace
        compresses every column as hard as it can at every opportunity and spends
        more compressors to get to the same place.

        Reduction stops at height 2. The remaining two rows are summed by
        generate_final_addition(), which emits the final carry-propagate adder.

        Columns are visited left-to-right within a stage so that carries pushed
        into column j+1 are counted in that column's height before it is reduced.

        Args:
            self: The instance of the DaddaTree class.
            bit_groups: A dictionary mapping column index -> list of bit signal names.
            N: The buswidth.

        Returns:
            bit_groups: The reduced bit groups, every column at height <= 2.
        '''
        max_digits_idx = len(str(2 * N - 1))

        max_height = max(len(group) for group in bit_groups.values())

        # Stage targets: every Dadda number strictly below the starting height,
        # walked downwards and terminating at 2.
        dadda_numbers = self.generate_dadda_numbers(100)
        stage_targets = sorted(
            (d for d in dadda_numbers if 2 <= d < max_height), reverse=True
        )

        # Per-column operation counter, so every generated wire name is unique
        # across stages (a column can be touched in several stages).
        op_seq = {bit_idx: 0 for bit_idx in range(2 * N)}

        def _emit(bit_idx, kind):
            '''Emit one compressor on column bit_idx. kind is 'fa' or 'ha'.'''
            op_seq[bit_idx] += 1
            formatted_idx = str(bit_idx).zfill(max_digits_idx)
            formatted_op = str(op_seq[bit_idx]).zfill(2)
            sum_name = f'w_sum_{formatted_idx}_{formatted_op}'
            carry_name = f'w_carry_{formatted_idx}_{formatted_op}'
            self.instruction(f'wire {sum_name}, {carry_name};')

            if kind == 'fa':
                a, b, c = bit_groups[bit_idx][:3]
                bit_groups[bit_idx] = bit_groups[bit_idx][3:]
                self.instruction(
                    f'math_adder_carry_save CSA_{formatted_idx}_{formatted_op}'
                    f'(.i_a({a}), .i_b({b}), .i_c({c}), '
                    f'.ow_sum({sum_name}), .ow_carry({carry_name}));'
                )
            else:
                a, b = bit_groups[bit_idx][:2]
                bit_groups[bit_idx] = bit_groups[bit_idx][2:]
                self.instruction(
                    f'math_adder_half       HA__{formatted_idx}_{formatted_op}'
                    f'(.i_a({a}), .i_b({b}), '
                    f'.ow_sum({sum_name}), .ow_carry({carry_name}));'
                )

            # Sum stays in this column, carry advances one column.
            bit_groups[bit_idx].append(sum_name)
            bit_groups[bit_idx + 1].append(carry_name)

        for stage, target in enumerate(stage_targets, start=1):
            self.comment(f'Dadda reduction stage {stage}: max column height {target}')
            for bit_idx in range(2 * N - 1):
                excess = len(bit_groups[bit_idx]) - target
                while excess > 0:
                    # Consume oldest bits first; freshly produced sums are appended
                    # to the tail and so are naturally deferred to the next stage.
                    _emit(bit_idx, 'fa' if excess >= 2 else 'ha')
                    excess = len(bit_groups[bit_idx]) - target
            self.instruction('')

        return bit_groups


    def verilog(self, file_path):  # sourcery skip: extract-duplicate-method
        N = self.buswidth

        bit_groups = self.partial_products(N)
        bit_groups = self.dadda_reduction(bit_groups, N)
        # Brent-Kung CPA rather than the ripple chain: the reduction tree is
        # log-depth, so an O(N) ripple would dominate the critical path and
        # negate it. See generate_final_addition_bk().
        self.generate_final_addition_bk(bit_groups, N)

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')
