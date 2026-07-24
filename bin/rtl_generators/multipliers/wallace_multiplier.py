# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: WallaceTree
# Purpose: Wallace Multiplier implementation
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



class WallaceTree(Module, MultiplierMixin):
    module_str = 'math_multiplier_wallace_tree'
    param_str = 'parameter int N=8'
    port_str = '''
    input  [N-1:0]    i_multiplier,
    input  [N-1:0]    i_multiplicand,
    output [2*N-1:0]  ow_product
    '''

    def __init__(self, type, buswidth):
        Module.__init__(self, module_name=self.module_str)
        self.buswidth = buswidth
        self.type = type
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.params.set_param_value('N', self.buswidth)
        if type == 'csa':
            self.module_name = f'{self.module_name}_csa_{str(self.buswidth).zfill(3)}'
        else:
            self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'


    def wallace_reduction(self, bit_groups, type, N):
        '''
        Performs Wallace reduction on the given bit groups.

        This method applies Wallace reduction to the bit groups, reducing the number of bits in each group by performing addition operations using either full adders or carry-save adders based on the specified type.

        Args:
            self: The instance of the WallaceMultiplier class.
            bit_groups: A dictionary containing the bit groups to be reduced.
            type: The type of adder to be used ('fa' for full adder, 'csa' for carry-save adder).
            N: The buswidth.

        Returns:
            bit_groups: A dictionary containing the reduced bit groups.

        Example:
        ```python
        multiplier = WallaceMultiplier()
        bit_groups = {...}  # Populate the bit groups dictionary
        type = 'fa'  # Set the type of adder
        N = 8  # Set the buswidth
        reduced_bit_groups = multiplier.wallace_reduction(bit_groups, type, N)
        print(reduced_bit_groups)        
        '''
        self.comment('Partial products reduction using Wallace tree')

        max_digits_idx = len(str(2 * N - 1))

        # Wallace reduces in LAYERS. Within one layer every column is partitioned
        # into groups of three and ALL groups are compressed simultaneously:
        #
        #   3 bits  -> 3:2 compressor (sum stays, carry goes to column+1)
        #   2 bits  -> half adder     (sum stays, carry goes to column+1)
        #   1 bit   -> passes through untouched
        #
        # Layers repeat until every column is at height 2. The two surviving rows
        # are summed by the carry-propagate adder in generate_final_addition().
        #
        # That simultaneity is what makes it a Wallace tree and what distinguishes
        # it from Dadda: Wallace compresses everything it can as early as it can,
        # so it reaches height 2 in the fewest LAYERS but spends more compressors.
        # Dadda defers, using per-stage target heights to spend the FEWEST
        # compressors. Reducing greedily column-by-column in a single pass would
        # land on Dadda's compressor count and lose the distinction entirely.
        #
        # Reduction MUST stop at height 2. An earlier revision followed the 3:2
        # loop with a `while len == 2` half-adder loop that collapsed every column
        # to a single bit. The arithmetic was correct -- carries ripple into
        # column+1, which is processed later -- but it degenerated into a linear
        # carry-save array with a ripple spine, and left generate_final_addition()
        # with nothing to do, so no CPA was emitted at all.
        layer = 0
        while max(len(bit_groups[j]) for j in range(2 * N)) > 2:
            layer += 1
            self.comment(f'Wallace reduction layer {layer}')
            # One extra slot as the carry sink for the top column (see below).
            next_groups = {j: [] for j in range(2 * N + 1)}

            for bit_idx in range(2 * N):
                bits = bit_groups[bit_idx]
                pos = 0
                op = 0
                formatted_idx = str(bit_idx).zfill(max_digits_idx)

                # Every pair is compressed, including columns already at height 2.
                # Skipping those looks like a saving but is not: a passed-through
                # pair immediately receives a carry from the column below, becomes
                # a 3, and has to be reduced next layer anyway -- and so on. Adding
                # that guard took the 8x8 tree from 4 layers to 9. Compressing
                # everything every layer is what buys Wallace its log depth; the
                # surplus half adders are exactly the price Wallace pays over Dadda.
                while len(bits) - pos >= 2:
                    op += 1
                    tag = f'{formatted_idx}_{layer}_{str(op).zfill(2)}'
                    sum_name = f'w_sum_{tag}'
                    carry_name = f'w_carry_{tag}'

                    if len(bits) - pos >= 3:
                        a, b, c = bits[pos:pos + 3]
                        pos += 3
                        self.instruction(f'wire {sum_name}, {carry_name};')
                        if type == 'fa':
                            self.instruction(f'math_adder_full       FA_{tag}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));')
                        else:
                            self.instruction(f'math_adder_carry_save CSA_{tag}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));')
                    else:
                        a, b = bits[pos:pos + 2]
                        pos += 2
                        self.instruction(f'wire {sum_name}, {carry_name};')
                        self.instruction(f'math_adder_half       HA_{tag}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_carry({carry_name}));')

                    next_groups[bit_idx].append(sum_name)
                    next_groups[bit_idx + 1].append(carry_name)

                # Odd bit left over: it is not compressed this layer, it just
                # advances to the next one.
                next_groups[bit_idx].extend(bits[pos:])

            # The top column MUST be reduced too, not just used as a carry sink.
            # It gains a carry from column 2N-2 on every layer, so left alone it
            # climbs to 3-4 bits and generate_final_addition() -- which handles at
            # most two operands plus a carry-in -- silently drops the rest. That is
            # exactly what broke the 8x8 and 16x16 products.
            #
            # Its own carry-out lands in slot 2N and is discarded: an N x N product
            # is strictly less than 2**(2N), so a carry out of the top column is
            # provably zero. The wire is left driven and unread, matching the
            # existing treatment of w_carry_{2N-1} in generate_final_addition().
            next_groups.pop(2 * N, None)
            bit_groups = next_groups
            self.instruction('')

        return bit_groups


    def verilog(self, file_path):  # sourcery skip: extract-duplicate-method
        N = self.buswidth

        bit_groups = self.partial_products(N)
        bit_groups = self.wallace_reduction(bit_groups, self.type, N)
        # Brent-Kung CPA rather than the ripple chain: the reduction tree is
        # log-depth, so an O(N) ripple would dominate the critical path and
        # negate it. See generate_final_addition_bk().
        self.generate_final_addition_bk(bit_groups, N)

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')
