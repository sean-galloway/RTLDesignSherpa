# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MultiplierMixin
# Purpose: Multiplier Mixin implementation
#
# Documentation: docs/markdown/RTLCommon/index.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

import itertools
from rtl_generators.verilog.module import Module


class MultiplierMixin():

    def partial_products(self, N):
        '''
        Generates partial products for a Dadda/Wallace multiplier.

        This method generates partial products for a Dadda multiplier by populating bit groups based on the given buswidth.

        Args:
            self: The instance of the DaddaMultiplier class.

        Returns:
            bit_groups: A dictionary containing the populated bit groups.

        Example:
        ```python
        multiplier = DaddaMultiplier()
        partial_products = multiplier.partial_products()
        print(partial_products)
        '''
        # Define bit groups here, then populate it as we generate the partial products
        bit_groups = {i: [] for i in range(2 * N)}
        # Determine the max number of digits needed
        max_digits = len(str(N - 1))
        self.comment('Partial Products')
        for i, j in itertools.product(range(N), range(N)):
            formatted_i = str(i).zfill(max_digits)
            formatted_j = str(j).zfill(max_digits)
            sig = f'w_pp_{formatted_i}_{formatted_j}'
            self.instruction(f'wire {sig} = i_multiplier[{i:2}] & i_multiplicand[{j:2}];')
            bit_groups[i + j].append(sig)

        self.instruction('')
        return bit_groups


    def partial_products_booth_radix_4(self, N):
        '''
        Generates partial products for a Booth radix-4 multiplier.

        This method generates partial products for a Booth radix-4 multiplier by populating bit groups based on the given buswidth.

        Args:
            self: The instance of the Multiplier class.

        Returns:
            bit_groups: A dictionary containing the populated bit groups.

        Example:
        ```python
        multiplier = BoothMultiplier()
        partial_products = multiplier.partial_products()
        print(partial_products)
        ```
        '''
        N_padded = N + N % 3  # Pad N to be divisible by 3
        max_idx = 2 * N + (N // 3)  # Maximum index possible after Booth encoding
        bit_groups = {i: [] for i in range(max_idx)}  # Initialize up to maximum index

        # Pad the multiplier and its 2's complement to be divisible by 3
        self.instruction(f"wire [{N_padded-1}:0] multiplier_padded = {{{{N_padded - N{{1'b0}}}}, i_multiplier}};")
        padding = f"{N_padded - N}{{1'b0}}"
        self.instruction(f'wire [{N_padded-1}:0] multiplier_padded = {{ {padding}, i_multiplier }};')


        max_digits = len(str(N - 1))
        self.comment('Partial Products using Booth Radix-4')

        for i in range(N_padded):
            formatted_i = str(i).zfill(max_digits)
            self.instruction(f'wire [2:0] booth_group_{formatted_i} = multiplier_padded[{i+2}:{i}];')
            self.instruction(f'wire [1:0] booth_encoded_{formatted_i};')
            self.instruction(f'math_multiplier_booth_radix_4_encoder booth_encoder_{formatted_i} (.booth_group(booth_group_{formatted_i}), .booth_encoded(booth_encoded_{formatted_i}));')

        for i, j in itertools.product(range(N_padded), range(N)):
            formatted_i = str(i).zfill(max_digits)
            formatted_j = str(j).zfill(max_digits)
            self.instruction(f'wire w_pp_{formatted_i}_{formatted_j} = booth_encoded_{formatted_i} * i_multiplicand[{j:2}];')

            # Dynamically initialize keys if they don't exist
            if i + j not in bit_groups:
                bit_groups[i + j] = []
            bit_groups[i + j].append(f'w_pp_{formatted_i}_{formatted_j}')

        self.instruction('')
        return bit_groups


    def generate_final_addition(self, bit_groups, N):
        '''
        Generates the final addition stage for the multiplier.

        This function generates the final addition stage by performing bit by bit addition based on the given bit groups.

        Args:
            self: The instance of the MultiplierMixin class.
            bit_groups: A dictionary containing the bit groups.
            N: The buswidth.

        Returns:
            None

        Example:
        ```python
        multiplier = MultiplierMixin()
        bit_groups = {...}  # Populate the bit groups dictionary
        N = 8  # Set the buswidth
        multiplier.generate_final_addition(bit_groups, N)
        '''
        # RIPPLE carry-propagate adder. Retained for reference and for any
        # generator that wants the smallest possible final stage, but the Wallace
        # and Dadda generators now call generate_final_addition_bk() instead --
        # this chain is O(N) and would dominate their log-depth reduction trees.
        # This function will generate the final addition stage.
        max_digits_bit = len(str(2*N - 1))

        # Prepare output for bit by bit addition
        self.comment('Final addition stage')
        previous_carry = None
        for bit in range(2*N):
            formatted_bit = str(bit).zfill(max_digits_bit)

            sum_name = f'w_sum_{formatted_bit}'
            carry_name = f'w_carry_{formatted_bit}'
            variables = bit_groups.get(bit, [])

            # Operands for this column: whatever the reduction left here (0, 1 or 2
            # bits), plus the carry rippling in from the column below.
            #
            # The incoming carry MUST be consumed even when the column itself is
            # nearly empty. Earlier revisions dropped it in the 0-bit and 1-bit
            # cases, which was invisible only because the reduction stage used to
            # collapse every column to height 1, so no carries ever reached here.
            # A real height-2 reduction makes that path live, and dropping a carry
            # silently truncates the product.
            operands = list(variables)
            if previous_carry is not None:
                operands.append(previous_carry)

            # A column with fewer than two operands cannot generate a carry, so the
            # carry wire is a literal zero. Propagate None rather than that wire's
            # name, otherwise the next column would instantiate an adder against a
            # constant 0 -- which is what the Wallace path (height-1 columns
            # throughout) would otherwise now do for every single bit.
            if not operands:
                self.instruction(f"wire {sum_name} = 1'b0;")
                self.instruction(f"wire {carry_name} = 1'b0;")
                previous_carry = None
                continue

            if len(operands) == 1:
                self.instruction(f'wire {sum_name} = {operands[0]};')
                self.instruction(f"wire {carry_name} = 1'b0;")
                previous_carry = None
                continue

            if len(operands) == 2:
                self.instruction(f'wire {sum_name}, {carry_name};')
                self.instruction(
                    f'math_adder_half       HA__{formatted_bit}'
                    f'(.i_a({operands[0]}), .i_b({operands[1]}), '
                    f'.ow_sum({sum_name}), .ow_carry({carry_name}));'
                )
            else:
                self.instruction(f'wire {sum_name}, {carry_name};')
                self.instruction(
                    f'math_adder_full       FA__{formatted_bit}'
                    f'(.i_a({operands[0]}), .i_b({operands[1]}), .i_c({operands[2]}), '
                    f'.ow_sum({sum_name}), .ow_carry({carry_name}));'
                )

            previous_carry = carry_name
        self.instruction('')


    def generate_final_addition_bk(self, bit_groups, N):
        '''
        Emits the final carry-propagate addition using a Brent-Kung adder.

        After a Wallace or Dadda reduction every column holds at most two bits.
        Those two bits per column are exactly the two rows of a carry-save
        representation, so the product is their sum. This method packs them into
        two 2N-wide vectors and hands them to math_adder_brent_kung_{2N}.

        This replaces generate_final_addition() + generate_final_assignments(),
        which together emit a RIPPLE chain. The ripple is correct but its carry
        walks all 2N columns, so it costs O(N) and dominates the critical path --
        which throws away the whole point of spending a log-depth reduction tree.
        Brent-Kung is O(log N), so the adder stops being the bottleneck.

        Note the width: an N x N product is 2N bits, so an 8-bit multiplier needs
        the 16-bit adder, 16-bit needs 32, and 32-bit needs 64.

        Args:
            self: The instance of the MultiplierMixin class.
            bit_groups: Reduced bit groups; every column must be at height <= 2.
            N: The buswidth.

        Returns:
            None
        '''
        width = 2 * N
        adder = f'math_adder_brent_kung_{str(width).zfill(3)}'

        over = {b: len(bit_groups.get(b, [])) for b in range(width)
                if len(bit_groups.get(b, [])) > 2}
        if over:
            raise ValueError(
                f'{adder}: reduction left columns above height 2: {over}. '
                'The CPA consumes exactly two rows; a taller column would be '
                'silently truncated.'
            )

        self.comment('Final addition stage: two reduced rows into a Brent-Kung CPA')

        # Row 0 takes the first bit of each column, row 1 the second. Columns
        # with fewer bits contribute a literal zero in that position.
        for row in (0, 1):
            bits = []
            for bit in range(width):
                col = bit_groups.get(bit, [])
                bits.append(col[row] if len(col) > row else "1'b0")
            # Concatenation is MSB-first.
            packed = ', '.join(reversed(bits))
            self.instruction(f'wire [{width - 1}:0] w_cpa_row{row} = {{{packed}}};')

        self.instruction('')
        # The carry-out is unused: an N x N product is strictly less than 2**(2N),
        # so the adder cannot carry out of the top column.
        self.instruction('/* verilator lint_off UNUSEDSIGNAL */')
        self.instruction('wire w_cpa_carry_unused;')
        self.instruction('/* verilator lint_on UNUSEDSIGNAL */')
        self.instruction(
            f'{adder} #(.N({width})) u_final_cpa ('
            f'.i_a(w_cpa_row0), .i_b(w_cpa_row1), .i_c(1\'b0), '
            f'.ow_sum(ow_product), .ow_carry(w_cpa_carry_unused));'
        )
        self.instruction('')


    def generate_final_assignments(self, N):
        '''
        This function assigns the final product values to the output based on the calculated sums from the final addition stage.

        Args:
            self: The instance of the MultiplierMixin class.
            N: The buswidth.

        Returns:
            None

        Example:
        ```python
        multiplier = MultiplierMixin()
        N = 8  # Set the buswidth
        multiplier.generate_final_assignments(N)
        '''
        self.comment('Final product assignment')

        # Calculate the maximum number of digits required
        max_digits = len(str(2 * N - 1))

        for i in range(2 * N):
            formatted_idx = str(i).zfill(max_digits)
            self.instruction(f'assign ow_product[{i:2}] = w_sum_{formatted_idx};')

        self.instruction('')
