import itertools
import math
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

            # if no variables are present for this bit, just output a 0
            if not variables:
                self.instruction(f"wire {sum_name} = 1'b0;")
                self.instruction(f"wire {carry_name} = 1'b0;")
                continue

            if len(variables) == 1:
                self.instruction(f'wire {sum_name} = {variables[0]};')
                self.instruction(f"wire {carry_name} = 1'b0;")
            else:
                # Wire the sum and carry
                self.instruction(f'wire {sum_name}, {carry_name};')
                
                ic_value = previous_carry or "1'b0"
                fa_line = f'math_adder_full FA_{formatted_bit}(.i_a({variables[0]}), .i_b({variables[1]}), .i_c({ic_value}), .ow_sum({sum_name}), .ow_carry({carry_name}));'
                self.instruction(fa_line)

            previous_carry = carry_name
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
