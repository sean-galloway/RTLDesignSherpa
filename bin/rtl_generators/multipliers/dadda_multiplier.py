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

        The function generates a list of Dadda numbers based on the given value of `n`. The initial list contains the numbers 1 and 2. The function then iterates `n - 2` times and calculates the next Dadda number based on the previous number in the list. If the index is even, the next number is calculated by multiplying the previous number by 1.5 and rounding up. If the index is odd, the next number is calculated by multiplying the previous number by 4/3 and rounding up. The generated Dadda numbers are appended to the list and returned.

        Args:
            n (int): The number of Dadda numbers to generate. Defaults to 100.

        Returns:
            list: A list of Dadda numbers.

        Example:
        ```python
        dadda_nums = generate_dadda_numbers(10)
        print(dadda_nums)
        # Output: [1, 2, 3, 4, 6, 9, 14, 21, 32, 48]
        '''
        dadda_numbers = [1, 2]
        for i, _ in enumerate(range(n - 2)):  # We already have the first two numbers
            next_dadda = (
                math.ceil(dadda_numbers[-1] * 1.5)
                if i % 2 == 0
                else math.ceil(dadda_numbers[-1] * 4 / 3)
            )
            dadda_numbers.append(next_dadda)
        return dadda_numbers


    @staticmethod
    def next_smaller_dadda_number(dadda_numbers, n):
        '''
        Returns the next smaller Dadda number from a given list of Dadda numbers.

        The function takes a list of Dadda numbers and a target number `n`. It returns the next smaller Dadda number from the list that is less than `n`. If no such number exists, it returns 1. If `n` is None, it returns 1.

        Args:
            dadda_numbers (list): A list of Dadda numbers.
            n (int): The target number.

        Returns:
            int: The next smaller Dadda number less than `n`, or 1 if no such number exists or `n` is None.

        Example:
        ```python
        dadda_nums = [1, 2, 3, 4, 6, 9, 14, 21, 32, 48]
        next_smaller = next_smaller_dadda_number(dadda_nums, 10)
        print(next_smaller)
        # Output: 9
        '''
        return 1 if n is None else next((num for num in dadda_numbers if n > num), 1)


    def dadda_reduction(self, bit_groups, N):
        '''
        Performs Dadda reduction on the given bit groups.

        This method applies Dadda reduction to the bit groups, reducing the number of bits in each group by performing addition operations.

        Args:
            self: The instance of the DaddaMultiplier class.
            bit_groups: A dictionary containing the bit groups to be reduced.
            N: The buswidth.

        Returns:
            bit_groups: A dictionary containing the reduced bit groups.

        Example:
        ```python
        multiplier = DaddaMultiplier()
        bit_groups = {...}  # Populate the bit groups dictionary
        N = 8  # Set the buswidth
        reduced_bit_groups = multiplier.dadda_reduction(bit_groups, N)
        print(reduced_bit_groups)        
        '''
        max_digits_idx = len(str(2 * N - 1))
        max_digits_len = len(str(max(len(group) for group in bit_groups.values())))

        # Generate the first 100 Dadda numbers
        dadda_numbers = self.generate_dadda_numbers(100)
        dadda_numbers = dadda_numbers[::-1]
        self.comment('Dadda Reduction stage')
        for bit_idx in range(2 * N - 1):
            goal = self.next_smaller_dadda_number(dadda_numbers, len(bit_groups[bit_idx]))
            # print(f'{goal=}')
            while len(bit_groups[bit_idx]) > goal:
                while len(bit_groups[bit_idx]) > 2:
                    a, b, c = bit_groups[bit_idx][:3]
                    formatted_idx = str(bit_idx).zfill(max_digits_idx)
                    formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

                    sum_name = f'w_sum_{formatted_idx}_{formatted_len}'
                    carry_name = f'w_carry_{formatted_idx}_{formatted_len}'

                    self.instruction(f'wire {sum_name}, {carry_name};')
                    self.instruction(f'math_adder_carry_save CSA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));')

                    bit_groups[bit_idx] = bit_groups[bit_idx][3:]
                    bit_groups[bit_idx].append(sum_name)
                    bit_groups[bit_idx + 1].append(carry_name)

                while len(bit_groups[bit_idx]) == 2:
                    a, b = bit_groups[bit_idx][:2]
                    formatted_idx = str(bit_idx).zfill(max_digits_idx)
                    formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

                    sum_name = f'w_sum_{formatted_idx}_{formatted_len}'
                    carry_name = f'w_carry_{formatted_idx}_{formatted_len}'

                    self.instruction(f'wire {sum_name}, {carry_name};')
                    self.instruction(f'math_adder_half       HA__{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_carry({carry_name}));')

                    bit_groups[bit_idx] = bit_groups[bit_idx][2:]
                    bit_groups[bit_idx].append(sum_name)
                    bit_groups[bit_idx + 1].append(carry_name)

        self.instruction('')
        return bit_groups


    def verilog(self, file_path):  # sourcery skip: extract-duplicate-method
        N = self.buswidth

        bit_groups = self.partial_products(N)
        bit_groups = self.dadda_reduction(bit_groups, N)
        self.generate_final_addition(bit_groups,N)
        self.generate_final_assignments(N)

        self.instruction('')
        self.instruction('// synopsys translate_off')
        self.instruction('initial begin')
        self.instruction('    $dumpfile("waves.vcd");')
        self.instruction(f'    $dumpvars(0, {self.module_name});')
        self.instruction('end')
        self.instruction('// synopsys translate_on')
        self.instruction('')

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')
