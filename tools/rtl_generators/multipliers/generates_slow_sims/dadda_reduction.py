import itertools
import math
from rtl_generators.verilog.module import Module


class DaddaReduction(Module):
    module_str = 'math_multiplier_dadda_reduction'
    param_str = 'parameter N=8'
    port_str = '''
    input  [N-1:0][N-1:0] i_pp,
    output [2*N-1:0]      ow_product
    '''


    def __init__(self, buswidth):
        self.buswidth = buswidth
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.params.set_param_value('N', self.buswidth)
        self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'


    @staticmethod
    def generate_dadda_numbers(n=100):
        """
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
        """
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
        """
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
        """
        return 1 if n is None else next((num for num in dadda_numbers if n > num), 1)


    def dadda_reduction(self, N):
        # Recreate the bit_groups
        bit_groups = {i: [] for i in range(2 * N)}
        for i, j in itertools.product(range(N), range(N)):
            bit_groups[i+j].append(f'i_pp[{i}][{j}]')

        max_digits_idx = len(str(2 * N - 1))
        max_digits_len = len(str(max(len(group) for group in bit_groups.values())))

        # Generate the first 100 Dadda numbers
        dadda_numbers = self.generate_dadda_numbers(4)
        dadda_numbers = dadda_numbers[::-1]

        for bit_idx in range(2 * N - 1):
            goal = self.next_smaller_dadda_number(dadda_numbers, len(bit_groups[bit_idx]))
            # print(f'{goal=}')
            while len(bit_groups[bit_idx]) > goal:
                while len(bit_groups[bit_idx]) > 2:
                    a, b, c = bit_groups[bit_idx][:3]
                    formatted_idx = str(bit_idx).zfill(max_digits_idx)
                    formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

                    sum_name = f"w_sum_{formatted_idx}_{formatted_len}"
                    carry_name = f"w_carry_{formatted_idx}_{formatted_len}"

                    self.instruction(f"wire {sum_name}, {carry_name};")
                    self.instruction(f"math_adder_carry_save CSA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));")

                    bit_groups[bit_idx] = bit_groups[bit_idx][3:]
                    bit_groups[bit_idx].append(sum_name)
                    bit_groups[bit_idx + 1].append(carry_name)

                while len(bit_groups[bit_idx]) == 2:
                    a, b = bit_groups[bit_idx][:2]
                    formatted_idx = str(bit_idx).zfill(max_digits_idx)
                    formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

                    sum_name = f"w_sum_{formatted_idx}_{formatted_len}"
                    carry_name = f"w_carry_{formatted_idx}_{formatted_len}"

                    self.instruction(f"wire {sum_name}, {carry_name};")
                    self.instruction(f"math_adder_half HA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_carry({carry_name}));")

                    bit_groups[bit_idx] = bit_groups[bit_idx][2:]
                    bit_groups[bit_idx].append(sum_name)
                    bit_groups[bit_idx + 1].append(carry_name)

        self.instruction("")
        return bit_groups


    def generate_final_addition(self, bit_groups, N):
        # This function will generate the final addition stage.
        max_digits_bit = len(str(2*N - 1))

        # Prepare output for bit by bit addition
        self.comment("// Final addition stage")
        previous_carry = None
        for bit in range(2*N):
            formatted_bit = str(bit).zfill(max_digits_bit)

            sum_name = f"ow_sum_{formatted_bit}"
            carry_name = f"ow_carry_{formatted_bit}"
            variables = bit_groups.get(bit, [])

            # if no variables are present for this bit, just output a 0
            if not variables:
                self.instruction(f"assign {sum_name} = 1'b0;")
                continue

            if len(variables) == 1:
                self.instruction(f"assign {sum_name} = {variables[0]};")
            else:
                # Wire the sum and carry
                self.instruction(f"wire {sum_name}, {carry_name};")
                
                ic_value = previous_carry or "1'b0"
                fa_line = f"math_adder_full FA_{formatted_bit}(.i_a({variables[0]}), .i_b({variables[1]}), .i_c({ic_value}), .ow_sum({sum_name}), .ow_c({carry_name}));"
                self.instruction(fa_line)

            previous_carry = carry_name
        self.instruction("")


    def generate_final_assignments(self, N):
        self.instruction("// Final product assignment")

        # Calculate the maximum number of digits required
        max_digits = len(str(2 * N - 1))

        for i in range(2 * N):
            formatted_idx = str(i).zfill(max_digits)
            self.instruction(f"assign ow_product[{i}] = ow_sum_{formatted_idx};")

        self.instruction("")

    def verilog(self, file_path):
        # sourcery skip: merge-list-append, move-assign-in-block
        N = self.buswidth

        bit_groups = self.dadda_reduction(N)
        self.generate_final_addition(bit_groups,N)
        self.generate_final_assignments(N)

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')

