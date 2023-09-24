import itertools
import math
from rtl_generators.verilog.module import Module


class WallaceTree(Module):
    module_str = 'math_multiplier_wallace_tree'
    param_str = 'parameter N=8'
    port_str = '''
    input  [N-1:0]    i_multiplier,
    input  [N-1:0]    i_multiplicand,
    output [2*N-1:0]  ow_product
    '''

    def __init__(self, type, buswidth):
        self.buswidth = buswidth
        self.type = type
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.params.set_param_value('N', self.buswidth)
        if type == 'csa':
            self.module_name = f'{self.module_name}_csa_{str(self.buswidth).zfill(3)}'
        else:
            self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'


    def partial_products(self):
        """
        Generates partial products for a Dadda multiplier.

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
        """
        # Define bit groups here, then populate it as we generate the partial products
        N = self.buswidth
        bit_groups = {i: [] for i in range(2 * N)}

        # Determine the max number of digits needed
        max_digits = len(str(N - 1))
        self.comment('Partial Products')
        for i, j in itertools.product(range(N), range(N)):
            formatted_i = str(i).zfill(max_digits)
            formatted_j = str(j).zfill(max_digits)

            self.instruction(f"wire w_pp_{formatted_i}_{formatted_j} = i_multiplier[{i:2}] & i_multiplicand[{j:2}];")
            bit_groups[i + j].append(f"w_pp_{formatted_i}_{formatted_j}")
            # bit_groups[i+j].append(f'w_pp[{formatted_i}][{formatted_j}]')

        self.instruction('')
        return bit_groups


    def wallace_reduction(self, bit_groups, type, N):
        self.instruction("// Partial products reduction using Wallace tree")

        max_digits_idx = len(str(2 * N - 1))
        max_digits_len = len(str(max(len(group) for group in bit_groups.values())))
        for bit_idx in range(2 * N - 1):
            while len(bit_groups[bit_idx]) > 2:
                a, b, c = bit_groups[bit_idx][:3]
                formatted_idx = str(bit_idx).zfill(max_digits_idx)
                formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

                sum_name = f"w_sum_{formatted_idx}_{formatted_len}"
                carry_name = f"w_carry_{formatted_idx}_{formatted_len}"

                self.instruction(f"wire {sum_name}, {carry_name};\n")

                if type == 'fa':
                    self.instruction(f"math_adder_full FA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));")
                else:
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

            sum_name = f"w_sum_{formatted_bit}"
            carry_name = f"w_carry_{formatted_bit}"
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
        self.instruction("// Final product assignment\n")

        # Calculate the maximum number of digits required
        max_digits = len(str(2 * N - 1))

        for i in range(2 * N):
            formatted_idx = str(i).zfill(max_digits)
            self.instruction(f"assign ow_product[{i}] = w_sum_{formatted_idx};")

        self.instruction("")

    def verilog(self, file_path):  # sourcery skip: extract-duplicate-method
        N = self.buswidth

        bit_groups = self.partial_products()
        bit_groups = self.wallace_reduction(bit_groups, self.type, N)
        self.generate_final_addition(bit_groups,N)
        self.generate_final_assignments(N)

        self.instruction('')
        self.instruction('// synopsys translate_off')
        self.instruction('initial begin')
        self.instruction('    $dumpfile("dump.vcd");')
        self.instruction(f'    $dumpvars(0, {self.module_name});')
        self.instruction('end')
        self.instruction('// synopsys translate_on')
        self.instruction('')

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')
