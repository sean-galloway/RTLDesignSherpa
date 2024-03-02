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
        max_digits_len = len(str(max(len(group) for group in bit_groups.values())))
        for bit_idx in range(2 * N - 1):
            while len(bit_groups[bit_idx]) > 2:
                a, b, c = bit_groups[bit_idx][:3]
                formatted_idx = str(bit_idx).zfill(max_digits_idx)
                formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

                sum_name = f'w_sum_{formatted_idx}_{formatted_len}'
                carry_name = f'w_carry_{formatted_idx}_{formatted_len}'

                self.instruction(f'wire {sum_name}, {carry_name};\n')

                if type == 'fa':
                    self.instruction(f'math_adder_full       FA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));')
                else:
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
                self.instruction(f'math_adder_half       HA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_carry({carry_name}));')

                bit_groups[bit_idx] = bit_groups[bit_idx][2:]
                bit_groups[bit_idx].append(sum_name)
                bit_groups[bit_idx + 1].append(carry_name)


        self.instruction('')
        return bit_groups


    def verilog(self, file_path):  # sourcery skip: extract-duplicate-method
        N = self.buswidth

        bit_groups = self.partial_products(N)
        bit_groups = self.wallace_reduction(bit_groups, self.type, N)
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
