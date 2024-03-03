import sys
import os
import subprocess
import io

base_path = '/home/sean/github/RTL_Design_Projects/tools/rtl_generators/'

# Get the directory containing verilog_parser.py
module_dir = os.path.abspath(base_path)

# Add the directory to the sys.path
sys.path.append(module_dir)


from verilog.module import Module


class SumLogic(Module):
    module_str = 'math_adder_brent_kung_sum'
    param_str = 'parameter int N=8'
    port_str = '''
    input  logic [N:0]   i_p,
    input  logic [N:0]   i_gg,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
    '''

    def __init__(self, buswidth):
        self.buswidth = buswidth
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)


    def verilog(self, file_path):
        # sourcery skip: extract-duplicate-method
        self.instruction('// Loop over bits')
        self.instruction('genvar k;')
        self.instruction('generate')
        self.instruction('    for (k = 0; k < N; k=k+1) begin : gen_loop ')
        self.instruction('        assign ow_sum[k] = i_gg[k] ^ i_p[k+1];')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')
        self.instruction('assign ow_carry = i_gg[N];')

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')


